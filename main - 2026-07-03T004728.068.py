import os
import asyncio
import random
import time
import logging
import re
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from collections import defaultdict, Counter
from datetime import datetime
from html import escape as escape_html

from dotenv import load_dotenv
from telethon import TelegramClient, events, errors, Button
from motor.motor_asyncio import AsyncIOMotorClient
from pymongo import ReturnDocument
from deep_translator import GoogleTranslator

load_dotenv()

# ==========================================
# ⚙️ CONFIGURATIONS
# ==========================================
MONGO_URI = os.getenv("MONGO_URI")
APP_ID = int(os.getenv("APP_ID"))
APP_HASH = os.getenv("APP_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
OWNER_ID = int(os.getenv("OWNER_ID"))
SPECIFIC_GROUP = int(os.getenv("SPECIFIC_GROUP"))
SPECIFIC_CONTROL_GROUP = int(os.getenv("SPECIFIC_CONTROL_GROUP", SPECIFIC_GROUP))

STORAGE_CHANNEL = SPECIFIC_CONTROL_GROUP
TAGLINE = "\n\nAlso try this @Imjustkidding_bot"
CARDS_PER_PAGE = 5

# ==========================================
# 🌐 Render Port-Binding Fix
# ==========================================
# Render's "Web Service" type kills/restarts deploys that never open a port.
# Telethon bots don't need a port, so we spin up a tiny dummy HTTP server
# just so Render's port scanner is satisfied. Harmless no-op if unused.
def _start_health_server():
    port = int(os.getenv("PORT", "8080"))

    class _Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.end_headers()
            self.wfile.write(b"OK - bot is running")

        def log_message(self, *args):
            pass  # silence default request logging

    try:
        server = HTTPServer(("0.0.0.0", port), _Handler)
        server.serve_forever()
    except Exception as e:
        logging.error(f"Health server failed to start: {e}")

# ==========================================
# MongoDB
# ==========================================
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]

users_catcher_col = db["users_catcher_data"]
characters_base_col = db["characters_base_data"]
groups_config_col = db["groups_catcher_config"]
groups_col = db["active_groups"]
groups_counters_col = db["groups_msg_counters"]
spawn_disabled_col = db["spawn_disabled_chats"]
banned_users_col = db["banned_users"]

# ==========================================
# Rarity System (7 Tiers)
# ==========================================
RARITY_TIERS = [
    {"name": "Bear",      "emoji": "🧸", "value": 1000},
    {"name": "Rainbow",   "emoji": "🌈", "value": 800},
    {"name": "Crossverse","emoji": "⚡️", "value": 600},
    {"name": "Trident",   "emoji": "🔱", "value": 400},
    {"name": "Koinobori", "emoji": "🎏", "value": 200},
    {"name": "Medium",    "emoji": "💛", "value": 100},
    {"name": "Lower",     "emoji": "💜", "value": 50}
]
RARITY_EMOJI = {t["name"]: t["emoji"] for t in RARITY_TIERS}
RARITY_ORDER = {t["name"]: idx for idx, t in enumerate(RARITY_TIERS)}

def classify_rarity(rarity_str):
    if not rarity_str: return "Lower"
    for tier in RARITY_TIERS:
        if tier["name"].lower() in rarity_str.lower():
            return tier["name"]
    return "Lower"

def get_rarity_value(rarity_name):
    for tier in RARITY_TIERS:
        if tier["name"] == rarity_name:
            return tier["value"]
    return 50

# ==========================================
# Global Variables
# ==========================================
bot1 = None
active_spawns = {}
spawn_locks = defaultdict(asyncio.Lock)

# ==========================================
# Helpers
# ==========================================
async def reply_tag(event, text, **kwargs):
    if TAGLINE not in text: text += TAGLINE
    await event.reply(text, **kwargs)

def bl(mm_text, en_text):
    """Bilingual message helper: Myanmar text + English text stacked together."""
    return f"{mm_text}\n\n🇬🇧 {en_text}"

async def get_mention(client, user_id, name=None):
    if name is None:
        try:
            user = await client.get_entity(user_id)
            first = getattr(user, 'first_name', '') or ''
            last = getattr(user, 'last_name', '') or ''
            name = f"{first} {last}".strip() or getattr(user, 'username', '') or f"User {user_id}"
        except:
            name = f"User {user_id}"
    return f"<a href='tg://user?id={user_id}'><b>{escape_html(name)}</b></a>"

def normalize_name(text):
    if not text: return ""
    text = text.lower().strip()
    text = re.sub(r'[^\w\s]', '', text)
    text = re.sub(r'\s+', ' ', text)
    return text.strip()

async def ensure_user_registered(user_id, fullname):
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {
            "$setOnInsert": {
                "wallet_balance": 0,
                "total_caught": 0,
                "harem": [],
                "fullname": fullname,
                "fav_card": None,
                "rarity_filter": None,
                "rarity_counts": {t["name"]: 0 for t in RARITY_TIERS},
                "last_daily": 0,
                "last_hunt": 0
            }
        },
        upsert=True
    )

async def get_balance(user_id):
    doc = await users_catcher_col.find_one({"user_id": user_id})
    if not doc:
        await users_catcher_col.insert_one({"user_id": user_id, "wallet_balance": 0, "total_caught": 0, "harem": []})
        return 0
    return doc.get("wallet_balance", 0)

async def add_balance(user_id, amount):
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": amount}}, upsert=True)

# ==========================================
# Character Spawn System
# ==========================================
async def spawn_cleaner():
    while True:
        now = time.time()
        expired = [c for c, data in active_spawns.items() if now - data["spawn_time"] > 300]
        for c in expired:
            del active_spawns[c]
        await asyncio.sleep(60)

async def trigger_dynamic_spawn(chat_id):
    if chat_id in active_spawns:
        return
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    if disabled and disabled.get("disabled", False):
        return
    all_chars = await characters_base_col.find().to_list(length=None)
    if not all_chars:
        return
    available_chars = []
    for c in all_chars:
        spawn_count = c.get('spawn_count', 0)
        spawn_limit = c.get('spawn_limit', 0)
        if spawn_limit > 0 and spawn_count >= spawn_limit:
            continue
        available_chars.append(c)
    if not available_chars:
        return
    weights = []
    for c in available_chars:
        rarity = classify_rarity(c.get("rarity", "Lower"))
        weight = 100 - (RARITY_ORDER.get(rarity, 6) * 10)
        weights.append(max(1, weight))
    chosen = random.choices(available_chars, weights=weights, k=1)[0]
    storage_msg_id = chosen.get("storage_msg_id")
    if not storage_msg_id:
        return
    try:
        stored_msg = await bot1.get_messages(STORAGE_CHANNEL, ids=storage_msg_id)
        if not stored_msg or not stored_msg.media:
            return
    except:
        return
    await characters_base_col.update_one({"char_id": chosen["char_id"]}, {"$inc": {"spawn_count": 1}})
    caption = bl(
        "🔱 ဇာတ်ကောင်တစ်ကောင် ပေါ်လာပါပြီ!\n➕ ဖမ်းလိုက်ရန် /gases [ နာမည် ]",
        "🔱 A character has spawned in this chat!\n➕ Add to harem using /gases [ NAME ]"
    )
    sent_msg = await bot1.send_message(chat_id, caption, file=stored_msg.media)
    active_spawns[chat_id] = {
        "char_id": chosen.get("char_id"),
        "name": chosen.get("name"),
        "series": chosen.get("series", "Unknown"),
        "rarity": classify_rarity(chosen.get("rarity", "Lower")),
        "spawn_time": time.time(),
        "claimed": False,
        "spawn_msg_id": sent_msg.id
    }

# ==========================================
# HANDLERS (Functions, no decorators)
# ==========================================

async def message_counter_for_spawn(event):
    if event.is_private or event.chat_id == SPECIFIC_GROUP:
        return
    chat_id = event.chat_id
    if chat_id in active_spawns:
        return
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    if disabled and disabled.get("disabled", False):
        return
    config = await groups_config_col.find_one({"chat_id": chat_id})
    target = config.get("spawn_target", 50) if config else 50
    counter_doc = await groups_counters_col.find_one_and_update(
        {"chat_id": chat_id},
        {"$inc": {"counter": 1}},
        upsert=True,
        return_document=ReturnDocument.AFTER
    )
    if counter_doc and counter_doc.get("counter", 0) >= target:
        await groups_counters_col.update_one({"chat_id": chat_id}, {"$set": {"counter": 0}})
        await trigger_dynamic_spawn(chat_id)

# ---- /gases (or /catch) ----
async def catch_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    user_id = event.sender_id
    name = event.pattern_match.group(1).strip()
    if chat_id not in active_spawns:
        await reply_tag(event, bl("❌ ဒီချတ်ထဲမှာ ဇာတ်ကောင်မရှိသေးပါ။", "❌ No character has spawned in this chat."))
        return
    spawn_data = active_spawns[chat_id]
    if spawn_data["claimed"]:
        await reply_tag(event, bl("❌ တခြားသူက ဖမ်းသွားပြီးပါပြီ!", "❌ Already caught by someone else!"))
        return
    if time.time() - spawn_data["spawn_time"] > 300:
        del active_spawns[chat_id]
        await reply_tag(event, bl("⏱️ နောက်ကျသွားပါပြီ! ဇာတ်ကောင်ပျောက်သွားပါပြီ။", "⏱️ Too late! The character vanished."))
        return
    if normalize_name(name) != normalize_name(spawn_data["name"]):
        await reply_tag(event, bl("❌ နာမည်မှားနေပါတယ်! /w နဲ့ မှန်ကန်တဲ့ နာမည်ကို စစ်ဆေးပါ။", "❌ Wrong name! Use /w to check the exact name."))
        return
    async with spawn_locks[chat_id]:
        if active_spawns.get(chat_id, {}).get("claimed", True):
            await reply_tag(event, bl("❌ တခြားသူက ဖမ်းသွားပြီးပါပြီ!", "❌ Already caught by someone else!"))
            return
        active_spawns[chat_id]["claimed"] = True
        mention = await get_mention(bot1, user_id)
        await ensure_user_registered(user_id, mention)
        card_entry = {
            "char_id": spawn_data["char_id"],
            "name": spawn_data["name"],
            "series": spawn_data["series"],
            "rarity": spawn_data["rarity"],
            "caught_date": time.time()
        }
        await users_catcher_col.update_one(
            {"user_id": user_id},
            {
                "$push": {"harem": card_entry},
                "$inc": {
                    "total_caught": 1,
                    f"rarity_counts.{spawn_data['rarity']}": 1,
                    f"group_catches.{str(chat_id)}": 1
                }
            },
            upsert=True
        )
        value = get_rarity_value(spawn_data["rarity"])
        await add_balance(user_id, value)
        del active_spawns[chat_id]
        success_text = (
            f"✨ {mention}, ဇာတ်ကောင်အသစ်ရပါပြီ! / you got a new character!\n\n"
            f"🌟 Name / နာမည်: {spawn_data['name']}\n"
            f"{RARITY_EMOJI.get(spawn_data['rarity'], '')} Rarity / အဆင့်: {spawn_data['rarity']}\n"
            f"🔥 Anime / စီးရီး: {spawn_data['series']}\n"
            f"💰 +{value:,} MMK\n\n"
            f"🖼 /harem ကို စစ်ဆေးလိုက်ပါ! / Check your /harem now!"
        )
        await reply_tag(event, success_text, parse_mode='html')

# ---- /w ----
async def w_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    if chat_id not in active_spawns:
        await reply_tag(event, bl("❌ ဇာတ်ကောင်တစ်ကောင်မှ မပေါ်သေးပါ။", "❌ No character has spawned."))
        return
    data = active_spawns[chat_id]
    await reply_tag(event,
        f"🌟 Name / နာမည်: {data['name']}\n"
        f"📺 Series / စီးရီး: {data['series']}\n"
        f"💎 Rarity / အဆင့်: {RARITY_EMOJI.get(data['rarity'], '')} {data['rarity']}"
    )

# ---- /who (reply required) ----
async def who_reveal_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    if chat_id not in active_spawns:
        await reply_tag(event, bl("❌ ဒီချတ်ထဲမှာ ဇာတ်ကောင်မရှိသေးပါ။", "❌ No character has spawned in this chat."))
        return
    spawn_data = active_spawns[chat_id]
    if time.time() - spawn_data["spawn_time"] > 300:
        if chat_id in active_spawns:
            del active_spawns[chat_id]
        await reply_tag(event, bl("⏱️ ဇာတ်ကောင်ပျောက်သွားပါပြီ! နောက်တစ်ကြိမ်ကြိုးစားပါ။", "⏱️ The character has vanished! Try again later."))
        return
    if not event.is_reply:
        await reply_tag(event, bl("⚠️ ကျေးဇူးပြု၍ spawn message ကို reply ပေးပါ!", "⚠️ Please reply directly to the spawn message to reveal the character name!"))
        return
    if event.reply_to_msg_id != spawn_data["spawn_msg_id"]:
        await reply_tag(event, bl("⚠️ spawn message ကိုသာ reply ပေးပါ၊ တခြားစာကို reply မလုပ်ပါနဲ့!", "⚠️ Please reply directly to the spawn message, not to other messages!"))
        return
    await reply_tag(event,
        f"🌟 Name: {spawn_data['name']}\n"
        f"📺 Series: {spawn_data['series']}\n"
        f"💎 Rarity: {RARITY_EMOJI.get(spawn_data['rarity'], '')} {spawn_data['rarity']}"
    )

# ---- /hmode ----
async def hmode_handler(event):
    user_id = event.sender_id
    doc = await users_catcher_col.find_one({"user_id": user_id})
    current_filter = doc.get("rarity_filter") if doc else None
    buttons = []
    for tier in RARITY_TIERS:
        label = f"✅ {tier['emoji']} {tier['name']}" if current_filter == tier['name'] else f"{tier['emoji']} {tier['name']}"
        buttons.append([Button.inline(label, data=f"hfilter_{tier['name']}_{user_id}")])
    clear_label = "🔓 Clear Filter" if current_filter else "🔒 No Filter"
    buttons.append([Button.inline(clear_label, data=f"hfilter_clear_{user_id}")])
    await reply_tag(
        event,
        f"🎯 Select Rarity to prioritize in /harem\nCurrent: {current_filter if current_filter else 'None (Show All)'}",
        buttons=buttons
    )

# ---- /harem ----
async def harem_handler(event):
    user_id = event.sender_id
    mention = await get_mention(bot1, user_id)
    await ensure_user_registered(user_id, mention)
    await send_harem_cover(event, user_id)

async def send_harem_cover(event, user_id, edit_msg_id=None):
    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = doc.get("harem", []) if doc else []
    if not harem:
        msg = bl(
            "📭 သင့် harem ထဲမှာ ကဒ်တစ်ခုမှ မရှိသေးပါ။ /w နဲ့ ဇာတ်ကောင်စောင့်ပြီး /gases [နာမည်] နဲ့ ဖမ်းလိုက်ပါ။",
            "📭 Your harem is empty. Watch for a spawn with /w and catch it with /gases [name]."
        )
        if edit_msg_id:
            try:
                await bot1.edit_message(event.chat_id, edit_msg_id, msg + TAGLINE)
            except Exception:
                pass
        else:
            await reply_tag(event, msg)
        return

    # Auto-assign a random favorite card if none is set yet (or it no longer exists)
    fav_id = doc.get("fav_card")
    fav_card = next((c for c in harem if c.get("char_id") == fav_id), None) if fav_id else None
    if not fav_card:
        fav_card = random.choice(harem)
        await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"fav_card": fav_card["char_id"]}})

    char_data = await characters_base_col.find_one({"char_id": fav_card.get("char_id")})
    media = None
    if char_data and char_data.get("storage_msg_id"):
        try:
            stored = await bot1.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if stored and stored.media:
                media = stored.media
        except Exception:
            pass

    total = len(harem)
    balance = doc.get("wallet_balance", 0)
    owner_name = doc.get("fullname") or "User"
    caption = (
        f"🎐 <b>{escape_html(owner_name)}</b>'s Harem\n\n"
        f"⭐ Favorite / အကြိုက်ဆုံးကဒ်: {RARITY_EMOJI.get(fav_card.get('rarity'), '')} {fav_card.get('name')}\n"
        f"📺 Series / စီးရီး: {fav_card.get('series')}\n"
        f"💎 Rarity / အဆင့်: {fav_card.get('rarity')}\n\n"
        f"👒 Total Cards / စုစုပေါင်းကဒ်: {total}\n"
        f"💰 Balance: {balance:,} MMK\n\n"
        f"👇 ⭐ ကို ပြောင်းရန် /fav [ID] သုံးပါ / Use /fav [ID] to change favorite"
    )
    buttons = [
        [Button.inline(f"🎐 Look your harem ({total}) / ကဒ်များကြည့်ရန်", data=f"hgal_1_{user_id}")],
        [Button.inline("🎯 Set Rarity Priority", data=f"goto_hmode_{user_id}")]
    ]

    if edit_msg_id:
        try:
            if media:
                await bot1.edit_message(event.chat_id, edit_msg_id, caption, file=media, parse_mode='html', buttons=buttons)
            else:
                await bot1.edit_message(event.chat_id, edit_msg_id, caption + TAGLINE, parse_mode='html', buttons=buttons)
            return
        except Exception as e:
            logging.error(f"harem cover edit failed, sending fresh copy: {e}")
            # fall through to send a brand-new message below

    if media:
        await bot1.send_file(event.chat_id, media, caption=caption + TAGLINE, parse_mode='html', buttons=buttons)
    else:
        await reply_tag(event, caption, parse_mode='html', buttons=buttons)

# ---- Harem Gallery (view any user's cards, anyone can browse) ----
async def send_harem_gallery(event, owner_id, page, edit_msg_id):
    doc = await users_catcher_col.find_one({"user_id": owner_id})
    harem = doc.get("harem", []) if doc else []
    if not harem:
        return
    rarity_filter = doc.get("rarity_filter")
    if rarity_filter:
        harem = sorted(harem, key=lambda c: 0 if c.get("rarity") == rarity_filter else 1)
    total = len(harem)
    if page < 1: page = 1
    if page > total: page = total
    card = harem[page - 1]
    char_data = await characters_base_col.find_one({"char_id": card.get("char_id")})
    media = None
    if char_data and char_data.get("storage_msg_id"):
        try:
            stored = await bot1.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if stored and stored.media:
                media = stored.media
        except Exception:
            pass
    caption = (
        f"🃏 {page}/{total}\n\n"
        f"🌟 Name / နာမည်: {card.get('name')}\n"
        f"📺 Series / စီးရီး: {card.get('series')}\n"
        f"💎 Rarity / အဆင့်: {RARITY_EMOJI.get(card.get('rarity'), '')} {card.get('rarity')}\n"
        f"🆔 ID: {card.get('char_id')}"
    )
    nav_row = []
    if page > 1:
        nav_row.append(Button.inline("⬅️ Prev", data=f"hgal_{page-1}_{owner_id}"))
    if page < total:
        nav_row.append(Button.inline("Next ➡️", data=f"hgal_{page+1}_{owner_id}"))
    buttons = []
    if nav_row:
        buttons.append(nav_row)
    buttons.append([Button.inline("🔙 Back / နောက်သို့", data=f"hback_{owner_id}")])
    try:
        if media:
            await bot1.edit_message(event.chat_id, edit_msg_id, caption + TAGLINE, file=media, parse_mode='html', buttons=buttons)
        else:
            await bot1.edit_message(event.chat_id, edit_msg_id, caption + TAGLINE, parse_mode='html', buttons=buttons)
    except Exception as e:
        logging.error(f"harem gallery edit failed: {e}")

# ---- /fav ----
async def fav_handler(event):
    user_id = event.sender_id
    char_id = event.pattern_match.group(1).strip()
    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = doc.get("harem", []) if doc else []
    owned = next((c for c in harem if c.get("char_id") == char_id), None)
    if not owned:
        await reply_tag(event, bl(
            "❌ ဒီ ID ရဲ့ ကဒ်ကို သင့် harem ထဲမှာ မတွေ့ပါ။",
            "❌ You don't own a card with that ID in your harem."
        ))
        return
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"fav_card": char_id}})
    await reply_tag(event, bl(
        f"⭐ Favorite ကဒ်ကို {owned.get('name')} အဖြစ် သတ်မှတ်ပြီးပါပြီ။ /harem ကို ပြန်စစ်ကြည့်ပါ။",
        f"⭐ Favorite card set to {owned.get('name')}. Check /harem to see it."
    ))


# ---- Inline Query ----
async def harem_inline(event):
    query_text = (event.text or "").strip()
    if not query_text.startswith("harem."):
        return
    try:
        target_user_id = int(query_text.split(".", 1)[1])
    except (ValueError, IndexError):
        return
    if event.sender_id != target_user_id:
        await event.answer([], switch_pm="❌ This is not your vault!", switch_pm_param="start")
        return
    doc = await users_catcher_col.find_one({"user_id": target_user_id})
    if not doc or not doc.get("harem"):
        await event.answer([], switch_pm="📭 Your vault is empty!", switch_pm_param="start")
        return
    harem = doc.get("harem", [])
    results = []
    builder = event.builder
    for card in harem[:50]:
        char_id = card.get("char_id")
        if not char_id:
            continue
        char_data = await characters_base_col.find_one({"char_id": char_id})
        if not char_data:
            continue
        storage_id = char_data.get("storage_msg_id")
        if not storage_id:
            continue
        try:
            stored_msg = await bot1.get_messages(STORAGE_CHANNEL, ids=storage_id)
            if not stored_msg or not stored_msg.media:
                continue
            caption = (
                f"🌟 {card.get('name', 'Unknown')}\n"
                f"🆔 {char_id}\n"
                f"🎭 {card.get('series', 'Unknown')}\n"
                f"💎 {card.get('rarity', 'Unknown')}"
            )
            if stored_msg.photo:
                results.append(builder.photo(
                    file=stored_msg.media,
                    id=char_id,
                    text=caption,
                    parse_mode='html'
                ))
            elif stored_msg.video:
                results.append(builder.video(
                    file=stored_msg.media,
                    id=char_id,
                    text=caption,
                    parse_mode='html'
                ))
            else:
                results.append(builder.document(
                    file=stored_msg.media,
                    title=card.get('name', 'Card'),
                    id=char_id,
                    text=caption,
                    parse_mode='html'
                ))
        except Exception as e:
            logging.error(f"Inline error for {char_id}: {e}")
            continue
    await event.answer(results, cache_time=0)

# ---- /myinfo ----
async def myinfo_handler(event):
    user_id = event.sender_id
    mention = await get_mention(bot1, user_id)
    await ensure_user_registered(user_id, mention)
    doc = await users_catcher_col.find_one({"user_id": user_id})
    if not doc:
        await reply_tag(event, "❌ User not found.")
        return
    total = doc.get("total_caught", 0)
    balance = doc.get("wallet_balance", 0)
    r_counts = doc.get("rarity_counts", {t["name"]: 0 for t in RARITY_TIERS})
    fav = doc.get("fav_card")
    fav_name = None
    if fav:
        fav_doc = await characters_base_col.find_one({"char_id": fav})
        if fav_doc:
            fav_name = fav_doc["name"]
    rarity_lines = []
    for tier in RARITY_TIERS:
        count = r_counts.get(tier["name"], 0)
        if count:
            rarity_lines.append(f"├─➩ {RARITY_EMOJI[tier['name']]} {tier['name']}: {count}")
    text = (
        f"🔰 User Info / အကောင့်အချက်အလက်\n\n"
        f"👤 Name / နာမည်: {mention}\n"
        f"🔩 User ID: {user_id}\n"
        f"👒 Waifu Count / ကဒ်အရေအတွက်: {total}\n"
        f"💰 Balance / လက်ကျန်ငွေ: {balance:,} MMK\n"
    )
    if fav_name:
        text += f"⭐ Favorite / အကြိုက်ဆုံး: {fav_name}\n"
    text += "\n✳️ Rarity Counts / အဆင့်အလိုက်ရေတွက်: \n╭───────────────────\n" + "\n".join(rarity_lines) + "\n╰───────────────────"
    photos = await bot1.get_profile_photos(user_id, limit=1)
    if photos:
        await bot1.send_file(event.chat_id, photos[0], caption=text + TAGLINE, parse_mode='html')
    else:
        await reply_tag(event, text)

# ---- /check ----
async def check_handler(event):
    char_id = event.pattern_match.group(1).strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, bl("❌ ဒီ ID နဲ့ ကဒ်ကို ရှာမတွေ့ပါ။", "❌ Character not found."))
        return
    media = None
    try:
        stored = await bot1.get_messages(STORAGE_CHANNEL, ids=char_doc.get("storage_msg_id"))
        if stored and stored.media:
            media = stored.media
    except:
        pass
    rarity = char_doc.get("rarity", "Unknown")
    info = (
        f"🃏 Card Details / ကဒ်အချက်အလက်\n"
        f"ID: {char_id}\n"
        f"Name / နာမည်: {char_doc['name']}\n"
        f"Series / စီးရီး: {char_doc['series']}\n"
        f"Rarity / အဆင့်: {rarity}\n"
        f"Spawn count: {char_doc.get('spawn_count', 0)}\n"
        f"Max Spawn: {char_doc.get('spawn_limit', 0)}\n"
        f"Events: {char_doc.get('events', 'None')}"
    )
    pipeline = [
        {"$match": {"harem.char_id": char_id}},
        {"$project": {"fullname": 1, "count": {"$size": {"$filter": {"input": "$harem", "as": "item", "cond": {"$eq": ["$$item.char_id", char_id]}}}}}},
        {"$sort": {"count": -1}}, {"$limit": 5}
    ]
    owners = await users_catcher_col.aggregate(pipeline).to_list(length=5)
    if owners:
        info += "\n\nTop Owners:"
        for i, o in enumerate(owners, 1):
            mention = await get_mention(bot1, o['user_id'], o.get('fullname'))
            count = o['count']
            info += f"\n{i}. {mention} — x{count}"
    if media:
        await bot1.send_file(event.chat_id, media, caption=info + TAGLINE, parse_mode='html')
    else:
        await reply_tag(event, info)

# ---- /addcharacter ----
async def addcharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to a media file (photo/video).")
        return
    parts = event.pattern_match.groups()
    name = parts[0].strip()
    series = parts[1].strip()
    rarity_input = parts[2].strip()
    char_id = parts[3].strip()
    events = parts[4].strip()
    spawn_limit = int(parts[5]) if parts[5] else 0
    if not char_id:
        await reply_tag(event, "❌ ID cannot be empty.")
        return
    existing = await characters_base_col.find_one({"char_id": char_id})
    if existing:
        await reply_tag(event, f"❌ ID '{char_id}' already exists.")
        return
    rarity_name = None
    for tier in RARITY_TIERS:
        if tier["name"].lower() == rarity_input.lower():
            rarity_name = tier["name"]
            break
    if not rarity_name:
        await reply_tag(event, f"❌ Invalid rarity. Use: Bear, Rainbow, Crossverse, Trident, Koinobori, Medium, Lower")
        return
    reply_msg = await event.get_reply_message()
    if not (reply_msg.photo or reply_msg.video or reply_msg.document):
        await reply_tag(event, "❌ Media not found.")
        return
    try:
        stored = await bot1.send_file(STORAGE_CHANNEL, reply_msg.media)
        storage_msg_id = stored.id
    except Exception as e:
        await reply_tag(event, f"❌ Failed to store media: {e}")
        return
    char_data = {
        "char_id": char_id,
        "name": name,
        "series": series,
        "rarity": rarity_name,
        "events": events,
        "spawn_limit": spawn_limit,
        "spawn_count": 0,
        "storage_msg_id": storage_msg_id
    }
    await characters_base_col.insert_one(char_data)
    await reply_tag(event, f"✅ Character added:\nID: {char_id}\nName: {name}\nSeries: {series}\nRarity: {rarity_name}\nEvents: {events}\nMax Spawn: {spawn_limit if spawn_limit > 0 else 'Infinite'}")

# ---- /removecharacter ----
async def removecharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    char_id = event.pattern_match.group(1).strip()
    result = await characters_base_col.delete_one({"char_id": char_id})
    await reply_tag(event, f"✅ Character {char_id} removed." if result.deleted_count else "❌ Not found.")

# ---- /fspawn ----
async def force_spawn(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    chat_id = int(chat_id) if chat_id else event.chat_id
    await trigger_dynamic_spawn(chat_id)
    await reply_tag(event, f"✅ Forced spawn in {chat_id}.")

# ---- /spawnoff ----
async def spawn_toggle(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = int(event.pattern_match.group(1))
    state = event.pattern_match.group(2)
    if state is None:
        doc = await spawn_disabled_col.find_one({"chat_id": chat_id})
        new_state = not (doc.get("disabled", False) if doc else False)
    else:
        new_state = (state.lower() == "off")
    await spawn_disabled_col.update_one({"chat_id": chat_id}, {"$set": {"disabled": new_state}}, upsert=True)
    await reply_tag(event, f"✅ Spawn for {chat_id} is now {'disabled' if new_state else 'enabled'}.")

# ---- /spawnstats ----
async def spawn_stats(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    chat_id = int(chat_id) if chat_id else event.chat_id
    counter = await groups_counters_col.find_one({"chat_id": chat_id})
    count = counter.get("counter", 0) if counter else 0
    config = await groups_config_col.find_one({"chat_id": chat_id})
    target = config.get("spawn_target", 50) if config else 50
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    disabled = disabled.get("disabled", False) if disabled else False
    await reply_tag(event, f"📊 Spawn stats for {chat_id}\nCounter: {count}\nTarget: {target}\nRemaining: {max(0, target-count)}\nDisabled: {disabled}")

# ---- /changetime ----
async def changetime_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    args = event.pattern_match.groups()
    if args[1] is not None:
        chat_id = int(args[0])
        target = int(args[1])
        await groups_config_col.update_one({"chat_id": chat_id}, {"$set": {"spawn_target": target}}, upsert=True)
        await reply_tag(event, f"✅ Spawn target for {chat_id} set to {target}.")
    else:
        target = int(args[0])
        await groups_config_col.update_one({"chat_id": "global"}, {"$set": {"spawn_target": target}}, upsert=True)
        await reply_tag(event, f"✅ Global spawn target set to {target}.")

# ---- /status ----
async def status_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    total_chats = await groups_col.count_documents({})
    total_users = await users_catcher_col.count_documents({})
    pipeline = [{"$group": {"_id": None, "total": {"$sum": {"$size": "$harem"}}}}]
    res = await users_catcher_col.aggregate(pipeline).to_list(length=1)
    total_waifus = res[0]["total"] if res else 0
    total_anime = len(await characters_base_col.distinct("series"))
    r_counts = {}
    pipeline = [{"$unwind": "$harem"}, {"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}]
    r_res = await users_catcher_col.aggregate(pipeline).to_list(length=None)
    for r in r_res:
        r_counts[r["_id"]] = r["count"]
    text = f"📊 Bot Statistics\nTotal Chats: {total_chats}\nTotal Users: {total_users}\nTotal Waifus: {total_waifus}\nTotal Anime: {total_anime}\n"
    for tier in RARITY_TIERS:
        text += f"{RARITY_EMOJI[tier['name']]} {tier['name']}: {r_counts.get(tier['name'], 0)}\n"
    await reply_tag(event, text)

# ---- /balance ----
async def balance_handler(event):
    user_id = event.sender_id
    bal = await get_balance(user_id)
    await reply_tag(event, f"💰 Balance: {bal:,} MMK")

# ---- /daily ----
async def daily_handler(event):
    user_id = event.sender_id
    now = time.time()
    doc = await users_catcher_col.find_one({"user_id": user_id})
    last = doc.get("last_daily", 0) if doc else 0
    balance = doc.get("wallet_balance", 0) if doc else 0
    if now - last < 86400:
        rem = int(86400 - (now - last))
        await reply_tag(event, f"⏳ Already claimed. Next in {rem//3600}h {(rem%3600)//60}m.")
        return
    bonus = 50000
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"wallet_balance": balance + bonus, "last_daily": now}}, upsert=True)
    await reply_tag(event, f"🎉 Daily bonus +{bonus:,} MMK. Balance: {balance+bonus:,} MMK")

# ---- /slot ----
SYMBOLS = ["🍒", "🍋", "🔔", "💎", "7️⃣"]
async def slot_handler(event):
    args = event.pattern_match.group(1)
    if not args:
        await reply_tag(event, "🎰 Usage: /slot <amount>")
        return
    try:
        bet = int(args.strip())
    except:
        await reply_tag(event, "❌ Invalid amount.")
        return
    user_id = event.sender_id
    balance = await get_balance(user_id)
    if bet <= 0 or balance < bet:
        await reply_tag(event, f"❌ Insufficient balance. You have {balance} MMK.")
        return
    await add_balance(user_id, -bet)
    status_msg = await event.reply("🎰 [ 🔄 | 🔄 | 🔄 ]\n*Spinning...*")
    for _ in range(3):
        await asyncio.sleep(0.5)
        fake = [random.choice(SYMBOLS) for _ in range(3)]
        try:
            await status_msg.edit(f"🎰 [ {' | '.join(fake)} ]\n*Spinning...*")
        except:
            pass
    reels = [random.choice(SYMBOLS) for _ in range(3)]
    payout = 0
    if reels == ["7️⃣", "7️⃣", "7️⃣"]: payout = bet * 5
    elif reels[0] == reels[1] == reels[2]: payout = bet * 2
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]: payout = int(bet * 1.5)
    if payout > 0: await add_balance(user_id, payout)
    win = f"🎉 Win: +{payout:,} MMK" if payout > 0 else "😭 Lost!"
    final = f"🎰 [ {' | '.join(reels)} ]\nBet: {bet:,} MMK\n{win}\nBalance: {await get_balance(user_id):,} MMK"
    try:
        await status_msg.edit(final + TAGLINE)
    except:
        await reply_tag(event, final)

# ---- /top /gtop ----
async def top_handler(event): await send_leaderboard(event, "local")
async def gtop_handler(event): await send_leaderboard(event, "global")

async def send_leaderboard(event, scope):
    if scope == "local":
        field = f"group_catches.{str(event.chat_id)}"
        cursor = users_catcher_col.find({field: {"$gt": 0}}).sort(field, -1).limit(10)
        title = "🏆 TOP 10 IN THIS GROUP"
    else:
        field = "total_caught"
        cursor = users_catcher_col.find({field: {"$gt": 0}}).sort(field, -1).limit(10)
        title = "🌐 GLOBAL TOP 10"
    top = await cursor.to_list(length=10)
    if not top:
        await reply_tag(event, "❌ No data.")
        return
    msg = f"{title}\n\n"
    medals = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]
    for i, doc in enumerate(top):
        uid = doc.get("user_id")
        val = doc.get(field, 0)
        try:
            user = await bot1.get_entity(uid)
            name = user.first_name or "User"
        except:
            name = f"User {uid}"
        msg += f"{medals[i]} {name} — {val:,} catches\n"
    await reply_tag(event, msg)

# ---- /tr ----
async def translate_command(event):
    text = event.pattern_match.group(1).strip()
    if not text and event.is_reply:
        reply = await event.get_reply_message()
        if reply and reply.text:
            text = reply.text
    if not text:
        await reply_tag(event, "❌ Usage: /tr <text> (or reply)")
        return
    try:
        translated = GoogleTranslator(source='auto', target='en').translate(text)
        await reply_tag(event, f"🔤 Translated:\n`{translated}`")
    except:
        await reply_tag(event, "⚠️ Translation failed.")

# ---- auto_calc ----
async def auto_calc(event):
    if event.text and event.text.startswith('/'):
        return
    text = event.text.strip() if event.text else ""
    if not text:
        return
    math_expr = text.replace("÷", "/").replace("×", "*").replace("^", "**")
    if re.match(r'^[0-9.+\-*/()%\s]+$', math_expr) and any(op in math_expr for op in "+-*/%"):
        try:
            if "**" in math_expr and len(math_expr) > 20:
                return
            result = eval(math_expr, {"__builtins__": None}, {})
            if isinstance(result, float) and result.is_integer():
                result = int(result)
            await reply_tag(event, f"`{text} = {result}`")
        except:
            pass

# ---- /id ----
async def id_handler(event):
    target = await event.get_sender() if not event.is_reply else await (await event.get_reply_message()).get_sender()
    uid = target.id
    name = target.first_name or "User"
    username = f"@{target.username}" if target.username else "None"
    await reply_tag(event, f"👤 {name}\n🆔 {uid}\n🌐 {username}\n📌 Chat: {event.chat_id}")

# ---- /start ----
async def start_handler(event):
    user_id = event.sender_id
    mention = await get_mention(bot1, user_id)
    await ensure_user_registered(user_id, mention)
    if event.is_private:
        text = bl(
            "👋 <b>မင်္ဂလာပါ!</b> Character Catcher Bot မှ ကြိုဆိုပါတယ်။\n\n"
            "🎮 ဂရုပ်ထဲမှာ ဇာတ်ကောင်တွေ ပေါ်လာရင် /gases [နာမည်] နဲ့ ဖမ်းနိုင်ပါတယ်။\n"
            "🎒 /harem — သင့်ကဒ်များကြည့်ရန်\n"
            "🔰 /myinfo — သင့်ပရိုဖိုင်ကြည့်ရန်\n"
            "💰 /balance, /daily — ငွေစာရင်းကြည့်ရန်\n"
            "❓ /help — command အားလုံးကြည့်ရန်",
            "<b>Welcome to Character Catcher Bot!</b>\n\n"
            "🎮 Watch for characters spawning in your group and catch them with /gases [name].\n"
            "🎒 /harem — view your collected cards\n"
            "🔰 /myinfo — view your profile\n"
            "💰 /balance, /daily — check your wallet\n"
            "❓ /help — see all commands"
        )
        try:
            me = await bot1.get_me()
            buttons = [
                [Button.url("➕ Add me to a group / ဂရုပ်ထဲထည့်ရန်", f"https://t.me/{me.username}?startgroup=true")],
                [Button.switch_inline("🔍 My Harem / ကဒ်များကြည့်ရန်", query=f"harem.{user_id}", same_peer=False)]
            ]
        except Exception:
            buttons = None
        await event.reply(text + TAGLINE, parse_mode='html', buttons=buttons)
    else:
        await reply_tag(event, bl(
            "👋 Bot အသင့်ပါ! /help ကို သုံးပြီး command များကြည့်ပါ။",
            "👋 Bot is ready! Use /help to see available commands."
        ))

# ---- /help ----
async def help_handler(event):
    help_text = (
        "🤖 <b>Commands / လမ်းညွှန်</b>\n\n"
        "🎮 <b>Catching / ဖမ်းခြင်း</b>\n/w, /gases [name], /harem, /myinfo, /fav [ID]\n/check [ID], /hmode (rarity priority)\n\n"
        "💰 <b>Economy / ငွေကြေး</b>\n/balance, /daily, /slot [amount], /top, /gtop\n\n"
        "🛠️ <b>Utility / အထောက်အကူ</b>\n/tr [text], /id, /start\n\n"
        "👑 <b>Owner</b>\n/addcharacter, /removecharacter, /editcharacter\n/fspawn, /spawnoff, /spawnstats, /changetime, /status"
    )
    await reply_tag(event, help_text, parse_mode='html')

# ---- /gban ----
async def gban_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    uid = int(event.pattern_match.group(1))
    reason = event.pattern_match.group(2) or "No reason"
    await banned_users_col.update_one({"user_id": uid}, {"$set": {"banned": True, "reason": reason}}, upsert=True)
    await reply_tag(event, f"✅ User {uid} banned.")

# ---- /unban ----
async def unban_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    uid = int(event.pattern_match.group(1))
    result = await banned_users_col.delete_one({"user_id": uid})
    if result.deleted_count:
        await reply_tag(event, f"✅ User {uid} unbanned.")
    else:
        await reply_tag(event, f"❌ User {uid} is not banned.")

# ---- check_ban ----
async def check_ban(event):
    if event.sender_id == OWNER_ID:
        return
    banned = await banned_users_col.find_one({"user_id": event.sender_id})
    if banned and banned.get("banned", False):
        await reply_tag(event, "❌ You are banned.")
        raise events.StopPropagation

# ---- message_counter ----
async def message_counter_for_spawn(event):
    if event.is_private or event.chat_id == SPECIFIC_GROUP:
        return
    chat_id = event.chat_id
    if chat_id in active_spawns:
        return
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    if disabled and disabled.get("disabled", False):
        return
    config = await groups_config_col.find_one({"chat_id": chat_id})
    target = config.get("spawn_target", 50) if config else 50
    counter_doc = await groups_counters_col.find_one_and_update(
        {"chat_id": chat_id},
        {"$inc": {"counter": 1}},
        upsert=True,
        return_document=ReturnDocument.AFTER
    )
    if counter_doc and counter_doc.get("counter", 0) >= target:
        await groups_counters_col.update_one({"chat_id": chat_id}, {"$set": {"counter": 0}})
        await trigger_dynamic_spawn(chat_id)

# ---- Callback Query ----
async def callback_handler(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    if data.startswith("hgal_"):
        parts = data.split("_")
        page = int(parts[1])
        owner_id = int(parts[2])
        await event.answer()
        msg = await event.get_message()
        await send_harem_gallery(event, owner_id, page, msg.id)
        return
    if data.startswith("hback_"):
        owner_id = int(data.split("_")[1])
        await event.answer()
        msg = await event.get_message()
        await send_harem_cover(event, owner_id, edit_msg_id=msg.id)
        return
    if data.startswith("goto_hmode_"):
        target_user_id = int(data.split("_")[2])
        if user_id != target_user_id:
            await event.answer(bl("⚠️ ဒါက သင့်ရဲ့ menu မဟုတ်ပါ။", "⚠️ This is not your menu."), alert=True)
            return
        await event.answer("Opening Rarity Filter...")
        await hmode_handler(event)
        return
    if data.startswith("hfilter_"):
        parts = data.split("_")
        if parts[1] == "clear":
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": None}}, upsert=True)
            await event.answer("🔓 Filter cleared!", alert=True)
        else:
            rarity = parts[1]
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": rarity}}, upsert=True)
            await event.answer(f"✅ Priority set to {rarity}", alert=True)
        try:
            await hmode_handler(event)
        except:
            pass
        return

# ==========================================
# 🚀 STARTUP
# ==========================================
async def startup():
    global bot1
    threading.Thread(target=_start_health_server, daemon=True).start()
    bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH)
    
    # Register all handlers
    bot1.add_event_handler(message_counter_for_spawn, events.NewMessage(incoming=True))
    bot1.add_event_handler(start_handler, events.NewMessage(pattern=r'^/start(?:@\w+)?$'))
    bot1.add_event_handler(catch_handler, events.NewMessage(pattern=r'^(?:/gases|/catch)(?:@\w+)?\s+(.+)$'))
    bot1.add_event_handler(w_handler, events.NewMessage(pattern=r'^/w(?:@\w+)?$'))
    bot1.add_event_handler(who_reveal_handler, events.NewMessage(pattern=r'^/who(?:@\w+)?$'))
    bot1.add_event_handler(hmode_handler, events.NewMessage(pattern=r'^/hmode(?:@\w+)?$'))
    bot1.add_event_handler(harem_handler, events.NewMessage(pattern=r'^/harem(?:@\w+)?$'))
    bot1.add_event_handler(harem_inline, events.InlineQuery)
    bot1.add_event_handler(myinfo_handler, events.NewMessage(pattern=r'^/myinfo(?:@\w+)?$'))
    bot1.add_event_handler(fav_handler, events.NewMessage(pattern=r'^/fav(?:@\w+)?\s+(\S+)$'))
    bot1.add_event_handler(check_handler, events.NewMessage(pattern=r'^/check(?:@\w+)?\s+(\S+)$'))
    bot1.add_event_handler(addcharacter_handler, events.NewMessage(pattern=r'^/addcharacter(?:@\w+)?\s+(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)(?:\s*\|\s*(\d+))?$'))
    bot1.add_event_handler(removecharacter_handler, events.NewMessage(pattern=r'^/removecharacter(?:@\w+)?\s+(\S+)$'))
    bot1.add_event_handler(force_spawn, events.NewMessage(pattern=r'^/fspawn(?:@\w+)?(?:\s+([-\d]+))?$'))
    bot1.add_event_handler(spawn_toggle, events.NewMessage(pattern=r'^/spawnoff(?:@\w+)?\s+([-\d]+)(?:\s+(on|off))?$'))
    bot1.add_event_handler(spawn_stats, events.NewMessage(pattern=r'^/spawnstats(?:@\w+)?(?:\s+([-\d]+))?$'))
    bot1.add_event_handler(changetime_handler, events.NewMessage(pattern=r'^/changetime(?:@\w+)?\s+(\d+)(?:\s+(\d+))?$'))
    bot1.add_event_handler(status_handler, events.NewMessage(pattern=r'^/status(?:@\w+)?$'))
    bot1.add_event_handler(balance_handler, events.NewMessage(pattern=r'^/balance(?:@\w+)?$'))
    bot1.add_event_handler(daily_handler, events.NewMessage(pattern=r'^/daily(?:@\w+)?$'))
    bot1.add_event_handler(slot_handler, events.NewMessage(pattern=r'^/slot(?:@\w+)?(?:\s+(\d+))?'))
    bot1.add_event_handler(top_handler, events.NewMessage(pattern=r'^/top(?:@\w+)?$'))
    bot1.add_event_handler(gtop_handler, events.NewMessage(pattern=r'^/gtop(?:@\w+)?$'))
    bot1.add_event_handler(translate_command, events.NewMessage(pattern=r'^/tr(?:@\w+)?(.*)'))
    bot1.add_event_handler(auto_calc, events.NewMessage)
    bot1.add_event_handler(id_handler, events.NewMessage(pattern=r'^/id(?:@\w+)?$'))
    bot1.add_event_handler(help_handler, events.NewMessage(pattern=r'^/help(?:@\w+)?$'))
    bot1.add_event_handler(gban_handler, events.NewMessage(pattern=r'^/gban(?:@\w+)?\s+(\d+)(?:\s+(.*))?$'))
    bot1.add_event_handler(unban_handler, events.NewMessage(pattern=r'^/unban(?:@\w+)?\s+(\d+)$'))
    bot1.add_event_handler(check_ban, events.NewMessage(pattern=r'^/'))
    bot1.add_event_handler(callback_handler, events.CallbackQuery)
    
    await users_catcher_col.create_index("user_id", unique=True)
    await characters_base_col.create_index("char_id", unique=True)
    await groups_col.create_index("chat_id", unique=True)
    asyncio.create_task(spawn_cleaner())
    await bot1.start(bot_token=BOT_TOKEN)
    print("Bot is running.")
    await bot1.run_until_disconnected()

if __name__ == "__main__":
    asyncio.run(startup())
