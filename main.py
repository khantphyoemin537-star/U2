import os
import asyncio
import random
import time
import logging
import re
from collections import defaultdict, Counter
from datetime import datetime
from html import escape as escape_html

from dotenv import load_dotenv
from telethon import TelegramClient, events, errors, Button, types
from telethon.tl.types import MessageMediaPhoto, MessageMediaDocument
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
# Helpers
# ==========================================
async def reply_tag(event, text, **kwargs):
    if TAGLINE not in text: text += TAGLINE
    await event.reply(text, **kwargs)

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
                "rarity_filter": None,  # For /hmode sorting
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
# Bot Client
# ==========================================
bot1 = None 

# ==========================================
# Character Spawn System
# ==========================================
active_spawns = {}
spawn_locks = defaultdict(asyncio.Lock)

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
    
    # Get all characters
    all_chars = await characters_base_col.find().to_list(length=None)
    if not all_chars:
        return
    
    # Filter out characters that have reached their spawn limit
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
    
    # Increment spawn count
    await characters_base_col.update_one({"char_id": chosen["char_id"]}, {"$inc": {"spawn_count": 1}})
    
    caption = f"🔱 A character has spawned in this chat!\nAdd to harem using /gases [ NAME ]"
    sent_msg = await bot1.send_message(chat_id, file=stored_msg.media, caption=caption)
    active_spawns[chat_id] = {
        "char_id": chosen.get("char_id"),
        "name": chosen.get("name"),
        "series": chosen.get("series", "Unknown"),
        "rarity": classify_rarity(chosen.get("rarity", "Lower")),
        "spawn_time": time.time(),
        "claimed": False,
        "spawn_msg_id": sent_msg.id
    }

@bot1.on(events.NewMessage(incoming=True))
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

# ==========================================
# 📌 COMMAND HANDLERS
# ==========================================

# ---- /gases (or /catch) ----
@bot1.on(events.NewMessage(pattern=r'^(?:/gases|/catch)(?:@\w+)?\s+(.+)$'))
async def catch_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    user_id = event.sender_id
    name = event.pattern_match.group(1).strip()
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return
    spawn_data = active_spawns[chat_id]
    if spawn_data["claimed"]:
        await reply_tag(event, "❌ Already caught by someone else!")
        return
    if time.time() - spawn_data["spawn_time"] > 300:
        del active_spawns[chat_id]
        await reply_tag(event, "⏱️ Too late! The character vanished.")
        return
    if normalize_name(name) != normalize_name(spawn_data["name"]):
        await reply_tag(event, f"❌ Wrong name! Use /w to check the exact name.")
        return
    async with spawn_locks[chat_id]:
        if active_spawns.get(chat_id, {}).get("claimed", True):
            await reply_tag(event, "❌ Already caught by someone else!")
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
            f"✨ {mention}, you got a new character!\n\n"
            f"🌟 Name: {spawn_data['name']}\n"
            f"{RARITY_EMOJI.get(spawn_data['rarity'], '')} Rarity: {spawn_data['rarity']}\n"
            f"🔥 Anime: {spawn_data['series']}\n\n"
            f"🖼 Check your /harem now!"
        )
        await reply_tag(event, success_text)

# ---- /w ----
@bot1.on(events.NewMessage(pattern=r'^(?:/w|/waifu)(?:@\w+)?$'))
async def who_reveal_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    
    # 1️⃣ Spawn ရှိမရှိ စစ်ဆေးမယ်
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return
        
    spawn_data = active_spawns[chat_id]
    
    # 2️⃣ အချိန်ကုန်သွားပြီလား စစ်ဆေးမယ် (၅ မိနစ်)
    if time.time() - spawn_data["spawn_time"] > 300:
        if chat_id in active_spawns:
            del active_spawns[chat_id]
        await reply_tag(event, "⏱️ The character has vanished! Try again later.")
        return
    
    # 3️⃣ Reply ထောက်ထားရဲ့လား စစ်ဆေးမယ်
    if not event.is_reply:
        await reply_tag(event, "⚠️ Please reply directly to the spawn message to reveal the character name!")
        return
    
    # 4️⃣ Reply ထောက်ထားတဲ့စာက မူရင်း Spawn စာနဲ့ ကိုက်ညီလား စစ်ဆေးမယ်
    if event.reply_to_msg_id != spawn_data["spawn_msg_id"]:
        await reply_tag(event, "⚠️ Please reply directly to the spawn message, not to other messages!")
        return
    
    # 5️⃣ အားလုံးပြီးရင် ကဒ်အချက်အလက်တွေကို ပြပေးမယ်
    await reply_tag(event,
        f"🌟 Name: {spawn_data['name']}\n"
        f"📺 Series: {spawn_data['series']}\n"
        f"💎 Rarity: {RARITY_EMOJI.get(spawn_data['rarity'], '')} {spawn_data['rarity']}"
                   )

# ---- /hmode (Set Rarity Filter / Sorting Priority) ----
@bot1.on(events.NewMessage(pattern=r'^/hmode(?:@\w+)?$'))
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

# ---- /harem (with Pagination & Sorting) ----
@bot1.on(events.NewMessage(pattern=r'^/harem(?:@\w+)?$'))
async def harem_handler(event):
    user_id = event.sender_id
    await ensure_user_registered(user_id, "User")
    await send_harem_page(event, user_id, page=1, edit_msg_id=None)

async def send_harem_page(event, user_id, page=1, edit_msg_id=None, callback_query=None):
    doc = await users_catcher_col.find_one({"user_id": user_id})
    if not doc or not doc.get("harem"):
        msg = "📭 Your harem is empty."
        if edit_msg_id:
            await bot1.edit_message(event.chat_id, edit_msg_id, msg + TAGLINE)
        else:
            await reply_tag(event, msg)
        return
    
    harem_list = doc.get("harem", [])
    rarity_filter = doc.get("rarity_filter")  # e.g., "Bear"
    
    # Sort: If filter is set, put that rarity first, then others
    if rarity_filter:
        def sort_key(item):
            if item.get("rarity") == rarity_filter:
                return 0
            return 1
        harem_list = sorted(harem_list, key=sort_key)
    
    total = len(harem_list)
    total_pages = max(1, (total + CARDS_PER_PAGE - 1) // CARDS_PER_PAGE)
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    
    start = (page - 1) * CARDS_PER_PAGE
    end = min(start + CARDS_PER_PAGE, total)
    page_items = harem_list[start:end]
    
    # Build text
    output = "🎒 Your Harem Collection\n"
    if rarity_filter:
        output += f"⭐ Prioritizing: {rarity_filter}\n"
    output += f"📑 Page {page}/{total_pages} | Total: {total} cards\n\n"
    
    for idx, card in enumerate(page_items, start=start+1):
        name = card.get("name", "Unknown")
        series = card.get("series", "Unknown")
        rarity = card.get("rarity", "Lower")
        char_id = card.get("char_id", "N/A")
        output += f"{idx}. {RARITY_EMOJI.get(rarity, '')} {name} ({series}) [ID: {char_id}]\n"
    
    # Build buttons
    buttons = []
    nav_row = []
    if page > 1:
        nav_row.append(Button.inline("⬅️ Prev", data=f"hpage_{page-1}_{user_id}"))
    if page < total_pages:
        nav_row.append(Button.inline("Next ➡️", data=f"hpage_{page+1}_{user_id}"))
    if nav_row:
        buttons.append(nav_row)
    
    # Add HMODE button for convenience
    buttons.append([Button.inline("🎯 Set Rarity Priority", data=f"goto_hmode_{user_id}")])
    
    if edit_msg_id:
        await bot1.edit_message(event.chat_id, edit_msg_id, output + TAGLINE, parse_mode='html', buttons=buttons)
    else:
        await event.reply(output + TAGLINE, parse_mode='html', buttons=buttons)

# ---- Inline Query (Harem Gallery with Images/Videos) ----
@bot1.on(events.InlineQuery)
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
    
    # Show up to 50 cards in inline mode
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
            
            # Determine media type
            if stored_msg.photo:
                results.append(builder.photo(
                    file=stored_msg.media,
                    id=char_id,
                    text=caption,
                    parse_mode='html'
                ))
            elif stored_msg.video:
                # Send as video
                results.append(builder.video(
                    file=stored_msg.media,
                    id=char_id,
                    text=caption,
                    parse_mode='html'
                ))
            else:
                # Document or other
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
@bot1.on(events.NewMessage(pattern=r'^/myinfo(?:@\w+)?$'))
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
        f"🔰 User Info\n\n"
        f"👤 Name: {mention}\n"
        f"🔩 User ID: {user_id}\n"
        f"👒 Waifu Count: {total}\n"
        f"💰 Balance: {balance:,} MMK\n"
    )
    if fav_name:
        text += f"⭐ Favorite: {fav_name}\n"
    text += "\n✳️ Rarity Counts:\n╭───────────────────\n" + "\n".join(rarity_lines) + "\n╰───────────────────"
    photos = await bot1.get_profile_photos(user_id, limit=1)
    if photos:
        await bot1.send_file(event.chat_id, photos[0], caption=text + TAGLINE, parse_mode='html')
    else:
        await reply_tag(event, text)

# ---- /check (with image) ----
@bot1.on(events.NewMessage(pattern=r'^/check(?:@\w+)?\s+(\S+)$'))
async def check_handler(event):
    char_id = event.pattern_match.group(1).strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    
    # 📸 ပုံကို ဆွဲယူမယ်
    media = None
    try:
        stored = await bot1.get_messages(STORAGE_CHANNEL, ids=char_doc.get("storage_msg_id"))
        if stored and stored.media:
            media = stored.media
    except:
        pass
    
    # 🏆 ပိုင်ရှင်တွေကို ဆွဲယူမယ်
    pipeline = [
        {"$match": {"harem.char_id": char_id}},
        {"$project": {"fullname": 1, "count": {"$size": {"$filter": {"input": "$harem", "as": "item", "cond": {"$eq": ["$$item.char_id", char_id]}}}}}},
        {"$sort": {"count": -1}}, {"$limit": 5}
    ]
    owners = await users_catcher_col.aggregate(pipeline).to_list(length=5)
    
    # 📝 စာသားကို သန့်သန့်ရှင်းရှင်း ပြင်ဆင်မယ်
    rarity = char_doc.get("rarity", "Unknown")
    rarity_emoji = RARITY_EMOJI.get(rarity, "")
    spawn_count = char_doc.get("spawn_count", 0)
    spawn_limit = char_doc.get("spawn_limit", 0)
    
    # 🃏 Card Details
    info_lines = [
        " CARD DETAILS",
        "━━━━━━━━━━━━━━━━━━━━",
        f"🆔 ID: {char_id}",
        f"📛 Name: {char_doc['name']}",
        f"📺 Series: {char_doc['series']}",
        f"💎 Rarity: {rarity_emoji} {rarity}",
        f"📈 Spawn count: {spawn_count}",
    ]
    if spawn_limit > 0:
        info_lines.append(f"🔒 Max Spawn: {spawn_limit}")
    if char_doc.get('events'):
        info_lines.append(f"🏷️ Events: {char_doc['events']}")
    
    # 🏆 Top Owners (နှိပ်လို့ရအောင် ပြင်ထားတယ်)
    if owners:
        info_lines.append("")
        info_lines.append("🏆 TOP OWNERS")
        info_lines.append("━━━━━━━━━━━━━━━━━━━━")
        for i, o in enumerate(owners, 1):
            mention = await get_mention(bot1, o['user_id'], o.get('fullname'))
            count = o['count']
            info_lines.append(f"{i}. {mention} — x{count}")
    else:
        info_lines.append("")
        info_lines.append("📭 No one owns this card yet.")
    
    # 📝 စာသားအားလုံးကို ပေါင်းပြီး ပို့မယ်
    full_text = "\n".join(info_lines)
    
    # 📸 ပုံနဲ့တကွ ပို့မယ်
    if media:
        await bot1.send_file(
            event.chat_id,
            media,
            caption=full_text + TAGLINE,
            parse_mode='html'
        )
    else:
        await reply_tag(event, f"<code>{full_text}</code>")
# ---- /addcharacter (Name | Series | Rarity | ID | Events | SpawnLimit) ----
@bot1.on(events.NewMessage(pattern=r'^/addcharacter(?:@\w+)?\s+(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)(?:\s*\|\s*(\d+))?$'))
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
    spawn_limit = int(parts[5]) if parts[5] else 0  # 0 = infinite
    
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
@bot1.on(events.NewMessage(pattern=r'^/removecharacter(?:@\w+)?\s+(\S+)$'))
async def removecharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    char_id = event.pattern_match.group(1).strip()
    result = await characters_base_col.delete_one({"char_id": char_id})
    await reply_tag(event, f"✅ Character {char_id} removed." if result.deleted_count else "❌ Not found.")

# ---- /fspawn ----
@bot1.on(events.NewMessage(pattern=r'^/fspawn(?:@\w+)?(?:\s+([-\d]+))?$'))
async def force_spawn(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    chat_id = int(chat_id) if chat_id else event.chat_id
    await trigger_dynamic_spawn(chat_id)
    await reply_tag(event, f"✅ Forced spawn in {chat_id}.")

# ---- /spawnoff ----
@bot1.on(events.NewMessage(pattern=r'^/spawnoff(?:@\w+)?\s+([-\d]+)(?:\s+(on|off))?$'))
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
@bot1.on(events.NewMessage(pattern=r'^/spawnstats(?:@\w+)?(?:\s+([-\d]+))?$'))
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
@bot1.on(events.NewMessage(pattern=r'^/changetime(?:@\w+)?\s+(\d+)(?:\s+(\d+))?$'))
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
@bot1.on(events.NewMessage(pattern=r'^/status(?:@\w+)?$'))
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
@bot1.on(events.NewMessage(pattern=r'^/balance(?:@\w+)?$'))
async def balance_handler(event):
    user_id = event.sender_id
    bal = await get_balance(user_id)
    await reply_tag(event, f"💰 Balance: {bal:,} MMK")

# ---- /daily ----
@bot1.on(events.NewMessage(pattern=r'^/daily(?:@\w+)?$'))
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
@bot1.on(events.NewMessage(pattern=r'^/slot(?:@\w+)?(?:\s+(\d+))?'))
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
@bot1.on(events.NewMessage(pattern=r'^/top(?:@\w+)?$'))
async def top_handler(event): await send_leaderboard(event, "local")
@bot1.on(events.NewMessage(pattern=r'^/gtop(?:@\w+)?$'))
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

# ---- /tr (Translator) ----
@bot1.on(events.NewMessage(pattern=r'^/tr(?:@\w+)?(.*)'))
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

# ---- /calc (Auto Calculator) ----
@bot1.on(events.NewMessage)
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
@bot1.on(events.NewMessage(pattern=r'^/id(?:@\w+)?$'))
async def id_handler(event):
    target = await event.get_sender() if not event.is_reply else await (await event.get_reply_message()).get_sender()
    uid = target.id
    name = target.first_name or "User"
    username = f"@{target.username}" if target.username else "None"
    await reply_tag(event, f"👤 {name}\n🆔 {uid}\n🌐 {username}\n📌 Chat: {event.chat_id}")

# ---- /help ----
@bot1.on(events.NewMessage(pattern=r'^/help(?:@\w+)?$'))
async def help_handler(event):
    help_text = (
        "🤖 Commands\n\n"
        "🎮 Catching\n/w, /gases [name], /harem, /myinfo, /fav [ID]\n/check [ID], /hmode (rarity priority)\n"
        "💰 Economy\n/balance, /daily, /slot [amount], /top, /gtop\n"
        "🛠️ Utility\n/tr [text], /id\n"
        "👑 Owner\n/addcharacter, /removecharacter, /editcharacter\n/fspawn, /spawnoff, /spawnstats, /changetime, /status"
    )
    await reply_tag(event, help_text)

# ---- /gban ----
@bot1.on(events.NewMessage(pattern=r'^/gban(?:@\w+)?\s+(\d+)(?:\s+(.*))?$'))
async def gban_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    uid = int(event.pattern_match.group(1))
    reason = event.pattern_match.group(2) or "No reason"
    await banned_users_col.update_one({"user_id": uid}, {"$set": {"banned": True, "reason": reason}}, upsert=True)
    await reply_tag(event, f"✅ User {uid} banned.")

@bot1.on(events.NewMessage(pattern=r'^/'))
async def check_ban(event):
    if event.sender_id == OWNER_ID:
        return
    banned = await banned_users_col.find_one({"user_id": event.sender_id})
    if banned and banned.get("banned", False):
        await reply_tag(event, "❌ You are banned.")
        raise events.StopPropagation


@bot1.on(events.NewMessage(pattern=r'^/unban(?:@\w+)?\s+(\d+)$'))
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
# ==========================================
# 🔄 CALLBACK QUERY HANDLERS
# ==========================================
@bot1.on(events.CallbackQuery)
async def callback_handler(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    
    # Harem Pagination
    if data.startswith("hpage_"):
        parts = data.split("_")
        page = int(parts[1])
        target_user_id = int(parts[2])
        if user_id != target_user_id:
            await event.answer("⚠️ This is not your harem.", alert=True)
            return
        await event.answer()
        # Get original message and edit
        msg = await event.get_message()
        await send_harem_page(event, target_user_id, page=page, edit_msg_id=msg.id, callback_query=event)
        return
    
    # Go to HMODE from harem
    if data.startswith("goto_hmode_"):
        target_user_id = int(data.split("_")[2])
        if user_id != target_user_id:
            await event.answer("⚠️ This is not your menu.", alert=True)
            return
        await event.answer("Opening Rarity Filter...")
        # Simulate /hmode by sending a new message or editing
        await hmode_handler(event)
        return
    
    # HMODE Filter selection
    if data.startswith("hfilter_"):
        parts = data.split("_")
        if parts[1] == "clear":
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": None}}, upsert=True)
            await event.answer("🔓 Filter cleared!", alert=True)
        else:
            rarity = parts[1]
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": rarity}}, upsert=True)
            await event.answer(f"✅ Priority set to {rarity}", alert=True)
        
        # Update the hmode message to reflect change
        try:
            await hmode_handler(event)
        except:
            pass
        return

# ==========================================
# 🚀 STARTUP
# ==========================================
async def startup():
    global bot1  # ✅ ဒီစာကြောင်း ထည့်ပါ (bot1 ကို အပြင်ကနေသုံးလို့ရအောင်)
    
    print("Starting bot...")
    
    # ✅ ဒီမှာ bot1 ကို အသက်သွင်းပါ
    bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH)
    
    await users_catcher_col.create_index("user_id", unique=True)
    await characters_base_col.create_index("char_id", unique=True)
    await groups_col.create_index("chat_id", unique=True)
    asyncio.create_task(spawn_cleaner())
    await bot1.start(bot_token=BOT_TOKEN)
    print("Bot is running.")
    await bot1.run_until_disconnected()

if __name__ == "__main__":
    asyncio.run(startup())
