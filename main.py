import os
import io
import json
import asyncio
import random
import time
import logging
import re
import threading
import pytz
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, HTTPServer
from collections import defaultdict, Counter
from datetime import datetime, timedelta
from html import escape as escape_html
import aiohttp
from bson import json_util
from dotenv import load_dotenv
from telethon import TelegramClient, events, errors, Button
from telethon.tl.functions.channels import GetParticipantRequest
from telethon.tl.functions.messages import ExportChatInviteRequest
from telethon.errors import UserNotParticipantError, FloodWaitError
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
CARDS_PER_PAGE = 10
HAREM_PAGE_CHAR_BUDGET = 700
DAILY_CATCH_LIMIT = 30
SPAM_MSG_WINDOW = 60  # seconds
SPAM_MSG_THRESHOLD = 13
SPAM_MUTE_SECONDS = 480  # 8 minutes

# ==========================================
# 🌐 Render Port-Binding Fix
# ==========================================
def _start_health_server():
    port = int(os.getenv("PORT", "8080"))
    class _Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.end_headers()
            self.wfile.write(b"OK - bot is running")
        def log_message(self, *args):
            pass
    try:
        server = HTTPServer(("0.0.0.0", port), _Handler)
        server.serve_forever()
    except Exception as e:
        logging.error(f"Health server failed: {e}")

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
bot_owners_col = db["bot_owners"]

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

def rarity_from_num(num):
    try:
        idx = int(num) - 1
        if 0 <= idx < len(RARITY_TIERS):
            return RARITY_TIERS[idx]["name"]
    except:
        pass
    return None

# ==========================================
# Own-username command guard
# ==========================================
BOT_USERNAME = None
_OWN_MENTION_RE = re.compile(r'^[/.]\S*?@(\w+)')

def own_pattern(regex_str):
    compiled = re.compile(regex_str)
    def matcher(text):
        if not text:
            return None
        m = compiled.match(text)
        if not m:
            return None
        mention = _OWN_MENTION_RE.match(text)
        if mention:
            if BOT_USERNAME and mention.group(1).lower() != BOT_USERNAME:
                return None
        return m
    return matcher

# ==========================================
# Global variables
# ==========================================
bot = None
active_spawns = {}
spawn_locks = defaultdict(asyncio.Lock)
pending_rarity_quiz = {}
RARITY_GATE_TIERS = {"Bear", "Rainbow"}
RARITY_GATE_TIMEOUT = 120
group_spawn_counters = {}  # in-memory counters for batch writing
user_spam_data = {}  # (user_id, chat_id) -> list of timestamps
user_mute_until = {}  # user_id -> timestamp when mute expires

# ==========================================
# Helpers
# ==========================================
async def reply_tag(event, text, **kwargs):
    return await event.reply(text, **kwargs)

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
                "last_hunt": 0,
                "daily_catches": 0,
                "last_catch_date": None,
                "achievements": [],
                "total_gifted": 0,
                "total_received": 0
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

async def is_owner(user_id):
    return user_id == OWNER_ID

TZ = pytz.timezone('Asia/Yangon')

async def send_daily_report():
    # Get yesterday's stats
    now = datetime.now(TZ)
    yesterday_start = (now - timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    today_start = now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp()

    pipeline = [
        {"$unwind": "$harem"},
        {"$match": {"harem.caught_date": {"$gte": yesterday_start, "$lt": today_start}}},
        {"$facet": {
            "totals": [{"$group": {"_id": None, "total": {"$sum": 1}, "catchers": {"$addToSet": "$user_id"}, "groups": {"$addToSet": "$harem.chat_id"}}}],
            "rarity": [{"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}]
        }}
    ]
    result = await users_catcher_col.aggregate(pipeline).to_list(length=1)
    doc = result[0] if result else {"totals": [], "rarity": []}
    totals = doc["totals"][0] if doc["totals"] else {"total": 0, "catchers": [], "groups": []}
    rarity = {r["_id"]: r["count"] for r in doc["rarity"]}

    text = f"📊 **Daily Report – {yesterday_start_date}**\n"
    text += f"🐇 Total Catches: {totals['total']}\n"
    text += f"👥 Unique Catchers: {len(totals['catchers'])}\n"
    text += f"🪐 Groups Active: {len(totals['groups'])}\n\n"
    text += "**Rarity Breakdown:**\n"
    for tier in RARITY_TIERS:
        count = rarity.get(tier["name"], 0)
        if count:
            text += f"{RARITY_EMOJI[tier['name']]} {tier['name']}: {count}\n"
    # Send to owner
    try:
        await bot.send_message(OWNER_ID, text, parse_mode='markdown')
    except:
        pass

async def daily_report_scheduler():
    while True:
        now = datetime.now(TZ)
        target = now.replace(hour=6, minute=0, second=0, microsecond=0)
        if now >= target:
            target += timedelta(days=1)
        await asyncio.sleep((target - now).seconds)
        await send_daily_report()

# ==========================================
# Batch writing for spawn counters
# ==========================================
async def group_counter_flush_loop():
    while True:
        await asyncio.sleep(48)
        try:
            snapshot = dict(group_spawn_counters)
            if not snapshot:
                continue
            ops = [
                UpdateOne({"chat_id": cid}, {"$set": {"counter": val}}, upsert=True)
                for cid, val in snapshot.items()
            ]
            await groups_counters_col.bulk_write(ops, ordered=False)
        except Exception as e:
            logging.error(f"Group counter flush error: {e}")

# ==========================================
# Spam protection
# ==========================================
async def spam_detection_and_mute(event):
    if event.is_private or event.sender_id == OWNER_ID:
        return
    if not event.text and not event.media:
        return
    user_id = event.sender_id
    chat_id = event.chat_id
    now = time.time()
    # Only track if user is not already muted globally
    if user_id in user_mute_until and now < user_mute_until[user_id]:
        # Already muted, block commands
        if _extract_command_word(event.text) in ['/obtain', '/w']:
            try:
                await event.delete()
            except:
                pass
        return

    key = (user_id, chat_id)
    if key not in user_spam_data:
        user_spam_data[key] = []
    # Clean old entries
    user_spam_data[key] = [t for t in user_spam_data[key] if now - t < SPAM_MSG_WINDOW]
    user_spam_data[key].append(now)

    if len(user_spam_data[key]) >= SPAM_MSG_THRESHOLD:
        # Mute this user globally from catching commands
        user_mute_until[user_id] = now + SPAM_MUTE_SECONDS
        user_spam_data[key] = []
        try:
            sender = await event.get_sender()
            mention = await get_mention(event.client, user_id)
            await event.respond(
                f"🧹 {mention} သင်သည် စာတွေ အများကြီးပို့လို့ /obtain နဲ့ /w ကို {SPAM_MUTE_SECONDS//60} မိနစ် ပိတ်ထားပါပြီ။",
                parse_mode='html'
            )
        except:
            pass
        try:
            await event.delete()
        except:
            pass

def _extract_command_word(text):
    if not text or not text[0] in ('/', '.'):
        return None
    rest = text[1:]
    word = rest.split()[0] if rest.split() else rest
    return '/' + word.split('@')[0]

# ==========================================
# Daily catch reset
# ==========================================
async def check_daily_reset(user_id):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        return
    last_date = user_doc.get("last_catch_date")
    today = datetime.now().date()
    if last_date:
        last_date = datetime.fromtimestamp(last_date).date() if isinstance(last_date, (int, float)) else last_date.date()
        if last_date != today:
            # Reset daily catches
            await users_catcher_col.update_one(
                {"user_id": user_id},
                {"$set": {"daily_catches": 0, "last_catch_date": time.time()}}
            )

# ==========================================
# Rarity Gate Quiz
# ==========================================
async def start_rarity_gate_quiz(chat_id, chosen_char):
    if chat_id in pending_rarity_quiz:
        return False
    a = random.randint(1, 10)
    b = random.randint(1, 10)
    op = random.choice(['+', '-'])
    if op == '+':
        correct = a + b
        wrong = [correct + random.randint(-3, 3) for _ in range(3)]
        wrong = [x for x in wrong if x != correct and x >= 0]
        while len(wrong) < 3:
            wrong.append(correct + random.randint(1, 5))
        options = [correct] + wrong[:3]
        random.shuffle(options)
        correct_index = options.index(correct)
        question = f"{a} + {b} = ?"
    else:
        if a < b: a, b = b, a
        correct = a - b
        wrong = [correct + random.randint(-3, 3) for _ in range(3)]
        wrong = [x for x in wrong if x != correct and x >= 0]
        while len(wrong) < 3:
            wrong.append(correct + random.randint(1, 5))
        options = [correct] + wrong[:3]
        random.shuffle(options)
        correct_index = options.index(correct)
        question = f"{a} - {b} = ?"

    quiz_text = (
        f"🧠 **Rarity Gate – {chosen_char['rarity']}**\n"
        f"Answer correctly to release the character!\n\n"
        f"❓ {question}\n"
        f"⏱ {RARITY_GATE_TIMEOUT}s – first correct tap wins!"
    )
    buttons = [[Button.inline(f"{i+1}. {opt}", data=f"rgate_{chat_id}_{i}")] for i, opt in enumerate(options)]
    try:
        sent = await bot.send_message(chat_id, quiz_text, buttons=buttons, parse_mode='markdown')
    except:
        return False
    pending_rarity_quiz[chat_id] = {
        "char": chosen_char,
        "options": options,
        "correct_index": correct_index,
        "question": question,
        "msg_id": sent.id,
        "quiz_time": time.time(),
        "solved": False,
        "attempted_users": set()
    }
    asyncio.create_task(rarity_gate_timeout(chat_id, sent.id))
    return True

async def rarity_gate_timeout(chat_id, msg_id):
    await asyncio.sleep(RARITY_GATE_TIMEOUT)
    quiz = pending_rarity_quiz.get(chat_id)
    if quiz and quiz.get("msg_id") == msg_id and not quiz.get("solved"):
        pending_rarity_quiz.pop(chat_id, None)
        try:
            await bot.edit_message(chat_id, msg_id, "⏰ Time's up! The character vanished.", buttons=None, parse_mode='markdown')
        except:
            pass

@bot.on(events.CallbackQuery(pattern=r'^rgate_(-?\d+)_(\d)$'))
async def rarity_gate_callback(event):
    chat_id = int(event.pattern_match.group(1))
    chosen_idx = int(event.pattern_match.group(2))
    quiz = pending_rarity_quiz.get(chat_id)
    if not quiz or quiz.get("solved"):
        return await event.answer("⌛ This gate is closed.", alert=True)
    if time.time() - quiz["quiz_time"] > RARITY_GATE_TIMEOUT:
        return await event.answer("⏰ Time's up!", alert=True)
    attempted = quiz.setdefault("attempted_users", set())
    if event.sender_id in attempted:
        return await event.answer("You already used your one attempt.", alert=True)
    attempted.add(event.sender_id)

    if chosen_idx != quiz["correct_index"]:
        return await event.answer("❌ Wrong answer. No second chance.", alert=True)

    # Correct!
    quiz["solved"] = True
    async with spawn_locks[chat_id]:
        if chat_id in pending_rarity_quiz:
            del pending_rarity_quiz[chat_id]
    await event.answer("✅ Correct! Releasing the character...", alert=True)
    await release_spawn(chat_id, quiz["char"])

# ==========================================
# Spawn system
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
    async with spawn_locks[chat_id]:
        if chat_id in active_spawns:
            return
        disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
        if disabled and disabled.get("disabled", False):
            return
        all_chars = await characters_base_col.find().to_list(length=None)
        if not all_chars:
            return
        available = [c for c in all_chars if c.get('spawn_count', 0) < c.get('spawn_limit', 0) or c.get('spawn_limit', 0) == 0]
        if not available:
            return
        weights = []
        for c in available:
            rarity = classify_rarity(c.get("rarity", "Lower"))
            weight = 100 - (RARITY_ORDER.get(rarity, 6) * 10)
            weights.append(max(1, weight))
        chosen = random.choices(available, weights=weights, k=1)[0]
        storage_id = chosen.get("storage_msg_id")
        if not storage_id:
            return
        try:
            stored = await bot.get_messages(STORAGE_CHANNEL, ids=storage_id)
            if not stored or not stored.media:
                return
        except:
            return

        tier = classify_rarity(chosen.get("rarity", "Lower"))
        if tier in RARITY_GATE_TIERS:
            ok = await start_rarity_gate_quiz(chat_id, chosen)
            if ok:
                return
            # fall through
        await release_spawn(chat_id, chosen)

async def release_spawn(chat_id, chosen_char):
    try:
        storage_id = chosen_char.get("storage_msg_id")
        stored = await bot.get_messages(STORAGE_CHANNEL, ids=storage_id)
        if not stored or not stored.media:
            return False
        caption = (
            f"🦄 A character has spawned in this chat!\n"
            f"🍟 Add to harem using /obtain [ NAME ]\n"
            f"(reply /w to reveal the name)"
        )
        sent = await bot.send_message(chat_id, caption, file=stored.media, spoiler=True, parse_mode='html')
        active_spawns[chat_id] = {
            "char_id": chosen_char.get("char_id"),
            "name": chosen_char.get("name"),
            "series": chosen_char.get("series", "Unknown"),
            "rarity": classify_rarity(chosen_char.get("rarity", "Lower")),
            "spawn_time": time.time(),
            "claimed": False,
            "spawn_msg_id": sent.id
        }
        return True
    except Exception as e:
        logging.error(f"release_spawn error: {e}")
        return False

# ==========================================
# Message counter for spawn (with batch)
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
    if not config:
        config = await groups_config_col.find_one({"chat_id": "global"})
    target = config.get("spawn_target", 50) if config else 50

    # Increment in-memory counter
    new_count = group_spawn_counters.get(chat_id, 0) + 1
    group_spawn_counters[chat_id] = new_count
    if new_count >= target:
        group_spawn_counters[chat_id] = new_count - target
        await trigger_dynamic_spawn(chat_id)

# ==========================================
# /w – reveal
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/w(?:@\w+)?$')))
async def reveal_spawn_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return
    spawn_data = active_spawns[chat_id]
    if time.time() - spawn_data["spawn_time"] > 400:
        del active_spawns[chat_id]
        await reply_tag(event, "⏱️ The character has vanished! Try again later.")
        return
    if not event.is_reply:
        await reply_tag(event, "⚠️ Reply directly to the spawn message to reveal the character!")
        return
    reply_msg_id = event.reply_to_msg_id
    if reply_msg_id != spawn_data["spawn_msg_id"]:
        try:
            reply_to_obj = await event.get_reply_message()
            if reply_to_obj and reply_to_obj.sender_id != (await bot.get_me()).id:
                await reply_tag(event, "⚠️ Reply directly to the spawn message to reveal the character!")
                return
        except:
            await reply_tag(event, "⚠️ Reply directly to the spawn message to reveal the character!")
            return

    rarity = spawn_data["rarity"]
    rarity_emoji = RARITY_EMOJI.get(rarity, "⭐️")
    reveal_text = (
        f"🔍 **Character Revealed!**\n\n"
        f"🌟 **Name:** `{spawn_data['name']}`\n"
        f"⚜️ **Series:** {spawn_data['series']}\n"
        f"{rarity_emoji} **Rarity:** {rarity}\n\n"
        f"🍟 **Catch it with:** `/obtain {spawn_data['name']}`"
    )
    await reply_tag(event, reveal_text, parse_mode='markdown')

# ==========================================
# /obtain – catch (with daily limit and spam mute check)
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/obtain(?:@\w+)?\s+(.+)$')))
async def catch_handler(event):
    if event.is_private:
        return
    user_id = event.sender_id
    chat_id = event.chat_id

    # Check spam mute
    if user_id in user_mute_until and time.time() < user_mute_until[user_id]:
        await reply_tag(event, "⛔ You are currently muted from catching. Please wait.")
        return

    # Check daily limit
    await check_daily_reset(user_id)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    daily_catches = user_doc.get("daily_catches", 0) if user_doc else 0
    if daily_catches >= DAILY_CATCH_LIMIT:
        await reply_tag(event, f"📅 You've reached your daily catch limit of {DAILY_CATCH_LIMIT}. Come back tomorrow!")
        return

    name = event.pattern_match.group(1).strip()
    if not name:
        await reply_tag(event, "❓ Usage: /obtain [name]")
        return
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
        await reply_tag(event, "❌ Wrong name! Use /w to reveal the exact name.")
        return

    temp_msg = await event.reply("🍓")
    await asyncio.sleep(1.5)

    async with spawn_locks[chat_id]:
        if active_spawns.get(chat_id, {}).get("claimed", True):
            try:
                await temp_msg.delete()
            except:
                pass
            await reply_tag(event, "❌ Already caught by someone else!")
            return
        active_spawns[chat_id]["claimed"] = True
        mention = await get_mention(event.client, user_id)
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
                    f"group_catches.{str(chat_id)}": 1,
                    "daily_catches": 1
                },
                "$set": {"last_catch_date": time.time(), "fullname": mention}
            },
            upsert=True
        )
        await characters_base_col.update_one(
            {"char_id": spawn_data["char_id"]}, {"$inc": {"spawn_count": 1}}
        )
        value = get_rarity_value(spawn_data["rarity"])
        await add_balance(user_id, value)
        del active_spawns[chat_id]
        try:
            await temp_msg.delete()
        except:
            pass
        success_text = (
            f"✨ {mention}, you got a new character!\n\n"
            f"🌟 Name: <code>{escape_html(spawn_data['name'])}</code>\n"
            f"{RARITY_EMOJI.get(spawn_data['rarity'], '')} Rarity: {escape_html(spawn_data['rarity'])}\n"
            f"🔥 Anime: {escape_html(spawn_data['series'])}\n"
            f"💰 +{value:,} MMK\n\n"
            f"❕ Check your /harem now!"
        )
        await reply_tag(event, success_text, parse_mode='html')

# ==========================================
# /harem – with pagination and photo
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/harem(?:@\w+)?$')))
async def harem_handler(event):
    user_id = event.sender_id
    mention = await get_mention(event.client, user_id)
    await ensure_user_registered(user_id, mention)
    await send_harem_overview(event, user_id, page=1)

async def send_harem_overview(event, user_id, page=1, edit_msg_id=None):
    doc = await users_catcher_col.find_one({"user_id": user_id})
    if not doc:
        doc = {"harem": []}
    harem = doc.get("harem", [])
    if not harem:
        msg = "📭 Your harem is empty. Watch for a spawn with /w and catch it with /obtain [name]."
        if edit_msg_id:
            try:
                await event.client.edit_message(event.chat_id, edit_msg_id, msg, buttons=None, parse_mode='html')
            except:
                pass
        else:
            await reply_tag(event, msg)
        return

    blocks = []
    for item in harem:
        char_id = item.get("char_id")
        if not char_id:
            continue
        char_doc = await characters_base_col.find_one({"char_id": char_id})
        if not char_doc:
            continue
        rarity = classify_rarity(char_doc.get("rarity", "Lower"))
        series = char_doc.get("series", "Unknown")
        blocks.append(
            f"☘️ Name: {escape_html(char_doc.get('name', 'Unknown'))}\n"
            f"{RARITY_EMOJI.get(rarity, '•')} Rarity: {rarity}\n"
            f"⚜️ Anime: {escape_html(series)}\n"
            f"🆔 ID: <code>{escape_html(char_id)}</code>"
        )

    pages, current, current_len = [], [], 0
    for block in blocks:
        block_len = len(block) + 2
        if current and current_len + block_len > HAREM_PAGE_CHAR_BUDGET:
            pages.append("\n\n".join(current))
            current, current_len = [block], block_len
        else:
            current.append(block)
            current_len += block_len
    if current:
        pages.append("\n\n".join(current))
    total_pages = len(pages) or 1
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    body = pages[page - 1]

    caption = f"{escape_html(doc.get('fullname', 'User'))}'s Harem - Page: {page}/{total_pages}\n\n{body}"
    fav_id = doc.get("fav_card")
    media = None
    if fav_id:
        char_data = await characters_base_col.find_one({"char_id": fav_id})
        if char_data and char_data.get("storage_msg_id"):
            try:
                stored = await event.client.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
                if stored and stored.media:
                    media = stored.media
            except:
                pass

    nav_buttons = []
    if page > 1:
        nav_buttons.append(Button.inline("⬅️ Prev", data=f"hpage_{page-1}_{user_id}"))
    if page < total_pages:
        nav_buttons.append(Button.inline("Next ➡️", data=f"hpage_{page+1}_{user_id}"))
    buttons = [nav_buttons] if nav_buttons else []
    buttons.append([Button.switch_inline("🔍 Browse & Search", query=f"harem.{user_id} ", same_peer=True)])

    if edit_msg_id:
        try:
            if media:
                await event.client.edit_message(event.chat_id, edit_msg_id, caption, file=media, parse_mode='html', buttons=buttons)
            else:
                await event.client.edit_message(event.chat_id, edit_msg_id, caption, parse_mode='html', buttons=buttons)
            return
        except:
            pass

    if media:
        await event.client.send_file(event.chat_id, media, caption=caption, parse_mode='html', buttons=buttons)
    else:
        await reply_tag(event, caption, parse_mode='html', buttons=buttons)

# ==========================================
# Inline query for harem
# ==========================================
@bot.on(events.InlineQuery)
async def harem_inline(event):
    query_text = event.text or ""
    if not query_text.startswith("harem."):
        return
    try:
        target_user_id = int(query_text.split(".")[1].split()[0])
    except:
        return
    doc = await users_catcher_col.find_one({"user_id": target_user_id})
    if not doc or not doc.get("harem"):
        await event.answer([], switch_pm="📭 This vault is empty!", switch_pm_param="start")
        return
    harem = doc.get("harem", [])
    results = []
    builder = event.builder
    count = 0
    for item in harem:
        if count >= 50:
            break
        char_id = item.get("char_id")
        if not char_id:
            continue
        char_data = await characters_base_col.find_one({"char_id": char_id})
        if not char_data or not char_data.get("storage_msg_id"):
            continue
        try:
            stored = await bot.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if not stored or not stored.media:
                continue
            rarity = classify_rarity(char_data.get("rarity", "Lower"))
            emoji = RARITY_EMOJI.get(rarity, '')
            caption = f"🌟 {char_data.get('name', 'Unknown')}\n{emoji} {rarity}\n⚜️ {char_data.get('series', 'Unknown')}\n🆔 {char_id}"
            if stored.photo:
                results.append(builder.photo(file=stored.media, id=char_id, text=caption, parse_mode='html'))
            elif stored.video:
                results.append(builder.video(file=stored.media, id=char_id, text=caption, parse_mode='html'))
            else:
                results.append(builder.document(file=stored.media, id=char_id, text=caption, parse_mode='html'))
            count += 1
        except:
            continue
    await event.answer(results, cache_time=0)

# ==========================================
# /addcharacter & /ac – auto ID (no BOD)
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/(?:addcharacter|ac)(?:@\w+)?\s+(.+)\s*\|\s*(.+)\s*\|\s*([1-7])\s*\|\s*(.+)(?:\s*\|\s*(\d+))?$')))
async def addcharacter_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to a media file (photo/video).")
        return

    parts = event.pattern_match.groups()
    name = parts[0].strip()
    series = parts[1].strip()
    rarity_num = parts[2].strip()
    event_name = parts[3].strip() if parts[3] else "General"
    spawn_limit = int(parts[4]) if parts[4] else 0

    rarity_name = rarity_from_num(rarity_num)
    if not rarity_name:
        await reply_tag(event, "❌ Invalid rarity number. Use 1-7.")
        return

    # Auto-generate ID without BOD prefix
    char_id = str(random.randint(1000, 9999))
    while await characters_base_col.find_one({"char_id": char_id}):
        char_id = str(random.randint(1000, 9999))

    reply_msg = await event.get_reply_message()
    if not (reply_msg.photo or reply_msg.video or reply_msg.document):
        await reply_tag(event, "❌ Media not found.")
        return

    try:
        stored = await event.client.send_file(STORAGE_CHANNEL, reply_msg.media)
        storage_msg_id = stored.id
    except Exception as e:
        await reply_tag(event, f"❌ Failed to store media: {e}")
        return

    char_data = {
        "char_id": char_id,
        "name": name,
        "series": series,
        "rarity": rarity_name,
        "events": event_name,
        "spawn_limit": spawn_limit,
        "spawn_count": 0,
        "storage_msg_id": storage_msg_id
    }
    await characters_base_col.insert_one(char_data)
    await reply_tag(event,
        f"✅ Character added:\n"
        f"ID: {char_id}\n"
        f"Name: {name}\n"
        f"Series: {series}\n"
        f"Rarity: {rarity_name}\n"
        f"Event: {event_name}\n"
        f"Max Spawn: {spawn_limit if spawn_limit > 0 else 'Infinite'}",
        parse_mode='html'
    )

# ==========================================
# /migratestorage – move all media to new group
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/migratestorage(?:@\w+)?\s+(-?\d+)$')))
async def migrate_storage_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    new_group = int(event.pattern_match.group(1))
    if new_group == STORAGE_CHANNEL:
        await reply_tag(event, "❌ New group is same as current storage. No change.")
        return

    status_msg = await reply_tag(event, "⏳ Migrating media to new storage group... This may take a while.")
    all_chars = await characters_base_col.find().to_list(length=None)
    if not all_chars:
        await status_msg.edit("📭 No characters to migrate.")
        return

    updated = 0
    failed = 0
    for char in all_chars:
        old_id = char.get("storage_msg_id")
        if not old_id:
            continue
        try:
            old_msg = await bot.get_messages(STORAGE_CHANNEL, ids=old_id)
            if not old_msg or not old_msg.media:
                failed += 1
                continue
            new_msg = await bot.send_file(new_group, old_msg.media)
            new_storage_id = new_msg.id
            await characters_base_col.update_one(
                {"char_id": char["char_id"]},
                {"$set": {"storage_msg_id": new_storage_id}}
            )
            updated += 1
            await asyncio.sleep(0.5)
        except Exception as e:
            logging.error(f"Migrate error for {char['char_id']}: {e}")
            failed += 1
    await status_msg.edit(f"✅ Migration complete.\nUpdated: {updated}\nFailed: {failed}\nNew storage group: {new_group}")

# ==========================================
# /gift [char_id] – gift a card to replied user
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/gift(?:@\w+)?\s+(\S+)$')))
async def gift_handler(event):
    user_id = event.sender_id
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to the person you want to gift.")
        return
    char_id = event.pattern_match.group(1).strip()
    reply_msg = await event.get_reply_message()
    receiver_id = reply_msg.sender_id
    if receiver_id == user_id:
        await reply_tag(event, "❌ You can't gift to yourself.")
        return

    # Check if sender owns this card
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        await reply_tag(event, "❌ You don't have any cards.")
        return
    harem = user_doc.get("harem", [])
    card_item = next((c for c in harem if c.get("char_id") == char_id), None)
    if not card_item:
        await reply_tag(event, f"❌ You don't own card ID {char_id}.")
        return

    # Remove from sender
    new_harem = [c for c in harem if c.get("char_id") != char_id]
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$set": {"harem": new_harem}, "$inc": {"total_gifted": 1}}
    )

    # Add to receiver
    receiver_mention = await get_mention(event.client, receiver_id)
    await ensure_user_registered(receiver_id, receiver_mention)
    await users_catcher_col.update_one(
        {"user_id": receiver_id},
        {
            "$push": {"harem": card_item},
            "$inc": {"total_caught": 1, "total_received": 1}
        }
    )

    await reply_tag(
        event,
        f"🎁 Gifted {escape_html(card_item.get('name', 'Unknown'))} to {receiver_mention}!",
        parse_mode='html'
    )

# ==========================================
# /profile – enhanced profile
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/profile(?:@\w+)?$')))
async def profile_handler(event):
    try:
        if event.is_private:
            # DM မှာလည်း အလုပ်လုပ်အောင်
            pass
        user_id = event.sender_id
        mention = await get_mention(event.client, user_id)
        await ensure_user_registered(user_id, mention)
        doc = await users_catcher_col.find_one({"user_id": user_id})
        if not doc:
            await reply_tag(event, "❌ User not found.")
            return

        total = doc.get("total_caught", 0)
        balance = doc.get("wallet_balance", 0)
        daily = doc.get("daily_catches", 0)
        gifted = doc.get("total_gifted", 0)
        received = doc.get("total_received", 0)
        r_counts = doc.get("rarity_counts", {t["name"]: 0 for t in RARITY_TIERS})
        fav = doc.get("fav_card")
        fav_name = None
        if fav:
            fav_doc = await characters_base_col.find_one({"char_id": fav})
            if fav_doc:
                fav_name = fav_doc["name"]

        # Global rank
        rank = await users_catcher_col.count_documents({"total_caught": {"$gt": total}}) + 1

        rarity_lines = []
        for tier in RARITY_TIERS:
            count = r_counts.get(tier["name"], 0)
            if count:
                rarity_lines.append(f"├─➩ {RARITY_EMOJI[tier['name']]} {tier['name']}: {count}")

        text = (
            f"👤 **{mention}**\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🏆 **Global Rank:** #{rank}\n"
            f"🎒 **Total Caught:** {total}\n"
            f"📅 **Today's Catches:** {daily}/{DAILY_CATCH_LIMIT}\n"
            f"💰 **Balance:** {balance:,} MMK\n"
            f"🎁 **Gifted:** {gifted}  |  📥 **Received:** {received}\n"
            f"⭐ **Favorite Card:** {fav_name if fav_name else 'None'}\n\n"
            "**Rarity Breakdown:**\n" + "\n".join(rarity_lines) + "\n━━━━━━━━━━━━━━━━━━━━\n"
            "<i>Use /harem to view your collection.</i>"
        )

        # Try to send with profile photo
        try:
            photos = await event.client.get_profile_photos(user_id, limit=1)
            if photos:
                await event.client.send_file(event.chat_id, photos[0], caption=text, parse_mode='markdown')
            else:
                await reply_tag(event, text, parse_mode='markdown')
        except Exception as e:
            # Profile photo can't be fetched, send text only
            await reply_tag(event, text, parse_mode='markdown')
    except Exception as e:
        logging.error(f"Profile error: {e}")
        await reply_tag(event, "❌ Profile loading error. Please try again later.", parse_mode='markdown')
        
# ==========================================
# /top – local top 10
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/top(?:@\w+)?$')))
async def top_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    cursor = users_catcher_col.find({f"group_catches.{str(chat_id)}": {"$gt": 0}}).sort(f"group_catches.{str(chat_id)}", -1).limit(10)
    top = await cursor.to_list(length=10)
    if not top:
        await reply_tag(event, "🏆 No catches in this group yet.")
        return
    msg = "🏆 **TOP 10 IN THIS GROUP**\n\n"
    medals = ["🥇", "🥈", "🥉"]
    for i, doc in enumerate(top):
        uid = doc.get("user_id")
        count = doc.get("group_catches", {}).get(str(chat_id), 0)
        mention = await get_mention(event.client, uid)
        rank = medals[i] if i < 3 else f"{i+1}."
        msg += f"{rank} {mention} — {count} catches\n"
    await reply_tag(event, msg, parse_mode='markdown')

# ==========================================
# /gtop – global top 10
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/gtop(?:@\w+)?$')))
async def gtop_handler(event):
    cursor = users_catcher_col.find({"total_caught": {"$gt": 0}}).sort("total_caught", -1).limit(10)
    top = await cursor.to_list(length=10)
    if not top:
        await reply_tag(event, "🌐 No catches globally yet.")
        return
    msg = "🌐 **GLOBAL TOP 10**\n\n"
    medals = ["🥇", "🥈", "🥉"]
    for i, doc in enumerate(top):
        uid = doc.get("user_id")
        count = doc.get("total_caught", 0)
        mention = await get_mention(event.client, uid)
        rank = medals[i] if i < 3 else f"{i+1}."
        msg += f"{rank} {mention} — {count} catches\n"
    await reply_tag(event, msg, parse_mode='markdown')

# ==========================================
# /stats – global stats
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/stats(?:@\w+)?$')))
async def stats_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return

    total_users = await users_catcher_col.count_documents({})
    total_groups = await groups_col.count_documents({})
    total_chars = await characters_base_col.count_documents({})
    total_catches = await users_catcher_col.aggregate([
        {"$group": {"_id": None, "total": {"$sum": "$total_caught"}}}
    ]).to_list(length=1)
    total_catches = total_catches[0]["total"] if total_catches else 0

    # Rarity breakdown from all caught cards
    pipeline = [
        {"$unwind": "$harem"},
        {"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}
    ]
    rarity_break = await users_catcher_col.aggregate(pipeline).to_list(length=None)
    rarity_lines = []
    for tier in RARITY_TIERS:
        count = next((r["count"] for r in rarity_break if r["_id"] == tier["name"]), 0)
        rarity_lines.append(f"{RARITY_EMOJI[tier['name']]} {tier['name']}: {count}")

    text = (
        "📊 **GLOBAL STATS**\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 **Total Users:** {total_users}\n"
        f"🪐 **Active Groups:** {total_groups}\n"
        f"🃏 **Total Characters:** {total_chars}\n"
        f"🐇 **Total Catches:** {total_catches}\n\n"
        "**Rarity Distribution:**\n" + "\n".join(rarity_lines)
    )
    await reply_tag(event, text, parse_mode='markdown')

# ==========================================
# /mau – monthly active users
@bot.on(events.NewMessage(pattern=own_pattern(r'^/mau(?:@\w+)?$')))
async def mau_handler(event):
    try:
        if not await is_owner(event.sender_id):
            await reply_tag(event, "❌ Owner only.", parse_mode='markdown')
            return
        total_users = await users_catcher_col.count_documents({})
        active_24h = await users_catcher_col.count_documents({"last_catch_date": {"$gte": time.time() - 86400}})
        total_groups = await groups_col.count_documents({})
        text = (
            "📊 **MAU Stats**\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"👥 **Total Users:** {total_users}\n"
            f"🔥 **Active (24h):** {active_24h}\n"
            f"🪐 **Active Groups:** {total_groups}"
        )
        await reply_tag(event, text, parse_mode='markdown')
    except Exception as e:
        logging.error(f"MAU error: {e}")
        await reply_tag(event, "❌ MAU stats error. Please try again later.", parse_mode='markdown')
@bot.on(events.NewMessage(pattern=own_pattern(r'^[/.]send(?:@\w+)?(?:\s+(.*))?$')))
async def broadcast_command(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.", parse_mode='html')
        return

    reply_msg = await event.get_reply_message()
    command_text = event.pattern_match.group(1) if event.pattern_match.group(1) else None

    # ဘာမှမပါရင် သုံးပုံပြပါ
    if not reply_msg and not command_text:
        await reply_tag(
            event,
            "📢 **Usage:**\n"
            "• Reply to a message with `/send` to forward it to all groups.\n"
            "• Or type `/send Hello everyone!` to broadcast a text message.",
            parse_mode='markdown'
        )
        return

    status_msg = await reply_tag(event, "📢 <b>BROADCAST INITIATED</b>", parse_mode='html')
    groups = await groups_col.find().to_list(length=None)
    if not groups:
        await status_msg.edit("⚠️ No groups found in database.", parse_mode='html')
        return

    success = 0
    fail = 0

    for g in groups:
        chat_id = g['chat_id']
        try:
            if reply_msg:
                await bot.forward_messages(chat_id, reply_msg)
            else:
                await bot.send_message(chat_id, command_text, parse_mode='html')
            success += 1
            await asyncio.sleep(4)  # Flood protection

        except FloodWaitError as e:
            # Flood wait ကျရင် စောင့်ပြီး ပြန်ကြိုးစားမယ် (တစ်ခါပဲ)
            await asyncio.sleep(e.seconds + 2)
            try:
                if reply_msg:
                    await bot.forward_messages(chat_id, reply_msg)
                else:
                    await bot.send_message(chat_id, command_text, parse_mode='html')
                success += 1
            except Exception:
                fail += 1
        except Exception:
            fail += 1

    await status_msg.edit(
        f"✅ <b>BROADCAST COMPLETE</b>\n"
        f"📨 <b>Success:</b> <code>{success}</code>\n"
        f"❌ <b>Failed:</b> <code>{fail}</code>",
        parse_mode='html'
            )

# ==========================================
# /today – today's top catchers
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/today(?:@\w+)?$')))
async def today_handler(event):
    today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    cursor = users_catcher_col.find(
        {"last_catch_date": {"$gte": today_start}, "daily_catches": {"$gt": 0}}
    ).sort("daily_catches", -1).limit(10)
    top = await cursor.to_list(length=10)
    if not top:
        await reply_tag(event, "📭 No catches today yet.")
        return
    msg = "📅 **Today's Top Catchers**\n\n"
    medals = ["🥇", "🥈", "🥉"]
    for i, doc in enumerate(top):
        uid = doc.get("user_id")
        count = doc.get("daily_catches", 0)
        mention = await get_mention(event.client, uid)
        rank = medals[i] if i < 3 else f"{i+1}."
        msg += f"{rank} {mention} — {count} catches\n"
    await reply_tag(event, msg, parse_mode='markdown')

# ==========================================
# /balance, /daily – unchanged but we keep them
# ==========================================
@bot.on(events.NewMessage(pattern=own_pattern(r'^/balance(?:@\w+)?$')))
async def balance_handler(event):
    bal = await get_balance(event.sender_id)
    await reply_tag(event, f"💰 Balance: {bal:,} MMK")

@bot.on(events.NewMessage(pattern=own_pattern(r'^/daily(?:@\w+)?$')))
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

# ==========================================
# Startup
# ==========================================
async def startup():
    global bot, BOT_USERNAME
    threading.Thread(target=_start_health_server, daemon=True).start()
    bot = TelegramClient('bot_session', APP_ID, APP_HASH)
    # Register event handlers (spam detection, message counter)
    bot.add_event_handler(spam_detection_and_mute, events.NewMessage)
    bot.add_event_handler(message_counter_for_spawn, events.NewMessage(incoming=True))
    # All command handlers are already decorated with @bot.on, so they are registered
    await bot.start(bot_token=BOT_TOKEN)
    me = await bot.get_me()
    if me.username:
        BOT_USERNAME = me.username.lower()
    # Start background tasks
    asyncio.create_task(group_counter_flush_loop())
    asyncio.create_task(spawn_cleaner())
    print(f"Bot started as @{me.username}")
    await bot.run_until_disconnected()

if __name__ == "__main__":
    asyncio.run(startup())
