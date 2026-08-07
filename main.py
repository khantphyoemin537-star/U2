import os
import io
import json
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

REQUIRED_GROUP_ID = int(os.getenv("REQUIRED_GROUP_ID", "0"))
REQUIRED_GROUP_LINK = os.getenv("REQUIRED_GROUP_LINK", "https://t.me/your_group_link")

STORAGE_CHANNEL = SPECIFIC_CONTROL_GROUP
CARDS_PER_PAGE = 10
HAREM_PAGE_CHAR_BUDGET = 700

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
bot_owners_col = db["bot_owners"]  # New: stores owner IDs
import_state_col = db["bulk_import_state"]  # Tracks AniList bulk-import progress (resumable)

# All collections that exist in this bot's database — used by /resetall.
# Keep this list in sync whenever a new collection is added above.
ALL_COLLECTIONS = {
    "users_catcher_data": users_catcher_col,
    "characters_base_data": characters_base_col,
    "groups_catcher_config": groups_config_col,
    "active_groups": groups_col,
    "groups_msg_counters": groups_counters_col,
    "spawn_disabled_chats": spawn_disabled_col,
    "banned_users": banned_users_col,
    "bot_owners": bot_owners_col,
    "bulk_import_state": import_state_col,
}

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
# 🌐 AniList Bulk Import (name + series + image, auto rarity)
# ==========================================
# We use AniList's public GraphQL API instead of MyAnimeList/Jikan:
# Jikan's own docs state that using it to populate/build your own database
# breaches MyAnimeList's Terms of Service. AniList has no such restriction,
# gives a generous 90 req/min limit, and its Character type reliably pairs
# a character's name with the anime/manga (series) they appear in.
ANILIST_API_URL = "https://graphql.anilist.co"
ANILIST_PER_PAGE = 25          # characters fetched per GraphQL page
ANILIST_MIN_DELAY = 1.4        # seconds between AniList requests (~43/min, safely under 90/min)
TELEGRAM_SEND_DELAY = 1.2      # seconds between uploads to the storage channel (avoids flood-wait)

ANILIST_CHARACTERS_QUERY = """
query ($page: Int, $perPage: Int) {
  Page(page: $page, perPage: $perPage) {
    pageInfo { hasNextPage currentPage lastPage }
    characters(sort: FAVOURITES_DESC) {
      id
      name { full native }
      image { large }
      favourites
      media(perPage: 1, sort: POPULARITY_DESC) {
        nodes { type title { english romaji } }
      }
    }
  }
}
"""

# Rarity is auto-assigned from AniList's "favourites" count (a solid, reliable
# popularity signal from real site data) instead of being typed in by hand.
# Tune these thresholds any time — first match (highest threshold first) wins.
RARITY_FAVOURITES_THRESHOLDS = [
    (15000, "Bear"),
    (6000,  "Rainbow"),
    (2500,  "Crossverse"),
    (800,   "Trident"),
    (250,   "Koinobori"),
    (50,    "Medium"),
    (0,     "Lower"),
]

def rarity_from_favourites(favourites: int) -> str:
    favourites = favourites or 0
    for threshold, name in RARITY_FAVOURITES_THRESHOLDS:
        if favourites >= threshold:
            return name
    return "Lower"

# ==========================================
# Global Variables
# ==========================================
bot1 = None
bot2 = None
active_spawns = {}
spawn_locks = defaultdict(asyncio.Lock)
bulk_import_task = None      # the running asyncio.Task for /bulkimport, if any
bulk_import_stop_requested = False

# ==========================================
# Ban duration parsing
# ==========================================
DURATION_UNITS = {
    "min": 60, "mins": 60, "minute": 60, "minutes": 60,
    "h": 3600, "hr": 3600, "hrs": 3600, "hour": 3600, "hours": 3600,
    "d": 86400, "day": 86400, "days": 86400,
    "m": 2592000, "mo": 2592000, "month": 2592000, "months": 2592000,
    "y": 31536000, "yr": 31536000, "year": 31536000, "years": 31536000,
}

def parse_duration(text):
    if not text:
        return "INVALID"
    text = text.strip().lower()
    if text in ("perm", "permanent", "forever", "0"):
        return None
    match = re.match(r'^(\d+)\s*([a-z]+)$', text)
    if not match:
        return "INVALID"
    value, unit = match.groups()
    seconds = DURATION_UNITS.get(unit)
    if seconds is None:
        return "INVALID"
    return int(value) * seconds

def format_duration(seconds):
    if not seconds:
        return "Permanent"
    for unit_seconds, label in ((31536000, "year"), (2592000, "month"), (86400, "day"), (3600, "hour")):
        if seconds % unit_seconds == 0:
            n = seconds // unit_seconds
            return f"{n} {label}{'s' if n != 1 else ''}"
    n = max(1, seconds // 60)
    return f"{n} min{'s' if n != 1 else ''}"

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
# Owner management
# ==========================================
async def is_owner(user_id: int) -> bool:
    doc = await bot_owners_col.find_one({"_id": "owners"})
    if not doc:
        return False
    return user_id in doc.get("ids", [])

async def get_owner_ids() -> list:
    doc = await bot_owners_col.find_one({"_id": "owners"})
    owner_ids = set(doc.get("ids", [])) if doc else set()
    owner_ids.add(OWNER_ID)
    return list(owner_ids)

async def notify_owners(msg, parse_mode='markdown'):
    """Send a message to OWNER_ID plus every owner added via /co."""
    for oid in await get_owner_ids():
        try:
            await bot1.send_message(oid, msg, parse_mode=parse_mode)
        except Exception as e:
            logging.error(f"Failed to notify owner {oid}: {e}")

# ==========================================
# 🗄️ Full Database Backup + Reset (/resetall)
# ==========================================
async def dump_full_database_to_json() -> bytes:
    """Serialize every collection to a single JSON blob (kept as a safety
    backup right before a destructive /resetall wipe)."""
    snapshot = {}
    for coll_name, coll in ALL_COLLECTIONS.items():
        docs = await coll.find().to_list(length=None)
        snapshot[coll_name] = docs
    raw = json_util.dumps(snapshot, indent=2).encode("utf-8")
    return raw

async def wipe_all_collections() -> dict:
    """Deletes every document from every collection. Returns per-collection
    deleted counts. Reseeds bot_owners_col with OWNER_ID afterwards so the
    bot owner is never locked out of admin commands."""
    counts = {}
    for coll_name, coll in ALL_COLLECTIONS.items():
        result = await coll.delete_many({})
        counts[coll_name] = result.deleted_count
    await bot_owners_col.update_one(
        {"_id": "owners"},
        {"$addToSet": {"ids": OWNER_ID}},
        upsert=True
    )
    return counts

# ==========================================
# 🌐 AniList Bulk Import — helpers
# ==========================================
async def anilist_fetch_characters_page(session: "aiohttp.ClientSession", page: int):
    """Fetch one page of characters from AniList, handling rate limiting."""
    payload = {"query": ANILIST_CHARACTERS_QUERY, "variables": {"page": page, "perPage": ANILIST_PER_PAGE}}
    while True:
        async with session.post(ANILIST_API_URL, json=payload) as resp:
            if resp.status == 429:
                retry_after = int(resp.headers.get("Retry-After", "60"))
                logging.warning(f"AniList rate-limited, sleeping {retry_after}s")
                await asyncio.sleep(retry_after + 1)
                continue
            resp.raise_for_status()
            data = await resp.json()
            return data["data"]["Page"]

async def download_bytes(session: "aiohttp.ClientSession", url: str) -> bytes:
    async with session.get(url) as resp:
        resp.raise_for_status()
        return await resp.read()

async def send_to_storage_with_retry(client, file_bytes: bytes, filename: str, caption: str = None):
    """Uploads to STORAGE_CHANNEL, auto-retrying on Telegram flood-wait."""
    while True:
        try:
            bio = io.BytesIO(file_bytes)
            bio.name = filename
            return await client.send_file(STORAGE_CHANNEL, bio, caption=caption)
        except FloodWaitError as e:
            logging.warning(f"Flood wait, sleeping {e.seconds}s")
            await asyncio.sleep(e.seconds + 1)

def pick_series_title(media_nodes: list) -> str:
    if not media_nodes:
        return None
    node = media_nodes[0]
    title = node.get("title") or {}
    return title.get("english") or title.get("romaji")

def pick_character_name(name_obj: dict) -> str:
    if not name_obj:
        return None
    return name_obj.get("full") or name_obj.get("native")

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
    async with spawn_locks[chat_id]:
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
        except Exception as e:
            logging.error(f"Failed to fetch stored media for spawn in {chat_id}: {e}")
            return
        caption = "🦄 A character has spawned in this chat!\n🍟 Add to harem using /w and then /fuck [ NAME ]"
        try:
            sent_msg = await bot1.send_message(chat_id, caption, file=stored_msg.media)
        except Exception as e:
            logging.error(f"Failed to send spawn message to {chat_id}: {e}")
            return
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
# HANDLERS
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
    counter_doc = await groups_counters_col.find_one_and_update(
        {"chat_id": chat_id},
        {"$inc": {"counter": 1}},
        upsert=True,
        return_document=ReturnDocument.AFTER
    )
    if counter_doc and counter_doc.get("counter", 0) >= target:
        await groups_counters_col.update_one({"chat_id": chat_id}, {"$set": {"counter": 0}})
        await trigger_dynamic_spawn(chat_id)

async def on_bot_added(event):
    if not event.is_group:
        return

    me = await bot1.get_me()
    if event.user_id != me.id:
        return

    chat_id = event.chat_id
    chat = await event.get_chat()
    chat_title = getattr(chat, 'title', 'Unknown Group') or "Unknown Group"

    if event.user_added or event.user_joined:
        existing = await groups_col.find_one({"chat_id": chat_id})
        if existing:
            await groups_col.update_one(
                {"chat_id": chat_id},
                {"$set": {"title": chat_title, "timestamp": time.time()}}
            )
            return

        await groups_col.update_one(
            {"chat_id": chat_id},
            {"$set": {"chat_id": chat_id, "title": chat_title, "timestamp": time.time()}},
            upsert=True
        )

        try:
            full_chat = await bot1.get_entity(chat_id)
            member_count = getattr(full_chat, 'participants_count', 'Unknown')
        except:
            member_count = "Unknown"

        is_admin = False
        try:
            participant = await bot1(GetParticipantRequest(channel=chat_id, participant=me.id))
            if hasattr(participant, 'admin_rights') and participant.admin_rights:
                is_admin = True
        except:
            pass

        invite_link = None
        try:
            invite = await bot1(ExportChatInviteRequest(chat_id))
            if invite and hasattr(invite, 'link'):
                invite_link = invite.link
        except:
            invite_link = None

        msg = (
            f"📥 **Bot Added to New Group!**\n\n"
            f"📛 **Group Name:** {chat_title}\n"
            f"🆔 **Group ID:** `{chat_id}`\n"
            f"👥 **Members Count:** {member_count}\n"
            f"⚙️ **Admin Permission:** {'Yes' if is_admin else 'No'}\n"
            f"🔗 **Invite Link:** {invite_link if invite_link else 'Not available'}\n"
        )

        await notify_owners(msg)

    elif event.user_left or event.user_kicked:
        await groups_col.delete_one({"chat_id": chat_id})
        
        msg = (
            f"❌ **Bot Removed from Group**\n\n"
            f"📛 **Name:** {chat_title}\n"
            f"🆔 **ID:** `{chat_id}`"
        )
        await notify_owners(msg)

# ---- /fuck (catch command) ----
async def catch_handler(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    user_id = event.sender_id
    name = event.pattern_match.group(1)
    if not name or not name.strip():
        await reply_tag(event,
            "❓ <b>Usage:</b> <code>/fuck [name]</code>\n"
            "Type the exact name while a character is spawned to catch it. Reply to the spawn message with /w to reveal it.",
            parse_mode='html')
        return
    name = name.strip()
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
        await reply_tag(event, "❌ Wrong name! Reply to the spawn message with /w to see the exact name.")
        return

    temp_msg = await event.reply("🍓")
    await asyncio.sleep(1.5)

    async with spawn_locks[chat_id]:
        if active_spawns.get(chat_id, {}).get("claimed", True):
            try:
                await temp_msg.delete()
            except Exception:
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
                    f"group_catches.{str(chat_id)}": 1
                }
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
        except Exception:
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

# ---- /w (handled entirely by the Main bot — no separate reveal bot involved) ----
async def reveal_spawn_handler(event):
    if event.is_private:
        return

    chat_id = event.chat_id
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return

    spawn_data = active_spawns[chat_id]
    if time.time() - spawn_data["spawn_time"] > 400:
        if chat_id in active_spawns:
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
            if reply_to_obj and reply_to_obj.sender_id != (await bot1.get_me()).id:
                await reply_tag(event, "⚠️ Reply directly to the spawn message to reveal the character!")
                return
        except Exception:
            await reply_tag(event, "⚠️ Reply directly to the spawn message to reveal the character!")
            return

    rarity = spawn_data["rarity"]
    rarity_emoji = RARITY_EMOJI.get(rarity, "⭐️")
    reveal_text = (
        f"🔍 **Character Revealed!**\n\n"
        f"🌟 **Name:** `{spawn_data['name']}`\n"
        f"⚜️ **Series:** {spawn_data['series']}\n"
        f"{rarity_emoji} **Rarity:** {rarity}\n\n"
        f"🍟 **Catch it with:** `/fuck {spawn_data['name']}`"
    )
    await reply_tag(event, reveal_text, parse_mode='markdown')

# ---- /hmode ----
async def hmode_handler(event):
    user_id = event.sender_id
    doc = await users_catcher_col.find_one({"user_id": user_id})
    current_filter = doc.get("rarity_filter") if doc else None
    harem = doc.get("harem", []) if doc else []
    rarity_counts = Counter(c.get("rarity") for c in harem)

    buttons = []
    for tier in RARITY_TIERS:
        count = rarity_counts.get(tier['name'], 0)
        label = f"{'✅ ' if current_filter == tier['name'] else ''}{tier['emoji']} {tier['name']} ({count})"
        buttons.append([Button.inline(label, data=f"hfilter_{tier['name']}_{user_id}")])

    clear_label = "🔓 Clear Filter" if current_filter else "🔒 No Filter"
    buttons.append([Button.inline(clear_label, data=f"hfilter_clear_{user_id}")])

    caption = f"🎯 Select Rarity to prioritize in /harem\nCurrent: {current_filter if current_filter else 'None (Show All)'}"
    await event.reply(caption, buttons=buttons)

# ---- /harem ----
async def harem_handler(event):
    user_id = event.sender_id
    mention = await get_mention(event.client, user_id)
    await ensure_user_registered(user_id, mention)

    target_user_id = None
    if event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg:
            target_user_id = reply_msg.sender_id
    else:
        args = event.pattern_match.group(1)
        if args:
            args = args.strip()
            if args.startswith('@'):
                try:
                    entity = await event.client.get_entity(args)
                    target_user_id = entity.id
                except Exception:
                    await reply_tag(event, "❌ User not found. Use @username or reply to their message.")
                    return
            elif args.isdigit():
                target_user_id = int(args)
            else:
                await reply_tag(event, "❌ Invalid format. Use /harem @username, or reply to their message.")
                return

    if target_user_id is None:
        target_user_id = user_id
    elif target_user_id != user_id:
        try:
            target_mention = await get_mention(event.client, target_user_id)
        except Exception:
            target_mention = f"User {target_user_id}"
        await ensure_user_registered(target_user_id, target_mention)

    await send_harem_overview(event, target_user_id, viewer_id=user_id, page=1)

async def build_harem_cards(harem, rarity_filter=None):
    counts, latest_catch = {}, {}
    for c in harem:
        cid = c.get("char_id")
        if not cid:
            continue
        counts[cid] = counts.get(cid, 0) + 1
        cd = c.get("caught_date", 0) or 0
        if cid not in latest_catch or cd > latest_catch[cid]:
            latest_catch[cid] = cd
    if not counts:
        return []

    char_docs = await characters_base_col.find({"char_id": {"$in": list(counts.keys())}}).to_list(length=None)
    char_by_id = {cd["char_id"]: cd for cd in char_docs}

    owned_per_series = defaultdict(int)
    for cid in counts:
        cd = char_by_id.get(cid)
        if cd:
            owned_per_series[cd.get("series") or "Unknown"] += 1
    series_totals = {s: await characters_base_col.count_documents({"series": s}) for s in owned_per_series}

    ordered_ids = sorted(counts.keys(), key=lambda cid: latest_catch.get(cid, 0), reverse=True)
    if rarity_filter:
        ordered_ids.sort(key=lambda cid: 0 if classify_rarity(char_by_id.get(cid, {}).get("rarity", "")) == rarity_filter else 1)

    blocks = []
    for cid in ordered_ids:
        cd = char_by_id.get(cid)
        if not cd:
            continue
        rarity = classify_rarity(cd.get("rarity", "Lower"))
        qty = counts[cid]
        series = cd.get("series") or "Unknown"
        owned_n = owned_per_series.get(series, 1)
        total_n = series_totals.get(series, owned_n)
        blocks.append(
            f"☘️ Name: {escape_html(cd.get('name', 'Unknown'))} (x{qty}) · <code>{escape_html(str(cid))}</code>\n"
            f"{RARITY_EMOJI.get(rarity, '•')} Rarity: {rarity}\n"
            f"⚜️ Anime: {escape_html(series)} ({owned_n}/{total_n})"
        )
    return blocks

def paginate_harem_cards(card_blocks, budget=HAREM_PAGE_CHAR_BUDGET):
    pages, current, current_len = [], [], 0
    for block in card_blocks:
        block_len = len(block) + 2
        if current and current_len + block_len > budget:
            pages.append("\n\n".join(current))
            current, current_len = [block], block_len
        else:
            current.append(block)
            current_len += block_len
    if current:
        pages.append("\n\n".join(current))
    return pages or [""]

async def send_harem_overview(event, target_user_id, viewer_id=None, page=1, edit_msg_id=None):
    if viewer_id is None:
        viewer_id = target_user_id
    is_own = (viewer_id == target_user_id)
    doc = await users_catcher_col.find_one({"user_id": target_user_id})
    harem = doc.get("harem", []) if doc else []
    if not harem:
        msg = ("📭 Your harem is empty. Watch for a spawn with /w and catch it with /fuck [name]."
               if is_own else "📭 This user's harem is empty.")
        if edit_msg_id:
            try:
                await event.client.edit_message(event.chat_id, edit_msg_id, msg, buttons=None)
            except Exception:
                pass
        else:
            await reply_tag(event, msg)
        return

    rarity_filter = doc.get("rarity_filter")
    card_blocks = await build_harem_cards(harem, rarity_filter)
    pages = paginate_harem_cards(card_blocks)
    total_pages = len(pages)
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    body = pages[page - 1]

    try:
        target_entity = await event.client.get_entity(target_user_id)
        fullname = (getattr(target_entity, 'first_name', '') or '').strip() or getattr(target_entity, 'username', None) or "User"
    except Exception:
        fullname = "User"

    caption = f"{escape_html(fullname)}'s Recent Waifus - Page: {page}/{total_pages}\n\n{body}"
    if rarity_filter and is_own:
        caption += f"\n\n🎯 Priority filter: {RARITY_EMOJI.get(rarity_filter, '')} {rarity_filter} (change with /hmode)"
    if is_own:
        caption += "\n\n⭐ /fav [ID] — set favorite   🎁 /gift [ID] — gift a card (reply to recipient)"
        caption += "\n🧹 /clean [rarity] — wipe cards you don't want   🔍 Browse & Search — inline gallery with name/rarity search"

    fav_id = doc.get("fav_card")
    fav_card = next((c for c in harem if c.get("char_id") == fav_id), None) if fav_id else None
    if not fav_card:
        fav_card = random.choice(harem)
        if is_own:
            await users_catcher_col.update_one({"user_id": target_user_id}, {"$set": {"fav_card": fav_card["char_id"]}})

    media = None
    char_data = await characters_base_col.find_one({"char_id": fav_card.get("char_id")})
    if char_data and char_data.get("storage_msg_id"):
        try:
            stored = await event.client.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if stored and stored.media:
                media = stored.media
        except Exception:
            pass

    nav_row = []
    if page > 1:
        nav_row.append(Button.inline("⬅️ Prev", data=f"hpage_{page-1}_{target_user_id}"))
    if page < total_pages:
        nav_row.append(Button.inline("Next ➡️", data=f"hpage_{page+1}_{target_user_id}"))
    buttons = []
    if nav_row:
        buttons.append(nav_row)
    buttons.append([Button.switch_inline("🔍 Browse & Search", query=f"harem.{target_user_id} ", same_peer=True)])

    if edit_msg_id:
        try:
            if media:
                await event.client.edit_message(event.chat_id, edit_msg_id, caption, file=media, parse_mode='html', buttons=buttons)
            else:
                await event.client.edit_message(event.chat_id, edit_msg_id, caption, parse_mode='html', buttons=buttons)
            return
        except Exception as e:
            logging.error(f"harem overview edit failed, sending fresh copy: {e}")

    if media:
        try:
            await event.client.send_file(event.chat_id, media, caption=caption, parse_mode='html', buttons=buttons)
        except Exception as e:
            logging.error(f"harem overview send with media failed, falling back to text-only: {e}")
            await reply_tag(event, caption, parse_mode='html', buttons=buttons)
    else:
        await reply_tag(event, caption, parse_mode='html', buttons=buttons)

# ---- /fav ----
async def fav_handler(event):
    user_id = event.sender_id
    char_id = event.pattern_match.group(1)
    if not char_id or not char_id.strip():
        await reply_tag(event,
            "❓ <b>Usage:</b> <code>/fav [ID]</code>\n"
            "Example: <code>/fav 3946</code>\n"
            "Set a card from your own harem as your favorite. Find the ID in /harem.",
            parse_mode='html')
        return
    char_id = char_id.strip()
    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = doc.get("harem", []) if doc else []
    owned = next((c for c in harem if c.get("char_id") == char_id), None)
    if not owned:
        await reply_tag(event, "❌ You don't own a card with that ID in your harem.")
        return

    char_data = await characters_base_col.find_one({"char_id": char_id})
    media = None
    if char_data and char_data.get("storage_msg_id"):
        try:
            stored = await event.client.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if stored and stored.media:
                media = stored.media
        except Exception:
            pass

    prompt = f"⭐ Do you want to set this character as your favourite?\n\n⤿ {escape_html(owned.get('name', 'Unknown'))} ({escape_html(owned.get('series', 'Unknown'))})"
    buttons = [[Button.inline("✅ Yes", data=f"fyes_{char_id}_{user_id}"), Button.inline("❌ No", data=f"fno_{user_id}")]]
    if media:
        await event.client.send_file(event.chat_id, media, caption=prompt, parse_mode='html', buttons=buttons, reply_to=event.id)
    else:
        await event.reply(prompt, parse_mode='html', buttons=buttons)

# ---- /gift ----
async def gift_handler(event):
    if event.is_private:
        return
    user_id = event.sender_id
    char_id = event.pattern_match.group(1)
    if not char_id or not char_id.strip():
        await reply_tag(event,
            "❓ <b>Usage:</b> Reply to the person you want to gift, then send <code>/gift [ID]</code>.\n"
            "Example: reply to their message with <code>/gift 3946</code>",
            parse_mode='html')
        return
    char_id = char_id.strip()
    if not event.is_reply:
        await reply_tag(event, "⚠️ You need to reply to the recipient's message to gift a card to them.")
        return
    reply_msg = await event.get_reply_message()
    receiver = await reply_msg.get_sender() if reply_msg else None
    if not receiver or getattr(receiver, "bot", False):
        await reply_tag(event, "❌ You can't gift a card to that user.")
        return
    receiver_id = receiver.id
    if receiver_id == user_id:
        await reply_tag(event, "❌ You can't gift a card to yourself.")
        return

    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = doc.get("harem", []) if doc else []
    owned = next((c for c in harem if c.get("char_id") == char_id), None)
    if not owned:
        await reply_tag(event, "❌ You don't own a card with that ID in your harem.")
        return

    receiver_mention = await get_mention(event.client, receiver_id)
    char_data = await characters_base_col.find_one({"char_id": char_id})
    media = None
    if char_data and char_data.get("storage_msg_id"):
        try:
            stored = await event.client.get_messages(STORAGE_CHANNEL, ids=char_data["storage_msg_id"])
            if stored and stored.media:
                media = stored.media
        except Exception:
            pass

    prompt = f"🎁 Do you want to gift this character to {receiver_mention}?\n\n⤿ {escape_html(owned.get('name', 'Unknown'))} ({escape_html(owned.get('series', 'Unknown'))})"
    buttons = [[
        Button.inline("✅ Yes", data=f"gyes_{char_id}_{user_id}_{receiver_id}"),
        Button.inline("❌ No", data=f"gno_{user_id}")
    ]]
    if media:
        await event.client.send_file(event.chat_id, media, caption=prompt, parse_mode='html', buttons=buttons, reply_to=event.id)
    else:
        await event.reply(prompt, parse_mode='html', buttons=buttons)

# ---- /clean — wipe your own harem (all of it, or just one rarity) ----
CLEAN_USAGE_TEXT = (
    "❓ <b>Usage:</b>\n"
    "<code>/clean</code> — wipe your ENTIRE harem\n"
    "<code>/clean [rarity]</code> — wipe only that rarity, e.g. <code>/clean Lower</code>\n"
    "Valid rarities: " + ", ".join(f"{t['emoji']} {t['name']}" for t in RARITY_TIERS) + "\n\n"
    "You'll be asked to confirm before anything is deleted."
)

async def clean_handler(event):
    user_id = event.sender_id
    mention = await get_mention(event.client, user_id)
    await ensure_user_registered(user_id, mention)

    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = doc.get("harem", []) if doc else []
    if not harem:
        await reply_tag(event, "📭 Your harem is already empty — nothing to clean.")
        return

    arg = (event.pattern_match.group(1) or "").strip()
    if arg:
        rarity = next((t["name"] for t in RARITY_TIERS if t["name"].lower() == arg.lower()), None)
        if not rarity:
            await reply_tag(event, CLEAN_USAGE_TEXT, parse_mode='html')
            return
        target_count = sum(1 for c in harem if c.get("rarity") == rarity)
        if not target_count:
            await reply_tag(event, f"📭 You don't have any {RARITY_EMOJI.get(rarity, '')} {rarity} cards to clean.")
            return
        mode = rarity
        prompt = (
            f"🧹 <b>Clean {RARITY_EMOJI.get(rarity, '')} {rarity} cards?</b>\n\n"
            f"This will permanently remove <b>{target_count}</b> card{'s' if target_count != 1 else ''} "
            f"from your harem. This can't be undone."
        )
    else:
        mode = "ALL"
        prompt = (
            f"🧹 <b>Clean your ENTIRE harem?</b>\n\n"
            f"This will permanently remove all <b>{len(harem)}</b> card{'s' if len(harem) != 1 else ''} "
            f"from your harem. This can't be undone."
        )

    buttons = [[
        Button.inline("✅ Yes, clean it", data=f"cleanyes_{user_id}_{mode}"),
        Button.inline("❌ Cancel", data=f"cleanno_{user_id}")
    ]]
    await event.reply(prompt, parse_mode='html', buttons=buttons)

# ---- Inline Query (Character Cards) ----
# Query format: "harem.<user_id>" for the full collection, or
# "harem.<user_id> <search>" to filter by character name (substring) or an
# exact rarity name (e.g. "harem.12345 Rainbow"). Results are grouped by
# character (duplicates shown as "xN") and paged via Telegram's next_offset
# so scrolling works past the first 50 matches.
INLINE_PAGE_SIZE = 25

async def harem_inline(event):
    query_text = (event.text or "").strip()
    if not query_text.startswith("harem."):
        return

    remainder = query_text[len("harem."):]
    head, _, search_term = remainder.partition(" ")
    search_term = search_term.strip()
    try:
        target_user_id = int(head)
    except ValueError:
        return

    doc = await users_catcher_col.find_one({"user_id": target_user_id})
    harem = doc.get("harem", []) if doc else []
    if not harem:
        await event.answer([], switch_pm="📭 This vault is empty!", switch_pm_param="start")
        return

    try:
        owner_entity = await event.client.get_entity(target_user_id)
        owner_fullname = (getattr(owner_entity, 'first_name', '') or '').strip() or getattr(owner_entity, 'username', None) or "User"
    except Exception:
        owner_fullname = "User"

    # Group duplicate catches of the same character into one entry (qty + most recent catch date)
    counts, latest_catch = {}, {}
    for c in harem:
        cid = c.get("char_id")
        if not cid:
            continue
        counts[cid] = counts.get(cid, 0) + 1
        cd = c.get("caught_date", 0) or 0
        if cid not in latest_catch or cd > latest_catch[cid]:
            latest_catch[cid] = cd

    char_docs = await characters_base_col.find({"char_id": {"$in": list(counts.keys())}}).to_list(length=None)

    matched_rarity = None
    if search_term:
        matched_rarity = next((t["name"] for t in RARITY_TIERS if t["name"].lower() == search_term.lower()), None)
    search_lower = search_term.lower()

    entries = []
    for char_data in char_docs:
        if not char_data.get("storage_msg_id"):
            continue
        cid = char_data["char_id"]
        name = char_data.get("name", "Unknown")
        rarity = classify_rarity(char_data.get("rarity", ""))
        if search_term:
            if matched_rarity:
                if rarity != matched_rarity:
                    continue
            elif search_lower not in name.lower():
                continue
        event_note = char_data.get("events")
        event_line = str(event_note) if event_note and str(event_note).lower() != "none" else "None"
        entries.append({
            "char_id": cid,
            "name": name,
            "series": char_data.get("series") or "Unknown",
            "rarity": rarity,
            "event_line": event_line,
            "qty": counts.get(cid, 1),
            "storage_msg_id": char_data["storage_msg_id"],
            "latest": latest_catch.get(cid, 0),
        })

    # Rarest first, then most recently caught within the same rarity
    entries.sort(key=lambda e: (RARITY_ORDER.get(e["rarity"], len(RARITY_TIERS)), -e["latest"]))

    if not entries:
        note = "🔍 No cards matched that search." if search_term else "📭 This vault is empty!"
        await event.answer([], switch_pm=note, switch_pm_param="start")
        return

    try:
        start = int(event.offset) if event.offset else 0
    except ValueError:
        start = 0
    page = entries[start:start + INLINE_PAGE_SIZE]
    next_offset = str(start + INLINE_PAGE_SIZE) if start + INLINE_PAGE_SIZE < len(entries) else ""

    results = []
    builder = event.builder
    for entry in page:
        try:
            stored_msg = await event.client.get_messages(STORAGE_CHANNEL, ids=entry["storage_msg_id"])
            if not stored_msg or not stored_msg.media:
                continue
            rarity_emoji = RARITY_EMOJI.get(entry["rarity"], '')
            qty_note = f" (x{entry['qty']})" if entry["qty"] > 1 else ""

            caption = (
                f"Wow, check {escape_html(owner_fullname)}'s character card!\n"
                f"🆔 Id- <code>{escape_html(str(entry['char_id']))}</code>\n"
                f"🌟 Name- {escape_html(entry['name'])}{qty_note}\n"
                f"⚜️ Anime- {escape_html(entry['series'])}\n"
                f"🎡 Event- {escape_html(entry['event_line'])}\n"
                f"{rarity_emoji} Rarity- {escape_html(entry['rarity'])}"
            )

            if stored_msg.photo:
                results.append(builder.photo(
                    file=stored_msg.media,
                    id=entry["char_id"],
                    text=caption,
                    parse_mode='html'
                ))
            elif stored_msg.video:
                results.append(builder.video(
                    file=stored_msg.media,
                    id=entry["char_id"],
                    text=caption,
                    parse_mode='html'
                ))
            else:
                results.append(builder.document(
                    file=stored_msg.media,
                    title=f"{entry['name']}{qty_note}",
                    description=f"{rarity_emoji} {entry['rarity']} · {entry['series']}",
                    id=entry["char_id"],
                    text=caption,
                    parse_mode='html'
                ))
        except Exception as e:
            logging.error(f"Inline error for {entry['char_id']}: {e}")
            continue
    await event.answer(results, cache_time=0, next_offset=next_offset)

# ---- /myinfo ----
async def myinfo_handler(event):
    user_id = event.sender_id
    mention = await get_mention(event.client, user_id)
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
    text += "\n✳️ Rarity Counts: \n╭───────────────────\n" + "\n".join(rarity_lines) + "\n╰───────────────────"
    photos = await event.client.get_profile_photos(user_id, limit=1)
    if photos:
        await event.client.send_file(event.chat_id, photos[0], caption=text, parse_mode='html')
    else:
        await reply_tag(event, text)

# ---- /check ----
async def check_handler(event):
    char_id = event.pattern_match.group(1)
    if not char_id or not char_id.strip():
        await reply_tag(event,
            "❓ <b>Usage:</b> <code>/check [ID]</code>\n"
            "Example: <code>/check 3946</code>\n"
            "Shows a card's rarity, catch stats, and its top catchers.",
            parse_mode='html')
        return
    char_id = char_id.strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    media = None
    try:
        stored = await event.client.get_messages(STORAGE_CHANNEL, ids=char_doc.get("storage_msg_id"))
        if stored and stored.media:
            media = stored.media
    except:
        pass

    rarity = classify_rarity(char_doc.get("rarity", "Lower"))
    spawn_count = char_doc.get("spawn_count", 0)
    spawn_limit = char_doc.get("spawn_limit", 0)
    caught_line = f"{spawn_count}" if not spawn_limit else f"{spawn_count}/{spawn_limit} ({max(0, spawn_limit - spawn_count)} left)"

    pipeline = [
        {"$match": {"harem.char_id": char_id}},
        {"$project": {
            "user_id": 1,
            "fullname": 1,
            "count": {"$size": {"$filter": {"input": "$harem", "as": "item", "cond": {"$eq": ["$$item.char_id", char_id]}}}}
        }},
        {"$sort": {"count": -1}}, {"$limit": 10}
    ]
    owners = await users_catcher_col.aggregate(pipeline).to_list(length=10)

    info = (
        f"🃏 <b>Character Lookup</b>\n\n"
        f"🆔 ID: <code>{escape_html(char_id)}</code>\n"
        f"🌟 Name: <b>{escape_html(char_doc.get('name', 'Unknown'))}</b>\n"
        f"📺 Series: {escape_html(char_doc.get('series', 'Unknown'))}\n"
        f"{RARITY_EMOJI.get(rarity, '')} Rarity: {rarity}\n"
        f"🎯 Caught so far: {caught_line}\n"
    )
    events_note = char_doc.get("events")
    if events_note and str(events_note).lower() != "none":
        info += f"🎪 Event: {escape_html(str(events_note))}\n"

    if owners:
        medals = ["🥇", "🥈", "🥉"]
        info += f"\n🏆 <b>Top {len(owners)} Catchers</b>\n"
        for i, o in enumerate(owners, 1):
            mention = await get_mention(event.client, o["user_id"])
            rank = medals[i - 1] if i <= 3 else f"{i}."
            info += f"{rank} {mention} — x{o['count']}\n"
    else:
        info += "\n👻 Nobody has caught this character yet."

    if media:
        await event.client.send_file(event.chat_id, media, caption=info, parse_mode='html')
    else:
        await reply_tag(event, info, parse_mode='html')

# ---- /addcharacter ----
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
    rarity_input = parts[2].strip()
    char_id = parts[3].strip()
    event_note = parts[4].strip()
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
        "events": event_note,
        "spawn_limit": spawn_limit,
        "spawn_count": 0,
        "storage_msg_id": storage_msg_id
    }
    await characters_base_col.insert_one(char_data)
    await reply_tag(event, f"✅ Character added:\nID: {char_id}\nName: {name}\nSeries: {series}\nRarity: {rarity_name}\nEvents: {event_note}\nMax Spawn: {spawn_limit if spawn_limit > 0 else 'Infinite'}")

# ---- /removecharacter ----
async def removecharacter_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    char_id = event.pattern_match.group(1).strip()
    result = await characters_base_col.delete_one({"char_id": char_id})
    await reply_tag(event, f"✅ Character {char_id} removed." if result.deleted_count else "❌ Not found.")

# ==========================================
# 🚨 /resetall — wipe EVERY collection (irreversible)
# ==========================================
RESETALL_CONFIRM_PHRASE = "CONFIRM-RESET-ALL"

async def resetall_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    arg = (event.pattern_match.group(1) or "").strip()
    if arg != RESETALL_CONFIRM_PHRASE:
        await reply_tag(
            event,
            "🚨 <b>This wipes EVERY collection</b> — all users, wallets, harems, "
            "bans, group configs, AND the character catalog. There is no undo "
            "(a JSON backup will be posted to the storage channel first, but "
            "you'd have to restore it manually).\n\n"
            f"To proceed, send exactly:\n<code>/resetall {RESETALL_CONFIRM_PHRASE}</code>",
            parse_mode='html'
        )
        return
    status_msg = await reply_tag(event, "⏳ Backing up database before wipe...")
    try:
        backup_bytes = await dump_full_database_to_json()
        stamp = datetime.utcnow().strftime("%Y-%m-%d_%H-%M-%S")
        await send_to_storage_with_retry(
            event.client, backup_bytes, f"full_db_backup_{stamp}.json",
            caption=f"🗄️ Full DB backup before /resetall — {stamp} UTC"
        )
    except Exception as e:
        await status_msg.edit(f"❌ Backup failed, aborting wipe (nothing deleted): {e}")
        return
    await status_msg.edit("⏳ Backup stored. Wiping all collections...")
    counts = await wipe_all_collections()
    summary = "\n".join(f"• {name}: {n}" for name, n in counts.items())
    await status_msg.edit(f"✅ Everything wiped.\n\n{summary}\n\nBot owner re-seeded so you're not locked out.")

# ==========================================
# 🌐 /bulkimport — auto-populate characters from AniList
# ==========================================
async def run_bulk_import(target_count: int, client):
    global bulk_import_stop_requested
    state = await import_state_col.find_one({"_id": "anilist_import"})
    if state and state.get("status") == "completed" and state.get("target_count") == target_count:
        # fresh run with the same target that already finished — start over
        state = None
    page = state["last_page"] if state else 0
    imported = state["imported_count"] if state else 0
    skipped = state["skipped_count"] if state else 0

    async def save_state(status):
        await import_state_col.update_one(
            {"_id": "anilist_import"},
            {"$set": {
                "status": status, "target_count": target_count,
                "imported_count": imported, "skipped_count": skipped,
                "last_page": page, "updated_at": time.time()
            }},
            upsert=True
        )

    await save_state("running")
    try:
        async with aiohttp.ClientSession() as session:
            while imported < target_count:
                if bulk_import_stop_requested:
                    await save_state("stopped")
                    await notify_owners(f"⏹️ Bulk import stopped by request. Imported {imported}/{target_count}.")
                    return
                page += 1
                try:
                    page_data = await anilist_fetch_characters_page(session, page)
                except Exception as e:
                    logging.error(f"AniList page {page} fetch failed: {e}")
                    await asyncio.sleep(5)
                    continue
                characters = page_data.get("characters", [])
                if not characters:
                    break
                for c in characters:
                    if imported >= target_count:
                        break
                    name = pick_character_name(c.get("name"))
                    series = pick_series_title((c.get("media") or {}).get("nodes", []))
                    image_url = ((c.get("image") or {}).get("large"))
                    if not name or not series or not image_url:
                        skipped += 1
                        continue
                    char_id = f"al_{c['id']}"
                    existing = await characters_base_col.find_one({"char_id": char_id})
                    if existing:
                        skipped += 1
                        continue
                    rarity_name = rarity_from_favourites(c.get("favourites"))
                    try:
                        img_bytes = await download_bytes(session, image_url)
                        stored = await send_to_storage_with_retry(client, img_bytes, f"{char_id}.jpg")
                    except Exception as e:
                        logging.error(f"Failed to store image for {char_id}: {e}")
                        skipped += 1
                        continue
                    await characters_base_col.insert_one({
                        "char_id": char_id,
                        "name": name,
                        "series": series,
                        "rarity": rarity_name,
                        "events": "",
                        "spawn_limit": 0,       # 0 = infinite, as requested
                        "spawn_count": 0,
                        "storage_msg_id": stored.id,
                        "source": "anilist",
                        "anilist_favourites": c.get("favourites", 0),
                    })
                    imported += 1
                    await asyncio.sleep(TELEGRAM_SEND_DELAY)
                await save_state("running")
                if not page_data.get("pageInfo", {}).get("hasNextPage", False):
                    break
                await asyncio.sleep(ANILIST_MIN_DELAY)
        await save_state("completed")
        await notify_owners(f"✅ Bulk import finished. Imported {imported}, skipped {skipped} (no name/series/image or duplicate).")
    except Exception as e:
        logging.error(f"Bulk import crashed: {e}")
        await save_state("error")
        await notify_owners(f"❌ Bulk import crashed after {imported}/{target_count}: {e}")
    finally:
        bulk_import_stop_requested = False

async def bulkimport_handler(event):
    global bulk_import_task, bulk_import_stop_requested
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    if bulk_import_task and not bulk_import_task.done():
        await reply_tag(event, "⚠️ An import is already running. Use /importstatus or /importstop.")
        return
    count_str = (event.pattern_match.group(1) or "").strip()
    if not count_str.isdigit() or int(count_str) <= 0:
        await reply_tag(event, "❌ Usage: /bulkimport <count>  e.g. /bulkimport 5000")
        return
    target_count = int(count_str)
    bulk_import_stop_requested = False
    bulk_import_task = asyncio.create_task(run_bulk_import(target_count, event.client))
    await reply_tag(
        event,
        f"🚀 Started importing {target_count} characters from AniList "
        f"(name + series + image auto-filled, rarity from popularity, event=none, catch limit=0).\n"
        f"This runs in the background and can take a while — check /importstatus."
    )

async def importstatus_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    state = await import_state_col.find_one({"_id": "anilist_import"})
    if not state:
        await reply_tag(event, "ℹ️ No import has been run yet.")
        return
    await reply_tag(
        event,
        f"📊 <b>Import status:</b> {state.get('status')}\n"
        f"Imported: {state.get('imported_count', 0)}/{state.get('target_count', 0)}\n"
        f"Skipped: {state.get('skipped_count', 0)}\n"
        f"Last AniList page: {state.get('last_page', 0)}",
        parse_mode='html'
    )

async def importstop_handler(event):
    global bulk_import_stop_requested
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    if not bulk_import_task or bulk_import_task.done():
        await reply_tag(event, "ℹ️ No import is currently running.")
        return
    bulk_import_stop_requested = True
    await reply_tag(event, "⏹️ Stopping after the current character... check /importstatus.")

# ---- /fspawn ----
async def force_spawn(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    chat_id = int(chat_id) if chat_id else event.chat_id
    await trigger_dynamic_spawn(chat_id)
    await reply_tag(event, f"✅ Forced spawn in {chat_id}.")

# ---- /spawnoff ----
async def spawn_toggle(event):
    if not await is_owner(event.sender_id):
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
    if not await is_owner(event.sender_id):
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
    if not await is_owner(event.sender_id):
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
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return

    waifu_pipeline = [{"$group": {"_id": None, "total": {"$sum": {"$size": "$harem"}}}}]
    rarity_pipeline = [{"$unwind": "$harem"}, {"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}]

    total_chats, total_users, total_harems, anime_list, waifu_res, rarity_res = await asyncio.gather(
        groups_col.count_documents({}),
        users_catcher_col.count_documents({}),
        users_catcher_col.count_documents({"harem.0": {"$exists": True}}),
        characters_base_col.distinct("series"),
        users_catcher_col.aggregate(waifu_pipeline).to_list(length=1),
        users_catcher_col.aggregate(rarity_pipeline).to_list(length=None),
    )

    total_waifus = waifu_res[0]["total"] if waifu_res else 0
    total_anime = len(anime_list)
    r_counts = {r["_id"]: r["count"] for r in rarity_res}

    text = (
        "<b>Bot Statistics:</b>\n\n"
        f"•Total Chats: - {total_chats}\n"
        f"•Total Users: - {total_users}\n"
        f"•Total Waifus: - {total_waifus}\n"
        f"•Total Anime: - {total_anime}\n"
        f"•Total Harems: - {total_harems}\n\n"
    )
    for tier in RARITY_TIERS:
        text += f"{tier['name']} - {r_counts.get(tier['name'], 0)}\n"

    await reply_tag(event, text, parse_mode='html')

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
    result_msg = status_msg
    try:
        await status_msg.edit(final)
    except:
        result_msg = await reply_tag(event, final)

    # Auto-delete the /slot command and its result 10 seconds later
    asyncio.create_task(
        _auto_delete_messages(event.client, event.chat_id, [event.id, result_msg.id])
    )

async def _auto_delete_messages(client, chat_id, message_ids, delay=10):
    await asyncio.sleep(delay)
    try:
        await client.delete_messages(chat_id, message_ids)
    except Exception as e:
        logging.error(f"Auto-delete failed for chat {chat_id}: {e}")

# ---- /top /gtop ----
async def top_handler(event): await send_leaderboard(event, "local")
async def gtop_handler(event): await send_leaderboard(event, "global")

async def send_leaderboard(event, scope):
    if scope == "local":
        group_key = str(event.chat_id)
        field = f"group_catches.{group_key}"
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
        if scope == "local":
            val = (doc.get("group_catches") or {}).get(group_key, 0)
        else:
            val = doc.get("total_caught", 0)
        mention = await get_mention(event.client, uid)
        msg += f"{medals[i]} {mention} — {val:,} catches\n"
    await reply_tag(event, msg, parse_mode='html')

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
            if "**" in math_expr:
                if math_expr.count("**") > 1:
                    return
                if any(int(e) > 1000 for e in re.findall(r'\*\*\s*(\d+)', math_expr)):
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
    mention = await get_mention(event.client, user_id)
    await ensure_user_registered(user_id, mention)
    if event.is_private:
        text = (
            "<b>Welcome to Character Catcher Bot!</b>\n\n"
            "🎮 Watch for characters spawning in your group, reply /w to reveal one, then catch it with /fuck [name].\n"
            "🎒 /harem — view your collected cards\n"
            "🔰 /myinfo — view your profile\n"
            "💰 /balance, /daily — check your wallet\n"
            "❓ /help — see all commands"
        )
        try:
            me = await event.client.get_me()
            buttons = [
                [Button.url("➕ Add me to a group", f"https://t.me/{me.username}?startgroup=true")],
                [Button.switch_inline("🔍 Browse & Search", query=f"harem.{user_id} ", same_peer=False)]
            ]
        except Exception:
            buttons = None
        await event.reply(text, parse_mode='html', buttons=buttons)
    else:
        await reply_tag(event, "👋 Bot is ready! Use /help to see available commands.")

# ---- /help ----
async def help_handler(event):
    help_text = (
        "🤖 <b>Commands</b>\n\n"
        "🎮 <b>Catching</b>\n"
        "/fuck [name] — catch a spawned character\n"
        "/w — reply to the spawn message to reveal the character\n"
        "/harem [@user] — view a collection (or reply to their message)\n"
        "/myinfo, /fav [ID], /gift [ID] (reply)\n"
        "/check [ID], /hmode (rarity priority)\n"
        "/clean [rarity] — wipe cards from your harem (confirm first)\n\n"
        "💰 <b>Economy</b>\n/balance, /daily, /slot [amount], /top, /gtop\n\n"
        "🛠️ <b>Utility</b>\n/tr [text], /id, /start\n\n"
        "👑 <b>Owner</b>\n"
        "/addcharacter (reply to media), /removecharacter [ID]\n"
        "/bulkimport [count] — auto-import characters from AniList\n"
        "/importstatus, /importstop\n"
        "/resetall — wipe the ENTIRE database (irreversible, needs confirm phrase)\n"
        "/fspawn, /spawnoff, /spawnstats, /changetime, /status\n"
        "/gban [user_id] [reason] [duration] — e.g. /gban 123 spam 1d\n"
        "/co [user_id] — grant co-owner rights\n"
        "/unban [user_id]"
    )
    await reply_tag(event, help_text, parse_mode='html')

# ---- /gban (new simplified version) ----
# NOTE: registered once, centrally, in startup() below — do not add a
# second @bot1.on(...) decorator here, it double-fires the handler
# (and crashes at import since `bot1` is still None at module load time).
async def gban_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    user_id = int(event.pattern_match.group(1))
    reason = event.pattern_match.group(2).strip()
    duration_str = event.pattern_match.group(3).strip()
    duration_seconds = parse_duration(duration_str)
    if duration_seconds == "INVALID":
        await reply_tag(event, f"❌ Invalid duration format. Use e.g. 10min, 1d, 1m, 1y, perm")
        return
    banned_until = (time.time() + duration_seconds) if duration_seconds else None
    await banned_users_col.update_one(
        {"user_id": user_id},
        {"$set": {
            "banned": True,
            "reason": reason,
            "banned_at": time.time(),
            "banned_until": banned_until,
            "banned_by": event.sender_id
        }},
        upsert=True
    )
    await reply_tag(
        event,
        f"✅ User <code>{user_id}</code> banned.\n"
        f"📄 Reason: {escape_html(reason)}\n"
        f"⏰ Duration: {format_duration(duration_seconds)}",
        parse_mode='html'
    )

# ---- /co (add co-owner) ----
# NOTE: registered once, centrally, in startup() below — see note on
# gban_handler above.
async def co_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    new_owner_id = int(event.pattern_match.group(1))
    if new_owner_id == event.sender_id:
        await reply_tag(event, "❌ You are already an owner.")
        return
    await bot_owners_col.update_one(
        {"_id": "owners"},
        {"$addToSet": {"ids": new_owner_id}},
        upsert=True
    )
    await reply_tag(event, f"✅ User <code>{new_owner_id}</code> is now a co-owner.", parse_mode='html')

# ---- /unban ----
async def unban_handler(event):
    if not await is_owner(event.sender_id):
        await reply_tag(event, "❌ Owner only.")
        return
    uid = int(event.pattern_match.group(1))
    result = await banned_users_col.delete_one({"user_id": uid})
    if result.deleted_count:
        await reply_tag(event, f"✅ User {uid} unbanned.")
    else:
        await reply_tag(event, f"❌ User {uid} is not banned.")

# ---- Global Pre-Check (Ban & Force Join) ----
async def pre_check_handler(event):
    if await is_owner(event.sender_id):
        return

    # 1. Ban Check
    banned = await banned_users_col.find_one({"user_id": event.sender_id})
    if banned and banned.get("banned", False):
        banned_until = banned.get("banned_until")
        if banned_until and time.time() > banned_until:
            await banned_users_col.update_one({"user_id": event.sender_id}, {"$set": {"banned": False}})
        else:
            reason = banned.get("reason", "No reason provided")
            expiry_note = ""
            if banned_until:
                expiry_note = f"\n⏰ Expires: {time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime(banned_until))}"
            else:
                expiry_note = "\n⏰ Duration: Permanent"
            await reply_tag(event, f"❌ You are banned.\n📄 Reason: {reason}{expiry_note}")
            raise events.StopPropagation

    # 2. Force Join Check – Main Bot only
    text = event.text or ""
    if text.startswith('/'):
        cmd = text.split()[0].lower()
        if '@' in cmd:
            cmd = cmd.split('@')[0]
        force_join_commands = ['/fuck', '/harem']
        if cmd not in force_join_commands:
            return

    if REQUIRED_GROUP_ID:
        try:
            await bot1(GetParticipantRequest(channel=REQUIRED_GROUP_ID, participant=event.sender_id))
        except UserNotParticipantError:
            join_text = (
                "👋 **မင်္ဂလာပါခင်ဗျာ!**\n\n"
                "ဒီ Command ကို အသုံးပြုနိုင်ဖို့အတွက် ဦးစွာ ကျွန်တော်တို့ရဲ့ **Official Group** ထဲသို့ ဝင်ရောက်ပေးရန် လိုအပ်ပါတယ်ခင်ဗျာ။\n\n"
                "Group ထဲဝင်ပြီးမှ ဆက်လက် အသုံးပြုနိုင်မှာဖြစ်ပါတယ်!"
            )
            buttons = [[Button.url("💬 Join Group Here", REQUIRED_GROUP_LINK)]]
            await event.reply(join_text, buttons=buttons)
            raise events.StopPropagation
        except Exception as e:
            logging.error(f"Force Join Check Error: {e}")

# ---- Callback Query ----
async def callback_handler(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    if data.startswith("hpage_"):
        parts = data.split("_")
        page = int(parts[1])
        target_user_id = int(parts[2])
        await event.answer()
        msg = await event.get_message()
        await send_harem_overview(event, target_user_id, viewer_id=user_id, page=page, edit_msg_id=msg.id)
        return
    if data.startswith("hfilter_"):
        parts = data.split("_")
        if parts[1] == "clear":
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": None}}, upsert=True)
            await event.answer("🔓 Filter cleared!", alert=True)
        else:
            rarity = parts[1]
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"rarity_filter": rarity}}, upsert=True)
            doc = await users_catcher_col.find_one({"user_id": user_id})
            harem = doc.get("harem", []) if doc else []
            count = sum(1 for c in harem if c.get("rarity") == rarity)
            if count:
                msg = f"✅ Filter set to {rarity}. You have {count} card{'s' if count > 1 else ''} of this rarity."
            else:
                msg = f"✅ Filter set to {rarity}. You have no cards of this rarity yet."
            await event.answer(msg, alert=True)
        await hmode_handler(event)
        return
    if data.startswith("fyes_"):
        body = data[len("fyes_"):]
        char_id, target_str = body.rsplit("_", 1)
        target_user_id = int(target_str)
        if user_id != target_user_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        doc = await users_catcher_col.find_one({"user_id": user_id})
        harem = doc.get("harem", []) if doc else []
        owned = next((c for c in harem if c.get("char_id") == char_id), None)
        if not owned:
            await event.answer("❌ You no longer own this card.", alert=True)
            return
        await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"fav_card": char_id}})
        await event.answer("⭐ Set!")
        try:
            await event.edit(f"⭐ Favorite set to {escape_html(owned.get('name', 'Unknown'))}.", parse_mode='html', buttons=None)
        except Exception:
            pass
        return
    if data.startswith("fno_"):
        target_user_id = int(data.split("_", 1)[1])
        if user_id != target_user_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        await event.answer("Cancelled")
        try:
            await event.edit("🚫 Cancelled.", parse_mode='html', buttons=None)
        except Exception:
            pass
        return
    if data.startswith("gyes_"):
        body = data[len("gyes_"):]
        char_id, sender_str, receiver_str = body.rsplit("_", 2)
        sender_id, receiver_id = int(sender_str), int(receiver_str)
        if user_id != sender_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        doc = await users_catcher_col.find_one({"user_id": sender_id})
        harem_list = doc.get("harem", []) if doc else []
        item = next((c for c in harem_list if c.get("char_id") == char_id), None)
        if not item:
            await event.answer("❌ You no longer have this card.", alert=True)
            return
        harem_list.remove(item)
        await users_catcher_col.update_one({"user_id": sender_id}, {"$set": {"harem": harem_list}})
        receiver_mention = await get_mention(event.client, receiver_id)
        await ensure_user_registered(receiver_id, receiver_mention)
        await users_catcher_col.update_one(
            {"user_id": receiver_id},
            {
                "$push": {"harem": {**item, "caught_date": time.time()}},
                "$inc": {"total_caught": 1, f"rarity_counts.{item.get('rarity', 'Lower')}": 1}
            }
        )
        await event.answer("🎁 Gifted!")
        try:
            await event.edit(f"🎁 Gifted {escape_html(item.get('name', 'Unknown'))} to {receiver_mention}.", parse_mode='html', buttons=None)
        except Exception:
            pass
        return
    if data.startswith("gno_"):
        sender_id = int(data.split("_", 1)[1])
        if user_id != sender_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        await event.answer("Cancelled")
        try:
            await event.edit("🚫 Gift cancelled.", parse_mode='html', buttons=None)
        except Exception:
            pass
        return
    if data.startswith("cleanyes_"):
        body = data[len("cleanyes_"):]
        target_str, mode = body.split("_", 1)
        target_user_id = int(target_str)
        if user_id != target_user_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        doc = await users_catcher_col.find_one({"user_id": user_id})
        harem = doc.get("harem", []) if doc else []
        if mode == "ALL":
            removed = len(harem)
            new_harem = []
        else:
            removed = sum(1 for c in harem if c.get("rarity") == mode)
            new_harem = [c for c in harem if c.get("rarity") != mode]
        if not removed:
            await event.answer("❌ Nothing left to clean — your harem already changed.", alert=True)
            try:
                await event.edit("🚫 Cancelled — nothing to clean.", parse_mode='html', buttons=None)
            except Exception:
                pass
            return
        update = {"$set": {"harem": new_harem}}
        fav_id = doc.get("fav_card") if doc else None
        if fav_id and not any(c.get("char_id") == fav_id for c in new_harem):
            update["$set"]["fav_card"] = None
        await users_catcher_col.update_one({"user_id": user_id}, update)
        await event.answer("🧹 Cleaned!")
        label = "your entire harem" if mode == "ALL" else f"{RARITY_EMOJI.get(mode, '')} {mode} cards"
        try:
            await event.edit(
                f"✅ <b>Cleaned!</b> Removed <b>{removed}</b> card{'s' if removed != 1 else ''} ({label}).",
                parse_mode='html', buttons=None
            )
        except Exception:
            pass
        return
    if data.startswith("cleanno_"):
        target_user_id = int(data.split("_", 1)[1])
        if user_id != target_user_id:
            await event.answer("⚠️ This isn't your request.", alert=True)
            return
        await event.answer("Cancelled")
        try:
            await event.edit("🚫 Cancelled — your harem is untouched.", parse_mode='html', buttons=None)
        except Exception:
            pass
        return

# ==========================================
# 🚀 STARTUP
# ==========================================
async def startup():
    global bot1, bot2
    threading.Thread(target=_start_health_server, daemon=True).start()

    # Main bot
    bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH)
    bot1.add_event_handler(pre_check_handler, events.NewMessage(pattern=r'^/'))
    bot1.add_event_handler(message_counter_for_spawn, events.NewMessage(incoming=True))
    bot1.add_event_handler(start_handler, events.NewMessage(pattern=r'^/start(?:@\w+)?$'))
    bot1.add_event_handler(on_bot_added, events.ChatAction)
    bot1.add_event_handler(catch_handler, events.NewMessage(pattern=r'^/fuck(?:@\w+)?(?:\s+(.+))?$'))
    bot1.add_event_handler(reveal_spawn_handler, events.NewMessage(pattern=r'^/w(?:@\w+)?$'))
    bot1.add_event_handler(hmode_handler, events.NewMessage(pattern=r'^/hmode(?:@\w+)?$'))
    bot1.add_event_handler(harem_handler, events.NewMessage(pattern=r'^/harem(?:@\w+)?(?:\s+(.*))?$'))
    bot1.add_event_handler(harem_inline, events.InlineQuery)
    bot1.add_event_handler(myinfo_handler, events.NewMessage(pattern=r'^/myinfo(?:@\w+)?$'))
    bot1.add_event_handler(fav_handler, events.NewMessage(pattern=r'^/fav(?:@\w+)?(?:\s+(\S+))?$'))
    bot1.add_event_handler(gift_handler, events.NewMessage(pattern=r'^/gift(?:@\w+)?(?:\s+(\S+))?$'))
    bot1.add_event_handler(clean_handler, events.NewMessage(pattern=r'^/clean(?:@\w+)?(?:\s+(.+))?$'))
    bot1.add_event_handler(check_handler, events.NewMessage(pattern=r'^/check(?:@\w+)?(?:\s+(\S+))?$'))
    bot1.add_event_handler(addcharacter_handler, events.NewMessage(pattern=r'^/addcharacter(?:@\w+)?\s+(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)(?:\s*\|\s*(\d+))?$'))
    bot1.add_event_handler(removecharacter_handler, events.NewMessage(pattern=r'^/removecharacter(?:@\w+)?\s+(\S+)$'))
    bot1.add_event_handler(resetall_handler, events.NewMessage(pattern=r'^/resetall(?:@\w+)?(?:\s+(.+))?$'))
    bot1.add_event_handler(bulkimport_handler, events.NewMessage(pattern=r'^/bulkimport(?:@\w+)?\s+(\d+)$'))
    bot1.add_event_handler(importstatus_handler, events.NewMessage(pattern=r'^/importstatus(?:@\w+)?$'))
    bot1.add_event_handler(importstop_handler, events.NewMessage(pattern=r'^/importstop(?:@\w+)?$'))
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
    bot1.add_event_handler(gban_handler, events.NewMessage(pattern=r'^/gban(?:@\w+)?\s+(\d+)\s+(.+?)\s+(\S+)$'))  # new pattern
    bot1.add_event_handler(co_handler, events.NewMessage(pattern=r'^/co(?:@\w+)?\s+(\d+)$'))
    bot1.add_event_handler(unban_handler, events.NewMessage(pattern=r'^/unban(?:@\w+)?\s+(\d+)$'))
    bot1.add_event_handler(callback_handler, events.CallbackQuery)

    await bot1.start(bot_token=BOT_TOKEN)

    # Ensure OWNER_ID is in owners list
    await bot_owners_col.update_one(
        {"_id": "owners"},
        {"$addToSet": {"ids": OWNER_ID}},
        upsert=True
    )

    # 🩹 CHANGED: /w reveal is now handled directly by bot1 (see reveal_spawn_handler) — no more
    # separate reveal bot / REVEAL_BOT_TOKEN needed, so bot2 is never started for this anymore.
    bot2 = None

    # Indexes
    await users_catcher_col.create_index("user_id", unique=True)
    await characters_base_col.create_index("char_id", unique=True)
    await groups_col.create_index("chat_id", unique=True)

    asyncio.create_task(spawn_cleaner())

    print("Main bot is running.")
    await bot1.run_until_disconnected()

if __name__ == "__main__":
    asyncio.run(startup())
