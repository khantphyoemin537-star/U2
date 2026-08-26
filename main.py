#############
import io
import csv
import ast
import operator
import asyncio
import logging
import random
import os
import threading
import re
import time
import unicodedata
import urllib.request
import json
import pytz
from PIL import Image, ImageDraw, ImageFont
from collections import Counter, defaultdict
from telethon.tl.functions.channels import GetParticipantsRequest
from datetime import datetime, timedelta
from telethon.tl.functions.messages import ExportChatInviteRequest
from flask import Flask
from motor.motor_asyncio import AsyncIOMotorClient
from pymongo import ReturnDocument, UpdateOne
from html import escape as escape_html
from telethon.errors import FloodWaitError
from telethon import TelegramClient, events, functions, types, Button, errors
from telethon.tl.types import ChannelParticipantsAdmins
from telethon.extensions import html
from telethon.tl.types import MessageEntityCustomEmoji
from telethon.sessions import StringSession
from typing import Optional, List, Dict, Set
import redis.asyncio as redis

# ==========================================
# 🗃️ BOT STATE — every in-memory runtime cache/counter/game-state dict the bot keeps, in one
# place, instead of ~28 loose module-level globals scattered across the file. Gives us:
#   1. cleanup_expired() — a single periodic sweep that bounds memory on a 512MB Render
#      instance instead of relying on each cache to (maybe) self-prune on its own.
#   2. One obvious place to look when auditing "what does this process hold in RAM".
#
# BACKWARD COMPAT: right after this class, every attribute is ALSO exposed as a bare
# module-level name (e.g. `active_group_spawns = bot_state.active_group_spawns`). Dicts/sets/
# defaultdicts are mutable reference types in Python, so that bare name and the attribute on
# bot_state point at the literal same object — `active_group_spawns[x] = y` anywhere else in
# this file mutates bot_state.active_group_spawns too, and vice versa. This means every one of
# the hundreds of pre-existing references to these globals throughout the file keeps working
# completely unchanged; nothing needed to be renamed at the call sites.
# ==========================================
class BotState:
    def __init__(self):
        # ---- Simple rate-limit / anti-spam / UI-debounce caches: {key: last_action_ts} ----
        self._recent_callback_taps = {}
        self._last_callback_click = {}
        self._recent_event_ids = {}
        self._recent_bot_added_chats = {}
        self.recent_mod_actions = {}          # (chat_id, user_id) -> ts
        self.user_cooldowns = {}              # composite cache_key -> ts
        self.user_mute_until = {}             # user_id -> expiry ts (GLOBAL — applies in every group)
        self.force_sub_prompt_last_sent = {}  # user_id -> ts

        # ---- Caches with an explicit (payload, expiry_ts) or {"expiry": ts} shape ----
        self.force_sub_membership_cache = {}  # user_id -> (is_member, expiry_ts)
        self._welcome_toggle_cache = {}       # chat_id -> (enabled, ts)
        self._spawn_target_cache = {}         # chat_id -> (spawn_target, ts)
        self.admin_cache = {}                 # chat_id -> {"ids": [...], "expiry": ts}

        # ---- Per-user rolling-window trackers — already self-pruned inline on every write
        # (see check_sticker_spam/check_char_spam/spam checks), so cleanup_expired() leaves
        # these alone rather than duplicating that per-key pruning logic here. ----
        self.sticker_spam_data = {}
        self.char_spam_data = {}
        self.user_spam_data = {}

        # ---- Group message-interval counters — one small int per active group, reset by the
        # spawn/talk logic itself when it fires, no expiry concept to sweep. ----
        self.reply_msg_counters = {}
        self.random_talk_counters = {}
        # ⚡ PERFORMANCE: the spawn-progress counter for every group used to live purely in
        # Mongo, hit with a find_one_and_update on every single group message — the single
        # biggest source of database load in the whole bot. It now lives here in memory
        # (source of truth for spawn decisions) and is only durably written to Mongo in a
        # cheap periodic batch — see group_counter_flush_loop(). {chat_id: int}
        self.group_spawn_counters = {}

        # ---- Small admin/moderation-flow trackers, bounded by concurrent admin activity ----
        self.pending_editchar_prompt_ids = {}
        self.dark_passenger_targets = {}

        # ---- LIVE game/feature state — deliberately EXCLUDED from cleanup_expired(). Each of
        # these already has its own dedicated timeout task elsewhere that removes an entry at
        # exactly the right moment (spawn timeout, quiz timeout, game round ending, etc.). A
        # generic time-based sweep here could race with that and tear down something mid-play. ----
        self.active_group_spawns = {}
        self.active_haido_events = {}
        self.pending_rarity_quiz = {}

        # ---- asyncio.Lock factories — never swept; a lock can be actively held ----
        self.spawn_locks = defaultdict(asyncio.Lock)
        self.bot_added_locks = defaultdict(asyncio.Lock)

        # ---- Misc ----
        self.bot_ids = []
        self.admin_warned_sticker = set()  # (chat_id, admin_id)
        self.admin_warned_char = set()     # (chat_id, admin_id)

    def cleanup_expired(self):
        """Sweeps every cache above that has a known-safe expiry rule. Safe to call from a
        periodic background loop (see start_bot_state_cleanup_loop) or an admin command.
        Returns how many entries were removed, purely for logging."""
        now = time.time()
        removed = 0
        # {key: timestamp} — a generous 24h window. Every real cooldown/debounce/anti-spam
        # window in this bot is seconds-to-minutes long, so anything older than a day is
        # unambiguously stale no matter which of these dicts it's in.
        for d in (self._recent_callback_taps, self._last_callback_click, self._recent_event_ids,
                  self._recent_bot_added_chats, self.recent_mod_actions, self.user_cooldowns,
                  self.force_sub_prompt_last_sent, self.user_mute_until):
            stale_keys = [k for k, ts in list(d.items()) if isinstance(ts, (int, float)) and now - ts > 86400]
            for k in stale_keys:
                del d[k]
                removed += 1
        # {key: (payload, expiry_ts)} — expiry is explicit, so use it exactly
        for d in (self.force_sub_membership_cache, self._welcome_toggle_cache, self._spawn_target_cache):
            stale_keys = [k for k, v in list(d.items()) if isinstance(v, tuple) and len(v) == 2 and now > v[1]]
            for k in stale_keys:
                del d[k]
                removed += 1
        # {key: {"expiry": ts, ...}}
        for d in (self.admin_cache,):
            stale_keys = [k for k, v in list(d.items()) if isinstance(v, dict) and now > v.get("expiry", 0)]
            for k in stale_keys:
                del d[k]
                removed += 1
        return removed

bot_state = BotState()

# ==========================================
# ⚡ PREMIUM MATHEMATICAL BOLD SERIF FONT CONVERTER
# ==========================================
def f(text):
    normal = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    modern = "𝗔𝗕𝗖𝗗𝗘𝗙𝗚𝗛𝗜𝗝𝗞𝗟𝗠𝗡𝗢𝗣𝗤𝗥𝗦𝗧𝗨𝗩𝗪𝗫𝗬𝗭𝗮𝗯𝗰𝗱𝗲𝗳𝗴𝗵𝗶𝗷𝗸𝗹𝗺𝗻𝗼𝗽𝗾𝗿𝘀𝘁𝘂𝘃𝘄𝘅𝘆𝘇𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵"
    trans = str.maketrans(normal, modern)
    return text.translate(trans)

# ==========================================
# 🔡 SMALL-CAPS FONT CONVERTER — used for header/label flavor text (e.g. "ʀᴇᴄᴇɴᴛ ᴄʜᴀʀᴀᴄᴛᴇʀꜱ",
# "ᴘᴀɢᴇ") to match catch_bot's own header styling. Every letter (upper or lower) maps to the
# same small-capital glyph; anything that isn't a letter (numbers, punctuation, emoji, mentions)
# passes through unchanged. Never apply this to a user's actual display name/mention.
# ==========================================
_SMALL_CAPS_SRC = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
_SMALL_CAPS_DST = ("ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡxʏᴢ" "ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡxʏᴢ")
_SMALL_CAPS_TRANS = str.maketrans(_SMALL_CAPS_SRC, _SMALL_CAPS_DST)

def small_caps(text):
    """'Recent Characters' -> 'ʀᴇᴄᴇɴᴛ ᴄʜᴀʀᴀᴄᴛᴇʀꜱ'. Letters only — leave mentions/IDs/emoji alone."""
    return text.translate(_SMALL_CAPS_TRANS)

# ==========================================
# 🎪 EVENT TAG — a character's "event" field (synced from catch_bot's channel posts, e.g.
# 🎄𝑪𝒉𝒓𝒊𝒔𝒕𝒎𝒂𝒔🎄 / 🏖𝒔𝒖𝒎𝒎𝒆𝒓🏖 — see extract_event_change/_maybe_sync_event_change) is stored in
# full, but every card line in /harem and the harem inline-query only ever shows the compact
# "[emoji]" tag next to the name — this pulls just that leading emoji back out. Returns "" for
# no event (missing / the "General" default), so callers can do f" [{tag}]" if tag else "".
# ==========================================
_EVENT_EMOJI_RE = re.compile(
    r'^(?:[\U0001F1E6-\U0001FAFF\u2600-\u27BF\u2B00-\u2BFF\u2190-\u21FF]\uFE0F?)+'
)

def event_emoji_tag(event_str):
    if not event_str or not str(event_str).strip() or str(event_str).strip().lower() == "general":
        return ""
    m = _EVENT_EMOJI_RE.match(str(event_str).strip())
    return m.group(0) if m else ""

async def ensure_user_registered(user_id, fullname):
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {
            "$setOnInsert": {
                "total_caught": 0,
                "harem": [],
                "fullname": fullname,
                "daily_cooldown": 0,
                "hunt_cooldown": 0,
                "last_daily": 0,
                "daily_streak": 0,
                "referral_count": 0,
                "referred_by": None,
                "daily_catches": 0,
                "last_catch_date": None,
                "spam_mute_until": 0,
                "msg_history": [],
                "force_sub_rewarded": False
            }
        },
        upsert=True
    )

# ==========================================
# 🛡️ FLOOD WAIT PROTECTION ENGINE
# ==========================================
# 🩹 FIX: these used to retry through a FloodWaitError of ANY length, sleeping silently no
# matter how long Telegram asked for. Every caller already wraps these in a try/except — but
# an uncaught-by-them infinite sleep never reaches that except, so under load (e.g. right
# after a burst of activity) a command like /addchar or /exportchars would just hang with
# zero feedback, looking completely dead, sometimes for minutes. Short waits still get
# absorbed transparently (unnoticeable); anything longer is re-raised so the caller's own
# except block can report it instead of the command silently going nowhere.
FLOOD_WAIT_RETRY_CAP = 15  # seconds

async def send_safe_message(client, chat_id, text, **kwargs):
    while True:
        try:
            return await client.send_message(chat_id, text, **kwargs)
        except FloodWaitError as e:
            if e.seconds > FLOOD_WAIT_RETRY_CAP:
                logging.warning(f"⚠️ FloodWait too long ({e.seconds}s) — raising instead of blocking silently.")
                raise
            logging.warning(f"⚠️ FloodWait: sleeping {e.seconds}s...")
            await asyncio.sleep(e.seconds)
        except Exception as e:
            logging.error(f"❌ send_safe_message error: {e}")
            raise e

async def send_safe_file(client, chat_id, file, **kwargs):
    while True:
        try:
            return await client.send_file(chat_id, file, **kwargs)
        except FloodWaitError as e:
            if e.seconds > FLOOD_WAIT_RETRY_CAP:
                logging.warning(f"⚠️ FloodWait too long ({e.seconds}s) — raising instead of blocking silently.")
                raise
            logging.warning(f"⚠️ FloodWait (file): sleeping {e.seconds}s...")
            await asyncio.sleep(e.seconds)
        except Exception as e:
            logging.error(f"❌ send_safe_file error: {e}")
            raise e

# ==========================================
# 🧵 NON-BLOCKING EXECUTOR BRIDGE
# ==========================================
async def run_blocking(func, *args, **kwargs):
    loop = asyncio.get_running_loop()
    if kwargs:
        return await loop.run_in_executor(None, lambda: func(*args, **kwargs))
    return await loop.run_in_executor(None, func, *args)

# 🚀 COOLDOWN RATE-LIMITER
async def is_on_cooldown(user_id, command_name, cooldown_seconds=3):
    if user_id == OWNER_ID: return False, 0
    now = time.time()
    cache_key = (user_id, command_name)
    if cache_key in user_cooldowns:
        elapsed = now - user_cooldowns[cache_key]
        if elapsed < cooldown_seconds:
            return True, int(cooldown_seconds - elapsed)
    user_cooldowns[cache_key] = now
    return False, 0

# ==========================================
# 🔒 ATOMIC WALLET DEBIT — prevents double-spend / negative-balance races
# ==========================================
# The old pattern across the casino games used to be:
#   1. find_one() to read the balance
#   2. check `balance < bet` in Python
#   3. update_one({"$inc": {"wallet_balance": -bet}}) to actually deduct
# Steps 1 and 3 were NOT atomic — two rapid-fire requests from the same user (a fast
# double-tap, a spam script, or just bad luck with network timing) could both read the
# SAME pre-deduction balance, both pass the check, and both deduct — letting a player
# spend far more than they actually had, or drive their balance negative.
#
# This version does the check-and-deduct as a SINGLE atomic MongoDB operation: the
# `wallet_balance` filter and the `$inc` happen together, so Mongo guarantees only
# requests that still have enough balance AT THE MOMENT OF THE WRITE can succeed.


# ==========================================
# 🔒 INLINE-BUTTON DOUBLE-TAP GUARD — prevents duplicate execution of one-shot
# button actions (gifting a card, confirming a trade, joining a bet, resolving a
# hi-lo round, etc.)
# ==========================================
# Telegram can deliver a callback twice (client-side double-tap, network retry, an
# impatient user mashing the button before the message visibly updates). Without a
# guard, a single logical "click" could run the underlying handler code more than
# once — duplicating a card transfer, doubling a payout, or deducting a bet twice.
# Keyed on (user, message, exact button payload) so this only ever blocks a REPEAT of
# the same tap — different users, or the same user on a different button/message,
# are never affected.
_recent_callback_taps = bot_state._recent_callback_taps
CALLBACK_TAP_WINDOW = 2.5  # seconds — long enough to eat a double-tap, short enough to never block a genuine retry

def claim_single_tap(event, extra=""):
    """Returns True the first time this exact (user, message, button data) combo is
    seen within the window, and False for any repeat — the caller should bail out
    (just event.answer() and return) on False instead of re-running the action."""
    key = (event.sender_id, event.message_id, event.data, extra)
    now = time.time()
    last = _recent_callback_taps.get(key)
    if last is not None and (now - last) < CALLBACK_TAP_WINDOW:
        return False
    _recent_callback_taps[key] = now
    if len(_recent_callback_taps) > 5000:  # cheap bound so this dict can never grow unbounded
        cutoff = now - CALLBACK_TAP_WINDOW
        for k, ts in list(_recent_callback_taps.items()):
            if ts < cutoff:
                del _recent_callback_taps[k]
    return True

# ==========================================
# 🔀 DOT/SLASH COMMAND PREFIX HELPERS
# ==========================================
# Every command handler now matches both '/cmd' and '.cmd' (see the pattern= regexes below).
# These two helpers keep the handful of places OUTSIDE those regexes — moderation/mute
# enforcement, spam filters — in sync, so a muted user can't dodge enforcement just by
# switching prefix.
def _has_command_prefix(text):
    return bool(text) and text[0] in ('/', '.')

def _extract_command_word(text):
    """Normalizes a command message to '/wordname' regardless of whether the person used
    '/' or '.', and strips any '@botname' suffix AND any following arguments. Returns None if
    `text` isn't a command. (e.g. '.collect Sailor Moon' -> '/collect', not '/collect Sailor
    Moon' — a message with an argument is still that command.)"""
    if not _has_command_prefix(text):
        return None
    rest = text[1:]
    word = rest.split()[0] if rest.split() else rest
    return '/' + word.split('@')[0]

def today_start():
    return datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()

# ==========================================
# 🎯 OWN-USERNAME COMMAND GUARD
# ==========================================
# 🩹 FIX: every command pattern below used to accept ANY '@botname' mention, e.g.
# '^[/.]harem(?:@\w+)?...$' matches '/harem@ThisBot' AND '/harem@SomeOtherBot' equally — the
# regex never actually checked WHICH bot was mentioned. In a group with more than one bot
# sharing a command name, this bot fired even when the person explicitly addressed a
# different bot. own_pattern() wraps a pattern string so that when a message DOES contain an
# explicit @mention right after the command word, it's only treated as a match if that
# mention is this bot's own username — messages with no mention at all still match exactly
# as before. BOT1_USERNAME/BOT2_USERNAME are populated once at startup (see run_bot1_forever/
# run_bot2_forever); until then (a brief window before the very first connect), the check is
# skipped so nothing regresses.
BOT1_USERNAME = None
BOT2_USERNAME = None
BOT3_USERNAME = None
_OWN_MENTION_RE = re.compile(r'^[/.]\S*?@(\w+)')

def own_pattern(regex_str, bot='bot1'):
    """Wraps a command regex so it only matches when either (a) there's no explicit
    '@botname' mention at all, or (b) the mention is this bot's own username. Does NOT alter
    the original regex's capture groups — group(N) on the resulting match works exactly like
    it did before, since the mention check is a completely separate pass over the raw text."""
    compiled = re.compile(regex_str)
    def matcher(text):
        if not text:
            return None
        m = compiled.match(text)
        if not m:
            return None
        mention = _OWN_MENTION_RE.match(text)
        if mention:
            own_username = {'bot1': BOT1_USERNAME, 'bot2': BOT2_USERNAME, 'bot3': BOT3_USERNAME}.get(bot)
            if own_username and mention.group(1).lower() != own_username:
                return None
        return m
    return matcher

# 🚀 REAL-TIME USER METRICS TRACKER
def track_user_metrics(user_id, username, first_name):
    async def _track_bg():
        try:
            await users_col.update_one(
                {"user_id": user_id},
                {"$set": {"username": username, "first_name": first_name, "last_active": datetime.now(TZ)}},
                upsert=True
            )
        except Exception as e:
            print(f"Error in track_user_metrics: {e}")
    try:
        asyncio.create_task(_track_bg())
    except Exception:
        pass

# 🚀 CENTRALIZED ERROR NOTIFICATION
async def report_system_error(location, error_msg):
    try:
        alert_text = (
            f"🚨 <b>CRITICAL SYSTEM ERROR</b>\n"
            f"📍 <b>Location:</b> <code>{escape_html(location)}</code>\n"
            f"❌ <b>Error:</b> <code>{escape_html(str(error_msg))}</code>\n"
            f"⏰ <b>Time:</b> <code>{datetime.now(TZ).strftime('%Y-%m-%d %H:%M:%S')}</code>"
        )
        await bot1.send_message(OWNER_ID, bq(alert_text), parse_mode='html')
    except Exception: pass

async def get_today_stats():
    # 🩹 FIX: daily_report_scheduler fires this at 6:00 AM, intending to summarize the PREVIOUS
    # full day — but the query window here was [midnight TODAY, now), which at 6am is only the
    # last 6 HOURS of the brand-new day, not yesterday's full 24 hours. That's the real reason
    # catches, the rarity breakdown, AND groups-active all looked far smaller than actual daily
    # activity — the report was only ever seeing a 6-hour sliver, every single day. Window is
    # now the full [yesterday's midnight, today's midnight) range.
    now = datetime.now(TZ)
    today_midnight = now.replace(hour=0, minute=0, second=0, microsecond=0)
    period_end = today_midnight.timestamp()
    period_start = (today_midnight - timedelta(days=1)).timestamp()
    pipeline = [
        {"$unwind": "$harem"},
        {"$match": {"harem.caught_date": {"$gte": period_start, "$lt": period_end}}},
        {"$facet": {
            "totals": [{"$group": {
                "_id": None,
                "total": {"$sum": 1},
                "catchers": {"$addToSet": "$user_id"},
                "groups": {"$addToSet": "$harem.chat_id"}
            }}],
            "rarity": [{"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}]
        }}
    ]
    result = await users_catcher_col.aggregate(pipeline).to_list(length=1)
    doc = result[0] if result else {"totals": [], "rarity": []}
    totals = doc["totals"][0] if doc["totals"] else {"total": 0, "catchers": [], "groups": []}
    rarity_breakdown = {r["_id"]: r["count"] for r in doc["rarity"]}

    return {
        "total_catches": totals["total"],
        "groups": len(totals["groups"]),
        "rarity": rarity_breakdown,
        "catchers": len(totals["catchers"])
    }

async def send_daily_report():
    stats = await get_today_stats()
    # 🩹 FIX: label with the date actually being summarized — yesterday, since the window above
    # is [yesterday midnight, today midnight) — not today's date, which was misleading.
    report_date = (datetime.now(TZ) - timedelta(days=1)).strftime("%Y-%m-%d")
    text = f"📊 <b>Daily Report – {report_date}</b>\n"
    text += f"━━━━━━━━━━━━━━━━━━━━\n"
    text += f"🐇 <b>Total Catches:</b> <code>{stats['total_catches']}</code>\n"
    text += f"👥 <b>Unique Catchers:</b> <code>{stats['catchers']}</code>\n"
    text += f"🪐 <b>Groups Active:</b> <code>{stats['groups']}</code>\n\n"
    text += f"🏷️ <b>Rarity Breakdown:</b>\n"
    for rarity, count in sorted(stats['rarity'].items(), key=lambda x: x[1], reverse=True):
        text += f"  • {rarity} — <code>{count}</code>\n"
    if not stats['rarity']:
        text += "  <i>No catches that day.</i>\n"
    text += f"\n<code>/today</code> to see today's top catchers so far."

    # Send to force-sub group
    try:
        await send_safe_message(bot1, FORCE_SUB_CHAT_ID, text, parse_mode='html')
    except Exception as e:
        print(f"Daily report to group failed: {e}")

    # Send to owner's DM
    try:
        await send_safe_message(bot1, OWNER_ID, text, parse_mode='html')
    except Exception as e:
        print(f"Daily report to owner DM failed: {e}")
async def daily_report_scheduler():
    while True:
        now = datetime.now(TZ)
        target = now.replace(hour=6, minute=0, second=0, microsecond=0)
        if now >= target:
            target += timedelta(days=1)
        wait_seconds = (target - now).total_seconds()
        await asyncio.sleep(wait_seconds)

        # Check if already sent today (to avoid duplicates after restart)
        last_sent = await bot_settings_col.find_one({"_id": "daily_report_last_sent"})
        today_str = datetime.now(TZ).strftime("%Y-%m-%d")
        if last_sent and last_sent.get("date") == today_str:
            continue
        await send_daily_report()
        await bot_settings_col.update_one(
            {"_id": "daily_report_last_sent"},
            {"$set": {"date": today_str}},
            upsert=True
        )


# ==========================================
# 🏅 ACHIEVEMENT SYSTEM (Updated)
# ==========================================
# Rank 1 (rarest) -> Rank 9 (most common). All tiers accept photo or video media — no
# tier is restricted to a specific media type.
# 🩹 CHANGED (per owner request): expanded from 4 tiers to 9, matching catch_bot's own scheme
# 1:1 (Supreme..Common) instead of compressing it down. Every EXISTING character on the old
# 4-tier scheme (Sweetie/Blossom/Fluffy/Kawaii) is migrated to MYSTICAL — see
# _migrate_old_4tier_to_9tier() below — a deliberate one-time choice, not a "best guess"
# equivalence, since the old 4 tiers don't map onto the new 9 in any principled way.
RARITY_TIERS = ["SUPREME", "CATAPHRACT", "CROSSVERSE", "DIVINE", "MYSTICAL", "LEGENDARY", "RARE", "UNCOMMON", "COMMON"]
# ⚠️ SINGLE SOURCE OF TRUTH for rarity emoji (Rarity No.1 = SUPREME ... No.9 = COMMON).
# Change emoji here ONLY — RARITY_NUM_MAP below is generated from this, so spawns, /who,
# the /addchar legend, achievements, stats and /changeallrarity all stay in sync automatically.
# Emoji match catch_bot's own exactly, so a character's rarity looks identical either bot.
RARITY_EMOJI = {
    "SUPREME": "🪞", "CATAPHRACT": "✨", "CROSSVERSE": "⚡", "DIVINE": "⚜️",
    "MYSTICAL": "💮", "LEGENDARY": "🟡", "RARE": "🟠", "UNCOMMON": "🟣", "COMMON": "🔵"
}
RARITY_DEFAULT_EMOJI = "❓"  # fallback shown only when a tier truly can't be classified
RARITY_LABEL_STYLED = "𝙍𝘼𝙍𝙄𝙏𝙔"  # matches catch_bot's own inline-query card caption styling
MMK_PER_USD = 4000  # 1 USD = 4000 MMK (fixed peg)
def _build_fancy_font_reverse_map():
    mapping = {}
    for cp in range(0x1D400, 0x1D800):
        try:
            name = unicodedata.name(chr(cp))
        except ValueError:
            continue
        if not name.startswith("MATHEMATICAL "):
            continue
        tokens = name.split()
        last = tokens[-1]
        if "DIGIT" in tokens:
            digit_words = {"ZERO": "0", "ONE": "1", "TWO": "2", "THREE": "3", "FOUR": "4",
                           "FIVE": "5", "SIX": "6", "SEVEN": "7", "EIGHT": "8", "NINE": "9"}
            if last in digit_words:
                mapping[chr(cp)] = digit_words[last]
        elif "DOTLESS" in tokens:
            mapping[chr(cp)] = last.lower()
        elif len(last) == 1 and last.isalpha():
            if "SMALL" in tokens:
                mapping[chr(cp)] = last.lower()
            elif "CAPITAL" in tokens:
                mapping[chr(cp)] = last.upper()
    return mapping

_FANCY_TO_PLAIN = str.maketrans(_build_fancy_font_reverse_map())

def normalize_char_id_input(raw_id):
    """Accepts whatever a player typed for a character ID — with or without the internal
    'BOD' prefix, any case — and returns the canonical stored form (e.g. 'BOD1234').
    Players are no longer shown the 'BOD' prefix, so lookups must accept the bare number."""
    raw_id = (raw_id or "").strip().upper()
    if raw_id.isdigit():
        return f"BOD{raw_id}"
    return raw_id

def display_char_id(char_id):
    """Strips the internal 'BOD' prefix for display — players only ever see the number."""
    if isinstance(char_id, str) and char_id.upper().startswith("BOD"):
        return char_id[3:]
    return char_id

def artist_line(card_doc, prefix="", suffix="\n"):
    """Builds a formatted 'Artist' credit line for any character display, given either a
    full character document (dict with an 'artist' key) or the artist name itself.
    Returns '' when no artist is on file, so callers can safely inline this everywhere
    a character's name/rarity is shown (catch results, /check, /harem, gifts, etc.)."""
    if isinstance(card_doc, dict):
        artist = card_doc.get("artist")
    else:
        artist = card_doc
    if not artist or not str(artist).strip():
        return ""
    return f"{prefix}🎨 <b>Artist:</b> <code>{escape_html(str(artist).strip())}</code>{suffix}"

# ==========================================
# 🔎 PHOTO/VIDEO IDENTIFY — perceptual hash (dHash) so a re-uploaded/re-saved copy of a
# character's media (screenshotted, saved to gallery, re-compressed, etc.) can still be
# matched back to the original character, even though Telegram assigns it a brand-new
# file_id/file_unique_id on re-upload. Pure PIL implementation — no extra dependency.
# ==========================================
PHASH_SIZE = 16  # 16x16 -> 256-bit hash — bumped from 8 (64-bit) to fix false-positive character misidentification (see IDENTIFY_HAMMING_THRESHOLD below and _identify_media_and_reply)

def compute_dhash(media_bytes, hash_size=PHASH_SIZE):
    """Difference hash: robust to re-encoding/resizing, NOT robust to heavy crops/edits."""
    try:
        img = Image.open(io.BytesIO(media_bytes)).convert("L").resize(
            (hash_size + 1, hash_size), Image.LANCZOS
        )
        pixels = list(img.getdata())
        bits = []
        for row in range(hash_size):
            row_pixels = pixels[row * (hash_size + 1): (row + 1) * (hash_size + 1)]
            for col in range(hash_size):
                bits.append("1" if row_pixels[col] > row_pixels[col + 1] else "0")
        return format(int("".join(bits), 2), f'0{hash_size * hash_size // 4}x')
    except Exception as e:
        print(f"compute_dhash error: {e}")
        return None

def hamming_distance(hash_a, hash_b):
    if not hash_a or not hash_b:
        return 999
    try:
        return bin(int(hash_a, 16) ^ int(hash_b, 16)).count("1")
    except Exception:
        return 999

async def compute_phash_for_message(msg):
    """Given a Telethon message with a photo or video, return a dHash string of the
    image (or the video's thumbnail — we never download a full video, just its thumb)."""
    # 🩹 DIAGNOSTICS: this used to print only the bare exception, with no way to tell WHICH
    # message/character it was for or what kind of media tripped it up — so a character stuck
    # permanently "not recognized" (photo_phash never gets set, see find_character_by_media)
    # was a dead end to debug. Now every failure logs msg_id + media kind + exception TYPE, so
    # /rehashall's "couldn't re-fetch media for: <names>" list can actually be traced back to a
    # root cause (e.g. a video with no embedded thumbnail, or a sticker format PIL can't open)
    # instead of staying a mystery.
    media_kind = "photo" if msg.photo else "video" if msg.video else "document" if msg.document else "none"
    try:
        if msg.photo:
            media_bytes = await msg.download_media(file=bytes)
        elif msg.video or msg.document:
            media_bytes = await msg.download_media(thumb=-1, file=bytes)
        else:
            return None
        if not media_bytes:
            print(f"compute_phash_for_message: empty download (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}) — "
                  f"likely no embedded thumbnail to fetch.")
            return None
        result = compute_dhash(media_bytes)
        if not result:
            print(f"compute_phash_for_message: dHash failed to decode (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}) — "
                  f"see compute_dhash error above for the PIL exception.")
        return result
    except Exception as e:
        print(f"compute_phash_for_message error (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}): {type(e).__name__}: {e}")
        return None

def classify_rarity(rarity_str):
    if not rarity_str:
        return "OTHER"
    plain = rarity_str.translate(_FANCY_TO_PLAIN).upper()
    # Longest-first so a tier name that happens to contain a shorter tier name as a
    # substring of another (e.g. a past scheme had "RONIN" containing "ONI") never gets misclassified.
    for tier in sorted(RARITY_TIERS, key=len, reverse=True):
        if tier in plain:
            return tier
    return "OTHER"

_RARITY_NO_SUFFIX_RE = re.compile(r'\s*No\.?\s*\d+\s*$', re.IGNORECASE)

def strip_rarity_number(rarity_str):
    """Strips a trailing ' No.X' from a rarity display string — in ANY font, fancy
    math-unicode digits/letters included — e.g. '☀️ 𝖫𝖤𝖦𝖤𝖭𝖣 𝖭𝗈.𝟤' -> '☀️ 𝖫𝖤𝖦𝖤𝖭𝖣'.
    .translate() maps one character to exactly one character, so a plain-ASCII 'shadow' of
    the same string is guaranteed the same length — find the suffix in the shadow, then slice
    the ORIGINAL string at that same index, which keeps whatever font the rest was in."""
    if not rarity_str:
        return rarity_str
    plain_shadow = rarity_str.translate(_FANCY_TO_PLAIN)
    m = _RARITY_NO_SUFFIX_RE.search(plain_shadow)
    if m:
        return rarity_str[:m.start()].rstrip()
    return rarity_str

def rarity_rank_value(rarity_str):
    """Single source of truth for 'how rare is this, as a sortable number' — rank 1
    (rarest) gets the highest number, rank 4 (most common) gets the lowest. Replaces the
    hardcoded per-tier rank dicts that used to be copy-pasted in several places."""
    tier = classify_rarity(rarity_str)
    try:
        return len(RARITY_TIERS) - RARITY_TIERS.index(tier)
    except ValueError:
        return 0


# ==========================================
# 💵 USD / ⭐ STAR DISPLAY FORMATTING
# ==========================================
# 💵 2026-07: the bot's whole economy was migrated off the old uncapped MMK currency onto a
# fixed USD peg (see "USD ECONOMY" note near MMK_PER_USD) — this is the standard formatter
# for any USD balance/value shown to a player. ⭐ Star remains the separate second currency
# used for card trading and is untouched by this migration.



# ==========================================
# RARITY SPAWN WEIGHT — a single GLOBAL "level" dial (via /spawnweight) that boosts how often
# Supreme (No.1 — RARITY_GATE_TIERS, the quiz-gated tier, defined further down) spawns,
# relative to its own default below. No.2-9 are never touched by this — only the quiz-gated
# tier scales. "Global" means exactly that: one setting, shared by every chat, regardless of
# which chat the owner happens to type the command in.
DEFAULT_RARITY_WEIGHTS = dict(zip(RARITY_TIERS, [2, 4, 8, 15, 25, 40, 60, 85, 120]))
# No.1 Supreme=2 ... No.9 Common=120 — a 60x gap between rarest and most common by default.
# ✏️ To add more levels yourself later, just add another "level: multiplier" pair here — e.g.
# {1: 1, 2: 3, 3: 5} adds a level 3 that's 5x default. Nothing else needs to change.
SPAWNWEIGHT_LEVEL_MULTIPLIERS = {1: 1, 2: 3}
_cached_spawnweight_level = 1  # level 1 = 1x = untouched defaults

async def load_rarity_weight_cache():
    global _cached_spawnweight_level
    try:
        doc = await bot_settings_col.find_one({"_id": "rarity_spawn_weight_level"})
        if doc and doc.get("level") in SPAWNWEIGHT_LEVEL_MULTIPLIERS:
            _cached_spawnweight_level = doc["level"]
    except Exception as e:
        print(f"load_rarity_weight_cache error: {e}")


def get_effective_rarity_weights():
    """Per-tier weight dict for random.choices() spawn selection: DEFAULT_RARITY_WEIGHTS, with
    Sweetie (RARITY_GATE_TIERS) multiplied by whatever level /spawnweight is currently set
    to. Blossom/Fluffy/Kawaii always stay at their plain defaults."""
    multiplier = SPAWNWEIGHT_LEVEL_MULTIPLIERS.get(_cached_spawnweight_level, 1)
    weights = dict(DEFAULT_RARITY_WEIGHTS)
    for tier in RARITY_GATE_TIERS:
        weights[tier] = DEFAULT_RARITY_WEIGHTS[tier] * multiplier
    return weights

def build_progress_bar(current, total, length=10):
    pct = (current / total) if total > 0 else 0
    pct = max(0.0, min(pct, 1.0))
    filled = int(round(pct * length))
    return "█" * filled + "░" * (length - filled) + f" {pct * 100:.1f}%"

def build_block_progress_bar(current, total, length=10):
    """Same math as build_progress_bar, different glyphs (▰▱, no % suffix) — used by
    /profile's boxed layout specifically, to match the requested design exactly."""
    pct = (current / total) if total > 0 else 0
    pct = max(0.0, min(pct, 1.0))
    filled = int(round(pct * length))
    return "▰" * filled + "▱" * (length - filled)

PROFILE_CATCHES_PER_LEVEL = 40  # 🎮 "Experience Level" (see /profile) — one level per this many
# total catches. Purely a fun, catches-based progression display — doesn't gate or unlock
# anything, just gives long-time players a number that keeps climbing.

def get_experience_level(total_caught):
    """Returns (level, progress_within_level, catches_needed_for_next_level). Level 1 starts
    at 0 catches."""
    level = 1 + (total_caught // PROFILE_CATCHES_PER_LEVEL)
    progress = total_caught % PROFILE_CATCHES_PER_LEVEL
    return level, progress, PROFILE_CATCHES_PER_LEVEL

def utf16_len(s):
    """Telegram's message/caption length limits (4096 / 1024) are counted in UTF-16 code
    units, not Python characters. Fancy-font letters (used for rarity names) and many emoji
    live in the Unicode supplementary plane and take 2 UTF-16 units each (a surrogate pair),
    not 1 — plain len() undercounts those and can let a page slip past Telegram's real limit."""
    return len(s.encode('utf-16-le')) // 2

def generate_achievements():
    achievements = []
    # ... (all previous achievements remain, plus new ones)
    catch_targets = [1, 5, 10, 25, 50, 100, 200, 500, 1000, 2000, 5000]
    emojis = ["🎯", "📦", "🎒", "🧳", "🏅", "🏆", "👑", "💎", "🌌", "🌟", "💫"]
    for i, target in enumerate(catch_targets):
        achievements.append({
            "id": f"catch_{target}",
            "emoji": emojis[i % len(emojis)],
            "name": f"Catch {target} Characters",
            "desc": f"Capture {target} characters",
            "check": lambda u, t=target: u.get("total_caught", 0) >= t
        })
    streak_targets = [3, 7, 14, 30, 60, 100]
    streak_emojis = ["🔥", "☄️", "⚡", "🌞", "🌙", "⭐"]
    for i, target in enumerate(streak_targets):
        achievements.append({
            "id": f"streak_{target}",
            "emoji": streak_emojis[i],
            "name": f"{target}-Day Streak",
            "desc": f"Maintain a daily streak of {target} days",
            "check": lambda u, t=target: u.get("daily_streak", 0) >= t
        })
    ref_targets = [1, 5, 10, 25, 50]
    ref_emojis = ["🤝", "👥", "📢", "📣", "🌐"]
    for i, target in enumerate(ref_targets):
        achievements.append({
            "id": f"referral_{target}",
            "emoji": ref_emojis[i],
            "name": f"Invite {target} Friends",
            "desc": f"Get {target} friends to join via your referral link",
            "check": lambda u, t=target: u.get("referral_count", 0) >= t
        })
    leg_targets = [1, 5, 10, 50]
    leg_emojis = ["👑", "🌌", "💫", "🌟"]
    top_tier = RARITY_TIERS[0]
    for i, target in enumerate(leg_targets):
        achievements.append({
            "id": f"legendary_{target}",
            "emoji": leg_emojis[i],
            "name": f"Collect {target} {top_tier.title()} Cards",
            "desc": f"Own {target} {top_tier} rarity cards",
            "check": lambda u, t=target, tt=top_tier: sum(1 for item in u.get("harem", []) if isinstance(item, dict) and tt in (item.get("rarity", "").upper())) >= t
        })
    for target in [1, 10, 50]:
        achievements.append({
            "id": f"sell_{target}",
            "emoji": "🛒",
            "name": f"Sell {target} Cards on Market",
            "desc": f"Successfully sell {target} cards on the marketplace",
            "check": lambda u, t=target: u.get("total_sales", 0) >= t
        })
    for target in [1, 10, 50]:
        achievements.append({
            "id": f"trade_{target}",
            "emoji": "🤝",
            "name": f"Complete {target} Trades",
            "desc": f"Successfully trade {target} cards with other players",
            "check": lambda u, t=target: u.get("total_trades", 0) >= t
        })
    achievements.append({
        "id": "slot_jackpot", "emoji": "🎰", "name": "Slot Jackpot Winner",
        "desc": "Win a God‑Tier Jackpot (7 of a kind) on the slot machine",
        "check": lambda u: u.get("slot_jackpots", 0) >= 1
    })
    achievements.append({
        "id": "cardgame_win", "emoji": "🃏", "name": "Card Shark",
        "desc": "Win a multiplayer card game",
        "check": lambda u: u.get("cardgame_wins", 0) >= 1
    })
    achievements.append({
        "id": "gamble_win", "emoji": "💸", "name": "Lucky Gambler",
        "desc": "Win a gamble (double or nothing) 10 times",
        "check": lambda u: u.get("gamble_wins", 0) >= 10
    })
    for target in [1, 5, 10]:
        achievements.append({
            "id": f"guild_level_{target}",
            "emoji": "🏰",
            "name": f"Guild Level {target}",
            "desc": f"Reach Guild Level {target}",
            "check": lambda u, t=target: u.get("guild_level", 0) >= t
        })
    achievements.append({
        "id": "first_blood", "emoji": "🎯", "name": "First Blood",
        "desc": "Every legend starts somewhere. Catch your very first character.",
        "check": lambda u: u.get("total_caught", 0) >= 1
    })
    achievements.append({
        "id": "completionist", "emoji": "🌈", "name": "Completionist",
        "desc": f"Collect at least one of every rarity ({RARITY_TIERS[-1].title()} to {RARITY_TIERS[0].title()})",
        "check": lambda u: all(any(classify_rarity(item.get("rarity", "")) == tier for item in u.get("harem", []) if isinstance(item, dict)) for tier in RARITY_TIERS)
    })
    # New quiz achievement
    achievements.append({
        "id": "quiz_master",
        "emoji": "🧠",
        "name": "Quiz Master",
        "desc": "Correctly answer a Rarity 1 quiz question",
        "check": lambda u: u.get("quiz_correct", 0) >= 1
    })
    quiz_targets = [3, 5, 10, 20, 50]
    quiz_emojis = ["🐟", "🧩", "🎓", "🏅", "👑"]
    for i, target in enumerate(quiz_targets):
        achievements.append({
            "id": f"quiz_correct_{target}",
            "emoji": quiz_emojis[i % len(quiz_emojis)],
            "name": f"Rescue Quiz x{target}",
            "desc": f"Correctly answer {target} Rarity 1 Rescue Quiz questions",
            "check": lambda u, t=target: u.get("quiz_correct", 0) >= t
        })
    extra_milestones = [15, 20, 30, 40, 60, 70, 80, 90, 120, 150, 180, 210, 250, 300, 350, 400, 450, 600, 700, 800, 900, 1200, 1500, 2000, 2500, 3000, 4000, 5000]
    for target in extra_milestones:
        if not any(a["id"] == f"catch_{target}" for a in achievements):
            achievements.append({
                "id": f"catch_{target}",
                "emoji": "🃏",
                "name": f"Catch {target} Characters",
                "desc": f"Capture {target} characters",
                "check": lambda u, t=target: u.get("total_caught", 0) >= t
            })
    return achievements[:300]

ACHIEVEMENTS = generate_achievements()
ACHIEVEMENTS_BY_ID = {a["id"]: a for a in ACHIEVEMENTS}

async def check_and_award_achievements(user_id, notify_chat_id=None):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        return []
    earned_ids = set(user_doc.get("achievements", []))
    newly_earned = []
    for ach in ACHIEVEMENTS:
        if ach["id"] in earned_ids:
            continue
        try:
            if ach["check"](user_doc):
                newly_earned.append(ach)
        except Exception:
            continue
    if not newly_earned:
        return []
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$addToSet": {"achievements": {"$each": [a["id"] for a in newly_earned]}}}
    )
    if notify_chat_id:
        for ach in newly_earned:
            try:
                await send_safe_message(
                    bot1, notify_chat_id,
                    f"🏅 <b>ACHIEVEMENT UNLOCKED!</b>\n{ach['emoji']} <b>{ach['name']}</b>\n<i>{ach['desc']}</i>",
                    parse_mode='html'
                )
            except Exception:
                pass
    return newly_earned

def format_achievement_unlocks(newly_earned):
    if not newly_earned:
        return ""
    lines = "\n".join(f"{a['emoji']} <b>{a['name']}</b>" for a in newly_earned)
    return f"\n\n🏅 <b>ACHIEVEMENT UNLOCKED!</b>\n{lines}"

# ==========================================
# SMART TEXT NORMALIZER
# ==========================================
def normalize_name(text):
    if not text: return ""
    text = unicodedata.normalize('NFKC', text).lower().strip()
    text = re.sub(r'[^\w\s]', '', text)
    text = re.sub(r'\s+', ' ', text)
    return text.strip()

# ==========================================
# FLASK KEEP-ALIVE
# ==========================================
app = Flask('')
@app.route('/')
def home(): return "Bot Control System is Active!"

def run_flask():
    port = int(os.environ.get('PORT', 10000))
    app.run(host='0.0.0.0', port=port)

logging.basicConfig(format='%(asctime)s - %(levelname)s - %(message)s', level=logging.ERROR)

# ==========================================
# ENVIRONMENT & DATABASE
# ==========================================
def _require_env(name):
    value = os.environ.get(name)
    if not value:
        raise RuntimeError(f"❌ Missing required environment variable: {name}.")
    return value

OWNER_ID = int(_require_env("OWNER_ID"))
MONGO_URI = _require_env("MONGO_URI")
APP_ID = int(_require_env("APP_ID"))
APP_HASH = _require_env("APP_HASH")
MAIN_BOT_TOKEN = _require_env("MAIN_BOT_TOKEN")
# 🔐 OWNER BOT — a second, separate bot token used ONLY for owner-only commands
# (/addchar, /ktr, /ktrr, /shadow, /unshadow). Keeping these on a distinct bot
# account means the sensitive control commands never share a token with the
# public-facing game bot.
OWNER_BOT_TOKEN = _require_env("OWNER_BOT_TOKEN")
# 🛡️ Guard Bot has been retired as a separate bot/token and fully merged into bot1 — see
# the bot3 comment near the client definitions below. No separate token needed anymore.
SPECIFIC_CONTROL_GROUP = int(_require_env("SPECIFIC_CONTROL_GROUP"))
SPECIFIC_GROUP = int(_require_env("SPECIFIC_GROUP"))
# Optional: a channel where every /addchar'd character gets auto-posted with full details.
# Not required — if unset, /addchar simply skips the channel post and says so.
# 🩹 CHANGED (per owner request): new channel is https://t.me/Character_Collocter
# (id 3997871300 → -1003997871300 in Bot API/MTProto form). This is only a FALLBACK default —
# if the CHARACTER_CHANNEL_ID env var is set on Render, that value wins. ⚠️ IMPORTANT: update
# the Render env var to -1003997871300 directly — don't rely on this fallback alone, since an
# old env var pointing at the previous channel would silently override it.
_character_channel_env = os.environ.get("CHARACTER_CHANNEL_ID")
CHARACTER_CHANNEL_ID = int(_character_channel_env) if _character_channel_env else -1003997871300
TZ = pytz.timezone('Asia/Yangon')
STORAGE_CHANNEL = SPECIFIC_CONTROL_GROUP
GLOBAL_SPAWN_CHAT_KEY = "global"  # groups_config_col doc key used for the default/global spawn_target

# MongoDB with connection pool
client_mongo = AsyncIOMotorClient(MONGO_URI, maxPoolSize=10)
db = client_mongo["telegram_bot"]
allow_col = db["allowed_users"]
groups_col = db["active_groups"]
talk_col = db["random_talk"]
ans_col = db["chatbot_answers"]
morgan_col = db["morgan_talk"]
system_col = db["system_col"]
reply_save_col = db["reply_save_col"]
users_col = db["users"]
user_game_profiles_col = db["user_game_profiles"]
characters_col = db["characters"]
muted_registry_col = db["muted_registry"]
characters_base_col = db["characters_base_data"]
users_catcher_col = db["users_catcher_data"]
groups_counters_col = db["groups_msg_counters"]
groups_config_col = db["groups_catcher_config"]
guilds_col = db["guilds_data"]
gift_history_col = db["gift_history"]
haido_history_col = db["haido_history"] # records each person-to-person /gift for profile stats
artists_col = db["artists"]  # 🎨 artist_name (lowercased) -> linked Telegram user_id, for Guard Bot collect rewards — see /linkartist
wealth_compression_log_col = db["wealth_compression_log"] # 🐋 audit trail — one doc per /compresswealth confirm run
force_sub_reclaim_log_col = db["force_sub_reclaim_log"] # 🧾 audit trail — one doc per /reclaimforcesub confirm run
rarity_quiz_bank_col = db["rarity_quiz_bank"] # 🔐 owner-authored Rarity 1-4 gate quiz questions
bot_settings_col = db["bot_settings"] # ⚙️ single-document global settings
debts_col = db["debts"]  # 💰 အကြွေးစာရင်း
added_owners_col = db["added_owners"]  # /addowner — see load_added_owners_cache below
# 🔭 CROSS-BOT MONITOR — merged in from the standalone "identify other bots' spawns" script.
# Separate collections from characters_col/characters_base_col on purpose: these hold OTHER
# people's bots' characters (catch_bot, obtain_bot, ...), never our own — see the big comment
# block above userbot_channel_listener() further down for the full picture.
xbot_hashes_col = db["xbot_character_hashes"]      # hash -> {name, source_bot, chat_id, ...}
monitored_channels_col = db["xbot_monitored_channels"]  # chat_id -> source_bot type being watched
bot_mapping_col = db["xbot_bot_mapping"]           # other bot's user_id -> source_bot type
# Redis caching with connection pool
# NOTE: previously hardcoded to host='localhost' — if Redis runs anywhere other
# than the same machine as the bot (managed Redis, separate container, Redis
# Cloud/Upstash, etc.) that connection can never succeed. Set REDIS_URL in the
# environment (e.g. redis://user:pass@host:port/0 or rediss://... for TLS) to
# point at the real instance. Falls back to localhost for local/dev setups.
REDIS_URL = os.environ.get("REDIS_URL", "redis://localhost:6379")
redis_client = redis.Redis.from_url(REDIS_URL, decode_responses=True, max_connections=10)

async def get_cached_user(user_id):
    try:
        cached = await redis_client.get(f"user:{user_id}")
        if cached:
            return json.loads(cached)
    except Exception as e:
        print(f"⚠️ Redis get_cached_user error: {e}")
    user = await users_catcher_col.find_one({"user_id": user_id}, {"_id": 0})  # exclude ObjectId (not JSON serializable)
    if user:
        try:
            await redis_client.setex(f"user:{user_id}", 300, json.dumps(user, default=str))
        except Exception as e:
            print(f"⚠️ Redis get_cached_user write error: {e}")
    return user

# ---- Character-data cache: characters_base_data barely changes (only via /addchar, /editchar,
# /delchar) but is read on almost every group message (spawn trigger) and every /dex lookup.
# TTL is short on purpose: a newly-hit spawn_limit may stay "eligible" for a few seconds longer
# than it should, which is a harmless, rare edge case compared to hitting Mongo on every message.
CHAR_CACHE_TTL = 300  # 5 minutes — roster only changes on /addchar,/editchar,/delchar (which invalidate this explicitly anyway)

async def get_all_characters_cached():
    try:
        cached = await redis_client.get("cache:chars:all")
        if cached:
            return json.loads(cached)
    except Exception as e:
        print(f"⚠️ Redis get_all_characters_cached error: {e}")
    data = await characters_base_col.find({}, {"_id": 0}).to_list(length=None)
    try:
        await redis_client.setex("cache:chars:all", CHAR_CACHE_TTL, json.dumps(data, default=str))
    except Exception as e:
        print(f"char cache write error: {e}")
    return data

async def get_all_categories_cached():
    try:
        cached = await redis_client.get("cache:chars:categories")
        if cached:
            return json.loads(cached)
    except Exception as e:
        print(f"⚠️ Redis get_all_categories_cached error: {e}")
    data = await characters_base_col.distinct("category")
    try:
        await redis_client.setex("cache:chars:categories", CHAR_CACHE_TTL, json.dumps(data, default=str))
    except Exception as e:
        print(f"category cache write error: {e}")
    return data

async def get_category_totals_cached():
    """{category: total_card_count} across the whole roster — used by /harem to show
    'owned/total' per series. Only changes on /addchar, /editchar, /delchar, so it's
    cached the same way as the other character-roster lookups above."""
    try:
        cached = await redis_client.get("cache:chars:category_totals")
        if cached:
            return json.loads(cached)
    except Exception as e:
        print(f"⚠️ Redis get_category_totals_cached error: {e}")
    pipeline = [{"$group": {"_id": "$category", "count": {"$sum": 1}}}]
    data = {(doc["_id"] or "Unknown Series"): doc["count"] for doc in await characters_base_col.aggregate(pipeline).to_list(length=None)}
    try:
        await redis_client.setex("cache:chars:category_totals", CHAR_CACHE_TTL, json.dumps(data))
    except Exception as e:
        print(f"category totals cache write error: {e}")
    return data

# ---- Character display-photo cache ----
# Every place that shows a character's photo (spawns, /check, /who, /harem, gallery, gift
# confirms, etc.) currently does its own fresh client.get_messages(SPECIFIC_CONTROL_GROUP,
# ids=storage_msg_id) call — a live Telegram API round trip, every single time, for media
# that essentially never changes. Under concurrent traffic from many groups at once, this is
# the same bot account repeatedly hitting the same handful of messages in the SAME storage
# chat — exactly the kind of pattern that can trip Telegram's own flood-wait limits for this
# bot account, which would slow things down for every group at once, not just one.
# In-memory (not Redis) on purpose: Telethon's message/media objects aren't JSON-safe, and
# this process is a single Render instance anyway, so a plain dict is the simplest cache that
# actually fits the architecture.
_CHAR_PHOTO_CACHE = {}  # char_id -> (media_object, cached_at)
CHAR_PHOTO_CACHE_TTL = 3600  # 1 hour — cleared early anyway by invalidate_character_caches()

async def get_char_display_media(client, char_id, storage_msg_id):
    """Cached wrapper around client.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_msg_id)
    for a character's stored photo. Returns the media object, or None if it can't be fetched."""
    cached = _CHAR_PHOTO_CACHE.get(char_id)
    if cached and (time.time() - cached[1]) < CHAR_PHOTO_CACHE_TTL:
        return cached[0]
    media = None
    try:
        storage_msg = await client.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_msg_id)
        if storage_msg and storage_msg.media:
            media = storage_msg.media
    except Exception as e:
        print(f"⚠️ get_char_display_media fetch error for {char_id}: {e}")
    _CHAR_PHOTO_CACHE[char_id] = (media, time.time())
    return media

async def get_char_display_media_batch(client, cards):
    """Batched sibling of get_char_display_media, for a whole page of cards at once (the
    inline galleries need many cards' media in a single inline-query response, and Telegram's
    ~10s inline-query timeout means these can't afford one round trip per card). Returns
    {char_id: media_or_None}. Only cards missing from the cache (or past its TTL) trigger a
    real fetch — and that fetch is still ONE batched get_messages() call covering every miss
    at once, same principle as get_user_ranks_for_cards' cache-then-batch-fill pattern, so a
    page that's mostly cache hits (very likely once anything has been browsed once) costs
    nothing beyond that dict lookup."""
    now = time.time()
    result = {}
    missing_cards = []
    for card in cards:
        cid = card["char_id"]
        cached = _CHAR_PHOTO_CACHE.get(cid)
        if cached and (now - cached[1]) < CHAR_PHOTO_CACHE_TTL:
            result[cid] = cached[0]
        else:
            missing_cards.append(card)
    if missing_cards:
        missing_ids = [c["storage_msg_id"] for c in missing_cards]
        try:
            fetched = await client.get_messages(SPECIFIC_CONTROL_GROUP, ids=missing_ids)
        except Exception as e:
            print(f"⚠️ get_char_display_media_batch fetch error: {e}")
            fetched = [None] * len(missing_cards)
        for card, msg in zip(missing_cards, fetched):
            cid = card["char_id"]
            media = msg.media if (msg and msg.media) else None
            _CHAR_PHOTO_CACHE[cid] = (media, now)
            result[cid] = media
    return result

async def send_with_char_media(char_id, storage_msg_id, send_func):
    """THE FIX for the file_reference bug: runs send_func(media) using this character's
    cached photo. A Telegram file_reference (the part of a media object that actually lets
    you attach it to a BRAND NEW message) is only valid for a limited window after it was
    obtained — reusing the SAME cached media object to send new messages later (which is
    exactly what caching is for) will eventually raise errors.FileReferenceExpiredError once
    enough time has passed since that reference was fetched. This is almost certainly what
    caused spawns/collect/haido to start failing after the caching change shipped: the first
    send after caching works fine (fresh reference), but every later reuse of that same
    cached entry carries a reference that's progressively more likely to have gone stale —
    which is also why it got WORSE over time and eventually spawns stopped entirely, instead
    of failing consistently from the start.
    On that specific error, this invalidates just the one cache entry, fetches a genuinely
    fresh reference, and retries send_func ONCE more. Any other exception (or a second
    failure) propagates normally to the caller's own try/except, unchanged from before."""
    media = await get_char_display_media(bot1, char_id, storage_msg_id)
    if media is None:
        return None
    try:
        return await send_func(media)
    except errors.FileReferenceExpiredError:
        _CHAR_PHOTO_CACHE.pop(char_id, None)
        fresh_media = await get_char_display_media(bot1, char_id, storage_msg_id)
        if fresh_media is None:
            raise
        print(f"♻️ Refreshed stale file_reference for {char_id} and retried send.")
        return await send_func(fresh_media)

async def invalidate_character_caches():
    """Call this right after /addchar, /editchar, or /delchar successfully changes the roster."""
    _CHAR_PHOTO_CACHE.clear()  # cheap in-process clear — cheaper to wipe it all than to track exactly which char_id(s) changed
    try:
        await redis_client.delete("cache:chars:all", "cache:chars:categories", "cache:chars:category_totals")
    except Exception as e:
        print(f"char cache invalidate error: {e}")

async def _generate_new_char_id():
    """BOD-prefixed random ID. 🩹 CHANGED (per owner request): starts as 4 digits
    (BOD1..BOD9999, ~9999 possible IDs) same as before, but once that range is full — or even
    just heavily saturated, so blind random retries start colliding a lot — it automatically
    expands to 5 digits (BOD10000..BOD99999) instead of retrying forever inside an
    increasingly-crowded 4-digit space. A bounded number of random attempts is the "is this
    range full?" signal, cheaper than a COUNT query on every single call."""
    for _ in range(50):
        candidate = f"BOD{random.randint(1, 9999)}"
        if not await characters_base_col.find_one({"char_id": candidate}):
            return candidate
    while True:
        candidate = f"BOD{random.randint(10000, 99999)}"
        if not await characters_base_col.find_one({"char_id": candidate}):
            return candidate

# ---- Rarity-gate quiz illustration cache ----
# Same idea as _CHAR_PHOTO_CACHE, separate small dict since this is keyed by
# question_media_msg_id (a quiz's own optional flavor image, set via /addquiz) rather than a
# char_id — this fires every time a Rarity 1-4 spawn gets quiz-gated, across every group, so
# it's a hot path too. No explicit invalidation hook (quiz illustrations are essentially
# never replaced after creation) — the TTL alone is enough here.
_QUIZ_MEDIA_CACHE = {}  # question_media_msg_id -> (media_object, cached_at)

async def get_quiz_question_media(client, question_media_msg_id):
    cached = _QUIZ_MEDIA_CACHE.get(question_media_msg_id)
    if cached and (time.time() - cached[1]) < CHAR_PHOTO_CACHE_TTL:
        return cached[0]
    media = None
    try:
        q_storage_msg = await client.get_messages(SPECIFIC_CONTROL_GROUP, ids=question_media_msg_id)
        if q_storage_msg and q_storage_msg.media:
            media = q_storage_msg.media
    except Exception:
        pass
    _QUIZ_MEDIA_CACHE[question_media_msg_id] = (media, time.time())
    return media






# ==========================================
# 🚨 AML "BUST" — comedic flavor event AND bot3's real max-single-bet ceiling
# ==========================================
# Root cause of the currency-inflation problem: none of bot3's games ever capped how large a
# single bet could be. With payout multipliers up to 100x (crash) / 50x (tower) / 25x
# (colortower) / 14x (roulette green) and NO ceiling, a player only ever needs a handful of
# lucky high-multiplier wins in a row — each one multiplying their ENTIRE current balance — to
# snowball into an astronomical, uncountable number. That's exactly the pattern of the /richest
# leaderboard: each rank a huge multiple of the next, not a gradual accumulation.
# AML_BUST_THRESHOLD closes that off directly: no bet can ever be placed at or above it, full
# stop — dressed up as a satirical "money-laundering investigation" instead of a flat error, per
# request. It is flavor text only; nothing here is a real restriction on the user's account
# outside the game layer.
AML_BUST_THRESHOLD = 1_000_000    # USD — the hard ceiling on any single bot3 bet
AML_JAIL_SECONDS = 600            # 10 min "under investigation" — bot3 games refuse to start




async def _dedupe_groups_config():
    pipeline = [
        {"$group": {"_id": "$chat_id", "count": {"$sum": 1}}},
        {"$match": {"count": {"$gt": 1}}}
    ]
    dupes = await groups_config_col.aggregate(pipeline).to_list(length=None)
    for group in dupes:
        docs = await groups_config_col.find({"chat_id": group["_id"]}).sort("_id", 1).to_list(length=None)
        merged = {}
        for doc in docs:
            for k, v in doc.items():
                if k == "_id":
                    continue
                merged[k] = v
        keep_id = docs[-1]["_id"]
        await groups_config_col.update_one({"_id": keep_id}, {"$set": merged})
        remove_ids = [d["_id"] for d in docs if d["_id"] != keep_id]
        if remove_ids:
            await groups_config_col.delete_many({"_id": {"$in": remove_ids}})

async def _migrate_rarity_tiers():
    """Backfill the rarity_tier field for characters saved before this field existed,
    so rarity-based lookups (quiz rewards, hmode filter, dex breakdown) can use an index
    instead of scanning + re-classifying every document every time."""
    untagged = await characters_base_col.find({"rarity_tier": {"$exists": False}}, {"_id": 1, "rarity": 1}).to_list(length=None)
    if not untagged:
        return
    ops = [UpdateOne({"_id": doc["_id"]}, {"$set": {"rarity_tier": classify_rarity(doc.get("rarity", ""))}}) for doc in untagged]
    if ops:
        await characters_base_col.bulk_write(ops)
        print(f"🏷️ Backfilled rarity_tier for {len(ops)} characters.")

async def _migrate_old_4tier_to_9tier():
    """One-time migration: the rarity system expanded from 4 tiers (Sweetie/Blossom/Fluffy/
    Kawaii) to 9 (matching catch_bot's own scheme exactly — see RARITY_TIERS above). Every
    character on the OLD scheme becomes MYSTICAL under the new one — a deliberate one-time
    choice per owner request, not an attempt to "best guess" an equivalent new tier, since the
    old 4 tiers don't correspond to any of the new 9 in a principled way.
    Matches on the literal old tier tokens directly (both the rarity_tier field AND a fallback
    regex on the rarity display string) rather than re-running classify_rarity() — that way
    this is correct regardless of whether _migrate_rarity_tiers() above has already run in
    this same startup using the NEW RARITY_TIERS (which no longer contains the old names, so
    classify_rarity() on an old-scheme character would come back "OTHER", not the old tier)."""
    old_tier_names = ["SWEETIE", "BLOSSOM", "FLUFFY", "KAWAII"]
    new_rarity_display = RARITY_NUM_MAP[RARITY_TIER_TO_NUM["MYSTICAL"]]["name"]
    result = await characters_base_col.update_many(
        {
            "$or": [
                {"rarity_tier": {"$in": old_tier_names}},
                {"rarity": {"$regex": "SWEETIE|BLOSSOM|FLUFFY|KAWAII", "$options": "i"}}
            ]
        },
        {"$set": {"rarity_tier": "MYSTICAL", "rarity": new_rarity_display}}
    )
    if result.modified_count:
        print(f"🏷️ Migrated {result.modified_count} characters from the old 4-tier scheme to MYSTICAL under the new 9-tier scheme.")
        await invalidate_character_caches()

async def _migrate_name_normalized():
    """Backfill name_normalized (see _normalize_catchbot_name) for auto-imported characters
    saved before that field existed — without this, _find_imported_character's fast path
    misses them and always falls back to the slower raw-regex match, which is exactly the
    kind of exact-string match that variation-selector differences can silently break."""
    missing = await characters_base_col.find(
        {"auto_imported_from": {"$exists": True}, "name_normalized": {"$exists": False}},
        {"_id": 1, "name": 1}
    ).to_list(length=None)
    if not missing:
        return
    ops = [UpdateOne({"_id": doc["_id"]}, {"$set": {"name_normalized": _normalize_catchbot_name(doc.get("name", ""))}}) for doc in missing]
    if ops:
        await characters_base_col.bulk_write(ops)
        print(f"🏷️ Backfilled name_normalized for {len(ops)} auto-imported characters.")

async def create_indexes():
    print("⚡ Creating Database Indexes...")
    await users_col.create_index("user_id", unique=True)
    await users_catcher_col.create_index("user_id", unique=True)
    await groups_col.create_index("chat_id", unique=True)
    await reply_save_col.create_index("trigger")
    # 🗣️ /rton — random_talk is looked up filtered by chat_id on every speak, and grows one
    # document per harvested message while active, so this needs an index from day one.
    await talk_col.create_index("chat_id")
    await users_catcher_col.create_index("total_caught")
    await users_catcher_col.create_index([("group_catches.$**", 1)])
    await users_catcher_col.create_index([("total_caught", -1)])
    await users_catcher_col.create_index([("total_gifted", -1)])
    await users_catcher_col.create_index([("daily_streak", -1)])
    await users_catcher_col.create_index([("last_daily", 1)])
    await users_catcher_col.create_index([("group_catches.chat_id", -1)])
    await users_catcher_col.create_index([("last_catch_date", -1), ("daily_catches", -1)])
    await users_catcher_col.create_index([("quiz_correct", -1)])
    # ⚡ backs /today's "who hit the daily catch limit first" ranking (see
    # render_today_leaderboard) — a sparse index since only users who've actually hit the
    # cap today have this field set at all.
    await users_catcher_col.create_index([("daily_limit_hit_at", 1)], sparse=True)
    # ⚡ harem.char_id (multikey) — backs the rank-leaderboard aggregation used by
    # /harem. Without this, every rank lookup was a full collection scan.
    await users_catcher_col.create_index("harem.char_id")
    await _dedupe_groups_config()
    await groups_config_col.create_index("chat_id", unique=True)
    await muted_registry_col.create_index([("chat_id", 1), ("user_id", 1)])
    await user_game_profiles_col.create_index("user_id", unique=True)
    await characters_col.create_index("name", unique=True)
    await characters_base_col.create_index("char_id", unique=True)
    await characters_base_col.create_index("category")
    await characters_base_col.create_index("rarity_tier")
    await characters_base_col.create_index("spawn_limit")
    await characters_base_col.create_index("name_normalized")
    await gift_history_col.create_index([("sender_id", 1), ("timestamp", -1)])
    await gift_history_col.create_index([("receiver_id", 1), ("timestamp", -1)])
    # haido_history_col indexes
    await haido_history_col.create_index([("chat_id", 1), ("timestamp", -1)])
    await haido_history_col.create_index([("claimed_by", 1), ("timestamp", -1)])
    await haido_history_col.create_index("claimed")
    # 📈 Catcher indexes
    await users_catcher_col.create_index([("daily_catches", -1)])
    await users_catcher_col.create_index("harem.caught_date")
    await users_catcher_col.create_index("harem.chat_id")
    # ⚡ groups_msg_counters is read+written on almost EVERY group message (the spawn-trigger
    # counter) — it had no index at all, meaning every single message did a full collection
    # scan. This is the single hottest query path in the whole bot.
    await groups_counters_col.create_index("chat_id", unique=True)
    await artists_col.create_index("artist_name", unique=True)
    # ❌ REMOVED: gotu_pairs_col, gotu_games_col, gotu_players_col, quiz_questions_col, quiz_msg_counters_col
    # 🔭 Cross-bot monitor (xbot_*) — hash is looked up on every /who miss against our own
    # roster; monitored_channels/bot_mapping are tiny admin tables, unique on their key.
    await xbot_hashes_col.create_index("hash", unique=True)
    await xbot_hashes_col.create_index("name")
    await xbot_hashes_col.create_index("source_bot")
    await xbot_hashes_col.create_index("chat_id")
    await monitored_channels_col.create_index("chat_id", unique=True)
    await bot_mapping_col.create_index("bot_id", unique=True)
    await _migrate_rarity_tiers()
    await _migrate_old_4tier_to_9tier()
    await _migrate_name_normalized()
    print("Database Indexes synchronized! ✔️")

try:
    asyncio.get_event_loop()
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH, flood_sleep_threshold=10)
# 🛡️ bot2/bot3 have been fully retired — everything now runs on bot1. bot3 is kept as a
# permanent `None` (rather than deleting the name outright) so any leftover `bot3 is None` /
# `bot3 is not None` check elsewhere still resolves safely instead of raising a NameError.
bot3 = None
bot_ids = bot_state.bot_ids
active_group_spawns = bot_state.active_group_spawns
STEALTH_MAU_MODE = False
spawn_locks = bot_state.spawn_locks
pending_editchar_prompt_ids = bot_state.pending_editchar_prompt_ids
sticker_spam_data = bot_state.sticker_spam_data
char_spam_data = bot_state.char_spam_data
admin_cache = bot_state.admin_cache
dark_passenger_targets = bot_state.dark_passenger_targets
# 👑 /addowner — user_ids granted the SAME unlimited-vault viewing/fav privilege as OWNER_ID,
# but deliberately NOT the same gift bypass — see add_owner_command's own docstring further
# down for the full reasoning. Loaded once at startup (load_added_owners_cache), kept in sync
# in-memory on every /addowner or /removeowner.
added_owner_ids = set()

async def load_added_owners_cache():
    global added_owner_ids
    try:
        docs = await added_owners_col.find({}, {"user_id": 1}).to_list(length=None)
        added_owner_ids = {d["user_id"] for d in docs}
    except Exception as e:
        print(f"load_added_owners_cache error: {e}")
IS_REPLY_ACTIVE = False
REPLY_INTERVAL = 4
reply_msg_counters = bot_state.reply_msg_counters
group_spawn_counters = bot_state.group_spawn_counters
# 🗣️ Random talk (retired): used to quietly save clean lines from real chat and say one back
# every RANDOM_TALK_INTERVAL messages, unprompted. /rton and /rtoff are removed, so this stays
# permanently off — see random_talk_engine below. /rtclean still exists to wipe talk_col.
IS_RANDOM_TALK_ACTIVE = False
RANDOM_TALK_INTERVAL = 50
random_talk_counters = bot_state.random_talk_counters
USER_METRICS_BUFFER = []
BUFFER_LOCK = asyncio.Lock()
user_cooldowns = bot_state.user_cooldowns
# ---- SLOT SESSIONS (မြန်မာလို Inline-Button နဲ့ ဆက်ကစားမယ်) ----
active_slot_sessions = {}  # user_id -> {bet, net, msg_id, chat_id, spins}
# လောင်းငွေ ပေါင်းထည့်ခလုတ်တွေအတွက် ပမာဏများ
BET_PRESETS = [1, 10, 100, 1000, 10000, 100000]
# ==========================================
# 🖱️ INLINE BUTTON SPAM-CLICK GUARD
# ==========================================
# 🩹 FIX: no inline button anywhere in the bot was rate-limited — every tap re-fired its
# handler instantly. Most handlers just .edit() a message, which is wasteful but harmless.
# A few (e.g. the "My Profile" button shown on a successful catch — see catchprofile_ in
# system_callback_router) call event.respond(), which posts a BRAND NEW message every time.
# A user mashing that button could flood the chat with duplicate profile cards in seconds,
# and every rapid click also burns a fresh DB read. This handler is registered before every
# other CallbackQuery handler in the file, so (Telethon dispatches handlers in registration
# order) it always runs first. If the same user taps again inside the cooldown window, we
# answer the tap immediately with a small non-blocking toast — so the button doesn't look
# "stuck" or broken — and raise StopPropagation so none of the real handlers below ever see
# that click. First tap and every tap after the cooldown passes through untouched.
CALLBACK_CLICK_COOLDOWN = 1.0  # seconds between accepted clicks, per user
_last_callback_click = bot_state._last_callback_click  # user_id -> timestamp

@bot1.on(events.CallbackQuery())
async def callback_spam_click_guard(event):
    user_id = event.sender_id
    if user_id == OWNER_ID:
        return  # owner needs fast, unthrottled access to admin panels/navigation
    now = time.time()
    last = _last_callback_click.get(user_id, 0)
    if now - last < CALLBACK_CLICK_COOLDOWN:
        try:
            await event.answer("ခနစောင့် အချစ်ကလေး!", alert=False)
        except Exception:
            pass
        raise events.StopPropagation
    _last_callback_click[user_id] = now
    if len(_last_callback_click) > 5000:  # opportunistic cleanup, keeps this from growing forever
        cutoff = now - 300
        for k, ts in list(_last_callback_click.items()):
            if ts < cutoff:
                del _last_callback_click[k]

# Spam & Daily catch tracking
user_spam_data = bot_state.user_spam_data  # (user_id, chat_id) -> list of timestamps
user_mute_until = bot_state.user_mute_until  # user_id -> timestamp (GLOBAL — applies in every group)
active_haido_events = bot_state.active_haido_events  # chat_id -> {"char_id", "char_name", "rarity", "spawn_time", "claimed_by", "claimed"}
HAIDO_TIMEOUT_SECONDS = 900  # 15 minutes

# ---- Supreme (No.1, the rarest tier) spawns are gated behind a quiz: chosen_char is picked
# as usual, but instead of spawning immediately, a question + 4 inline buttons is posted. Only
# the FIRST correct tap actually releases the spawn (normal /who + /collect flow after that).
# chat_id -> {"char", "options", "correct_index", "question", "msg_id", "quiz_time", "solved"}
pending_rarity_quiz = bot_state.pending_rarity_quiz
RARITY_GATE_TIERS = {RARITY_TIERS[0], RARITY_TIERS[1], RARITY_TIERS[2], RARITY_TIERS[3]}
RARITY_GATE_TIMEOUT_SECONDS = 60
RARITY_QUIZ_BANK = []
# ---- /ban, /unban, /kick fire a ChatAction (participant update) themselves — e.g. lifting a
# ban via /unban shows up to Telethon as the user "leaving", which used to trigger a spurious
# goodbye message right after the UNBAN OPERATION confirmation. Anything we changed ourselves
# via /ban, /unban, or /kick is recorded here for a few seconds so welcome_goodbye can ignore
# the resulting ChatAction instead of misfiring a welcome/goodbye text for it.
recent_mod_actions = bot_state.recent_mod_actions  # (chat_id, user_id) -> timestamp
MOD_ACTION_SUPPRESS_WINDOW = 10  # seconds

def mark_mod_action(chat_id, user_id):
    recent_mod_actions[(chat_id, user_id)] = time.time()

def was_recent_mod_action(chat_id, user_id):
    ts = recent_mod_actions.pop((chat_id, user_id), None)
    return ts is not None and (time.time() - ts) <= MOD_ACTION_SUPPRESS_WINDOW

# ---- Telegram/Telethon sometimes deliver more than one raw update for a SINGLE "bot was
# added to this group" action (e.g. a service message update AND a separate participant
# update). Without a guard, welcome_goodbye below would fire 2-3x, sending the owner-notify
# and the group intro message that many times. Same lock-then-recheck shape as spawn_locks.
bot_added_locks = bot_state.bot_added_locks
_recent_bot_added_chats = bot_state._recent_bot_added_chats  # chat_id -> timestamp
BOT_ADDED_DEDUP_WINDOW = 30  # seconds

def bq(text): return f"<b>{text}</b>"
def owner_tag():
    return f"<a href='tg://user?id={OWNER_ID}'><b>Owner</b></a>"

# ==========================================
# 💵 USD ECONOMY — fixed peg, replaces the old uncapped MMK economy
# ==========================================
# 2026-07 MIGRATION: the old MMK economy had no ceiling and had inflated to
# quadrillions of USD for long-time players, making every balance unreadable. Every
# MMK-denominated constant in this file has been divided by MMK_PER_USD (kept as
# "<old MMK value> / MMK_PER_USD" inline, so the original number is still visible for
# audit) and the whole bot now speaks USD only. Existing player balances are migrated
# exactly once by the owner-only /changeusd confirm command — see run_usd_migration().
MMK_PER_USD = 4000  # the fixed peg: 1 USD = 4000 MMK (old currency, no longer displayed)

# Rarity 1 (highest) → 4 (lowest). Emoji come from RARITY_EMOJI so there is only
# ever ONE place to change them. "name" is what gets stored on characters/harem items and
# shown everywhere — it's just the emoji + fancy font tier name, no rank number, so the
# name itself stays clean (no "No.X", no Burmese) wherever it's displayed.
_RARITY_VALUE_MAP = {
    "SUPREME": 1000, "CATAPHRACT": 700, "CROSSVERSE": 500, "DIVINE": 350, "MYSTICAL": 250,
    "LEGENDARY": 150, "RARE": 100, "UNCOMMON": 60, "COMMON": 30
}
# ⚠️ Display name for each tier, English only (no Burmese in the rarity name).
# classify_rarity() still matches on the bare RARITY_TIERS token (e.g. "SUPREME"), which is
# always the English display name here too, so this is safe to change freely without touching
# classification/sorting/weights.
RARITY_DISPLAY_NAME = {
    "SUPREME": "Supreme", "CATAPHRACT": "Cataphract", "CROSSVERSE": "CrossVerse", "DIVINE": "Divine",
    "MYSTICAL": "Mystical", "LEGENDARY": "Legendary", "RARE": "Rare", "UNCOMMON": "Uncommon", "COMMON": "Common"
}
RARITY_NUM_MAP = {
    str(i + 1): {
        "name": f"{RARITY_EMOJI[tier]} {f(RARITY_DISPLAY_NAME[tier])}",
        "value": _RARITY_VALUE_MAP[tier]
    }
    for i, tier in enumerate(RARITY_TIERS)
}
# Reverse lookup: canonical tier name -> its rarity number ("1".."4"). Used by /changeallrarity
# and anywhere we need to re-derive the current official display name for an existing tier.
RARITY_TIER_TO_NUM = {tier: str(i + 1) for i, tier in enumerate(RARITY_TIERS)}

# ==========================================
# ⭐ STAR EXCHANGE — TUNING CONSTANTS
# ==========================================
# HELPER FUNCTIONS
# ==========================================
async def get_plain_name(event, user_id=None):
    """Returns just the user's display name as plain text (no HTML) — safe to store in the DB.
    Never store the output of get_html_mention() in a database field: it contains <a>/<b> tags
    which get double-escaped and shown as literal text wherever that field is later displayed."""
    if not user_id: user_id = event.sender_id
    try:
        sender = await event.client.get_entity(user_id)
        first_name = getattr(sender, 'first_name', '') or ''
        last_name = getattr(sender, 'last_name', '') or ''
        fullname = f"{first_name} {last_name}".strip()
        if not fullname: fullname = getattr(sender, 'username', '') or f"Agent {user_id}"
    except:
        fullname = f"Agent {user_id}"
    return fullname

async def get_html_mention(event, user_id=None):
    fullname = await get_plain_name(event, user_id)
    if not user_id: user_id = event.sender_id
    return f"<a href='tg://user?id={user_id}'><b>{escape_html(fullname)}</b></a>"

# 🩹 FIX: these two used to hardcode `bot2` no matter which bot's handler called them.
# Bot1's own welcome_goodbye_enhanced was calling them too, which meant every single join
# and leave in ANY group bot2 isn't a member of (i.e. almost every public group, since bot2
# is the owner-only control bot) paid for a network round-trip that was guaranteed to fail
# before falling back to "Could not fetch" — wasted latency on the hottest possible event
# (member joins), and the reason bot1's welcome/goodbye could look unreliable. Both now take
# the calling client explicitly so each bot uses its own connection.
async def get_user_profile_data(user, chat_id, client=None):
    """User Profile အပြည့်အစုံကို စုစည်းပေးမယ်"""
    client = client or bot1
    first = getattr(user, 'first_name', '') or ''
    last = getattr(user, 'last_name', '') or ''
    fullname = f"{first} {last}".strip() or "Unknown User"
    username = f"@{user.username}" if getattr(user, 'username', None) else "None"
    user_id = user.id
    
    # Premium Status
    is_premium = getattr(user, 'premium', False)
    premium_status = "⭐ Premium" if is_premium else "Standard"
    
    # Bio (အကယ်၍ ရှိရင်)
    bio = getattr(user, 'about', '') or "No bio available."
    
    # Join Date (အဖွဲ့ထဲဝင်ခဲ့တဲ့ရက်စွဲ)
    join_date = "Unknown"
    try:
        participant = await client.get_participants(chat_id, filter=types.ChannelParticipantsSearch(user_id))
        if participant:
            join_date = participant[0].date.strftime("%Y-%m-%d %H:%M:%S") if participant[0].date else "Unknown"
    except Exception:
        join_date = "Could not fetch"
    
    return {
        "fullname": fullname,
        "username": username,
        "user_id": user_id,
        "premium_status": premium_status,
        "is_premium": is_premium,
        "bio": bio,
        "join_date": join_date,
        "user": user
    }

    
async def get_profile_photo(user, client=None):
    """User Profile Photo ကို ယူပေးမယ် (ရှိရင်)"""
    client = client or bot1
    try:
        photos = await client.get_profile_photos(user.id, limit=1)
        if photos:
            return photos[0]
    except Exception:
        pass
    return None

def format_join_message(profile):
    """Join Message ကို UI လှအောင် ဖော်မတ်လုပ်မယ်"""
    premium_emoji = "⭐" if profile["is_premium"] else ""
    return f"""
🪪 <b>Hey,Thers is a New Member.</b>

🪩 <b>Name:</b> {escape_html(profile['fullname'])}
🦖 <b>User ID:</b> <code>{profile['user_id']}</code>
🍭 <b>Username:</b> {profile['username']}
{premium_emoji} <b>Status:</b> {profile['premium_status']}
🐇 <b>Bio:</b> {escape_html(profile['bio'][:100])}
🎒 <b>Join Date:</b> <code>{profile['join_date']}</code>

🎒 <i>Welcome to the group! Have a great time.</i>
    """

def format_leave_message(profile):
    """Leave Message ကို UI လှအောင် ဖော်မတ်လုပ်မယ်"""
    premium_emoji = "⭐" if profile["is_premium"] else ""
    return f"""
🪪 <b>MEMBER LEFT</b>

🪩 <b>Name:</b> {escape_html(profile['fullname'])}
🦖 <b>User ID:</b> <code>{profile['user_id']}</code>
🍭 <b>Username:</b> {profile['username']}
{premium_emoji} <b>Status:</b> {profile['premium_status']}
🎒 <b>Join Date:</b> <code>{profile['join_date']}</code>

🎒 <i>Goodbye! Hope to see you again.</i>
    """


def clean_display_name(name, max_len=25, fallback="Unknown"):
    """Sanitize a name pulled from the DB before displaying it.
    - Strips any HTML tags (defensive: older bug versions could save an HTML mention
      string straight into the fullname field, which then showed up as literal tag
      text once escaped again at display time).
    - Truncates long/heavily-decorated real Telegram names so tables like the
      leaderboard don't break their alignment.
    Always escape_html() the result before embedding it in an HTML-parsed message."""
    if not name:
        return fallback
    name = re.sub(r'<[^>]+>', '', str(name)).strip()
    if not name:
        return fallback
    if len(name) > max_len:
        name = name[:max_len].rstrip() + "…"
    return name

async def _delete_after_delay(client, chat_id, msg_id, delay=10):
    try:
        await asyncio.sleep(delay)
        await client.delete_messages(chat_id, msg_id)
    except Exception:
        pass


# ==========================================
# ALL GROUPS COMMAND INTERCEPTOR
# ==========================================
@bot1.on(events.NewMessage(pattern=r'^[/.]'))
async def global_slash_cmd_acc_opener(event):
    user_id = event.sender_id
    if not user_id: return
    try:
        user_entity = await event.get_sender()
        first_name = getattr(user_entity, 'first_name', '') or ''
        last_name = getattr(user_entity, 'last_name', '') or ''
        fullname = f"{first_name} {last_name}".strip()
        if not fullname: fullname = getattr(user_entity, 'username', '') or f"User {user_id}"
    except:
        fullname = f"User {user_id}"
    await ensure_user_registered(user_id, fullname)

# ==========================================
# 🔐 FORCE-SUBSCRIBE GATE
# ==========================================
# Players must belong to FORCE_SUB_CHAT_ID before they can use the game. This gates /harem,
# .who/.w/.waifu (and its "Who's this?" button), /collect, and the rest of the player-facing
# commands in FORCE_SUB_GATED_COMMANDS below — admin/owner-only commands (mute, ban, addchar,
# etc.) are never touched.
#
# Registered here, immediately after the ALL-GROUPS COMMAND INTERCEPTOR above and well before
# /who (4403), /collect (4602), /harem (4887) or any casino/economy handler further down —
# Telethon calls handlers in registration order, so this always gets first look at a gated
# command and raises events.StopPropagation to stop everything below it from running for
# that message. bot1/bot_ids/schedule_game_cleanup/_OWN_MENTION_RE/BOT1_USERNAME are all
# already defined above this point, so nothing here is a forward reference.
FORCE_SUB_CHAT_ID = int(os.environ.get("FORCE_SUB_CHAT_ID", "-1003580630981"))
FORCE_SUB_REWARD_USD = 500 / MMK_PER_USD
FORCE_SUB_MEMBERSHIP_TTL = 120  # seconds a "yes/no member" answer is cached per user
FORCE_SUB_PROMPT_COOLDOWN = 30  # seconds — don't re-nag the same user more than once per 5 min
FORCE_SUB_PROMPT_TTL = 30  # seconds — the join-nudge message deletes itself after this long

# Exactly the commands an ordinary player uses to play — everything listed in get_game_text()/
# get_casino_text()/get_collection_text(), plus catch/who/w/waifu/haido/trade/sell/buy/dex/
# search/scrap/richest/leaderboard/lb/achievements. Deliberately excludes /start, /help,
# /game, /weather, /gift, /fav, and every admin/owner-only command — /gift and /fav no longer
# nudge a non-member to join the force-sub group.
FORCE_SUB_GATED_COMMANDS = {"slot", "game", "morgan"}
_FORCE_SUB_CMD_RE = re.compile(r'^[/.](\w+)')

force_sub_membership_cache = bot_state.force_sub_membership_cache  # user_id -> (is_member: bool, expiry_ts: float)
force_sub_prompt_last_sent = bot_state.force_sub_prompt_last_sent  # user_id -> ts of the last join-nudge sent (anti-spam)
_force_sub_invite_link = None     # cached invite link for FORCE_SUB_CHAT_ID (fetched once)

async def get_force_sub_invite_link():
    """Fetches (and caches forever — invite links don't change unless revoked) the invite
    link for FORCE_SUB_CHAT_ID. Requires bot1 to have invite rights there; returns None
    (and the join-prompt just skips the button) if that isn't set up yet."""
    global _force_sub_invite_link
    if _force_sub_invite_link:
        return _force_sub_invite_link
    try:
        invite = await bot1(ExportChatInviteRequest(FORCE_SUB_CHAT_ID))
        _force_sub_invite_link = invite.link
    except Exception as e:
        print(f"⚠️ Force-sub invite link fetch failed: {e}")
    return _force_sub_invite_link

async def is_force_sub_member(user_id):
    """True if `user_id` currently belongs to FORCE_SUB_CHAT_ID. Cached briefly per user
    (FORCE_SUB_MEMBERSHIP_TTL) so a burst of commands from the same person doesn't hammer
    Telegram with a fresh permissions lookup every single time."""
    now = time.time()
    cached = force_sub_membership_cache.get(user_id)
    if cached and now < cached[1]:
        return cached[0]
    try:
        perms = await bot1.get_permissions(FORCE_SUB_CHAT_ID, user_id)
        is_member = perms is not None
    except Exception:
        is_member = False
    force_sub_membership_cache[user_id] = (is_member, now + FORCE_SUB_MEMBERSHIP_TTL)
    return is_member

async def send_force_sub_prompt(event):
    """Sends the bilingual (MM/EN) join-nudge and self-deletes it after FORCE_SUB_PROMPT_TTL
    seconds. Rate-limited per user via FORCE_SUB_PROMPT_COOLDOWN so a not-yet-joined person
    mashing a gated command — or a whole group full of them — never turns into the bot
    repeatedly spamming 'please join' messages, including in groups we don't own."""
    user_id = event.sender_id
    now = time.time()
    last = force_sub_prompt_last_sent.get(user_id, 0)
    if now - last < FORCE_SUB_PROMPT_COOLDOWN:
        return  # nudged this person recently already — stay quiet instead of piling on
    force_sub_prompt_last_sent[user_id] = now
    link = await get_force_sub_invite_link()
    text = (
        "🐉🦋 <b>ခဏစောင့်ဦးနော်!</b> ဒီကောင်လေးတွေကို Collect လုပ်ချင်ရင် အောက်က Group ထဲ အရင်ဝင်ဖို့လိုပါတယ် 🦄\n"
        "👇 Group ထဲဝင်ပြီးမှ ဒီ command ကို ပြန်ရိုက်ပေးပါ့။\n\n"
        "🐉🦋 <b>Hold up!</b> You'll need to join our group before you can collect these little guys 🦄\n"
        "👇 Tap below to join, then send the command again."
    )
    buttons = [[Button.url("Join Group / Group ဝင်ရန်", link)]] if link else None
    try:
        msg = await event.reply(text, parse_mode='html', buttons=buttons)
        asyncio.create_task(_delete_after_delay(event.client, event.chat_id, msg.id, delay=FORCE_SUB_PROMPT_TTL))
    except Exception as e:
        print(f"⚠️ Force-sub prompt send failed: {e}")

@bot1.on(events.NewMessage(pattern=r'^[/.]'))
async def force_sub_gate(event):
    user_id = event.sender_id
    if not user_id or user_id == OWNER_ID or user_id in bot_ids:
        return
    m = _FORCE_SUB_CMD_RE.match(event.raw_text or "")
    if not m:
        return
    cmd_word = m.group(1).split('@')[0].lower()
    if cmd_word not in FORCE_SUB_GATED_COMMANDS:
        return
    # Respect the same "only if THIS bot is the one being addressed" rule own_pattern() uses
    # on every individual handler — an explicit /cmd@othername mention should never be gated
    # by bot1's own force-sub rule.
    mention = _OWN_MENTION_RE.match(event.raw_text or "")
    if mention and BOT1_USERNAME and mention.group(1).lower() != BOT1_USERNAME:
        return
    if await is_force_sub_member(user_id):
        return
    await send_force_sub_prompt(event)
    raise events.StopPropagation

# ==========================================
# 🛡️ GAME SPAM THROTTLE (every group — not just the force-join room)
# ==========================================
# Originally scoped to just the force-join room, since that was bot1's busiest room for
# casino/economy commands. But the same problem — a group of people rapid-firing /slot,
# /dice, /mines etc. at once — happens in ANY group bot1 is in, and each one of those
# commands' several send/edit calls eats into bot1's own per-chat and per-account send
# budget. This now throttles game commands everywhere, using the same per-player cooldown.
# The notice is posted via the event's own client (bot1) — Guard Bot (bot3) has been merged
# into bot1, so there's no separate client to route this through anymore.
GUARD_GAME_COOLDOWN_SECONDS = 4  # minimum gap between game commands per player, in any one chat
GUARD_GAME_COMMANDS = {"slot", "cardgame", "flip", "dice", "hilo", "gamble", "mines", "box"}


# ---- JOIN REWARD — REMOVED. This used to grant +FORCE_SUB_REWARD_USD and one random
# character card to anyone joining FORCE_SUB_CHAT_ID (via a ChatAction watcher on new joins,
# plus a startup backfill for existing members). That grant path is gone — nobody gets paid
# for joining anymore. FORCE_SUB_REWARD_USD, the "force_sub_rewarded" flag, and harem entries
# tagged source="force_sub_reward" are KEPT below because /revokereward (single user) and
# /reclaimforcesub (bulk, see further down) both still need them to reverse what was already
# handed out historically. ----

@bot1.on(events.ChatAction(chats=FORCE_SUB_CHAT_ID))
async def force_sub_join_tracker(event):
    """All that's left of the old join-reward watcher: just keeps the membership cache warm
    on a live join, so is_force_sub_member() doesn't need a fresh API call immediately after
    someone joins. No reward is granted."""
    if not (event.user_joined or event.user_added):
        return
    user_id = event.user_id
    if not user_id or user_id in bot_ids:
        return
    force_sub_membership_cache[user_id] = (True, time.time() + FORCE_SUB_MEMBERSHIP_TTL)

# ==========================================
# 🛡️ GUARD BOT — JOIN / LEAVE WATCHER (force-join group only)
# ==========================================
# Separate concern from force_sub_join_tracker above (which just keeps the membership cache
# warm) — this just posts a profile card so the room can see who's coming and going, and it's
# specifically the Guard Bot's job. Reuses get_user_profile_data / get_profile_photo /
# format_join_message / format_leave_message, which already existed in this file (left over
# from before welcome/goodbye was disabled bot1-wide) but had nothing calling them — this
# wires them back up, scoped to just this one group, on bot1.
# ==========================================
GUARD_MASS_JOIN_LEAVE_THRESHOLD = 5

async def _guard_bot_join_leave_watcher(event):
    if event.chat_id != FORCE_SUB_CHAT_ID:
        return
    try:
        target_ids = event.user_ids or [event.user_id]
        real_ids = [uid for uid in target_ids if uid and uid not in bot_ids]
        if not real_ids:
            return

        if len(real_ids) > GUARD_MASS_JOIN_LEAVE_THRESHOLD:
            if event.user_added or event.user_joined:
                await bot1.send_message(event.chat_id, bq(f"🪪 <b>{len(real_ids)} new members joined at once.</b> Welcome all!"), parse_mode='html')
            elif event.user_kicked or event.user_left:
                await bot1.send_message(event.chat_id, bq(f"👋 <b>{len(real_ids)} members left at once.</b>"), parse_mode='html')
            return

        if event.user_added or event.user_joined:
            for uid in real_ids:
                try:
                    user = await bot1.get_entity(uid)
                except Exception:
                    continue
                if getattr(user, 'bot', False):
                    continue
                profile = await get_user_profile_data(user, event.chat_id, client=bot1)
                msg = format_join_message(profile)
                photo = await get_profile_photo(user, client=bot1)
                try:
                    if photo:
                        await bot1.send_file(event.chat_id, photo, caption=msg, parse_mode='html')
                    else:
                        await bot1.send_message(event.chat_id, msg, parse_mode='html')
                except Exception as e:
                    print(f"⚠️ Guard Bot join card failed for {uid}: {e}")

        elif event.user_kicked or event.user_left:
            for uid in real_ids:
                try:
                    user = await bot1.get_entity(uid)
                except Exception:
                    try:
                        await bot1.send_message(event.chat_id, f"👋 <b>User {uid}</b> has left the chat.", parse_mode='html')
                    except Exception:
                        pass
                    continue
                if getattr(user, 'bot', False):
                    continue
                profile = await get_user_profile_data(user, event.chat_id, client=bot1)
                msg = format_leave_message(profile)
                try:
                    await bot1.send_message(event.chat_id, msg, parse_mode='html')
                except Exception as e:
                    print(f"⚠️ Guard Bot leave card failed for {uid}: {e}")
    except Exception as e:
        print(f"⚠️ Guard Bot join/leave watcher error: {e}")

bot1.on(events.ChatAction)(_guard_bot_join_leave_watcher)

# ---- /revokereward [user_id] [confirm] — owner-only cleanup tool for an ALREADY-granted
# force-sub reward that shouldn't have gone out (e.g. a bot account rewarded before the
# is-this-a-bot fix above existed). Shows a preview first; nothing is touched until "confirm"
# is added. Only pulls harem entries tagged source="force_sub_reward" (added going forward) —
# rewards granted before that tag existed can still have their USD reversed here, but any card
# from them needs manual removal since there's no reliable way to tell it apart from a normal
# catch. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]revokereward(?:@\w+)?\s+(-?\d+)(?:\s+(confirm))?$', 'bot1')))
async def revoke_force_sub_reward(event):
    if event.sender_id != OWNER_ID: return
    target_id = int(event.pattern_match.group(1))
    is_confirm = bool(event.pattern_match.group(2))
    user_doc = await users_catcher_col.find_one({"user_id": target_id})
    if not user_doc or not user_doc.get("force_sub_rewarded"):
        return await event.reply(f"❌ No force-sub reward on record for <code>{target_id}</code> — nothing to revoke.", parse_mode='html')
    harem = user_doc.get("harem", [])
    reward_entries = [item for item in harem if isinstance(item, dict) and item.get("source") == "force_sub_reward"]
    wallet = user_doc.get("wallet_balance", 0)
    new_wallet = max(0, wallet - FORCE_SUB_REWARD_USD)
    if not is_confirm:
        preview = (
            f"⚠️ <b>Revoke force-sub reward for</b> <code>{target_id}</code>?\n\n"
            f"💰 Wallet: <code>{wallet:,}</code> → <code>{new_wallet:,}</code> USD\n"
            f"🎴 Tagged reward card(s) found: <code>{len(reward_entries)}</code>"
        )
        if not reward_entries:
            preview += (
                "\n\n⚠️ <i>No tagged reward card found (this account was rewarded before the "
                "tagging fix) — only the wallet USD will be reversed here; remove any card "
                "manually if needed.</i>"
            )
        preview += f"\n\nRun <code>/revokereward {target_id} confirm</code> to actually apply this."
        return await event.reply(preview, parse_mode='html')
    new_total_caught = max(0, user_doc.get("total_caught", 0) - len(reward_entries))
    new_daily_catches = max(0, user_doc.get("daily_catches", 0) - len(reward_entries))
    update_ops = {
        "$set": {"wallet_balance": new_wallet, "total_caught": new_total_caught, "daily_catches": new_daily_catches},
        "$unset": {"force_sub_rewarded": ""}
    }
    if reward_entries:
        update_ops["$pull"] = {"harem": {"source": "force_sub_reward"}}
    await users_catcher_col.update_one({"user_id": target_id}, update_ops)
    await event.reply(
        f"✅ <b>Reward revoked for</b> <code>{target_id}</code>\n"
        f"💰 Wallet: <code>{wallet:,}</code> → <code>{new_wallet:,}</code> USD\n"
        f"🎴 Removed <code>{len(reward_entries)}</code> tagged reward card(s).",
        parse_mode='html'
    )

# ==========================================
# 🧹 /reclaimforcesub [confirm] — owner-only BULK version of /revokereward above. Finds every
# account that was granted the (now-removed) join reward — force_sub_rewarded=True, with at
# least one harem entry tagged source="force_sub_reward" so the exact card(s) granted are
# known precisely — AND that has NEVER caught anything else: total_caught doesn't exceed how
# many reward cards it has. That combination is the signal for "joined only to collect the
# free USD/card and never actually played" as opposed to a genuine player who happened to
# also get the join reward along the way. Genuine players (any catch beyond the reward
# card(s)) are left completely untouched — not even the reward card is pulled from them.
# Same preview-then-confirm shape, and same audit-logging habit, as every other destructive
# owner command in this file (/compresswealth, /revokereward, /changeusd).
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]reclaimforcesub(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def reclaim_force_sub_rewards_bulk(event):
    if event.sender_id != OWNER_ID: return
    is_confirm = bool(event.pattern_match.group(1))

    candidates = await users_catcher_col.find(
        {"force_sub_rewarded": True, "harem": {"$elemMatch": {"source": "force_sub_reward"}}},
        {"user_id": 1, "fullname": 1, "wallet_balance": 1, "total_caught": 1, "daily_catches": 1, "harem": 1}
    ).to_list(length=None)

    to_reclaim = []
    for doc in candidates:
        harem = doc.get("harem", []) or []
        reward_entries = [x for x in harem if isinstance(x, dict) and x.get("source") == "force_sub_reward"]
        if not reward_entries:
            continue
        if doc.get("total_caught", 0) > len(reward_entries):
            continue  # genuine player — has catches beyond the reward card(s), leave alone
        to_reclaim.append((doc, reward_entries))

    if not to_reclaim:
        return await event.reply(
            "✅ <b>No matching accounts</b> — nobody currently qualifies "
            "(reward on record, but zero catches beyond it).",
            parse_mode='html'
        )

    total_usd = sum(min(doc.get("wallet_balance", 0), FORCE_SUB_REWARD_USD) for doc, _ in to_reclaim)
    total_cards = sum(len(entries) for _, entries in to_reclaim)

    if not is_confirm:
        sample_lines = "\n".join(
            f"• <code>{doc['user_id']}</code> ({escape_html(doc.get('fullname', '?'))}) — "
            f"wallet <code>{doc.get('wallet_balance', 0):,.2f}</code>, reward card(s) <code>{len(entries)}</code>"
            for doc, entries in to_reclaim[:15]
        )
        more_line = f"\n…and {len(to_reclaim) - 15} more" if len(to_reclaim) > 15 else ""
        return await event.reply(
            f"⚠️ <b>BULK FORCE-SUB RECLAIM</b>\n\n"
            f"Criteria: <code>force_sub_rewarded=True</code>, has a tagged reward card, "
            f"<b>zero catches beyond it</b> (never actually played).\n\n"
            f"👥 <b>Accounts matching:</b> <code>{len(to_reclaim)}</code>\n"
            f"💰 <b>Total USD to reverse:</b> <code>{total_usd:,.2f}</code>\n"
            f"🎴 <b>Total reward cards to remove:</b> <code>{total_cards}</code>\n\n"
            f"{sample_lines}{more_line}\n\n"
            f"❗ ဒါက <b>ပြန်ဖျက်လို့မရဘူး</b> — Run <code>/reclaimforcesub confirm</code> to proceed.",
            parse_mode='html'
        )

    reclaimed = 0
    for doc, entries in to_reclaim:
        uid = doc["user_id"]
        wallet = doc.get("wallet_balance", 0)
        new_wallet = max(0, wallet - FORCE_SUB_REWARD_USD)
        new_total_caught = max(0, doc.get("total_caught", 0) - len(entries))
        new_daily_catches = max(0, doc.get("daily_catches", 0) - len(entries))
        await users_catcher_col.update_one(
            {"user_id": uid},
            {
                "$set": {"wallet_balance": new_wallet, "total_caught": new_total_caught, "daily_catches": new_daily_catches},
                "$unset": {"force_sub_rewarded": ""},
                "$pull": {"harem": {"source": "force_sub_reward"}}
            }
        )
        reclaimed += 1

    await force_sub_reclaim_log_col.insert_one({
        "run_at": time.time(), "run_by": OWNER_ID, "accounts_reclaimed": reclaimed,
        "total_usd_reversed": total_usd, "total_cards_removed": total_cards,
        "user_ids": [doc["user_id"] for doc, _ in to_reclaim]
    })

    await event.reply(
        f"✅ <b>BULK RECLAIM COMPLETE</b>\n"
        f"👥 <b>Accounts reclaimed:</b> <code>{reclaimed}</code>\n"
        f"💰 <b>Total USD reversed:</b> <code>{total_usd:,.2f}</code>\n"
        f"🎴 <b>Total reward cards removed:</b> <code>{total_cards}</code>",
        parse_mode='html'
    )

# 🩹 REMOVED (per owner request): bot3 used to auto-run a perceptual-hash identify lookup on
# EVERY photo/video anyone posted in FORCE_SUB_CHAT_ID, unprompted — needless overhead for
# something that's rarely what the poster actually wanted. Identification in that group is
# still available on request: reply to a photo/video with /who (bot1), or DM the photo/video
# straight to the bot (see dm_auto_identify_handler below).

# ==========================================
# 🚨 ONE-TIME MIGRATION — required after the PHASH_SIZE 8→16 change above. Every character's
# stored photo_phash in the DB was computed with the OLD 8x8/64-bit dHash. New identify
# attempts now compute a 16x16/256-bit hash for the incoming media. hamming_distance() XORs the
# two as raw integers — comparing a 64-bit int against a 256-bit int this way does NOT degrade
# gracefully, it just produces a huge, meaningless distance, so every existing character would
# silently stop being identifiable at all until this runs once. Owner-only, run it once right
# after deploying this change (safe to re-run any time — it always recomputes from the original
# stored media, never from the old hash).
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]rehashall(?:@\w+)?$', 'bot1')))
async def rehash_all_characters_handler(event):
    if event.sender_id != OWNER_ID:
        return
    if is_duplicate_event(event):
        return
    all_chars = await characters_base_col.find({}, {"char_id": 1, "name": 1, "storage_msg_id": 1, "_id": 0}).to_list(length=None)
    status = await event.reply(f"🔄 Re-hashing {len(all_chars)} characters with the new 256-bit phash... 0/{len(all_chars)}")
    ops, done, failed = [], 0, []
    for i, char in enumerate(all_chars):
        try:
            msg = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=char["storage_msg_id"])
            new_hash = await compute_phash_for_message(msg) if msg else None
            if new_hash:
                ops.append(UpdateOne({"char_id": char["char_id"]}, {"$set": {"photo_phash": new_hash}}))
            else:
                failed.append(char.get("name", char["char_id"]))
        except Exception as e:
            failed.append(char.get("name", char["char_id"]))
            print(f"rehashall error for {char.get('char_id')}: {e}")
        done += 1
        await asyncio.sleep(0.05)  # gentle pacing — avoids FloodWaitError on get_messages
        if done % 50 == 0 or done == len(all_chars):
            try:
                await status.edit(f"🔄 Re-hashing... {done}/{len(all_chars)}")
            except Exception:
                pass
    for i in range(0, len(ops), 500):
        await characters_base_col.bulk_write(ops[i:i + 500])
    await invalidate_character_caches()
    result_text = f"✅ Re-hashed {len(ops)}/{len(all_chars)} characters."
    if failed:
        shown = ", ".join(failed[:15]) + (f" (+{len(failed) - 15} more)" if len(failed) > 15 else "")
        result_text += f"\n⚠️ Couldn't re-fetch media for {len(failed)}: {shown}"
    await status.edit(result_text)

# ==========================================
# 🔎 DM AUTO-IDENTIFY — in the bot's private chat, just sending a photo or video is enough
# to get it identified — no /who, no reply needed. (The old "forward every DM to owner"
# behavior that used to live here has been removed.)
# ==========================================
@bot1.on(events.NewMessage(incoming=True, func=lambda e: e.is_private and (e.photo or e.video) and not e.sticker))
async def dm_auto_identify_handler(event):
    if event.sender_id in bot_ids:
        return
    if event.sender_id == OWNER_ID:
        return  # owner's DM is also where /addquiz collects the quiz's own illustration photo
    text = (event.raw_text or "").strip()
    if _has_command_prefix(text):
        return  # an explicit "/who" (or ".who") caption is handled by who_reveal_handler's Path B instead
    await _identify_media_and_reply(event, event.message)
# ==========================================
# ADMIN CAPABILITY
# ==========================================
async def is_allowed(user_id):
    if user_id == OWNER_ID: return True
    user = await allow_col.find_one({"user_id": user_id})
    return user is not None

async def check_admin(chat_id, user_id):
    if user_id == OWNER_ID: return True
    now = time.time()
    if chat_id in admin_cache and now < admin_cache[chat_id]["expiry"]:
        return user_id in admin_cache[chat_id]["ids"]
    await update_admin_cache(bot1, chat_id)
    if chat_id in admin_cache:
        return user_id in admin_cache[chat_id]["ids"]
    return False

async def update_admin_cache(client, chat_id):
    try:
        admins = await client(GetParticipantsRequest(
            channel=chat_id, filter=ChannelParticipantsAdmins(),
            offset=0, limit=200, hash=0
        ))
        admin_ids = {p.user_id for p in admins.participants}
        admin_cache[chat_id] = {"ids": admin_ids, "expiry": time.time() + 300}
        return admin_ids
    except Exception as e:
        print(f"Error updating admin cache for {chat_id}: {e}")
        return set()


# ==========================================
# EVENT HANDLERS (start, help, etc.)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]start(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def system_start_router(event):
    is_cd, rem = await is_on_cooldown(event.sender_id, "start", 2)
    if is_cd: return
    sender = await event.get_sender()
    track_user_metrics(event.sender_id, getattr(sender, 'username', None), getattr(sender, 'first_name', 'User'))
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    payload = event.pattern_match.group(1)
    already_exists = await users_catcher_col.find_one({"user_id": user_id})
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    referral_note = ""
    if not already_exists and payload and payload.startswith("ref_"):
        try:
            referrer_id = int(payload[4:])
        except ValueError:
            referrer_id = None
        if referrer_id and referrer_id != user_id:
            referrer_doc = await users_catcher_col.find_one({"user_id": referrer_id})
            if referrer_doc:
                await users_catcher_col.update_one(
                    {"user_id": user_id},
                    {"$set": {"referred_by": referrer_id}}
                )
                await users_catcher_col.update_one(
                    {"user_id": referrer_id},
                    {"$inc": {"referral_count": 1}}
                )
                await check_and_award_achievements(referrer_id, notify_chat_id=referrer_id)
                referral_note = "\n\n🎉 <b>Referral linked!</b> Your friend now shows up on your referral count. 🎁"
    bot_me = await bot1.get_me()
    welcome_msg = (
        f"👑 <b>Morgan Bot</b> ကနေ ကြိုဆိုပါတယ်!\n\n"
        f"ကျွန်တော်က <b>Character Collector Bot</b> တစ်ခုပါ — ဒီ Group ထဲမှာ Character အသစ်တွေ "
        f"အခါအားလျော်စွာ ပေါ်လာမှာဖြစ်ပြီး၊ ဖော်ထုတ်ဖမ်းဆီးစုဆောင်းရတဲ့ <b>Collector Game</b> ကို "
        f"အဓိကထားပါတယ်။ <b>Group အုပ်ချုပ်ရေး</b> လုပ်ဆောင်ချက်တွေကိုပါ တစ်နေရာတည်း ပေါင်းစပ်ပေးထားပါတယ်။\n\n"
        f"အောက်က Button များ နှိပ်ပြီး ဘာတွေ ရနိုင်လဲ ကြည့်လိုက်ပါ။ 🙂"
        f"{referral_note}"
    )
    buttons = [
        [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
        [Button.url("🪐 Add Me To Your Group", f"https://t.me/{bot_me.username}?startgroup=true")],
        [Button.url("👥 Join Our Circle", "https://t.me/Comeback_BoD")]
    ]
    await event.respond(bq(welcome_msg), parse_mode='html', buttons=buttons)

def get_help_text():
    return (
        f"⚙️ <b><u>Command Terminal</u></b>\n\n"
        f" <code>/info</code> [Reply/@username] - User Profile Card ကြည့်ရန်\n"
        f" <code>/weather</code> - မြန်မာ &amp; ထိုင်း ရာသီဥတု တိုက်ရိုက်ကြည့်ရှုရန်\n\n"
        f"📖 <i>Command အားလုံးရဲ့ အပြည့်အစုံစာရင်းအတွက် <code>/introduce</code> ကို ကြည့်ပါ။</i>"
    )



def get_collection_text():
    return (
        f"🎒 <b><u>Collection Desk</u></b>\n\n"
        f"🎒 <code>/harem</code>\nView your vault — paginated inventory of everyone you've caught.\n\n"
        f"⭐ <code>/fav [ID]</code>\nSet a favourite card to pin at the top.\n\n"
        f"📊 <code>/profile</code>, <code>/myinfo</code>\nCheck your stats and collection at a glance.\n\n"
        f"🏆 <code>/top</code> / <code>/gtop</code>\nLocal and global leaderboards.\n\n"
        f"🔎 <code>/check [ID]</code>\nDetailed character info and its top collectors.\n\n"
        f"🖼 <code>/show</code>\nPick a rarity (2x2 button grid) and browse every character in it, full quality, with ⬅️ Prev / ➡️ Next. DM only.\n\n"
        f"🔗 <code>/referral</code>\nGet your invite link — friends who join through it count toward your referral total."
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'(?i)^[/.]help(?:@\w+)?$', 'bot1')))
async def help_command_handler(event):
    await event.reply(bq(get_help_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])


@bot1.on(events.CallbackQuery())
async def system_callback_router(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    if data == "nav_back_home":
        bot_me = await bot1.get_me()
        welcome_msg = (
            f"<b>🎮 Character Collector Bot</b>\n"
            f"Characters spawn in your groups for you to catch and collect — that's my main game."
        )
        buttons = [
            [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
            [Button.url("Add Me To Your Group", f"https://t.me/{bot_me.username}?startgroup=true")],
            [Button.url("Join Our Circle", "https://t.me/Comeback_BoD")]
        ]
        return await event.edit(bq(welcome_msg), parse_mode='html', buttons=buttons)
    elif data == "nav_help_main":
        return await event.edit(bq(get_help_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_collection_main":
        return await event.edit(bq(get_collection_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_hmode":
        await set_rarity_filter_handler(event)
    elif data.startswith("catchprofile_"):
        target_user_id = int(data.split("_", 1)[1])
        if user_id != target_user_id:
            return await event.answer("⚠️ This isn't your profile button!", alert=True)
        mention = await get_html_mention(event, user_id)
        text, buttons = await render_profile_full(event, user_id, mention)
        await event.respond(text, parse_mode='html', buttons=buttons)
        await event.answer()
    elif data.startswith("pf_stats_") or data.startswith("pf_back_") or data.startswith("pf_main_"):
        # 🩹 Legacy buttons from before the profile redesign — there's no separate stats page
        # to show anymore, so all of these just re-render the same combined view now.
        target_user_id = int(data.rsplit("_", 1)[1])
        if user_id != target_user_id:
            return await event.answer("⚠️ This isn't your profile button!", alert=True)
        mention = await get_html_mention(event, user_id)
        text, buttons = await render_profile_full(event, user_id, mention)
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()

# ---- CALCULATOR ----
# 🔒 Safe replacement for the old bare eval(text, {"__builtins__": None}, {}) — stripping
# __builtins__ does NOT make eval() a real sandbox in CPython (it's still possible to reach
# dangerous objects through attribute chains on ordinary Python objects). This walks a parsed
# ast.Expression tree instead and only ever evaluates numeric literals combined with
# +-*/%**() — no names, no function calls, no attribute/subscript access are even
# representable in the allowed node types below, so there's no code-execution surface at all.
_SAFE_CALC_BINOPS = {
    ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
    ast.Div: operator.truediv, ast.Mod: operator.mod, ast.FloorDiv: operator.floordiv,
    ast.Pow: operator.pow,
}
_SAFE_CALC_UNARYOPS = {ast.USub: operator.neg, ast.UAdd: operator.pos}
_SAFE_CALC_MAX_EXPONENT = 1000   # 2**99999999 would compute a multi-million-digit number
_SAFE_CALC_MAX_OPERAND = 10 ** 9  # otherwise and hang/eat RAM despite being a short, "safe-looking" string

def _safe_calc_eval(node):
    if isinstance(node, ast.Expression):
        return _safe_calc_eval(node.body)
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool) or not isinstance(node.value, (int, float)):
            raise ValueError("only plain numbers are allowed")
        return node.value
    if isinstance(node, ast.BinOp):
        op_func = _SAFE_CALC_BINOPS.get(type(node.op))
        if op_func is None:
            raise ValueError("operator not allowed")
        left, right = _safe_calc_eval(node.left), _safe_calc_eval(node.right)
        if isinstance(node.op, ast.Pow) and (abs(right) > _SAFE_CALC_MAX_EXPONENT or abs(left) > _SAFE_CALC_MAX_OPERAND):
            raise ValueError("operands too large")
        return op_func(left, right)
    if isinstance(node, ast.UnaryOp):
        op_func = _SAFE_CALC_UNARYOPS.get(type(node.op))
        if op_func is None:
            raise ValueError("operator not allowed")
        return op_func(_safe_calc_eval(node.operand))
    raise ValueError("expression not allowed")

def safe_calculate(text):
    """Parses+evaluates a plain arithmetic expression safely. Raises on anything invalid
    (syntax error, disallowed node, div-by-zero, oversized operands) — callers should catch
    Exception broadly and just ignore, same as the old eval() call site did."""
    return _safe_calc_eval(ast.parse(text, mode='eval'))

async def _run_auto_calculator(event):
    if event.text.startswith('/'): return
    text = event.text.strip()
    if re.match(r'^[\d\.\s\+\-\*\/\(\)\*\*]+$', text):
        if any(op in text for op in ['+', '-', '*', '/']):
            if len(text) > 50 or (text.count('**') > 1): return
            try:
                result = safe_calculate(text)
                await event.reply(f"🍺<b>Result:</b>\n<code>{text} = {result}</code>", parse_mode='html')
            except Exception:
                pass

TODAY_TOP_LIMIT = 20

async def render_today_leaderboard():
    """Returns the /today text, or None if nobody has caught anything yet today.

    Ranking: users who've already hit today's daily catch cap are listed first, ordered by
    daily_limit_hit_at ascending — i.e. whoever hit the cap earliest ranks #1. That's "who
    reached the limit first". Everyone else who's caught something today but isn't capped yet
    is listed after, ordered by daily_catches descending. Capped at TODAY_TOP_LIMIT total, one
    page — no pagination.

    🩹 FIX: daily_catches/daily_limit_hit_at only reset the next time THAT user runs /collect
    on a new day (see catch_handler), so without a date filter this leaderboard was pulling in
    anyone who'd EVER caught something and hadn't happened to trigger their own rollover yet —
    i.e. stale catches from days or weeks ago, not just today's. last_catch_date >= today's
    midnight (same filter /leaderboard's daily mode already uses) fixes that."""
    today_start = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0)
    proj = {"_id": 0, "user_id": 1, "fullname": 1, "daily_catches": 1, "daily_limit_hit_at": 1, "premium_until": 1}

    capped_users = await users_catcher_col.find(
        {"daily_limit_hit_at": {"$exists": True}, "last_catch_date": {"$gte": today_start}}, proj
    ).sort("daily_limit_hit_at", 1).limit(TODAY_TOP_LIMIT).to_list(length=TODAY_TOP_LIMIT)

    remaining = TODAY_TOP_LIMIT - len(capped_users)
    active_users = []
    if remaining > 0:
        active_users = await users_catcher_col.find(
            {"daily_catches": {"$gt": 0}, "daily_limit_hit_at": {"$exists": False}, "last_catch_date": {"$gte": today_start}}, proj
        ).sort("daily_catches", -1).limit(remaining).to_list(length=remaining)

    all_users = capped_users + active_users
    if not all_users:
        return None

    lines = []
    for idx, u in enumerate(all_users, start=1):
        medal = "🥇" if idx == 1 else "🥈" if idx == 2 else "🥉" if idx == 3 else f"#{idx}"
        name = clean_display_name(u.get("fullname"), fallback=f"User {u['user_id']}")
        mention = f"<a href='tg://user?id={u['user_id']}'>{escape_html(name)}</a>"
        hit_at = u.get("daily_limit_hit_at")
        if hit_at:
            time_str = hit_at.astimezone(TZ).strftime("%H:%M") if isinstance(hit_at, datetime) else "?"
            lines.append(f"{medal}  {mention} — 🏁 hit their daily limit at <code>{time_str}</code>")
        else:
            lines.append(f"{medal}  {mention} — <code>{u['daily_catches']} catches</code>")

    text = f"📅 <b>Today's Catchers</b> <i>(Top {TODAY_TOP_LIMIT})</i>\n"
    text += f"🏁 Ranked by who reached their daily catch limit first (limit: {DAILY_CATCH_LIMIT})\n\n"
    text += "\n".join(lines)
    return text

@bot1.on(events.NewMessage)
async def bot1_auto_calculator_handler(event):
    await _run_auto_calculator(event)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]today(?:@\w+)?$', 'bot1')))
async def today_command(event):
    text = await render_today_leaderboard()
    if text is None:
        return await event.reply("📭 <b>No catches today yet.</b>", parse_mode='html')
    await event.reply(text, parse_mode='html')

# ---- INFO / ID — shared target resolution + a richer profile card for both ----
async def resolve_info_target(event):
    """Figures out who /info or /id should describe: the replied-to user, an @username or
    ID argument, or the sender themself. Returns (target_id, target_user) or (None, None)
    with an error already sent to the chat."""
    if event.is_reply:
        reply_msg = await event.get_reply_message()
        target_id = reply_msg.sender_id
        target_user = await event.client.get_entity(target_id)
        return target_id, target_user
    parts = event.text.split()
    if len(parts) > 1:
        try:
            target_user = await event.client.get_entity(parts[1])
            return target_user.id, target_user
        except Exception:
            await event.reply("⚠️ <b>User not found!</b> Try replying to them instead, or double-check the @username/ID.", parse_mode='html')
            return None, None
    target_id = event.sender_id
    target_user = await event.client.get_entity(target_id)
    return target_id, target_user

async def render_profile_card(event, target_id, target_user):
    """Builds and sends the shared USER PROFILE card used by both /info and /id — with
    account badges (bot/premium/verified/scam/fake/restricted), a clickable name mention,
    and the user's profile photo when one is available."""
    full_name = f"{getattr(target_user, 'first_name', '') or ''} {getattr(target_user, 'last_name', '') or ''}".strip() or "Unknown"
    username = f"@{target_user.username}" if getattr(target_user, 'username', None) else "<i>none</i>"
    mention = f"<a href='tg://user?id={target_id}'><b>{escape_html(full_name)}</b></a>"

    badges = []
    if getattr(target_user, 'bot', False): badges.append("🤖 Bot")
    if getattr(target_user, 'premium', False): badges.append("⭐ Premium")
    if getattr(target_user, 'verified', False): badges.append("✅ Verified")
    if getattr(target_user, 'scam', False): badges.append("🚫 Scam")
    if getattr(target_user, 'fake', False): badges.append("⚠️ Fake")
    if getattr(target_user, 'restricted', False): badges.append("🔒 Restricted")
    badge_line = f"\n🏷️ <b>Badges:</b> {' · '.join(badges)}" if badges else ""

    caption = (
        f"🪪 <b>USER PROFILE</b>\n"
        f"👤 <b>Name:</b> {mention}\n"
        f"🔗 <b>Username:</b> {username}\n"
        f"🆔 <b>User ID:</b> <code>{target_id}</code>\n"
        f"💬 <b>Chat ID:</b> <code>{event.chat_id}</code>"
        f"{badge_line}\n"
        f"<i>💡 Tap any ID above to copy it instantly.</i>"
    )
    # Best-effort profile photo — falls back to plain text if the user has none or it can't be fetched.
    try:
        photos = await bot1.get_profile_photos(target_id, limit=1)
    except Exception:
        photos = None
    if photos:
        try:
            await event.reply(file=photos[0], message=caption, parse_mode='html')
            return
        except Exception:
            pass
    await event.reply(caption, parse_mode='html')

@bot1.on(events.NewMessage(pattern=r'(?i)^[/.]info'))
async def info_handler(event):
    try:
        target_id, target_user = await resolve_info_target(event)
        if target_user:
            await render_profile_card(event, target_id, target_user)
    except Exception as e:
        print(f"Error in /info: {e}")

# ---- WELCOME / GOODBYE ----
@bot1.on(events.ChatAction)
async def welcome_goodbye(event):
    try:
        chat = await event.get_chat()
        bot_me = await bot1.get_me()
        group_name = chat.title or "Unknown Group"
        target_ids = event.user_ids or [event.user_id]
        is_broadcast_channel = bool(getattr(chat, 'broadcast', False) and not getattr(chat, 'megagroup', False))
        
        # ---------- BOT ADDED TO GROUP ----------
        if (event.user_added or event.user_joined) and any(uid == bot_me.id for uid in target_ids if uid):
            async with bot_added_locks[chat.id]:
                now_ts = time.time()
                last_ts = _recent_bot_added_chats.get(chat.id)
                if last_ts and (now_ts - last_ts) <= BOT_ADDED_DEDUP_WINDOW:
                    return
                _recent_bot_added_chats[chat.id] = now_ts
                
                # ✅ Member count ကို get_participants နဲ့ မှန်ကန်အောင် ရယူမယ်
                member_count = "Unknown"
                try:
                    # get_participants က total ကို ပြန်ပေးတယ်
                    participants = await bot1.get_participants(chat.id, limit=0)
                    if hasattr(participants, 'total'):
                        member_count = f"{participants.total:,}"
                    elif isinstance(participants, list):
                        member_count = f"{len(participants):,}"
                except Exception as e:
                    print(f"Member count error (get_participants): {e}")
                    # Fallback: get_full_chat ကို စမ်းကြည့်မယ်
                    try:
                        full_chat = await bot1.get_full_chat(chat.id)
                        if hasattr(full_chat, 'participants_count'):
                            member_count = f"{full_chat.participants_count:,}"
                    except Exception as e2:
                        print(f"Member count error (get_full_chat): {e2}")
                        member_count = "N/A"
                
                # ✅ Invite link ရယူမယ်
                group_link = None
                try:
                    invite = await bot1(ExportChatInviteRequest(chat.id))
                    group_link = invite.link if invite else None
                except Exception:
                    group_link = "Cannot fetch (need admin rights)"
                if not group_link:
                    group_link = "Not available (or bot not admin)"
                
                # Owner ကို ပို့မယ့် Message
                owner_msg = (
                    f"✅ <b>Bot Added to New {'Channel' if is_broadcast_channel else 'Group'}!</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━\n"
                    f"📛 <b>Name:</b> <code>{escape_html(group_name)}</code>\n"
                    f"🆔 <b>ID:</b> <code>{chat.id}</code>\n"
                    f"👥 <b>Members:</b> <code>{member_count}</code>\n"
                    f"🔗 <b>Invite Link:</b> <code>{escape_html(str(group_link))}</code>\n"
                    f"⏰ <b>Time:</b> <code>{datetime.now(TZ).strftime('%Y-%m-%d %H:%M:%S')}</code>"
                )
                await bot1.send_message(OWNER_ID, owner_msg, parse_mode='html')
                try:
                    await bot1.send_message(SPECIFIC_GROUP, owner_msg, parse_mode='html')
                except Exception:
                    pass
                
                # Channel ဆိုရင် ဒီမှာပဲ ရပ်မယ်
                if is_broadcast_channel:
                    return
                
                # Group ဆိုရင် intro message ပို့မယ် (ဖယ်ရှားချင်ရင် ဒီအောက်က ၅ ကြောင်းကို comment လုပ်ပါ)
                intro_msg = (
                    f"<b>👾 Character Collector Bot</b> ကနေ ဒီ Group ထဲကို ရောက်ရှိလာပါပြီ!\n\n"
                    f"ကျွန်တော်ရဲ့ အဓိက ဂိမ်းက <b>Character များ ဖမ်းဆီးစုဆောင်းခြင်း (Collector Game)</b> "
                    f"ဖြစ်ပါတယ် — ဒီ Group ထဲမှာ Character အသစ်တွေ အခါအားလျော်စွာ ပေါ်လာမှာဖြစ်ပြီး၊ "
                    f"<code>/w</code>, <code>/waifu</code> or <code>/who</code> နဲ့ ဖော်ထုတ်ပြီး "
                    f"<code>/fuck [name]</code> နဲ့ ဖမ်းယူနိုင်ပါတယ်။ ဖမ်းရမိတဲ့ Character တွေကို "
                    f"<code>/harem</code> မှာ စုဆောင်းထားနိုင်ပါတယ်။\n\n"
                    f"📌 <b>စတင်ကြည့်ရှုရန်:</b>\n"
                    f"   • <code>/introduce</code> - ကျွန်တော် လုပ်ဆောင်ပေးနိုင်တာတွေ အသေးစိတ် ကြည့်ရန်\n"
                    f"   • <code>/help</code> - Command အားလုံး ကြည့်ရန်\n\n"
                    f"🎮 သင့် Group ကိုယ်ပိုင်မှာလည်း ဒီဂိမ်းကို ရစေချင်ရင် <b>@{bot_me.username}</b> ကို Add လုပ်ထားနိုင်ပါတယ်။\n\n"
                    f"✨ ကောင်းသောအချိန်ဖြစ်ပါစေ။"
                )
                await bot1.send_message(chat.id, intro_msg, parse_mode='html')
                await groups_col.update_one(
                    {"chat_id": chat.id},
                    {"$set": {"title": chat.title, "joined_at": datetime.now(TZ)}},
                    upsert=True
                )
                return
        
        # ---------- WELCOME & GOODBYE ကို လုံးဝ ဖယ်ရှားမယ် ----------
        # အောက်က ကျန်တဲ့ welcome/goodbye code တွေအကုန်ကို ဖယ်ရှားလိုက်မယ်
        # ဘယ်သူမှ join/leave လုပ်ရင် ဘာမှ မပို့တော့ဘူး
        return
        
    except Exception as e:
        await report_system_error("Welcome Goodbye Event", e)

# ---- MAU STATS ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mau(?:@\w+)?$', 'bot1')))
async def system_analytics_matrix(event):
    if event.sender_id != OWNER_ID: return
    loading = await event.reply("<code>🌌 Pulling every tracked name...</code>", parse_mode='html')
    try:
        total_tracked_users = await users_col.count_documents({})
        total_active_groups = await groups_col.count_documents({})
        day_ago = datetime.now(TZ) - timedelta(days=1)
        active_24h_users = await users_col.count_documents({"last_active": {"$gte": day_ago}})
        metrics_layout = (
            f"<b>MAU Stats</b>\n"
            f"👥 <b>Total Managed Users:</b> <code>{total_tracked_users} 👤</code>\n"
            f"🔥 <b>Active Users (24H):</b> <code>{active_24h_users} 🔥</code>\n"
            f"📍 <b>Active Groups:</b> <code>{total_active_groups} 🪐</code>\n"
            f"⚙️ <b>Engine Status:</b> <code>Everything is under control.</code>"
        )
        await loading.edit(bq(metrics_layout), parse_mode='html')
    except Exception as e:
        await loading.edit(bq(f"❌ Analytics Error: {e}"), parse_mode='html')


# ==========================================
# SPAM FILTERS (Updated with spam mute)
# ==========================================
SPAM_MSG_WINDOW_SECONDS = 60
SPAM_MSG_THRESHOLD = 13       # text, sticker, or other media messages within the window
SPAM_CATCH_MUTE_SECONDS = 480  # 8 minutes — how long /fuck (and /who, /w, /waifu) stay
# blocked, GLOBALLY across every group the user is in (not just the group where they spammed).

@bot1.on(events.NewMessage)
async def spam_detection_and_mute(event):
    if event.is_private:
        return
    if event.sender_id in bot_ids or event.sender_id == OWNER_ID:
        return
    # Counts toward the spam threshold: text OR sticker OR any other media (photo, video, gif,
    # voice, document, etc.) — a burst of stickers to force a spawn is spamming just as much
    # as a burst of text, so both need to count toward the same window.
    if not event.text and not event.media:
        return
    user_id = event.sender_id
    chat_id = event.chat_id
    # 🩹 CHANGED (per owner request): the MUTE is now GLOBAL — user_mute_until is keyed by
    # user_id alone, so spamming in Group A now blocks /fuck and /who in EVERY group, not
    # just Group A. The spam-DETECTION window (what counts toward tripping the mute) stays
    # scoped per-group below — that's about WHERE the burst happened, a separate concern from
    # where the resulting penalty applies.
    spam_key = (user_id, chat_id)
    now = time.time()

    # Already muted from catching — GLOBALLY — block the relevant commands and stop; don't
    # let this message also start counting toward a fresh spam window.
    if user_id in user_mute_until and now < user_mute_until[user_id]:
        if _extract_command_word(event.text) in ['/fuck', '/obtain', '/who', '/w', '/waifu']:
            try:
                await event.delete()
            except:
                pass
        return

    # Track message history for this (user, group) pair — text, sticker, and media all count
    if spam_key not in user_spam_data:
        user_spam_data[spam_key] = []
    # Clean old entries (>60s)
    user_spam_data[spam_key] = [t for t in user_spam_data[spam_key] if now - t < SPAM_MSG_WINDOW_SECONDS]
    user_spam_data[spam_key].append(now)

    # Too many messages in this group's window -> block catching GLOBALLY for
    # SPAM_CATCH_MUTE_SECONDS (PREMIUM_SPAM_MUTE_SECONDS for Premium users)
    if len(user_spam_data[spam_key]) >= SPAM_MSG_THRESHOLD:
        mute_seconds = SPAM_CATCH_MUTE_SECONDS
        user_mute_until[user_id] = now + mute_seconds
        user_spam_data[spam_key] = []  # start clean once the mute expires, instead of carrying
        # over timestamps from the burst that just tripped it
        mute_minutes = mute_seconds // 60
        try:
            sender = await event.get_sender()
            mention = f"<a href='tg://user?id={user_id}'>{escape_html(sender.first_name)}</a>"
            await event.respond(
                bq(f"<b>Notice:</b> {mention}, that's enough. "
                   f"You've been blocked from /fuck and /who <b>in every group</b> for {mute_minutes} minutes. "
                   f"Sit still for a while."),
                parse_mode='html'
            )
        except Exception:
            pass
        # Delete the message that tripped the threshold
        try:
            await event.delete()
        except:
            pass
        return
            
# ---- ID ----
@bot1.on(events.NewMessage(pattern=r'(?i)^[/.]id'))
async def id_handler(event):
    try:
        target_id, target_user = await resolve_info_target(event)
        if target_user:
            await render_profile_card(event, target_id, target_user)
    except Exception as e:
        print(f"Error in /id: {e}")

# ---- Post a character (full details + image) to CHARACTER_CHANNEL_ID ----
def _build_character_channel_caption(char_doc, is_new=True):
    # 🩹 CHANGED (per owner feedback — "obviously AI-written"): the old layout was a flat list
    # of "🆔 Emoji Label: value" rows, one emoji per field — the classic AI-listicle look. This
    # version gives the name top billing, drops the field-label emoji spam, and uses dividers
    # for structure instead — reads more like an actual announcement card than a database dump.
    limit_val = char_doc.get("spawn_limit")
    limit_text = "♾️ Unlimited" if not limit_val else str(limit_val)
    artist = char_doc.get("artist")
    name = escape_html(str(char_doc.get('name', '?')))
    category = escape_html(str(char_doc.get('category', '?')))
    rarity = char_doc.get('rarity', '?')
    event_name = str(char_doc.get('event') or '').strip()
    char_id = escape_html(str(char_doc.get('char_id', '?')))

    header = f('NEW CARD JUST DROPPED') if is_new else f('CARD UPDATED')
    header_emoji = "🆕" if is_new else "🔄"

    caption = (
        f"{header_emoji} <b>{header}</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n\n"
        f"<b>{name}</b>\n"
        f"<i>{category}</i>\n\n"
        f"{rarity}\n"
        f"🔁 {limit_text}\n"
    )
    if event_name and event_name.lower() != "general":
        caption += f"🎪 {escape_html(event_name)}\n"
    if artist:
        caption += f"🎨 {escape_html(str(artist))}\n"
    caption += (
        f"\n━━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 <code>{char_id}</code>"
    )
    return caption

_character_channel_entity_warmed = False

async def _ensure_character_channel_entity():
    """🩹 FIX (per owner report — 'Could not find the input entity for PeerChannel' spamming
    on every auto-import): Telethon needs an access_hash to turn a bare channel ID into a
    usable Peer, which it only has after bot1 has SEEN that channel somehow — a cached
    session from earlier interaction, or a fresh get_dialogs() call listing every chat bot1
    is actually in (which CHARACTER_CHANNEL_ID must be, since bot1 posts there). A session
    reset/redeploy can wipe that cache, and unlike a human-driven /addchar, the auto-import
    listener can hit this cold-cache state on its very first post-restart send. Only ever
    attempted once per process — it's a comparatively heavy paginated call — not once per
    character."""
    global _character_channel_entity_warmed
    if _character_channel_entity_warmed:
        return
    _character_channel_entity_warmed = True  # set BEFORE awaiting — never retry-storm this
    try:
        await bot1.get_dialogs()
    except Exception:
        pass

async def post_character_to_channel(char_doc, is_new=True):
    """Send one character's full details + image to CHARACTER_CHANNEL_ID.
    Raises on failure so callers (addchar) can catch and report it."""
    if not CHARACTER_CHANNEL_ID:
        raise RuntimeError("CHARACTER_CHANNEL_ID env var not set")
    storage_id = char_doc.get("storage_msg_id")
    if not storage_id:
        raise RuntimeError("character has no stored media (storage_msg_id missing)")
    storage_msg = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_id)
    if not storage_msg or not storage_msg.media:
        raise RuntimeError("stored media not found (deleted from storage group?)")
    caption = _build_character_channel_caption(char_doc, is_new=is_new)
    try:
        return await bot1.send_file(CHARACTER_CHANNEL_ID, file=storage_msg.media, caption=caption, parse_mode='html')
    except ValueError as e:
        if "Could not find the input entity" not in str(e):
            raise
        await _ensure_character_channel_entity()
        return await bot1.send_file(CHARACTER_CHANNEL_ID, file=storage_msg.media, caption=caption, parse_mode='html')

# ---- /purgechannelposts — OWNER ONLY: deletes EVERY previously-posted character-announcement
# message from CHARACTER_CHANNEL_ID (using each character's stored channel_msg_id), then clears
# that field on every character so the DB no longer thinks anything's been posted. Run this
# BEFORE switching CHARACTER_CHANNEL_ID to a new channel — it deletes from whatever channel is
# CURRENTLY configured. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]purgechannelposts(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def purge_channel_posts_handler(event):
    if event.sender_id != OWNER_ID: return
    confirm = bool(event.pattern_match.group(1))
    posted = await characters_base_col.find({"channel_msg_id": {"$exists": True, "$ne": None}}, {"char_id": 1, "channel_msg_id": 1}).to_list(length=None)
    if not posted:
        return await event.reply("📭 <b>ဖျက်ရန် Channel Post မရှိပါ</b> — Character ဘယ်ခုမှ Channel Message ID မှတ်ထားခြင်း မရှိပါ။", parse_mode='html')
    if not confirm:
        return await event.reply(
            f"⚠️ <b>Channel Post <code>{len(posted):,}</code> ခု ဖျက်တော့မလား?</b>\n"
            f"🎯 <b>Target Channel:</b> <code>{CHARACTER_CHANNEL_ID}</code> (လက်ရှိ Configure ထားတာ)\n\n"
            f"<i>ဒါက Channel ထဲက Post များကိုသာ ဖျက်တာပါ — Character Database ကို မထိခိုက်ပါဘူး။ "
            f"Channel ပြောင်းချင်ရင် ဒါကို ပထမဆုံး Run ပြီးမှ CHARACTER_CHANNEL_ID ကို ပြောင်းပါ။</i>\n\n"
            f"အတည်ပြုရန် <code>/purgechannelposts confirm</code> ကို ရိုက်ပါ။",
            parse_mode='html'
        )
    status_msg = await event.reply(f"🗑️ <b>Channel Post {len(posted):,} ခု ဖျက်နေပါသည်...</b>", parse_mode='html')
    msg_ids = [p["channel_msg_id"] for p in posted if p.get("channel_msg_id")]
    deleted, failed = 0, 0
    # delete_messages accepts up to 100 IDs per call — batch it, with pacing to stay flood-safe
    for i in range(0, len(msg_ids), 100):
        batch = msg_ids[i:i + 100]
        try:
            await bot1.delete_messages(CHARACTER_CHANNEL_ID, batch)
            deleted += len(batch)
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 2)
            try:
                await bot1.delete_messages(CHARACTER_CHANNEL_ID, batch)
                deleted += len(batch)
            except Exception:
                failed += len(batch)
        except Exception as ce:
            await report_system_error("purgechannelposts batch delete", ce)
            failed += len(batch)
        await asyncio.sleep(1)
    await characters_base_col.update_many({}, {"$unset": {"channel_msg_id": "", "channel_posted": ""}})
    await status_msg.edit(
        f"✅ <b>Channel Post ရှင်းလင်းပြီးပါပြီ!</b>\n"
        f"🗑️ <b>ဖျက်ပြီး:</b> <code>{deleted:,}</code>  │  ❌ <b>မဖျက်နိုင်:</b> <code>{failed:,}</code>\n\n"
        f"<i>Channel အသစ်ကို သုံးမယ်ဆိုရင် CHARACTER_CHANNEL_ID (Render Env Var) ကို ယခုပြောင်းနိုင်ပါပြီ၊ "
        f"ပြီးရင် /repostallchars ကို Run ပါ။</i>",
        parse_mode='html'
    )

# ---- /repostallchars — OWNER ONLY: posts EVERY existing character in the database to
# CHARACTER_CHANNEL_ID (whatever it's CURRENTLY configured to — run this AFTER switching to the
# new channel). Flood-safe paced, updates channel_msg_id on each character as it goes. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]repostallchars(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def repost_all_characters_handler(event):
    if event.sender_id != OWNER_ID: return
    if not CHARACTER_CHANNEL_ID:
        return await event.reply("❌ <b>CHARACTER_CHANNEL_ID</b> configure မထားပါ။", parse_mode='html')
    confirm = bool(event.pattern_match.group(1))
    total = await characters_base_col.count_documents({})
    if not total:
        return await event.reply("📭 <b>Database ထဲမှာ Character လုံးဝ မရှိသေးပါ။</b>", parse_mode='html')
    est_minutes = round(total * 3 / 60, 1)
    if not confirm:
        return await event.reply(
            f"⚠️ <b>Character <code>{total:,}</code> ခုလုံးကို Channel <code>{CHARACTER_CHANNEL_ID}</code> ဆီ Repost လုပ်တော့မလား?</b>\n"
            f"⏱ <b>ခန့်မှန်းအချိန်:</b> <code>~{est_minutes}</code> မိနစ် (Flood-safe pacing ကြောင့်)\n\n"
            f"အတည်ပြုရန် <code>/repostallchars confirm</code> ကို ရိုက်ပါ။",
            parse_mode='html'
        )
    status_msg = await event.reply(f"📢 <b>Character {total:,} ခုကို Channel ဆီ Post လုပ်နေပါသည်...</b>\n<code>0/{total}</code>", parse_mode='html')
    posted, failed = 0, 0
    async for char_doc in characters_base_col.find():
        try:
            channel_msg = await post_character_to_channel(char_doc, is_new=False)
            await characters_base_col.update_one(
                {"char_id": char_doc["char_id"]},
                {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None, "channel_posted": True}}
            )
            posted += 1
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 2)
            try:
                channel_msg = await post_character_to_channel(char_doc, is_new=False)
                await characters_base_col.update_one(
                    {"char_id": char_doc["char_id"]},
                    {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None, "channel_posted": True}}
                )
                posted += 1
            except Exception:
                failed += 1
        except Exception as ce:
            await report_system_error(f"repostallchars ({char_doc.get('char_id')})", ce)
            failed += 1
        if (posted + failed) % 20 == 0:
            try:
                await status_msg.edit(f"📢 <b>Character {total:,} ခုကို Channel ဆီ Post လုပ်နေပါသည်...</b>\n<code>{posted + failed}/{total}</code>", parse_mode='html')
            except Exception:
                pass
        await asyncio.sleep(3)  # flood-safe pacing
    await status_msg.edit(
        f"✅ <b>Repost ပြီးပါပြီ!</b>\n"
        f"📢 <b>Post ပြီး:</b> <code>{posted:,}</code>  │  ❌ <b>မအောင်မြင်:</b> <code>{failed:,}</code>",
        parse_mode='html'
    )

# ---- Telegram/Telethon occasionally redeliver the same update more than once — we've hit
# this for ChatAction events (bot-added-to-group) and for the spawn-trigger counter; it can
# just as easily double-fire a plain command handler like /addchar (which is what caused
# characters to get forwarded/posted 2-3x). Any handler with a real side effect (DB write,
# channel post, forwarding media) should call is_duplicate_event(event) first and bail if True.
_recent_event_ids = bot_state._recent_event_ids  # (chat_id, event.id) -> timestamp
EVENT_DEDUP_WINDOW = 15  # seconds

def is_duplicate_event(event):
    key = (event.chat_id, event.id)
    now = time.time()
    last_ts = _recent_event_ids.get(key)
    _recent_event_ids[key] = now
    if len(_recent_event_ids) > 5000:  # opportunistic cleanup, keeps this from growing forever
        cutoff = now - EVENT_DEDUP_WINDOW
        for k, ts in list(_recent_event_ids.items()):
            if ts < cutoff:
                del _recent_event_ids[k]
    return last_ts is not None and (now - last_ts) <= EVENT_DEDUP_WINDOW

# ---- ADD CHARACTER (owner-only bot2) ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addchar(?:@\w+)?(?:\s+(.+))?', 'bot1')))
async def add_character(event):
    if event.sender_id != OWNER_ID: return
    if is_duplicate_event(event): return
    input_text = event.pattern_match.group(1)
    if not input_text or '|' not in input_text:
        await event.reply(
            f"⚠️ <b>{f('Invalid format!')}</b>\n"
            f"📌 <b>{f('Usage')}:</b>\n"
            f"<code>/addchar Name | Category | Rarity_Number | Event | CatchLimit</code>\n"
            f"<i>(Reply to a media file. Event and CatchLimit are optional.)</i>\n\n"
            f"🔢 <b>{f('Rarity Tiers (1-4)')}:</b>\n"
            + "\n".join(
                f"<code>{num}</code> = {RARITY_NUM_MAP[num]['name']} (<code>{RARITY_NUM_MAP[num]['value']}</code> USD)"
                for num in sorted(RARITY_NUM_MAP.keys())
            ) + "\n\n"
            f"🎪 <b>Event:</b> free text, e.g. <code>Summer Festival</code> (leave blank/'-' for none)\n"
            f"🔁 <b>CatchLimit:</b> how many times total this character may be caught (0 or blank = infinite)",
            parse_mode='html'
        )
        return
    parts = [p.strip() for p in input_text.split('|')]
    if len(parts) < 3:
        return await event.reply(f"❌ <b>{f('Need 3 parts separated by |')}</b>", parse_mode='html')
    char_name, category_name, rarity_num = parts[0], parts[1], parts[2]
    if rarity_num not in RARITY_NUM_MAP:
        return await event.reply(f"❌ <b>{f('Rarity must be 1-4')}</b>", parse_mode='html')
    if not event.is_reply:
        return await event.reply(f"❌ <b>{f('Reply to a media file')}</b>", parse_mode='html')
    event_name = parts[3].strip() if len(parts) > 3 and parts[3].strip() and parts[3].strip() != "-" else "General"
    spawn_limit = 0
    if len(parts) > 4 and parts[4].strip().lstrip('-').isdigit():
        spawn_limit = max(0, int(parts[4].strip()))
    reply_msg = await event.get_reply_message()
    if not reply_msg or not (reply_msg.photo or reply_msg.video or reply_msg.document):
        return await event.reply(f"❌ <b>{f('Valid media not found')}</b>", parse_mode='html')
    # All 4 rarity tiers accept either photo or video — no tier is restricted to a
    # specific media type.
    # 🩹 FIX: large videos (the owner's own diagnosis was spot-on) could make /addchar go
    # completely silent. Two compounding causes:
    #  1. Telegram bots have a hard ~2000MB send/forward ceiling — a file over that was
    #     always going to fail, but nothing checked for it up front, so the failure only
    #     surfaced deep inside the network call with a cryptic Telegram error string.
    #  2. Forwarding an older/larger message's media can hit FileReferenceExpiredError
    #     (Telegram invalidates file references after a while), and — separately — a slow
    #     upload of a big file could hang past whatever the underlying connection tolerates.
    #     Both of those are real exceptions and SHOULD have been caught by the `except
    #     Exception` below... except large transfers are exactly the case most likely to be
    #     interrupted by asyncio.CancelledError, which is a BaseException in Python 3.8+ and
    #     slips straight through an `except Exception` clause — so the command would die
    #     with zero message ever reaching the owner. Fixed by: checking size up front,
    #     capping how long we wait, retrying once on an expired reference, and explicitly
    #     catching cancellation/timeout too so every failure path reports back.
    ADDCHAR_MAX_BYTES = 2000 * 1024 * 1024  # 2000MB — Telegram's own bot upload ceiling
    ADDCHAR_UPLOAD_TIMEOUT = 240  # seconds — generous for a big video, but never infinite
    media_size = getattr(getattr(reply_msg, "file", None), "size", None)
    if media_size and media_size > ADDCHAR_MAX_BYTES:
        return await event.reply(
            f"❌ <b>{f('File too large')}</b> "
            f"(<code>{media_size / 1024 / 1024:.1f}MB</code>) — Telegram bots can't send files "
            f"over <code>2000MB</code>. Compress it or trim the clip and try again.",
            parse_mode='html'
        )
    status_msg = None
    try:
        # 🩹 FIX: acknowledge receipt IMMEDIATELY, before the network calls (forwarding media
        # to storage, posting to the channel) that can take a moment or occasionally queue
        # behind a flood wait. Without this, /addchar could look completely silent for the
        # whole time those calls were in flight — now there's always instant confirmation
        # that the command was received and is being processed.
        status_msg = await event.reply("⏳ <b>Adding character...</b>", parse_mode='html')
        try:
            # 🩹 Uses bot2 here, not bot1 — reply_msg.media was fetched through bot2's own
            # connection (bot2 received this event), so its file_reference is only valid
            # for bot2's session. Passing it to a different client instance would fail.
            forwarded_msg = await asyncio.wait_for(
                send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media),
                timeout=ADDCHAR_UPLOAD_TIMEOUT
            )
        except errors.FileReferenceExpiredError:
            # Reference went stale (common with older or larger media) — refetch the
            # original message once to get a fresh reference, then retry a single time.
            fresh_reply_msg = await bot1.get_messages(event.chat_id, ids=reply_msg.id)
            if not fresh_reply_msg or not fresh_reply_msg.media:
                raise RuntimeError("media reference expired and the original message is no longer available")
            reply_msg = fresh_reply_msg
            forwarded_msg = await asyncio.wait_for(
                send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media),
                timeout=ADDCHAR_UPLOAD_TIMEOUT
            )
        except asyncio.TimeoutError:
            raise RuntimeError(
                f"upload timed out after {ADDCHAR_UPLOAD_TIMEOUT}s — the file may be too large "
                f"or Telegram is slow right now, try a smaller file or retry"
            )
        storage_id = forwarded_msg.id
        r_info = RARITY_NUM_MAP[rarity_num]
        char_id = await _generate_new_char_id()
        # 🔎 Fingerprint the media so a re-uploaded/re-saved copy of it can later be
        # recognized by identify_from_repost_handler even without a live spawn/reply.
        photo_phash = await compute_phash_for_message(reply_msg)
        character_data = {
            "char_id": char_id,
            "name": char_name,
            "category": category_name,
            "rarity": r_info["name"],
            "rarity_tier": classify_rarity(r_info["name"]),
            "storage_msg_id": storage_id,
            "currency_value": r_info["value"],
            "spawn_count": 0,
            "event": event_name,
            "spawn_limit": spawn_limit,
            "photo_phash": photo_phash,
            "created_at": time.time()  # 🔒 starts the NEW_CARD_PROTECTION_SECONDS window — see execute_star_shop_purchase()
        }
        await characters_base_col.insert_one(character_data)
        await invalidate_character_caches()
        limit_text = "♾️ Infinite" if spawn_limit == 0 else str(spawn_limit)

        channel_note = ""
        if CHARACTER_CHANNEL_ID:
            try:
                channel_msg = await post_character_to_channel(character_data, is_new=True)
                await characters_base_col.update_one(
                    {"char_id": char_id},
                    {"$set": {"channel_posted": True, "channel_msg_id": channel_msg.id if channel_msg else None}}
                )
                channel_note = "\n📢 <b>Channel:</b> Posted ✅"
            except Exception as ce:
                await report_system_error(f"AddChar channel post ({char_id})", ce)
                channel_note = f"\n⚠️ <b>Channel:</b> Post failed — <code>{escape_html(str(ce))}</code>"
        else:
            channel_note = "\n⚠️ <b>Channel:</b> <code>CHARACTER_CHANNEL_ID</code> not set — skipped."

        # 🩹 NEW (per owner question): Telegram itself compresses/downscales any image sent as
        # a "Photo" (not the bot's doing — it happens the instant it's uploaded, before the bot
        # ever sees it) — that compressed version is then what gets stored and re-sent forever
        # after, which is why spawns can look noticeably softer than the original 4K source
        # until you tap to view full-size. Sending as a "File" instead (already supported —
        # reply_msg.document was accepted above) skips Telegram's compression entirely and
        # keeps full original quality permanently. Surface which path was used right here so
        # it's obvious immediately, not discovered later from a blurry spawn.
        quality_note = (
            "\n🗜️ <b>Image sent as compressed Photo</b> — Telegram downscaled it on upload. "
            "For full original quality, reply with the image sent as a <b>File</b> instead."
            if reply_msg.photo else
            "\n✅ <b>Full quality preserved</b> (sent as File/Video)."
        )
        await status_msg.edit(
            f"🔥 <b>{f('DATABASE INJECTED')}</b>\n"
            f"🆔 <b>{f('Character ID')}:</b> <code>{char_id}</code>\n"
            f"👤 <b>{f('Name')}:</b> <code>{char_name}</code>\n"
            f"🏷️ <b>{f('Rarity')}:</b> {r_info['name']}\n"
            f"💎 <b>{f('Worth')}:</b> <code>{r_info['value']} USD</code>\n"
            f"🎡 <b>Event:</b> <code>{escape_html(event_name)}</code>\n"
            f"🔁 <b>Catch Limit:</b> <code>{limit_text}</code>"
            f"{channel_note}"
            f"{quality_note}",
            parse_mode='html'
        )
    except asyncio.CancelledError:
        # CancelledError is a BaseException (not Exception) in Python 3.8+, so it would
        # otherwise skip straight past the `except Exception` below and leave the owner
        # with zero feedback — exactly the "silent" failure reported. Report, then re-raise
        # so real cancellation (e.g. shutdown) still propagates correctly.
        try:
            err_text = "❌ <b>Database Inject Error</b>: <code>upload was cancelled/interrupted before finishing — please retry</code>"
            if status_msg:
                await status_msg.edit(err_text, parse_mode='html')
            else:
                await event.reply(err_text, parse_mode='html')
        except Exception:
            pass
        raise
    except Exception as e:
        err_text = f"❌ <b>Database Inject Error</b>: <code>{escape_html(str(e))}</code>"
        try:
            if status_msg:
                await status_msg.edit(err_text, parse_mode='html')
            else:
                await event.reply(err_text, parse_mode='html')
        except Exception:
            await event.reply(err_text, parse_mode='html')

# ---- CHANGE MEDIA: owner-only, swaps a character's stored media (e.g. upgrading a blurry
# upload to a clean one) WITHOUT touching char_id, name, rarity, or anything else. Every
# existing harem entry only ever stores char_id — never storage_msg_id directly — and media
# is always looked up fresh from characters_base_col at display time (/harem, /check, /show,
# spawns, /who), so this swap is instantly visible everywhere and nobody who already caught
# this character loses it or needs to do anything; they just see the better picture/video.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]change(?:@\w+)?\s+(\S+)$', 'bot1')))
async def change_character_media(event):
    if event.sender_id != OWNER_ID: return
    char_id = normalize_char_id_input(event.pattern_match.group(1))
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        return await event.reply(f"❌ No character found with ID <code>{escape_html(display_char_id(char_id))}</code>.", parse_mode='html')
    if not event.is_reply:
        return await event.reply("❌ Reply to the new photo/video with <code>/change [CharID]</code>.", parse_mode='html')
    reply_msg = await event.get_reply_message()
    if not reply_msg or not (reply_msg.photo or reply_msg.video or reply_msg.document):
        return await event.reply("❌ Valid media not found in the replied message.", parse_mode='html')
    # All 4 rarity tiers accept either photo or video — a media swap can freely go
    # between photo and video without restriction.
    CHANGE_MAX_BYTES = 2000 * 1024 * 1024  # Telegram's own bot upload ceiling
    CHANGE_UPLOAD_TIMEOUT = 240
    media_size = getattr(getattr(reply_msg, "file", None), "size", None)
    if media_size and media_size > CHANGE_MAX_BYTES:
        return await event.reply(
            f"❌ <b>File too large</b> (<code>{media_size / 1024 / 1024:.1f}MB</code>) — Telegram bots can't send files over <code>2000MB</code>.",
            parse_mode='html'
        )
    old_storage_id = char_doc.get("storage_msg_id")
    status_msg = await event.reply("⏳ <b>Swapping media...</b>", parse_mode='html')
    try:
        try:
            forwarded_msg = await asyncio.wait_for(
                send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media),
                timeout=CHANGE_UPLOAD_TIMEOUT
            )
        except errors.FileReferenceExpiredError:
            fresh_reply_msg = await bot1.get_messages(event.chat_id, ids=reply_msg.id)
            if not fresh_reply_msg or not fresh_reply_msg.media:
                raise RuntimeError("media reference expired and the original message is no longer available")
            reply_msg = fresh_reply_msg
            # 🩹 FIX: this used to forward through `bot2` even though `reply_msg` was just
            # re-fetched via `bot1.get_messages()` above — a file_reference is only valid for
            # the session that fetched it (same rule /addchar's comment documents), so handing
            # bot1-fetched media to bot2 would just fail again with another reference error,
            # silently defeating the whole point of this retry path. Use bot1 here, matching
            # both the fetch right above and the first attempt a few lines up.
            forwarded_msg = await asyncio.wait_for(
                send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media),
                timeout=CHANGE_UPLOAD_TIMEOUT
            )
        except asyncio.TimeoutError:
            raise RuntimeError(
                f"upload timed out after {CHANGE_UPLOAD_TIMEOUT}s — the file may be too large or Telegram is slow right now, try again"
            )
        new_storage_id = forwarded_msg.id
        new_phash = await compute_phash_for_message(reply_msg)
        # Update the DB FIRST, delete the old media LAST — a mid-way failure must never leave
        # characters_base_col pointing at media that's already gone.
        await characters_base_col.update_one(
            {"char_id": char_id},
            {"$set": {"storage_msg_id": new_storage_id, "photo_phash": new_phash}}
        )
        await invalidate_character_caches()
        old_deleted_note = ""
        if old_storage_id:
            try:
                await bot1.delete_messages(SPECIFIC_CONTROL_GROUP, [old_storage_id])
                old_deleted_note = "\n🗑 Old media deleted."
            except Exception:
                old_deleted_note = "\n⚠️ New media is live, but the old file couldn't be deleted (already gone?)."
        await status_msg.edit(
            f"✅ <b>Media updated for</b> <code>{display_char_id(char_id)}</code> — <b>{escape_html(char_doc['name'])}</b>"
            f"{old_deleted_note}\n"
            f"👥 Everyone who already caught this character keeps it — only the picture/video changed.",
            parse_mode='html'
        )
    except asyncio.CancelledError:
        try:
            await status_msg.edit("❌ <b>Media swap cancelled/interrupted before finishing</b> — please retry. The old media is untouched.", parse_mode='html')
        except Exception:
            pass
        raise
    except Exception as e:
        try:
            await status_msg.edit(f"❌ <b>Media Swap Error:</b> <code>{escape_html(str(e))}</code>\nThe old media is untouched.", parse_mode='html')
        except Exception:
            pass

# ---- DELETE CHARACTER ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](delchar|removechar)(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def delete_character_by_owner(event):
    if event.sender_id != OWNER_ID: return
    char_id = event.pattern_match.group(2)
    if not char_id:
        await event.reply(f"❌ Please provide the Character ID to delete.\nExample: `/delchar BOD789`")
        return
    query = {"$or": [{"id": char_id}, {"char_id": char_id}]}
    res1 = await db["characters"].delete_many(query)
    res2 = await db["characters_base_data"].delete_many(query)
    if res1.deleted_count > 0 or res2.deleted_count > 0:
        await invalidate_character_caches()
        await event.reply(f"🔥 {f('DATABASE REMOVED')}\n🆔 {f('Character ID')}: {char_id}\nStatus: Deleted.")
    else:
        await event.reply(f"❌ No character found with ID `{char_id}`.")

# ---- EDIT CHARACTER ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]editchar(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def edit_character_prompt(event):
    if event.sender_id != OWNER_ID: return
    target_id = event.pattern_match.group(1)
    if target_id:
        char_doc = await characters_base_col.find_one({"char_id": target_id.upper()})
        if not char_doc:
            return await event.reply(f"❌ No character found with ID <code>{escape_html(target_id)}</code>.", parse_mode='html')
        cur_event = char_doc.get("event", "General")
        cur_limit = char_doc.get("spawn_limit", 0)
        limit_text = "♾️ Infinite" if not cur_limit else str(cur_limit)
        text = (
            f"✏️ <b>Editing:</b> {escape_html(char_doc['name'])} (<code>{char_doc['char_id']}</code>)\n"
            f"🏷️ Rarity: {char_doc.get('rarity', 'Unknown')}\n"
            f"🎪 Current Event: <code>{escape_html(cur_event)}</code>\n"
            f"🔁 Current Catch Limit: <code>{limit_text}</code> (caught <code>{char_doc.get('spawn_count', 0)}</code> times so far)\n\n"
            f"↩️ <b>Reply to this message</b> with:\n"
            f"<code>Event | CatchLimit</code>\n"
            f"e.g. <code>Summer Festival | 5</code>\n"
            f"<i>Use - to leave a field unchanged. CatchLimit 0 = infinite.</i>"
        )
        sent = await event.reply(text, parse_mode='html')
        pending_editchar_prompt_ids[sent.id] = char_doc["char_id"]
        return
    all_chars = await characters_base_col.find().sort("char_id", 1).to_list(length=None)
    if not all_chars:
        return await event.reply("📭 No characters in the database yet. Use /addchar first.")
    header = "📋 <b>CHARACTER DATABASE</b>\n\n"
    lines = []
    for c in all_chars:
        cur_event = c.get("event", "General")
        cur_limit = c.get("spawn_limit", 0)
        limit_text = "♾️" if not cur_limit else str(cur_limit)
        lines.append(
            f"🆔 <code>{c['char_id']}</code> — <b>{escape_html(c['name'])}</b> (<i>{escape_html(c.get('category',''))}</i>)\n"
            f"     {c.get('rarity','')} | 🎪 {escape_html(cur_event)} | 🔁 {c.get('spawn_count',0)}/{limit_text}"
        )
    footer = (
        "\n\n↩️ <b>Reply to THIS message</b> with:\n"
        "<code>CharID | Event | CatchLimit</code>\n"
        "e.g. <code>BOD1234 | Summer Festival | 5</code>\n"
        "<i>Use - to leave a field unchanged. CatchLimit 0 = infinite.</i>\n"
        "💡 Tip: <code>/editchar CharID</code> jumps straight to one character."
    )
    chunks, current = [], header
    for line in lines:
        if len(current) + len(line) + 1 > 3500:
            chunks.append(current)
            current = ""
        current += line + "\n"
    chunks.append(current + footer)
    last_sent = None
    for chunk in chunks:
        last_sent = await event.reply(chunk, parse_mode='html')
    pending_editchar_prompt_ids[last_sent.id] = None

@bot1.on(events.NewMessage(incoming=True))
async def edit_character_apply(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_reply: return
    if event.reply_to_msg_id not in pending_editchar_prompt_ids: return
    fixed_char_id = pending_editchar_prompt_ids[event.reply_to_msg_id]
    raw = (event.text or "").strip()
    if not raw: return
    parts = [p.strip() for p in raw.split('|')]
    if fixed_char_id:
        char_id = fixed_char_id
        if len(parts) < 2:
            return await event.reply("⚠️ Format: <code>Event | CatchLimit</code>", parse_mode='html')
        new_event, new_limit_raw = parts[0], parts[1]
    else:
        if len(parts) < 3:
            return await event.reply("⚠️ Format: <code>CharID | Event | CatchLimit</code>", parse_mode='html')
        char_id, new_event, new_limit_raw = parts[0].strip().upper(), parts[1], parts[2]
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        return await event.reply(f"❌ No character found with ID <code>{escape_html(char_id)}</code>.", parse_mode='html')
    update_fields = {}
    if new_event and new_event != "-":
        update_fields["event"] = new_event
    if new_limit_raw and new_limit_raw != "-":
        if not new_limit_raw.lstrip('-').isdigit():
            return await event.reply("⚠️ CatchLimit must be a whole number (0 = infinite).")
        update_fields["spawn_limit"] = max(0, int(new_limit_raw))
    if not update_fields:
        return await event.reply("⚠️ Nothing to update — both fields were '-'.")
    await characters_base_col.update_one({"char_id": char_id}, {"$set": update_fields})
    await invalidate_character_caches()
    updated_doc = await characters_base_col.find_one({"char_id": char_id})
    spawned = updated_doc.get("spawn_count", 0)
    limit = updated_doc.get("spawn_limit", 0)
    remaining_text = "♾️ Infinite" if not limit else f"{max(0, limit - spawned)} left ({spawned}/{limit})"
    # 🩹 NEW (per owner request): edits used to update the DB silently with no channel
    # announcement at all. Now every /editchar posts an updated card to CHARACTER_CHANNEL_ID
    # too, same as /addchar does for brand-new cards.
    channel_note = ""
    if CHARACTER_CHANNEL_ID:
        try:
            channel_msg = await post_character_to_channel(updated_doc, is_new=False)
            await characters_base_col.update_one(
                {"char_id": char_id},
                {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None}}
            )
            channel_note = "\n📢 Channel: Posted ✅"
        except Exception as ce:
            await report_system_error(f"EditChar channel post ({char_id})", ce)
            channel_note = f"\n⚠️ Channel: Post failed — <code>{escape_html(str(ce))}</code>"
    await event.reply(
        f"✅ <b>{escape_html(updated_doc['name'])}</b> (<code>{char_id}</code>) updated!\n"
        f"🎡 Event: <code>{escape_html(updated_doc.get('event','General'))}</code>\n"
        f"🔁 Catches remaining: <b>{remaining_text}</b>"
        f"{channel_note}",
        parse_mode='html'
    )

# ---- EXPORT CHARACTERS: owner-only, sends the full character database (name, series,
# rarity, event) as a downloadable CSV document instead of a long chat message. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]exportchars(?:@\w+)?$', 'bot1')))
async def export_characters_handler(event):
    if event.sender_id != OWNER_ID: return
    status_msg = await event.reply("📄 <b>Building character export...</b>", parse_mode='html')
    try:
        all_chars = await characters_base_col.find().sort("char_id", 1).to_list(length=None)
        if not all_chars:
            return await status_msg.edit("📭 No characters in the database yet. Use /addchar first.", parse_mode='html')

        csv_buffer = io.StringIO()
        writer = csv.writer(csv_buffer)
        writer.writerow(["Character ID", "Name", "Series", "Rarity", "Event"])
        for c in all_chars:
            writer.writerow([
                display_char_id(c.get("char_id", "")),
                c.get("name", ""),
                c.get("category", "") or "Unknown Series",
                c.get("rarity", "") or "Unknown",
                c.get("event") or "General",
            ])
        # utf-8-sig adds a BOM so Excel/Sheets render Burmese and other non-ASCII text
        # correctly instead of showing garbled characters when the CSV is opened.
        file_bytes = io.BytesIO(csv_buffer.getvalue().encode("utf-8-sig"))
        file_bytes.name = f"characters_export_{datetime.now(TZ).strftime('%Y-%m-%d')}.csv"

        await send_safe_file(
            bot1, event.chat_id, file_bytes,
            caption=f"📄 <b>Character Database Export</b>\n🧩 <b>Total:</b> <code>{len(all_chars)}</code> characters",
            reply_to=status_msg.id,
            parse_mode='html'
        )
        await status_msg.delete()
    except Exception as e:
        await status_msg.edit(f"❌ <b>Export Error:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')
        await report_system_error("export_characters_handler", e)

# ==========================================
# 🗂️ /mergecategory & /mergecategories — owner-only category cleanup.
# category is stored ONLY on characters_base_col (characters_col is an unused legacy
# collection, and harem/user docs only ever keep a char_id — category is looked up fresh
# from characters_base_col every time), so a single update_many + cache invalidation is a
# complete fix everywhere the category name is shown (/harem, /dex, exports, etc.).
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mergecategory(?:@\w+)?\s+(.+)$', 'bot1')))
async def merge_category_handler(event):
    if event.sender_id != OWNER_ID: return
    raw = event.pattern_match.group(1)
    if '|' not in raw:
        return await event.reply(bq("⚠️ Format: <code>/mergecategory Old Name | New Name</code>"), parse_mode='html')
    old_name, new_name = (p.strip() for p in raw.split('|', 1))
    if not old_name or not new_name:
        return await event.reply(bq("⚠️ Need both an old and a new category name."), parse_mode='html')
    if old_name == new_name:
        return await event.reply(bq("⚠️ Old and new names are identical — nothing to do."), parse_mode='html')
    result = await characters_base_col.update_many({"category": old_name}, {"$set": {"category": new_name}})
    await invalidate_character_caches()
    await event.reply(
        bq(f"✅ Merged <b>{escape_html(old_name)}</b> → <b>{escape_html(new_name)}</b>\n<code>{result.modified_count}</code> character(s) moved."),
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mergecategories(?:@\w+)?\s+(.+)$', 'bot1')))
async def merge_categories_bulk_handler(event):
    if event.sender_id != OWNER_ID: return
    raw = event.pattern_match.group(1)
    if '|' not in raw:
        return await event.reply(bq("⚠️ Format: <code>/mergecategories Old A, Old B, Old C | New Name</code>"), parse_mode='html')
    old_names_raw, new_name = raw.split('|', 1)
    old_names = [n.strip() for n in old_names_raw.split(',') if n.strip()]
    new_name = new_name.strip()
    if not old_names or not new_name:
        return await event.reply(bq("⚠️ Need at least one old category name and a new name."), parse_mode='html')
    result = await characters_base_col.update_many({"category": {"$in": old_names}}, {"$set": {"category": new_name}})
    await invalidate_character_caches()
    await event.reply(
        bq(f"✅ Merged <code>{len(old_names)}</code> categories → <b>{escape_html(new_name)}</b>\n<code>{result.modified_count}</code> character(s) moved."),
        parse_mode='html'
    )

# ==========================================
# 🖼️ /show — full-quality rarity gallery browser, open to any user but DM-only.
# Walks EVERY character of a given rarity tier (/show no1 .. /show no9) one at a time with
# Prev/Next buttons. Media is sent by re-using the original stored file reference
# (storage_msg.media) instead of downloading+re-uploading, so quality never degrades — the
# exact same technique /check, /harem and spawns already rely on.
# ==========================================
async def _get_show_list(tier_num):
    tier = RARITY_TIERS[int(tier_num) - 1]
    chars = await characters_base_col.find({"rarity_tier": tier}).to_list(length=None)
    chars.sort(key=lambda c: (c.get("name") or "").lower())
    return chars

def _show_rarity_grid_buttons():
    """2x2 grid of rarity buttons (one per tier, with each tier's emoji + name) — shown for a
    bare /show, matching the 4-tier layout used everywhere else in the bot."""
    rows, row = [], []
    for num in sorted(RARITY_NUM_MAP.keys(), key=int):
        tier = RARITY_TIERS[int(num) - 1]
        emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
        row.append(Button.inline(f"{emoji} {RARITY_DISPLAY_NAME.get(tier, tier)}", data=f"shownav_{num}_0"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return rows

def _show_nav_buttons(tier_num, idx, total, char_doc=None):
    prev_idx = (idx - 1) % total
    next_idx = (idx + 1) % total
    rows = [[
        Button.inline("⬅️ Prev", data=f"shownav_{tier_num}_{prev_idx}"),
        Button.inline("➡️ Next", data=f"shownav_{tier_num}_{next_idx}")
    ]]
    rows.append([Button.inline("🔢 Rarity List", data="showgrid_back")])
    return rows

def _build_show_caption(char_doc, tier_num, idx, total):
    rarity_display = char_doc.get("rarity") or RARITY_NUM_MAP.get(tier_num, {}).get("name", "Unknown")
    limit = char_doc.get("spawn_limit", 0)
    spawned = char_doc.get("spawn_count", 0)
    caught_text = "♾️ <b>Infinite</b>" if not limit else f"<code>{spawned}/{limit}</code>"
    return (
        f"🖼️ <b>Rarity Gallery</b> — <code>{idx + 1}/{total}</code>\n"
        f""
        f"✨ <b>Name:</b> <code>{escape_html(char_doc.get('name',''))}</code>\n"
        f"🆔 <b>ID:</b> <code>{display_char_id(char_doc.get('char_id',''))}</code>\n"
        f"{rarity_display}\n"
        f"🫧 <b>Category:</b> <code>{escape_html(char_doc.get('category','') or 'Unknown')}</code>\n"
        f"{artist_line(char_doc)}"
        f"🔁 <b>Caught:</b> {caught_text}"
        f""
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]show(?:@\w+)?\s+(?:no)?([1-4])$', 'bot1')))
async def show_rarity_gallery_handler(event):
    if not event.is_private:
        return await event.reply("📩 <b>DM me</b> and use <code>/show</code> there — it only works in private chat.", parse_mode='html')
    tier_num = event.pattern_match.group(1)
    chars = await _get_show_list(tier_num)
    if not chars:
        r_info = RARITY_NUM_MAP.get(tier_num)
        label = r_info["name"] if r_info else "this rarity"
        return await event.reply(f"📭 <b>No characters found for {label} yet.</b>", parse_mode='html')
    idx = 0
    char_doc = chars[idx]
    caption = _build_show_caption(char_doc, tier_num, idx, len(chars))
    buttons = _show_nav_buttons(tier_num, idx, len(chars), char_doc)

    async def _send_show(media):
        return await event.reply(caption, file=media, buttons=buttons, parse_mode='html')

    sent = await send_with_char_media(char_doc["char_id"], char_doc["storage_msg_id"], _send_show)
    if sent is None:
        await event.reply(
            f"❌ <b>Media missing for</b> <code>{display_char_id(char_doc.get('char_id',''))}</code> "
            f"— its storage message may have been deleted.",
            parse_mode='html'
        )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]show(?:@\w+)?$', 'bot1')))
async def show_bare_usage_handler(event):
    if not event.is_private:
        return await event.reply("📩 <b>DM me</b> and use <code>/show</code> there — it only works in private chat.", parse_mode='html')
    await event.reply(
        f"🖼️ <b>ဝယ်ချင်တဲ့ ကဒ် Rarity ကိုရွေးပါ</b>\n"
        f"<i>ကြိုက်တဲ့ကဒ်တွေ့ရင် ⭐ Star နဲ့ တန်းဝယ်နိုင်ပါတယ်။</i>",
        parse_mode='html',
        buttons=_show_rarity_grid_buttons()
    )

@bot1.on(events.CallbackQuery(pattern=r'^showgrid_back$'))
async def show_rarity_grid_back_callback(event):
    text = (
        f"🖼️ <b>ဝယ်ချင်တဲ့ ကဒ် Rarity ကိုရွေးပါ</b>\n"
        f"<i>ကြိုက်တဲ့ကဒ်တွေ့ရင် ⭐ Star နဲ့ တန်းဝယ်နိုင်ပါတယ်။</i>"
    )
    buttons = _show_rarity_grid_buttons()
    try:
        await event.edit(text, parse_mode='html', buttons=buttons, file=None)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()
    except Exception:
        try:
            await event.delete()
        except Exception:
            pass
        await bot1.send_message(event.chat_id, text, parse_mode='html', buttons=buttons)
        await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^shownav_([1-4])_(\d+)$'))
async def show_rarity_gallery_nav(event):
    tier_num = event.pattern_match.group(1)
    idx_raw = event.pattern_match.group(2)
    if isinstance(tier_num, bytes): tier_num = tier_num.decode('utf-8')
    if isinstance(idx_raw, bytes): idx_raw = idx_raw.decode('utf-8')
    idx = int(idx_raw)
    chars = await _get_show_list(tier_num)
    if not chars:
        return await event.answer("📭 No characters left in this rarity.", alert=True)
    idx = idx % len(chars)
    char_doc = chars[idx]
    caption = _build_show_caption(char_doc, tier_num, idx, len(chars))
    buttons = _show_nav_buttons(tier_num, idx, len(chars), char_doc)

    async def _edit_show(media):
        return await event.edit(caption, file=media, buttons=buttons, parse_mode='html')

    try:
        result = await send_with_char_media(char_doc["char_id"], char_doc["storage_msg_id"], _edit_show)
        if result is None:
            return await event.answer("⚠️ Media missing for this one — skipping.", alert=True)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()
    except Exception:
        # Fallback for the rare case Telegram rejects an in-place media swap (e.g. a photo
        # entry followed by a video entry) — delete and resend fresh instead of getting stuck.
        try:
            await event.delete()
        except Exception:
            pass

        async def _resend_show(media):
            return await bot1.send_message(event.chat_id, caption, file=media, buttons=buttons, parse_mode='html')

        await send_with_char_media(char_doc["char_id"], char_doc["storage_msg_id"], _resend_show)
        await event.answer()

# ---- ADD ARTIST ----
async def _resolve_character_from_reply(reply_msg, chat_id):
    """Figures out which character a replied-to message refers to. Tries an exact, free,
    instant storage-message match first (only possible when the reply happens inside
    SPECIFIC_CONTROL_GROUP, where every character's canonical media lives at its own
    storage_msg_id) — then falls back to the same perceptual-hash lookup /who uses, so
    replying to ANY repost of that media (a channel post, a spawn, a DM identify result,
    a forward — anywhere) also works."""
    if not reply_msg:
        return None
    if chat_id == SPECIFIC_CONTROL_GROUP:
        char_doc = await characters_base_col.find_one({"storage_msg_id": reply_msg.id})
        if char_doc:
            return char_doc
    if reply_msg.photo or reply_msg.video or reply_msg.document:
        return await find_character_by_media(reply_msg)
    return None

async def _bulk_add_artist(event, char_ids, artist_name):
    """Sets (or clears, if artist_name == '-') the SAME artist credit on every CharID in
    char_ids in one shot — the bulk counterpart to add_artist_handler's single-card mode,
    triggered by replying to a plain message that's just a list of IDs (one per line)."""
    clearing = artist_name == "-"
    updated, not_found = [], []
    updated_docs = []
    for char_id in char_ids:
        char_doc = await characters_base_col.find_one({"char_id": char_id})
        if not char_doc:
            not_found.append(display_char_id(char_id))
            continue
        if clearing:
            await characters_base_col.update_one({"char_id": char_id}, {"$unset": {"artist": ""}})
        else:
            await characters_base_col.update_one({"char_id": char_id}, {"$set": {"artist": artist_name}})
        updated.append(f"{display_char_id(char_id)} — {escape_html(char_doc['name'])}")
        updated_docs.append(char_id)
    if updated:
        await invalidate_character_caches()
    # 🩹 NEW (per owner request): bulk credit-setting used to be silent too — announce each
    # updated card to the channel, not just single-card /addartist. Paced to stay flood-safe.
    # Clears aren't announced (removing info isn't really "news").
    channel_posted, channel_failed = 0, 0
    if not clearing and CHARACTER_CHANNEL_ID:
        for char_id in updated_docs:
            fresh_doc = await characters_base_col.find_one({"char_id": char_id})
            try:
                channel_msg = await post_character_to_channel(fresh_doc, is_new=False)
                await characters_base_col.update_one(
                    {"char_id": char_id},
                    {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None}}
                )
                channel_posted += 1
            except Exception as ce:
                await report_system_error(f"Bulk AddArtist channel post ({char_id})", ce)
                channel_failed += 1
            await asyncio.sleep(3)  # flood-safe pacing, same rate as /stardrop's broadcast loop
    action = "cleared" if clearing else f"set to <code>{escape_html(artist_name)}</code>"
    summary = [f"🎨 <b>Bulk Artist {'Clear' if clearing else 'Set'} Complete!</b>"]
    summary.append(f"✅ <b>Updated</b> <code>{len(updated)}</code>/<code>{len(char_ids)}</code> character(s) — artist {action}")
    if not clearing and CHARACTER_CHANNEL_ID:
        summary.append(f"📢 <b>Channel posts:</b> <code>{channel_posted}</code> sent, <code>{channel_failed}</code> failed")
    if updated:
        shown = "\n".join(f"• <code>{u}</code>" for u in updated[:40])
        if len(updated) > 40:
            shown += f"\n… (+{len(updated) - 40} more)"
        summary.append(f"{shown}")
    if not_found:
        shown = ", ".join(f"<code>{n}</code>" for n in not_found[:20])
        if len(not_found) > 20:
            shown += " …"
        summary.append(f"❌ <b>Not found:</b> <code>{len(not_found)}</code>")
        summary.append(f"{shown}")
    await event.reply("\n".join(summary), parse_mode='html')

_ADDARTIST_RARITY_RE = re.compile(r'^no\.?([1-4])\s+([\s\S]+)$', re.IGNORECASE)

async def _bulk_add_artist_by_rarity(event, rarity_num, artist_name):
    tier = RARITY_TIERS[int(rarity_num) - 1]
    r_info = RARITY_NUM_MAP[rarity_num]
    artist_name = artist_name.strip()
    if artist_name == "-":
        result = await characters_base_col.update_many({"rarity_tier": tier}, {"$unset": {"artist": ""}})
        await invalidate_character_caches()
        return await event.reply(
            f"🎨 <b>Artist credit cleared for every {r_info['name']} character.</b>\n"
            f"🗄️ <b>Characters updated:</b> <code>{result.modified_count}</code>",
            parse_mode='html'
        )
    affected_ids = [c["char_id"] async for c in characters_base_col.find({"rarity_tier": tier}, {"char_id": 1})]
    result = await characters_base_col.update_many({"rarity_tier": tier}, {"$set": {"artist": artist_name}})
    await invalidate_character_caches()
    status_msg = await event.reply(
        f"🎨 <b>Artist set for every {r_info['name']} character!</b>\n"
        f"🎨 <b>Artist:</b> <code>{escape_html(artist_name)}</code>\n"
        f"🗄️ <b>Characters updated:</b> <code>{result.modified_count}</code>\n"
        f"📢 <i>Posting each one to the channel now...</i>",
        parse_mode='html'
    )
    # 🩹 NEW (per owner request): announce every card in this rarity to the channel, paced to
    # stay flood-safe — same rate as /stardrop's broadcast loop.
    channel_posted, channel_failed = 0, 0
    if CHARACTER_CHANNEL_ID:
        for char_id in affected_ids:
            fresh_doc = await characters_base_col.find_one({"char_id": char_id})
            if not fresh_doc:
                continue
            try:
                channel_msg = await post_character_to_channel(fresh_doc, is_new=False)
                await characters_base_col.update_one(
                    {"char_id": char_id},
                    {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None}}
                )
                channel_posted += 1
            except Exception as ce:
                await report_system_error(f"Bulk-by-rarity AddArtist channel post ({char_id})", ce)
                channel_failed += 1
            await asyncio.sleep(3)
    await status_msg.edit(
        f"🎨 <b>Artist set for every {r_info['name']} character!</b>\n"
        f"🎨 <b>Artist:</b> <code>{escape_html(artist_name)}</code>\n"
        f"🗄️ <b>Characters updated:</b> <code>{result.modified_count}</code>\n"
        f"📢 <b>Channel posts:</b> <code>{channel_posted}</code> sent, <code>{channel_failed}</code> failed",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addartist(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def add_artist_handler(event):
    if event.sender_id != OWNER_ID: return
    if is_duplicate_event(event): return
    arg_text = (event.pattern_match.group(1) or "").strip()
    # ✅ BULK-BY-RARITY MODE: "/addartist no.<N> [Artist Name]" — sets that artist on EVERY
    # character currently in rarity tier N at once, no CharID list needed. Checked before the
    # normal CharID/reply parsing below so "no.1 Morgan" is never mistaken for a (nonexistent)
    # CharID called "no.1".
    rarity_bulk_match = _ADDARTIST_RARITY_RE.match(arg_text) if arg_text else None
    if rarity_bulk_match:
        return await _bulk_add_artist_by_rarity(event, rarity_bulk_match.group(1), rarity_bulk_match.group(2))
    char_doc, artist_name = None, None
    # Try classic "/addartist <CharID> <Artist Name>" parsing first — even on a reply, in case
    # the owner replied out of habit but still typed the ID explicitly; an explicit ID always wins.
    if arg_text:
        parts = arg_text.split(None, 1)
        if len(parts) == 2:
            candidate = await characters_base_col.find_one({"char_id": normalize_char_id_input(parts[0])})
            if candidate:
                char_doc, artist_name = candidate, parts[1]
    # Reply mode: no valid CharID found above — the whole argument is just the artist name,
    # and the character comes from whatever message was replied to.
    if char_doc is None and event.is_reply:
        reply_msg = await event.get_reply_message()
        resolved = await _resolve_character_from_reply(reply_msg, event.chat_id)
        if resolved:
            char_doc = resolved
            artist_name = arg_text
        elif arg_text and reply_msg and reply_msg.text:
            # ✅ BULK MODE: replying to a plain message that's just a list of CharIDs, one per
            # line — e.g.
            #   1234
            #   4567
            #   6421
            # then "/addartist <Artist Name>" sets that SAME artist on every ID found in that
            # list in one shot, instead of one /addartist per card.
            id_lines = [ln.strip() for ln in reply_msg.text.splitlines() if ln.strip()]
            candidate_ids = []
            for ln in id_lines:
                token = ln.split()[0] if ln.split() else ln
                norm = normalize_char_id_input(token)
                if norm and norm not in candidate_ids:
                    candidate_ids.append(norm)
            if candidate_ids:
                return await _bulk_add_artist(event, candidate_ids, arg_text.strip())
    if not artist_name or not artist_name.strip():
        return await event.reply(
            "⚠️ <b>Usage:</b>\n"
            "<code>/addartist [CharID] [Artist Name]</code>\n"
            "<i>or reply to that character's card/image/video with</i> <code>/addartist [Artist Name]</code>\n"
            "<i>CharID works with or without the BOD prefix.</i>\n\n"
            "<b>Examples:</b>\n"
            "<code>/addartist 1234 Morgan</code>\n"
            "<i>(replying to the character's media)</i> <code>/addartist Morgan</code>\n\n"
            "<b>Bulk by CharID list:</b> <i>reply to a message containing a list of CharIDs (one per line) with</i> "
            "<code>/addartist [Artist Name]</code> <i>to set it on all of them at once.</i>\n\n"
            "<b>Bulk by rarity:</b> <code>/addartist no.&lt;N&gt; [Artist Name]</code> "
            "<i>sets it on EVERY character in that rarity tier at once — e.g.</i> <code>/addartist no.1 Morgan</code>\n\n"
            "<i>Use</i> <code>-</code> <i>as the artist name to clear an existing credit (works with all three modes above).</i>",
            parse_mode='html'
        )
    if not char_doc:
        return await event.reply(
            "❌ <b>Notice:</b> Couldn't figure out which character that is — "
            "double check the CharID, or reply directly to that character's card/image/video.",
            parse_mode='html'
        )
    char_id = char_doc["char_id"]
    artist_name = artist_name.strip()
    if artist_name == "-":
        await characters_base_col.update_one({"char_id": char_id}, {"$unset": {"artist": ""}})
        await invalidate_character_caches()
        return await event.reply(
            f"🎨 <b>Artist credit cleared.</b>\n"
            f"🆔 <b>Character:</b> <code>{display_char_id(char_id)}</code> — <b>{escape_html(char_doc['name'])}</b>",
            parse_mode='html'
        )
    await characters_base_col.update_one({"char_id": char_id}, {"$set": {"artist": artist_name}})
    await invalidate_character_caches()
    # 🩹 NEW (per owner request): announce this to the channel too.
    channel_note = ""
    updated_doc = await characters_base_col.find_one({"char_id": char_id})
    if CHARACTER_CHANNEL_ID:
        try:
            channel_msg = await post_character_to_channel(updated_doc, is_new=False)
            await characters_base_col.update_one(
                {"char_id": char_id},
                {"$set": {"channel_msg_id": channel_msg.id if channel_msg else None}}
            )
            channel_note = "\n📢 Channel: Posted ✅"
        except Exception as ce:
            await report_system_error(f"AddArtist channel post ({char_id})", ce)
            channel_note = f"\n⚠️ Channel: Post failed — <code>{escape_html(str(ce))}</code>"
    await event.reply(
        f"<b>Noted down.</b>\n"
        f"🆔 <b>Character:</b> <code>{display_char_id(char_id)}</code> — <b>{escape_html(char_doc['name'])}</b>\n"
        f"🎨 <b>Artist:</b> <code>{escape_html(artist_name)}</code>\n\n"
        f"<i>This credit will now show up anywhere this character card appears.</i>"
        f"{channel_note}",
        parse_mode='html'
    )

# ==========================================
# 🎨 /linkartist — owner-only. /addartist only stores an artist's NAME on a character (free
# text, no Telegram account attached), which is all it ever needed to do for display purposes.
# But the Guard Bot's "pay the artist ⭐ Star when their card gets collected" feature needs an
# actual account to pay — this command is that missing link: it maps an artist NAME to a real
# Telegram user_id, once, and every card already/later credited to that name benefits from it.
# ==========================================
GUARD_ARTIST_REWARD_MIN = 2  # ⭐
GUARD_ARTIST_REWARD_MAX = 7  # ⭐

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]linkartist(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def link_artist_handler(event):
    if event.sender_id != OWNER_ID: return
    arg_text = (event.pattern_match.group(1) or "").strip()
    target_user_id, artist_name = None, None
    if event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg and reply_msg.sender_id:
            target_user_id = reply_msg.sender_id
            artist_name = arg_text
    if target_user_id is None and arg_text:
        parts = arg_text.split()
        if parts and parts[-1].lstrip('-').isdigit():
            target_user_id = int(parts[-1])
            artist_name = " ".join(parts[:-1])
    if not artist_name or not artist_name.strip() or not target_user_id:
        return await event.reply(
            "⚠️ <b>Usage:</b>\n"
            "<i>Reply to that artist's message with</i> <code>/linkartist [Artist Name]</code>\n"
            "<i>or, without a reply:</i> <code>/linkartist [Artist Name] [user_id]</code>\n\n"
            "<b>Example:</b> <code>/linkartist Morgan 123456789</code>\n\n"
            "🎨 This just links the NAME already used in <code>/addartist</code> to a real Telegram "
            "account, so the Guard Bot has somewhere to send their ⭐ Star reward when a card "
            "credited to that name gets collected. It doesn't change any card's artist credit.",
            parse_mode='html'
        )
    artist_name = artist_name.strip()
    display_name = (await get_plain_name(event, target_user_id)) if event.is_reply else artist_name
    await artists_col.update_one(
        {"artist_name": artist_name.lower()},
        {"$set": {"artist_name": artist_name.lower(), "display_name": display_name,
                   "user_id": target_user_id, "linked_at": time.time(), "linked_by": OWNER_ID}},
        upsert=True
    )
    mention = f"<a href='tg://user?id={target_user_id}'>{escape_html(display_name)}</a>"
    await event.reply(
        f"🎨 <b>Artist linked!</b>\n"
        f"<b>Name:</b> <code>{escape_html(artist_name)}</code> ↔ {mention}\n\n"
        f"Every character already credited to <code>{escape_html(artist_name)}</code> (and any added "
        f"later) will now pay {GUARD_ARTIST_REWARD_MIN}~{GUARD_ARTIST_REWARD_MAX}⭐ to this account "
        f"whenever it's collected.",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]unlinkartist(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def unlink_artist_handler(event):
    if event.sender_id != OWNER_ID: return
    artist_name = (event.pattern_match.group(1) or "").strip()
    if not artist_name:
        return await event.reply("⚠️ <b>Usage:</b> <code>/unlinkartist [Artist Name]</code>", parse_mode='html')
    result = await artists_col.delete_one({"artist_name": artist_name.lower()})
    if result.deleted_count:
        await event.reply(f"🎨 <b>Unlinked</b> <code>{escape_html(artist_name)}</code>. Collect rewards for this name stop until relinked.", parse_mode='html')
    else:
        await event.reply(f"❌ <b>No link found for</b> <code>{escape_html(artist_name)}</code>.", parse_mode='html')


# ---- SETCHAR ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]setchar(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def bulk_set_char_handler(event):
    if event.sender_id != OWNER_ID: return
    raw_block = event.pattern_match.group(1)
    if not raw_block and event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg and reply_msg.text:
            raw_block = reply_msg.text
    if not raw_block or not raw_block.strip():
        return await event.reply(
            "⚠️ <b>Usage</b>\n"
            "Send (or reply to) a block of lines — one character per line:\n"
            "<code>CharID | Event | CatchLimit</code>\n\n"
            "<b>Example</b> (paste as many lines as you like, e.g. 15 or 30 at once):\n"
            "<code>BOD1234 | Lightning⚡ | 75\nBOD5678 | Fire Festival | 30\nBOD9012 | - | 0</code>\n\n"
            "<i>Use - to leave a field unchanged. CatchLimit 0 = infinite.</i>",
            parse_mode='html'
        )
    lines = [ln.strip() for ln in raw_block.strip().splitlines() if ln.strip()]
    updated, skipped, failed = [], [], []
    for ln in lines:
        parts = [p.strip() for p in ln.split('|')]
        if len(parts) < 3:
            failed.append(f"<code>{escape_html(ln[:40])}</code> — needs 3 parts (CharID | Event | CatchLimit)")
            continue
        char_id, ev_raw, limit_raw = parts[0].upper(), parts[1], parts[2]
        char_doc = await characters_base_col.find_one({"char_id": char_id})
        if not char_doc:
            failed.append(f"<code>{char_id}</code> — not found")
            continue
        update_fields = {}
        if ev_raw and ev_raw != "-":
            update_fields["event"] = ev_raw
        if limit_raw and limit_raw != "-":
            if not limit_raw.lstrip('-').isdigit():
                failed.append(f"<code>{char_id}</code> — CatchLimit must be a whole number")
                continue
            update_fields["spawn_limit"] = max(0, int(limit_raw))
        if not update_fields:
            skipped.append(char_id)
            continue
        await characters_base_col.update_one({"char_id": char_id}, {"$set": update_fields})
        updated.append(char_id)
    if updated:
        await invalidate_character_caches()
    summary = [f"✅ <b>Bulk Set Complete!</b>\n🔁 <b>Updated:</b> <code>{len(updated)}</code> character(s) out of <code>{len(lines)}</code> line(s)"]
    if updated:
        shown = ", ".join(f"<code>{c}</code>" for c in updated[:40])
        if len(updated) > 40:
            shown += " …"
        summary.append(f"{shown}")
    if skipped:
        summary.append(f"➖ <b>Skipped</b> (nothing to change): <code>{len(skipped)}</code>")
    if failed:
        fail_preview = "\n".join(failed[:20])
        if len(failed) > 20:
            fail_preview += "\n…"
        summary.append(f"❌ <b>Failed:</b> <code>{len(failed)}</code>")
        summary.append(f"{fail_preview}")
    await event.reply("\n".join(summary), parse_mode='html')

# ---- CHANGE ALL RARITY (rebrand rarity emoji/name/value everywhere, DB-wide) ----
def _current_official_rarity_fields(old_rarity_str, fallback_tier=None):
    """Given whatever rarity string is currently stored (old emoji, old font, anything),
    work out its canonical tier and return today's official RARITY_NUM_MAP name + value
    for it. Returns (new_name, new_value, tier) or (None, None, "OTHER") if unclassifiable."""
    tier = fallback_tier or classify_rarity(old_rarity_str)
    num = RARITY_TIER_TO_NUM.get(tier)
    if not num:
        return None, None, "OTHER"
    return RARITY_NUM_MAP[num]["name"], RARITY_NUM_MAP[num]["value"], tier

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]changeallrarity(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def change_all_rarity_handler(event):
    """Owner-only. Rewrites EVERY stored rarity name (+ currency_value on the base character
    record) in the database (characters_base_data, characters, and every user's harem) to
    today's official RARITY_NUM_MAP name/emoji/value, so no old rarity name, emoji, or
    stale value is left anywhere — old data included. Run with 'confirm'."""
    if event.sender_id != OWNER_ID: return
    confirm_arg = (event.pattern_match.group(1) or "").lower()

    legend = "\n".join(
        f"<code>{num}</code> = {RARITY_NUM_MAP[num]['name']} (<code>{RARITY_NUM_MAP[num]['value']}</code> USD)"
        for num in sorted(RARITY_NUM_MAP.keys())
    )

    if confirm_arg != "confirm":
        return await event.reply(
            f"⚠️ <b>{f('CHANGE ALL RARITY')}</b>\n"
            f"This rewrites the <b>rarity</b> name/emoji AND <b>currency_value</b> on every "
            f"character in the database (+ the <b>rarity</b> name inside every player's "
            f"harem) to the current official values below. Old rarity names/emoji/values "
            f"will no longer appear anywhere.\n\n"
            f"🔢 <b>{f('Current Rarity Set')}:</b>\n{legend}\n\n"
            f"❗ <b>{f('This cannot be undone.')}</b>\n"
            f"Run <code>/changeallrarity confirm</code> to proceed.",
            parse_mode='html'
        )

    status_msg = await event.reply("⏳ <b>Rebranding rarity across the database...</b>", parse_mode='html')

    chars_updated, chars_skipped = 0, 0
    for col in (characters_base_col, characters_col):
        docs = await col.find({}, {"_id": 1, "rarity": 1, "rarity_tier": 1}).to_list(length=None)
        if not docs:
            continue
        ops = []
        for doc in docs:
            new_name, new_value, tier = _current_official_rarity_fields(doc.get("rarity", ""), doc.get("rarity_tier"))
            if not new_name:
                chars_skipped += 1
                continue
            ops.append(UpdateOne({"_id": doc["_id"]}, {"$set": {"rarity": new_name, "rarity_tier": tier, "currency_value": new_value}}))
        if ops:
            for i in range(0, len(ops), 500):
                await col.bulk_write(ops[i:i + 500])
            chars_updated += len(ops)

    harem_users_updated, harem_items_updated, harem_users_skipped = 0, 0, 0
    cursor = users_catcher_col.find({"harem.0": {"$exists": True}}, {"_id": 1, "harem": 1})
    batch = []
    async for user_doc in cursor:
        harem = user_doc.get("harem") or []
        changed = False
        new_harem = []
        for item in harem:
            if not isinstance(item, dict):
                new_harem.append(item)
                continue
            new_name, _new_value, _tier = _current_official_rarity_fields(item.get("rarity", ""))
            if new_name and new_name != item.get("rarity"):
                item = {**item, "rarity": new_name}
                changed = True
                harem_items_updated += 1
            new_harem.append(item)
        if changed:
            batch.append(UpdateOne({"_id": user_doc["_id"]}, {"$set": {"harem": new_harem}}))
            harem_users_updated += 1
        else:
            harem_users_skipped += 1
        if len(batch) >= 500:
            await users_catcher_col.bulk_write(batch)
            batch = []
    if batch:
        await users_catcher_col.bulk_write(batch)

    await invalidate_character_caches()
    try:
        await redis_client.delete("cache:chars:all", "cache:chars:categories")
    except Exception:
        pass

    await status_msg.edit(
        f"✅ <b>{f('RARITY REBRAND COMPLETE')}</b>\n"
        f"🗄️ <b>{f('Characters updated')}:</b> <code>{chars_updated}</code>"
        + (f" <i>(⚠️ {chars_skipped} unclassifiable, left untouched)</i>" if chars_skipped else "") + "\n"
        f"🎒 <b>{f('Players with harem updated')}:</b> <code>{harem_users_updated}</code>\n"
        f"🃏 <b>{f('Harem cards renamed')}:</b> <code>{harem_items_updated}</code>\n\n"
        f"🔢 <b>{f('New Rarity Set')}:</b>\n{legend}",
        parse_mode='html'
    )




# ==========================================
# 🔁 .cr — owner-only, force-changes ONE specific character's rarity tier by number
# (e.g. ".cr BOD1234 no3" moves BOD1234 to Rarity No.3), rewriting its stored rarity
# name/emoji/value AND every copy already sitting in players' harems, so the change is
# immediate and consistent everywhere (/harem, /check, marketplace, etc. all read rarity
# live off these same fields).
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cr(?:@\w+)?$', 'bot1')))
async def change_single_rarity_usage_handler(event):
    if event.sender_id != OWNER_ID: return
    legend = "\n".join(
        f"<code>no{num}</code> = {RARITY_NUM_MAP[num]['name']}" for num in sorted(RARITY_NUM_MAP.keys())
    )
    await event.reply(
        f"📌 <b>Usage:</b> <code>/cr CharID no&lt;N&gt;</code>\n"
        f"<i>Example:</i> <code>/cr BOD1234 no3</code> — force-changes BOD1234 to Rarity No.3.\n\n"
        f"📚 <b>Bulk:</b> reply to a message listing many CharIDs (spaces/commas/newlines) "
        f"with just <code>/cr no&lt;N&gt;</code> to change all of them at once.\n\n"
        f"🔢 <b>Rarity Tiers:</b>\n{legend}",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cr(?:@\w+)?\s+(\S+)\s+(?:no)?([1-4])$', 'bot1')))
async def change_single_rarity_handler(event):
    if event.sender_id != OWNER_ID: return
    char_id = normalize_char_id_input(event.pattern_match.group(1))
    rarity_num = event.pattern_match.group(2)
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        return await event.reply(f"❌ <b>No character found with ID</b> <code>{display_char_id(char_id)}</code>.", parse_mode='html')
    r_info = RARITY_NUM_MAP[rarity_num]
    new_tier = RARITY_TIERS[int(rarity_num) - 1]
    old_rarity_display = char_doc.get("rarity", "Unknown")
    old_tier = char_doc.get("rarity_tier") or classify_rarity(old_rarity_display)
    if old_tier == new_tier:
        return await event.reply(
            f"⚠️ <b>{escape_html(char_doc.get('name', ''))}</b> (<code>{display_char_id(char_id)}</code>) "
            f"is already {r_info['name']}. Nothing to change.",
            parse_mode='html'
        )
    status_msg = await event.reply("⏳ <b>Changing rarity...</b>", parse_mode='html')
    await characters_base_col.update_one(
        {"char_id": char_id},
        {"$set": {"rarity": r_info["name"], "rarity_tier": new_tier, "currency_value": r_info["value"]}}
    )
    # Rewrite every existing harem copy of THIS exact character so already-owned cards
    # immediately reflect the new rarity too — same technique /changeallrarity uses,
    # just scoped to a single char_id via the existing harem.char_id index.
    harem_users_updated, harem_items_updated = 0, 0
    batch = []
    cursor = users_catcher_col.find({"harem.char_id": char_id}, {"_id": 1, "harem": 1})
    async for user_doc in cursor:
        harem = user_doc.get("harem") or []
        changed = False
        new_harem = []
        for item in harem:
            if isinstance(item, dict) and item.get("char_id") == char_id and item.get("rarity") != r_info["name"]:
                item = {**item, "rarity": r_info["name"]}
                changed = True
                harem_items_updated += 1
            new_harem.append(item)
        if changed:
            batch.append(UpdateOne({"_id": user_doc["_id"]}, {"$set": {"harem": new_harem}}))
            harem_users_updated += 1
        if len(batch) >= 500:
            await users_catcher_col.bulk_write(batch)
            batch = []
    if batch:
        await users_catcher_col.bulk_write(batch)
    await invalidate_character_caches()
    await status_msg.edit(
        f"✅ <b>Rarity Changed!</b>\n\n"
        f"✨ <b>Character:</b> <code>{escape_html(char_doc.get('name', ''))}</code> (<code>{display_char_id(char_id)}</code>)\n"
        f"🔁 {old_rarity_display} ➜ {r_info['name']}\n\n"
        f"🎒 <b>Players updated:</b> <code>{harem_users_updated}</code>\n"
        f"🃏 <b>Harem cards renamed:</b> <code>{harem_items_updated}</code>",
        parse_mode='html'
    )

# ---- .cr BULK FORM: reply to a message containing many CharIDs (any mix of spaces,
# commas, or newlines, with or without the "BOD" prefix — up to a hundred+ at once) with
# just ".cr no<N>" to force-change ALL of them to that rarity tier in a single shot. The
# single-target ".cr CharID no<N>" form above still works unchanged for one-off edits. ----
CHAR_ID_TOKEN_RE = re.compile(r'^(?:bod)?\d+$', re.IGNORECASE)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cr(?:@\w+)?\s+(?:no)?([1-4])$', 'bot1')))
async def change_bulk_rarity_handler(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_reply:
        return await event.reply(
            "📌 <b>Bulk usage:</b> reply to a message that lists the CharIDs "
            "(separated by spaces, commas, or newlines — as many as you like) with "
            "<code>/cr no&lt;N&gt;</code>.\n"
            "<i>For a single card instead, use </i><code>/cr CharID no&lt;N&gt;</code>.",
            parse_mode='html'
        )
    rarity_num = event.pattern_match.group(1)
    reply_msg = await event.get_reply_message()
    raw_block = reply_msg.text if reply_msg else None
    if not raw_block or not raw_block.strip():
        return await event.reply("⚠️ <b>That message has no CharIDs I can read.</b>", parse_mode='html')

    # Pull out only clearly ID-like tokens (digits, optionally "BOD"-prefixed) — anything
    # else in the replied message (notes, punctuation, etc.) is silently ignored rather
    # than showing up as a noisy "not found" entry.
    char_ids, seen = [], set()
    for tok in re.split(r'[\s,]+', raw_block.strip()):
        tok = tok.strip()
        if not tok or not CHAR_ID_TOKEN_RE.match(tok):
            continue
        cid = normalize_char_id_input(tok)
        if cid not in seen:
            seen.add(cid)
            char_ids.append(cid)
    if not char_ids:
        return await event.reply("⚠️ <b>Couldn't find any CharIDs in that message.</b>", parse_mode='html')

    r_info = RARITY_NUM_MAP[rarity_num]
    new_tier = RARITY_TIERS[int(rarity_num) - 1]
    status_msg = await event.reply(f"⏳ <b>Changing rarity for {len(char_ids)} character(s)...</b>", parse_mode='html')

    # One query to fetch everything, one bulk_write to update everything — instead of a
    # find_one/update_one round trip per character, which is what makes this safe to run
    # against a hundred-plus IDs at once instead of just a couple.
    found_docs = await characters_base_col.find({"char_id": {"$in": char_ids}}).to_list(length=None)
    found_map = {d["char_id"]: d for d in found_docs}

    changed, already, not_found = [], [], []
    char_update_ops = []
    for cid in char_ids:
        char_doc = found_map.get(cid)
        if not char_doc:
            not_found.append(cid)
            continue
        old_tier = char_doc.get("rarity_tier") or classify_rarity(char_doc.get("rarity", ""))
        if old_tier == new_tier:
            already.append(cid)
            continue
        char_update_ops.append(UpdateOne(
            {"char_id": cid},
            {"$set": {"rarity": r_info["name"], "rarity_tier": new_tier, "currency_value": r_info["value"]}}
        ))
        changed.append(cid)

    harem_users_updated, harem_items_updated = 0, 0
    if char_update_ops:
        for i in range(0, len(char_update_ops), 500):
            await characters_base_col.bulk_write(char_update_ops[i:i + 500])
        # Rewrite every existing harem copy of every changed char_id in ONE cursor pass.
        changed_set = set(changed)
        batch = []
        cursor = users_catcher_col.find({"harem.char_id": {"$in": changed}}, {"_id": 1, "harem": 1})
        async for user_doc in cursor:
            harem = user_doc.get("harem") or []
            user_changed = False
            new_harem = []
            for item in harem:
                if isinstance(item, dict) and item.get("char_id") in changed_set and item.get("rarity") != r_info["name"]:
                    item = {**item, "rarity": r_info["name"]}
                    user_changed = True
                    harem_items_updated += 1
                new_harem.append(item)
            if user_changed:
                batch.append(UpdateOne({"_id": user_doc["_id"]}, {"$set": {"harem": new_harem}}))
                harem_users_updated += 1
            if len(batch) >= 500:
                await users_catcher_col.bulk_write(batch)
                batch = []
        if batch:
            await users_catcher_col.bulk_write(batch)
        await invalidate_character_caches()

    summary = [
        f"✅ <b>Bulk Rarity Change Complete!</b>\n"
        f"🔁 <b>New Rarity:</b> {r_info['name']}\n"
        f"✨ <b>Changed:</b> <code>{len(changed)}</code> / <code>{len(char_ids)}</code> character(s)"
    ]
    if changed:
        shown = ", ".join(f"<code>{display_char_id(c)}</code>" for c in changed[:40])
        if len(changed) > 40:
            shown += " …"
        summary.append(f"{shown}")
    if already:
        summary.append(f"➖ <b>Already this rarity:</b> <code>{len(already)}</code>")
    if not_found:
        preview = ", ".join(f"<code>{display_char_id(c)}</code>" for c in not_found[:20])
        if len(not_found) > 20:
            preview += " …"
        summary.append(f"❌ <b>Not found:</b> <code>{len(not_found)}</code>\n{preview}")
    summary.append(f"🎒 <b>Players updated:</b> <code>{harem_users_updated}</code> | 🃏 <b>Harem cards renamed:</b> <code>{harem_items_updated}</code>")
    await status_msg.edit("\n".join(summary), parse_mode='html')

# ---- /spawnweight: owner sets a GLOBAL level that boosts Rarity 1-4 spawn frequency (the
# same quiz-gated bracket) relative to its own defaults. Applies bot-wide no matter which
# chat the owner types it in — it's one shared setting, not a per-group one. ----
def _spawnweight_status_text():
    multiplier = SPAWNWEIGHT_LEVEL_MULTIPLIERS.get(_cached_spawnweight_level, 1)
    gated_list = "/".join(
        f"No.{RARITY_TIER_TO_NUM[t]} {t}"
        for t in sorted(RARITY_GATE_TIERS, key=lambda t: RARITY_TIER_TO_NUM[t])
    )
    levels_desc = "\n".join(
        f"<code>{lvl}</code> → <code>{mult}x</code>" for lvl, mult in sorted(SPAWNWEIGHT_LEVEL_MULTIPLIERS.items())
    )
    return (
        f"⚖️ <b>Rarity Spawn Weight</b> <i>(Global — same in every chat)</i>\n"
        f"<b>Current level:</b> <code>{_cached_spawnweight_level}</code> → <code>{multiplier}x</code> on {gated_list}\n\n"
        f"<b>Levels:</b>\n{levels_desc}\n\n"
        f"<b>Usage:</b> <code>/spawnweight &lt;level&gt;</code>\n"
        f"<i>Rarity 5-9 (the common tiers) are never affected — only the quiz-gated Rarity 1-4 "
        f"bracket scales, and it applies globally regardless of which chat you run this in.</i>"
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]spawnweight(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def rarity_spawn_weight_handler(event):
    if event.sender_id != OWNER_ID: return
    global _cached_spawnweight_level
    arg = (event.pattern_match.group(1) or "").strip()

    if not arg:
        return await event.reply(_spawnweight_status_text(), parse_mode='html')

    try:
        level = int(arg)
    except ValueError:
        return await event.reply(
            "❌ <b>Level must be a whole number.</b>\n\n" + _spawnweight_status_text(),
            parse_mode='html'
        )
    if level not in SPAWNWEIGHT_LEVEL_MULTIPLIERS:
        valid = ", ".join(str(l) for l in sorted(SPAWNWEIGHT_LEVEL_MULTIPLIERS))
        return await event.reply(
            f"❌ <b>Unknown level.</b> Valid levels: <code>{valid}</code>\n\n" + _spawnweight_status_text(),
            parse_mode='html'
        )
    _cached_spawnweight_level = level
    await bot_settings_col.update_one({"_id": "rarity_spawn_weight_level"}, {"$set": {"level": level}}, upsert=True)
    multiplier = SPAWNWEIGHT_LEVEL_MULTIPLIERS[level]
    await event.reply(
        f"✅ <b>Spawn weight level set to {level}</b> ({multiplier}x on Rarity 1-4) — applies globally, in every chat.\n\n"
        + _spawnweight_status_text(),
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]send(?:@\w+)?(?:\s+(.*))?$', 'bot1')))
async def broadcast(event):
    if event.sender_id != OWNER_ID: return
    reply_msg = await event.get_reply_message()
    command_text = event.pattern_match.group(1)
    if not reply_msg and not command_text: return
    success, fail = 0, 0
    status_msg = await event.respond(bq("<b>BROADCAST INITIATED</b>"), parse_mode='html')
    groups = await groups_col.find().to_list(length=None)
    for g in groups:
        chat_id = g['chat_id']
        try:
            if reply_msg: await bot1.forward_messages(chat_id, reply_msg)
            else: await bot1.send_message(chat_id, command_text, parse_mode='html')
            success += 1
            await asyncio.sleep(4)
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 2)
            try:
                if reply_msg: await bot1.forward_messages(chat_id, reply_msg)
                else: await bot1.send_message(chat_id, command_text, parse_mode='html')
                success += 104
            except: fail += 1
        except Exception: fail += 1
    await status_msg.edit(bq(f"<b>BROADCAST COMPLETE</b>\n✅ <b>Success:</b> <code>{success}</code>\n❌ <b>Failed:</b> None"), parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](fspawn|haii)(?:@\w+)?$', 'bot1')))
async def force_spawn_by_owner(event):
    if event.sender_id != OWNER_ID: return
    chat_id = event.chat_id
    # 🩹 DIAGNOSTIC: /haii used to call trigger_dynamic_spawn() and give ZERO feedback if a
    # stale active_group_spawns/pending_rarity_quiz entry for this chat was silently blocking
    # it (the very first guard inside trigger_dynamic_spawn). That made "/haii does nothing"
    # indistinguishable from "/haii isn't wired up at all". Surface the actual state instead.
    if chat_id in active_group_spawns:
        stuck_for = int(time.time() - active_group_spawns[chat_id].get("spawn_time", 0))
        return await event.reply(
            f"⚠️ <b>Spawn already active in this chat</b> (char <code>{active_group_spawns[chat_id].get('name')}</code>, "
            f"posted <code>{stuck_for}s</code> ago). Not spawning another one on top of it. "
            f"If this looks stuck/stale, wait for the 30-minute auto-cleaner or use the admin cleanup command.",
            parse_mode='html'
        )
    if chat_id in pending_rarity_quiz:
        return await event.reply(
            "⚠️ <b>A rarity-gate quiz is pending in this chat.</b> Not spawning until it resolves or times out.",
            parse_mode='html'
        )
    await trigger_dynamic_spawn(chat_id)

# ⚡ PERFORMANCE: spawn_target used to be re-fetched from Mongo (1-2 reads) on literally
# every single group message — the hottest path in the whole bot. It only ever changes
# via an explicit owner command, so cache it and just bust the cache on that one write path.
_spawn_target_cache = bot_state._spawn_target_cache
SPAWN_TARGET_CACHE_TTL = 120  # seconds

async def get_spawn_target(chat_id):
    cached = _spawn_target_cache.get(chat_id)
    now = time.time()
    if cached and (now - cached[1]) < SPAWN_TARGET_CACHE_TTL:
        return cached[0]
    group_config = await groups_config_col.find_one({"chat_id": chat_id})
    if group_config and "spawn_target" in group_config:
        spawn_target = group_config["spawn_target"]
    else:
        global_config = await groups_config_col.find_one({"chat_id": GLOBAL_SPAWN_CHAT_KEY})
        spawn_target = global_config.get("spawn_target", 50) if global_config else 50
    _spawn_target_cache[chat_id] = (spawn_target, now)
    return spawn_target

# ---- AUTOMATIC SPAWN PROCESSOR ----
GROUP_COUNTER_FLUSH_SECONDS = 48
# how often the in-memory spawn counters get batched to Mongo
@bot1.on(events.NewMessage(incoming=True))
async def global_message_counter_handler(event):
    if event.is_private or event.chat_id == SPECIFIC_CONTROL_GROUP: return
    chat_id = event.chat_id
    if chat_id in active_group_spawns or chat_id in pending_rarity_quiz: return
    spawn_target = await get_spawn_target(chat_id)
    # ⚡ PERFORMANCE: this used to be a MongoDB find_one_and_update on EVERY single group
    # message — the single biggest source of database load in the whole bot (one write per
    # message, across every active group, all day long). The counter now lives purely in
    # memory (group_spawn_counters, on bot_state) so a normal message costs zero DB calls.
    # Durability is handled two other ways instead: a cheap periodic bulk write every
    # GROUP_COUNTER_FLUSH_SECONDS (see group_counter_flush_loop), and one immediate write the
    # moment a spawn actually fires (rare — once per spawn_target messages, not per message).
    # Worst case on a crash: up to ~GROUP_COUNTER_FLUSH_SECONDS of message-count progress
    # toward the *next* spawn is lost — never a spawn itself, never any other state.
    new_count = group_spawn_counters.get(chat_id, 0) + 1
    group_spawn_counters[chat_id] = new_count
    if new_count >= spawn_target:
        # 🛡️ RELIABILITY: subtract spawn_target instead of hard-resetting to 0, so any
        # "overshoot" from the threshold check never silently disappears (same reasoning as
        # the old Mongo $inc version — just applied to the in-memory value now).
        group_spawn_counters[chat_id] = new_count - spawn_target
        try:
            await groups_counters_col.update_one(
                {"chat_id": chat_id},
                {"$set": {"counter": group_spawn_counters[chat_id]}},
                upsert=True
            )
        except Exception as e:
            logging.error(f"Group counter persist-on-spawn error: {e}")
        await trigger_dynamic_spawn(chat_id)

async def load_group_spawn_counters_cache():
    """One-time load of persisted spawn counters into memory on boot, so a restart doesn't
    reset every group's progress back to 0 — only whatever hadn't been flushed yet (at most
    ~GROUP_COUNTER_FLUSH_SECONDS worth) is at risk."""
    try:
        docs = await groups_counters_col.find({}, {"chat_id": 1, "counter": 1}).to_list(length=None)
        for d in docs:
            group_spawn_counters[d["chat_id"]] = d.get("counter", 0)
        print(f"📥 Loaded {len(docs)} group spawn counters into memory.")
    except Exception as e:
        print(f"load_group_spawn_counters_cache error: {e}")

async def group_counter_flush_loop():
    """Batches every group's in-memory spawn counter to Mongo in a single bulk_write every
    GROUP_COUNTER_FLUSH_SECONDS — this is the ONLY place (besides the on-spawn write above)
    that persists group_spawn_counters, replacing what used to be a write on every message."""
    while True:
        await asyncio.sleep(GROUP_COUNTER_FLUSH_SECONDS)
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
# ---- TRIGGER DYNAMIC SPAWN ----
async def trigger_dynamic_spawn(chat_id):
    if chat_id in active_group_spawns or chat_id in pending_rarity_quiz: return
    async with spawn_locks[chat_id]:
        if chat_id in active_group_spawns or chat_id in pending_rarity_quiz: return
        try:
            characters_list = await get_all_characters_cached()
            if not characters_list:
                await report_system_error(
                    f"trigger_dynamic_spawn (chat {chat_id})",
                    "characters_base_col is empty — no characters exist yet, spawn skipped silently."
                )
                return
            eligible_characters = []
            for char in characters_list:
                limit = char.get("spawn_limit", 0)
                if limit and limit > 0 and char.get("spawn_count", 0) >= limit:
                    continue
                eligible_characters.append(char)
            if not eligible_characters:
                await report_system_error(
                    f"trigger_dynamic_spawn (chat {chat_id})",
                    f"0 of {len(characters_list)} characters are eligible — every character has hit its "
                    f"CatchLimit (spawn_count >= spawn_limit). Spawn skipped silently. Use /editchar or "
                    f"raise CatchLimit to fix."
                )
                return
            RARITY_WEIGHTS = get_effective_rarity_weights()
            candidates = list(eligible_characters)
            max_attempts = min(5, len(candidates))
            for attempt in range(max_attempts):
                weights = [
                    RARITY_WEIGHTS.get(c.get("rarity_tier") or classify_rarity(c.get("rarity", "")), 20)
                    for c in candidates
                ]
                chosen_char = random.choices(candidates, weights=weights, k=1)[0]
                # ✅ Rarity gate ကို RARITY_GATE_TIERS ထဲပါတဲ့ Rarity တွေအတွက်သာ ဖွင့်မယ်
                tier = classify_rarity(chosen_char.get("rarity", ""))
                if tier in RARITY_GATE_TIERS:
                    ok = await start_rarity_gate_quiz(chat_id, chosen_char)
                else:
                    ok = await release_spawn(chat_id, chosen_char)
                if ok:
                    return
                candidates = [c for c in candidates if c["char_id"] != chosen_char["char_id"]]
                if not candidates:
                    break
            msg = f"⚠️ Spawn Reliability: exhausted {max_attempts} attempt(s) in chat {chat_id} without a usable character."
            print(msg)
            await report_system_error(f"trigger_dynamic_spawn (chat {chat_id})", msg + " (check storage media / SPECIFIC_CONTROL_GROUP)")
        except Exception as e:
            print(f"Spawn Error Tracker: {e}")
            await report_system_error(f"trigger_dynamic_spawn (chat {chat_id})", e)
async def release_spawn(chat_id, chosen_char):
    """Actually post the spawn message + open the /who window for chosen_char. Used both for
    normal spawns and for gated (Sweetie, No.1 only) spawns once their quiz gate has been solved.
    Returns True on success, False if it couldn't post (caller may retry with another char)."""
    if chat_id in active_group_spawns: return False
    try:
        # Do NOT increment spawn_count here; it will be incremented on successful catch.
        rarity_display = chosen_char.get("rarity", "Unknown")
        rarity_tier = classify_rarity(rarity_display)
        rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
        event_name = chosen_char.get("event", "General")
        event_display = escape_html(event_name) if event_name and event_name != "General" else "—"
        artist_raw = chosen_char.get("artist")
        # Spelled out step-by-step on purpose — players were missing that /who has to be a
        # REPLY to this exact message, and that there's a second /fuck step after that.
        spawn_lines = [
            "❓ ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!🧃",
            "ᴀᴅᴅ ᴛʜɪs ᴄʜᴀʀᴀᴄᴛᴇʀ ᴛᴏ ʏᴏᴜʀ ʜᴀʀᴇᴍ ᴜsɪɴɢ /fuck [ɴᴀᴍᴇ].."
        ]
        artist_credit = artist_line(artist_raw, prefix="\n", suffix="")
        if artist_credit:
            spawn_lines.append(artist_credit)
        spawn_text = "\n".join(spawn_lines)

        async def _post_spawn(media):
            # 🌸 The spawned character's photo/video is sent as a spoiler — hidden behind a
            # "tap to view" blur until someone actually chooses to look at it.
            # 🩹 FIX: this is the ONLY place in the whole file that passes spoiler=True to
            # send_message(). Older/mismatched Telethon builds raise TypeError: send_message()
            # got an unexpected keyword argument 'spoiler' on EVERY call — which, since
            # send_with_char_media only special-cases FileReferenceExpiredError, propagates
            # straight up and made every single spawn attempt fail (while /harem, /check, /fav
            # kept working fine, since none of them ever pass spoiler=True). Fall back to
            # sending without the spoiler blur instead of failing the spawn outright, and tell
            # the owner once so the real fix (pip install -U telethon) doesn't get missed.
            try:
                return await bot1.send_message(chat_id, spawn_text, parse_mode='html', file=media, spoiler=True)
            except TypeError as te:
                if "spoiler" not in str(te):
                    raise
                if not getattr(release_spawn, "_spoiler_warned", False):
                    release_spawn._spoiler_warned = True
                    await report_system_error(
                        "release_spawn — spoiler unsupported",
                        f"Installed Telethon version doesn't accept spoiler=True on send_message() "
                        f"({te}). Spawns will post WITHOUT the hidden/blur effect until you run "
                        f"`pip install -U telethon` and redeploy. This warning only fires once."
                    )
                return await bot1.send_message(chat_id, spawn_text, parse_mode='html', file=media)

        spawn_msg = await send_with_char_media(chosen_char["char_id"], chosen_char["storage_msg_id"], _post_spawn)
        if spawn_msg is None:
            msg = f"storage media missing for char_id={chosen_char.get('char_id')} (storage_msg_id={chosen_char.get('storage_msg_id')}) — likely deleted from SPECIFIC_CONTROL_GROUP. Spawn skipped, will retry with another character."
            print(f"⚠️ Spawn Reliability: {msg}")
            await report_system_error(f"release_spawn (chat {chat_id})", msg)
            return False

        active_group_spawns[chat_id] = {
            "spawn_msg_id": spawn_msg.id,
            "char_id": chosen_char["char_id"],
            "name": chosen_char["name"],
            "category": chosen_char["category"],
            "value": chosen_char["currency_value"],
            "rarity": rarity_display,
            "event": event_name,
            "artist": chosen_char.get("artist"),
            "spawn_time": time.time(),
            "revealed": False,
            "claimed": False
        }
        return True
    except Exception as e:
        print(f"Spawn Error Tracker: {e}")
        await report_system_error(f"release_spawn (chat {chat_id}, char {chosen_char.get('char_id')})", e)
        return False


# ---- RARITY GATE QUIZ (No.1 Sweetie only) ----
async def _get_quiz_pool():
    """Merge owner-authored quizzes (rarity_quiz_bank_col) with the static fallback bank.
    Custom quiz dicts carry an extra 'question_media_msg_id' key the static ones don't have."""
    custom = await rarity_quiz_bank_col.find({}, {"_id": 0}).to_list(length=None)
    return (custom or []) + RARITY_QUIZ_BANK

async def start_rarity_gate_quiz(chat_id, chosen_char):
    """Post a 4-option quiz for a Rarity No.1 (Sweetie) pick. The character itself is NEVER
    shown here — only the question (optionally with its own illustrative image, unrelated to
    the character) and the answer buttons. Only the first person to tap the correct answer
    unlocks release_spawn(); everyone else gets exactly one attempt, right or wrong."""
    try:
        pool = await _get_quiz_pool()
        q = random.choice(pool)
        shuffled_options = q["options"][:]
        correct_answer_text = shuffled_options[q["correct_index"]]
        random.shuffle(shuffled_options)
        correct_index = shuffled_options.index(correct_answer_text)

        # 🖼️ This is the QUIZ's own optional illustration (set via /addquiz) — never the
        # character's media. The character stays completely hidden until the gate is solved.
        media = None
        question_media_msg_id = q.get("question_media_msg_id")
        if question_media_msg_id:
            media = await get_quiz_question_media(bot1, question_media_msg_id)

        rarity_display = chosen_char.get("rarity", "Unknown")
        quiz_text = (
            f"<b>Rarity:</b> {rarity_display}\n\n"
            f"<b>{escape_html(q['question'])}</b>\n\n"
        )
        buttons = [[Button.inline(f"{chr(65 + i)}. {opt}", data=f"rgate_{chat_id}_{i}")] for i, opt in enumerate(shuffled_options)]

        if media:
            sent = await bot1.send_message(chat_id, quiz_text, file=media, buttons=buttons, parse_mode='html')
        else:
            sent = await bot1.send_message(chat_id, quiz_text, buttons=buttons, parse_mode='html')

        pending_rarity_quiz[chat_id] = {
            "char": chosen_char,
            "options": shuffled_options,
            "correct_index": correct_index,
            "question": q["question"],
            "msg_id": sent.id,
            "quiz_time": time.time(),
            "solved": False,
            "attempted_users": set(),
        }
        asyncio.create_task(rarity_gate_quiz_timeout_watcher(chat_id, sent.id))
        return True
    except Exception as e:
        print(f"Rarity Gate Quiz Error: {e}")
        return False

@bot1.on(events.CallbackQuery(pattern=r'^rgate_(-?\d+)_(\d)$'))
async def rarity_gate_answer_callback(event):
    chat_id = int(event.pattern_match.group(1))
    chosen_idx = int(event.pattern_match.group(2))
    quiz = pending_rarity_quiz.get(chat_id)
    if not quiz or quiz.get("solved"):
        return await event.answer("⌛ …too late, someone already has me.", alert=True)
    if time.time() - quiz["quiz_time"] > RARITY_GATE_TIMEOUT_SECONDS:
        return await event.answer("⌛ …time slipped away.", alert=True)
    # 🔒 One attempt per person, no retries — check-and-mark with no await between them so
    # a user double-tapping can't sneak in a second try.
    attempted_users = quiz.setdefault("attempted_users", set())
    if event.sender_id in attempted_users:
        return await event.answer("⚠️ …only one try, remember?", alert=True)
    attempted_users.add(event.sender_id)
    if chosen_idx != quiz["correct_index"]:
        return await event.answer("❌ …not quite. no second chances.", alert=True)
    async with spawn_locks[chat_id]:
        quiz = pending_rarity_quiz.get(chat_id)
        if not quiz or quiz.get("solved"):
            return await event.answer("⌛ …someone else found me first.", alert=True)
        quiz["solved"] = True
        winner_id = event.sender_id
    mention = await get_html_mention(event, winner_id)
    try:
        await event.edit(
            f"◈ <b>{mention} found the answer… I'm yours now</b>\n"
            f"✔ <b>Correct answer:</b> {escape_html(quiz['options'][quiz['correct_index']])}\n\n"
            f"🎒 <i>⋆｡˚ I'm stepping out to meet you now…</i>",
            parse_mode='html',
            buttons=None
        )
    except Exception:
        pass
    await event.answer("✅ …found me. I'm on my way~", alert=True)
    if pending_rarity_quiz.get(chat_id) is quiz:
        del pending_rarity_quiz[chat_id]
    released_ok = await release_spawn(chat_id, quiz["char"])
    if not released_ok:
        try:
            await event.edit(
                f"⚠️ <b>{mention} found the answer, but I got lost on my way to you…</b>\n"
                f"<i>Nothing was lost, though — a new someone will slip in again soon.</i>",
                parse_mode='html',
                buttons=None
            ) 
        except Exception:
            pass

async def rarity_gate_quiz_timeout_watcher(chat_id, msg_id):
    try:
        await asyncio.sleep(RARITY_GATE_TIMEOUT_SECONDS)
        quiz = pending_rarity_quiz.get(chat_id)
        if not quiz or quiz.get("solved") or quiz.get("msg_id") != msg_id:
            return
        del pending_rarity_quiz[chat_id]
        try:
            await bot1.edit_message(
                chat_id, msg_id,
                f"⏰ <b>…nobody answered. I slipped away again.</b>\n"
                f"✅ <b>The correct answer was:</b> {escape_html(quiz['options'][quiz['correct_index']])}",
                parse_mode='html',
                buttons=None
            )
        except Exception:
            pass
    except Exception as e:
        # 🛡️ RELIABILITY: no matter what goes wrong above, this chat's gate must never stay
        # stuck — a leftover pending_rarity_quiz entry silently blocks every future auto-spawn
        # in this chat (see the guard at the top of global_message_counter_handler).
        print(f"Rarity Gate Timeout Watcher Error: {e}")
        if pending_rarity_quiz.get(chat_id, {}).get("msg_id") == msg_id:
            del pending_rarity_quiz[chat_id]

# ---- /addquiz: owner-only, step-by-step authoring of a Rarity 1-4 gate question. DM-only so
# nobody sees it being built. Question may be plain text OR a photo/video with the question as
# caption — that image is the QUIZ's own illustration, never the character being gated. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addquiz(?:@\w+)?$', 'bot1')))
async def add_quiz_handler(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_private:
        return await event.reply(
            "⚠️ <b>Please DM me /addquiz</b> — quizzes are authored privately so nobody in the group sees it being built.",
            parse_mode='html'
        )
    option_labels = ["A", "B", "C", "D"]
    try:
        async with bot1.conversation(event.chat_id, timeout=300) as conv:
            await conv.send_message(
                "🔐 <b>New Rarity-Gate Quiz</b>\n\n"
                "Send me the <b>question</b> — as plain text, OR as a photo/video with the "
                "question typed as the caption. (That image is just an illustration for the "
                "question itself — it is never the character being gated.)\n\n"
                "Send /cancel anytime to stop.",
                parse_mode='html'
            )
            q_msg = await conv.get_response()
            if (q_msg.raw_text or "").strip().lower() == "/cancel":
                return await conv.send_message("❌ Cancelled.")
            question_text = (q_msg.raw_text or "").strip()
            if not question_text:
                return await conv.send_message("❌ I need question text (typed, or as a caption). Cancelled — run /addquiz again.")
            question_media_msg_id = None
            if q_msg.photo or q_msg.video:
                fwd = await send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=q_msg.media)
                question_media_msg_id = fwd.id

            options = []
            for label in option_labels:
                await conv.send_message(f"✏️ Send <b>Option {label}</b>:", parse_mode='html')
                opt_msg = await conv.get_response()
                opt_text = (opt_msg.raw_text or "").strip()
                if opt_text.lower() == "/cancel":
                    return await conv.send_message("❌ Cancelled.")
                if not opt_text:
                    return await conv.send_message("❌ Empty option. Cancelled — run /addquiz again.")
                options.append(opt_text)

            await conv.send_message("✅ Which option is <b>correct</b>? Reply with A, B, C, or D.", parse_mode='html')
            correct_msg = await conv.get_response()
            correct_letter = (correct_msg.raw_text or "").strip().upper()
            if correct_letter == "/CANCEL":
                return await conv.send_message("❌ Cancelled.")
            if correct_letter not in option_labels:
                return await conv.send_message("❌ That's not A/B/C/D. Cancelled — run /addquiz again.")
            correct_index = option_labels.index(correct_letter)

            quiz_doc = {
                "question": question_text,
                "options": options,
                "correct_index": correct_index,
                "question_media_msg_id": question_media_msg_id,
                "created_by": event.sender_id,
                "created_at": time.time(),
            }
            await rarity_quiz_bank_col.insert_one(quiz_doc)

            preview = f"❓ <b>{escape_html(question_text)}</b>\n\n" + "\n".join(
                f"{lbl}. {escape_html(opt)}" + (" ✅" if i == correct_index else "")
                for i, (lbl, opt) in enumerate(zip(option_labels, options))
            )
            if question_media_msg_id:
                try:
                    fwd_msg = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=question_media_msg_id)
                    await conv.send_message(preview, file=fwd_msg.media, parse_mode='html')
                except Exception:
                    await conv.send_message(preview, parse_mode='html')
            else:
                await conv.send_message(preview, parse_mode='html')
            await conv.send_message("✅ <b>Saved!</b> This will now show up in the Rarity 1-4 gate rotation.", parse_mode='html')
    except asyncio.TimeoutError:
        await event.reply("⌛ <b>Timed out waiting for your answer.</b> Run /addquiz again.", parse_mode='html')
    except Exception as e:
        print(f"add_quiz_handler error: {e}")
        await event.reply(f"❌ <b>Something went wrong:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]listquiz(?:@\w+)?$', 'bot1')))
async def list_quiz_handler(event):
    if event.sender_id != OWNER_ID: return
    custom = await rarity_quiz_bank_col.find({}, {"_id": 0, "question": 1}).to_list(length=None)
    lines = [f"<code>{i + 1}.</code> {escape_html(q['question'][:60])}" for i, q in enumerate(custom)]
    await event.reply(
        f"🔐 <b>Custom Gate Quizzes ({len(custom)})</b>\n" + ("\n".join(lines) if lines else "<i>None yet — use /addquiz.</i>")
        + f"\n\n<i>Plus {len(RARITY_QUIZ_BANK)} built-in fallback questions, always in rotation too.</i>\n"
        f"Use <code>/delquiz &lt;number&gt;</code> to remove one.",
        parse_mode='html'
    )

# ==========================================
# 🔎 IDENTIFY VIA /who ON A SAVED/REPOSTED PHOTO OR VIDEO — if a character's original media
# (added through /addchar) was saved to someone's gallery and later sent back — as a photo/
# video WITH "/who" as the caption, or as a plain photo/video that then gets replied to with
# /who — recognizes it via perceptual hash and shows name/id/rarity + a /collect hint.
# Works in groups AND in the bot's DM. INFO ONLY: never touches active_group_spawns, so it
# never makes anything catchable by itself — /collect still only works against a real live spawn.
# ==========================================
IDENTIFY_HAMMING_THRESHOLD = 40  # lower = stricter match. 0-256 possible now that PHASH_SIZE=16.
IDENTIFY_COOLDOWN_SECONDS = 1  # per-user, so repeated attempts don't spam replies

async def find_character_by_media(media_msg):
    """Core perceptual-hash character lookup — given a Telethon message with a photo/video,
    returns the best-matching character doc (or None). Shared by _identify_media_and_reply
    (the /who-style public lookup) and add_artist_handler's reply-based shortcut."""
    try:
        incoming_hash = await compute_phash_for_message(media_msg)
    except Exception as e:
        print(f"find_character_by_media hash error: {e}")
        return None
    if not incoming_hash:
        return None
    characters_list = await get_all_characters_cached()
    best_match, best_distance = None, IDENTIFY_HAMMING_THRESHOLD + 1
    for char in characters_list:
        char_hash = char.get("photo_phash")
        if not char_hash:
            continue
        dist = hamming_distance(incoming_hash, char_hash)
        if dist < best_distance:
            best_distance, best_match = dist, char
    return best_match

async def _identify_media_and_reply(event, media_msg, known_source_bot=None):
    user_id = event.sender_id
    is_cd, _ = await is_on_cooldown(user_id, "identify_repost", IDENTIFY_COOLDOWN_SECONDS)
    if is_cd:
        return
    # 🩹 FIX (per owner report): if we already know structurally which OTHER bot this spawn
    # is from — who_reveal_handler resolved this from the reply target's sender, mapped via
    # /xbotsetbot — go straight to the cross-bot lookup and skip our OWN character check
    # entirely. Checking our own db first used to cause a real bug: if the SAME artwork
    # happens to be used by both bots (e.g. a popular "Spiderman" image with an identical or
    # near-identical phash on both), find_character_by_media() would confidently return OUR
    # OWN match and hand back /fuck [our name] for a spawn that's unambiguously obtain_bot's
    # — a command that doesn't even work there. There's no ambiguity left to resolve by phash
    # once we already know the source bot from context, so don't even look.
    if known_source_bot:
        return await _xbot_identify_fallback_and_reply(event, media_msg, known_source_bot=known_source_bot)
    best_match = await find_character_by_media(media_msg)
    if not best_match:
        # 🩹 FIX (per owner report): this used to fall through to an UNSCOPED cross-bot
        # lookup here — any hash in xbot_hashes_col, from ANY bot, fuzzy-matched with no
        # context at all. That produced real false positives: a manually saved-and-reposted
        # photo, or even a reply to one of OUR OWN bot's past spawns that this exact-match
        # check happened to miss, could still get handed a /catch or /obtain suggestion for a
        # completely unrelated character just because its image was coincidentally close in
        # hash-space to something catch_bot or obtain_bot had stored. A cross-bot suggestion
        # is only trustworthy when we structurally KNOW which bot it's from (known_source_bot,
        # set above from the reply target's sender — see who_reveal_handler) — with no such
        # context, the honest answer is "not recognized", not a guess.
        return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')
    # 🔐 If this exact character is currently sitting behind an unsolved rarity-gate quiz
    # in ANY chat, don't confirm its identity — that would leak Rarity 1-4 characters before
    # the gate is actually cleared and the spawn is released.
    for quiz in pending_rarity_quiz.values():
        if not quiz.get("solved") and quiz.get("char", {}).get("char_id") == best_match["char_id"]:
            return await event.reply(
                "🔐 <b>Can't confirm this one yet — it's still sealed behind a gate somewhere.</b>",
                parse_mode='html'
            )
    try:
        rarity_tier = classify_rarity(best_match.get("rarity", ""))
        rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
        event_display = escape_html(best_match.get("event") or "") if best_match.get("event", "General") != "General" else "➖"
        reveal_text = (
            f"🔎 <b>Recognized!</b>\n\n"
            f"<b>Name:</b> <b>{escape_html(best_match['name'])}</b>\n"
            f"🔖 <b>Character ID:</b> <code>{display_char_id(best_match['char_id'])}</code>\n"
            f"{rarity_emoji} <b>Rarity:</b> {best_match.get('rarity', '?')}\n"
            f"🎡 <b>Event:</b> {event_display}\n"
            f"{artist_line(best_match)}\n\n"
            f"<code>/fuck {escape_html(best_match['name'])}</code>\n\n"
            f"📩 <b>Contact:</b> @Comeback_BoD"
        )
        await event.reply(reveal_text, parse_mode='html')
    except Exception as e:
        print(f"identify reply error: {e}")

# ---- /who (aliases: /w, /waifu) ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:who|w|waifu)(?:@\w+)?$', 'bot1')))
async def who_reveal_handler(event):
    user_id = event.sender_id
    chat_id = event.chat_id
    # Check if user is spam-muted — GLOBALLY, across every group.
    # 🩹 FIX (per owner report — "the biggest bug"): this used to reply "you're muted" EVERY
    # single time the user tried again during their mute window — spam_detection_and_mute
    # already sends the ONE proper notice the instant the mute is first triggered, and Telethon
    # dispatches this handler independently for the same message regardless. Replying again
    # here on every retry was itself spammy. Just stay silent now — the message-deletion in
    # spam_detection_and_mute already handles it.
    if user_id in user_mute_until and time.time() < user_mute_until[user_id]:
        return

    # 🩹 CHANGED (per owner request): only skip when this is a reply to ANOTHER BOT's own
    # message. Several different collector bots run their own /w, /waifu, /who in the same
    # groups — bot1 used to respond even when someone was clearly replying to a DIFFERENT
    # bot's spawn (Path B below matched on ANY photo/video reply, regardless of which bot
    # posted it). Note this only checks the sender's `bot` flag, NOT "is it bot1" — a reply
    # to a regular user's saved/reposted photo or video (the Path B identify-a-saved-character
    # use case) must still fall through below, or /w /waifu /who on those goes completely
    # silent, which was itself a bug (see owner report). A bare /who with no reply (e.g.
    # media-as-caption) is unaffected either way and still works as before.
    known_source_bot = None
    if event.is_reply:
        replied_msg = await event.get_reply_message()
        if not replied_msg:
            return
        bot_me = await bot1.get_me()
        if replied_msg.sender_id != bot_me.id:
            replied_sender = await replied_msg.get_sender()
            if getattr(replied_sender, 'bot', False):
                # 🔭 Exception for the cross-bot monitor: if this reply is to a bot we've
                # actually mapped via /xbotsetbot (catch_bot, obtain_bot, ...), let it fall
                # through to Path B below so _identify_media_and_reply's xbot fallback gets a
                # chance to reveal it — that's the whole point of that feature. Any other,
                # unmapped bot keeps the original silent behavior untouched. Remembered in
                # known_source_bot (not just discarded) so Path B below can skip straight to
                # the cross-bot lookup for it — see _identify_media_and_reply's docstring for
                # why that matters.
                mapped_source = await get_bot_mapping(replied_sender.id)
                if not mapped_source:
                    return
                known_source_bot = mapped_source

    # ---- Path A: replying to the CURRENT live spawn message in this group — original,
    # unchanged flow (expiry/claimed guards, catch button, etc.) ----
    if not event.is_private and chat_id in active_group_spawns:
        spawn_data = active_group_spawns[chat_id]
        if event.is_reply and event.reply_to_msg_id == spawn_data["spawn_msg_id"]:
            if time.time() - spawn_data["spawn_time"] > 300:
                del active_group_spawns[chat_id]
                return await event.reply(
                    "𓂃 ⋆｡˚ <i>…too late. I already wandered off. wait for the next one</i>",
                    parse_mode='html'
                )
            try:
                char_name = spawn_data['name']
                rarity_tier = classify_rarity(spawn_data.get('rarity', ''))
                rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
                raw_event_name = spawn_data.get('event')
                event_display = escape_html(raw_event_name) if raw_event_name and raw_event_name != "General" else ""
                name_line = f"{rarity_emoji} <b>{escape_html(char_name)}</b>"
                if event_display:
                    name_line += f" · 🎡 {event_display}"
                reveal_lines = ["◈ found me, huh?", "", name_line]
                artist_credit = artist_line(spawn_data.get('artist'), suffix="")
                if artist_credit:
                    reveal_lines.append(artist_credit)
                reveal_lines += ["", f"<code>/fuck {escape_html(char_name)}</code>", "", "…say it, and I'm yours."]
                reveal_text = "\n".join(reveal_lines)
                try:
                    # 🩹 FIX: Telethon's automatic buttons= classifier doesn't recognize
                    # KeyboardButtonCopy as an inline-only button (known Telethon bug —
                    # see LonamiWebs/Telethon#4588), so it was building a regular
                    # ReplyKeyboardMarkup instead of an inline one. Telegram's server then
                    # rejects KeyboardButtonCopy outside an inline markup with
                    # "ButtonTypeInvalidError". Building the ReplyInlineMarkup explicitly
                    # bypasses that broken classifier.
                    buttons = types.ReplyInlineMarkup(rows=[
                        types.KeyboardButtonRow(buttons=[
                            types.KeyboardButtonCopy(
                                text=f"🤍 it's me, {char_name}",
                                copy_text=f"/fuck {char_name}"
                            )
                        ])
                    ])
                    await event.reply(reveal_text, parse_mode='html', buttons=buttons)
                except Exception as button_error:
                    await report_system_error("who_button_fallback", f"Button error: {button_error}")
                    await event.reply(reveal_text, parse_mode='html')
            except KeyError as ke:
                error_msg = f"KeyError: {ke}. Spawn data: {spawn_data}"
                print(error_msg)
                await report_system_error("who_reveal_handler", error_msg)
                await event.reply(
                    "❌ <b>…something went quiet. try again in a moment?</b>",
                    parse_mode='html'
                )
            except Exception as e:
                error_msg = f"General error in /who: {e}\nSpawn data: {spawn_data}"
                print(error_msg)
                await report_system_error("who_reveal_handler", error_msg)
                await event.reply(
                    "❌ <b>…give me a second, something tripped me up.</b>",
                    parse_mode='html'
                )
            return

    # ---- Path B: identify a saved/reposted photo or video — works in groups AND DM.
    # Triggers if /who was sent AS the caption on the media, or as a reply to a message
    # that carries a photo/video. (Stickers excluded — animated .webm video-stickers carry a
    # DocumentAttributeVideo alongside DocumentAttributeSticker, so .video alone isn't enough
    # to tell a real video from a video-sticker.) ----
    media_msg = None
    if (event.photo or event.video) and not event.sticker:
        media_msg = event.message
    elif event.is_reply:
        replied = await event.get_reply_message()
        if replied and (replied.photo or replied.video) and not replied.sticker:
            media_msg = replied
    if media_msg is not None:
        return await _identify_media_and_reply(event, media_msg, known_source_bot=known_source_bot)

    # ---- Path C: nothing to show ----
    if event.is_private:
        return await event.reply(
            "<b>◈ send me a photo/video with /who as the caption, or reply to one… and I'll whisper who she is</b>",
            parse_mode='html'
        )
    if chat_id not in active_group_spawns:
        return await event.reply(
            "<b>…nobody's here right now. I haven't come around yet</b>",
            parse_mode='html'
        )
    return await event.reply(
        "📌 <b>reply directly to my spawn message to see who I am — "
        "or reply to a saved photo/video with /who if you want me to recognize her.</b>",
        parse_mode='html'
    )

# ==========================================
# 🔭 CROSS-BOT CHARACTER MONITOR — merged in from the standalone "identify other bots'
# spawns" script.
# ------------------------------------------------------------------------------------
# WHAT THIS IS: bot1's own /who /w /waifu (just above) already recognizes THIS bot's own
# spawned characters via perceptual hash — see find_character_by_media(). This section adds
# a SEPARATE hash database for OTHER bots' characters (catch_bot, obtain_bot, ...), built by
# a dedicated userbot — a real Telegram account, not bot1/bot2 — sitting quietly in those
# other bots' log/spawn channels. Those bots' own admin-log posts ("changed rarity for
# Character X", "updated image for Character X", brand-new-card-drop posts, ...) already
# print the character's name in plain text right there in the caption — this just reads that
# caption, hashes the attached photo/video, and remembers name <-> hash. Later, when a real
# UNREVEALED spawn from one of those bots shows up, /who on it finds the same hash and can
# say the name — same as it already does for bot1's own characters.
#
# INTEGRATION: _identify_media_and_reply (Path B of who_reveal_handler, just above) now
# falls back to this database whenever the photo/video isn't one of bot1's OWN characters —
# using the exact same "🔎 Recognized!" reveal-message style bot1 already uses, just swapping
# the printed command for /catch [name] or /obtain [name] — whichever bot it actually came
# from — instead of /fuck [name]. Nothing about bot1's own reveal flow changes.
#
# All owner/admin management for this (adding channels to watch, mapping bot IDs, giving the
# monitor userbot its login session, forcing a rescan, ...) is owner-only, gated the same way
# every other owner command in this file is (event.sender_id != OWNER_ID -> return), and lives
# on bot1 under an "xbot" prefix — /xbotaddchannel, /xbotsetsession, etc. — kept namespaced so
# none of it can ever collide with the game's existing command surface. See the mapping
# comment above the command handlers further down for the old (script) name of each command.
# ==========================================

XBOT_IDENTIFY_HAMMING_THRESHOLD = 10  # 🩹 FIX: was 30 — loose enough that two genuinely
# different character images (same rough composition: dark background, bright glowing
# subject) coincidentally fell inside the tolerance and got treated as the same character.
# 10/256 bits (~4%) still tolerates minor recompression of the SAME image, but won't paper
# over actual different artwork. Tune this up only after confirming (e.g. via /xbotscan
# results) that same-character reposts are landing further apart than this in practice.
XBOT_CACHE_TTL = 60  # seconds an xbot hash lookup is cached in memory before re-hitting Mongo

# Friendly label + the exact catch-style command each known source bot uses. `None` as the
# command means "we can identify it, but there's no single catch command to hand back"
# (e.g. a poll bot) — build_xbot_catch_command() below returns None in that case and the
# reveal message just omits the command line.
XBOT_SOURCE_LABELS = {
    "catch_bot": ("Catch Bot", "/catch"),
    "obtain_bot": ("Obtain Bot", "/obtain"),
    "poll_bot": ("Poll Bot", None),
}

# ---- Monitored channels + bot-ID mapping (loaded once at startup, kept in memory) ----
monitored_chat_ids: Set[int] = set()
monitored_chat_map: Dict[int, str] = {}
bot_mapping_cache: Dict[int, str] = {}
_xbot_hash_cache: Dict[str, dict] = {}  # hash -> {"doc": ..., "_cached_at": ts}

async def load_monitored_channels():
    global monitored_chat_ids, monitored_chat_map
    docs = await monitored_channels_col.find({}).to_list(length=None)
    monitored_chat_ids = {doc["chat_id"] for doc in docs}
    monitored_chat_map = {doc["chat_id"]: doc.get("source_bot", "unknown") for doc in docs}
    print(f"📋 [xbot monitor] Loaded {len(monitored_chat_ids)} monitored channels: {monitored_chat_ids}")

async def load_bot_mappings():
    global bot_mapping_cache
    docs = await bot_mapping_col.find({}).to_list(length=None)
    bot_mapping_cache = {doc["bot_id"]: doc.get("source_bot", "unknown") for doc in docs}
    print(f"🤖 [xbot monitor] Loaded {len(bot_mapping_cache)} bot mappings: {bot_mapping_cache}")

async def get_bot_mapping(bot_id: int) -> Optional[str]:
    if bot_id in bot_mapping_cache:
        return bot_mapping_cache[bot_id]
    doc = await bot_mapping_col.find_one({"bot_id": bot_id})
    return doc.get("source_bot") if doc else None

async def set_bot_mapping(bot_id: int, source_bot: str):
    await bot_mapping_col.update_one(
        {"bot_id": bot_id},
        {"$set": {"source_bot": source_bot, "updated_at": time.time()}},
        upsert=True
    )
    bot_mapping_cache[bot_id] = source_bot

# ---- Caption parsers — one per known bot's message format ----
def extract_name_catch_bot(caption: str) -> Optional[str]:
    if not caption:
        return None
    for line in caption.splitlines():
        line = line.strip()
        if line.startswith("🏖️ Character Name:"):
            name_part = line.split(":", 1)[1].strip()
            if name_part:
                return name_part
    return None

def extract_name_rarity_change(caption: str) -> Optional[str]:
    if not caption:
        return None
    # 🩹 FIX: this used to stop capturing at the first "[", which chopped off the emoji/tag
    # suffix that's actually part of the card's real current name (e.g. a rarity-change post
    # for "Katsuki Bakugo [🎖️]" was getting stored as bare "Katsuki Bakugo" — which then
    # collided with a completely different card that legitimately had that exact bare name).
    match = re.search(r'changed rarity for Character\s+(.+)', caption, re.IGNORECASE)
    if match:
        name = match.group(1).strip()
        return name if name else None
    return None

def extract_name_image_update(caption: str) -> Optional[str]:
    if not caption:
        return None
    match = re.search(r'updated image for Character\s+(.+)', caption, re.IGNORECASE)
    if match:
        name = re.sub(r'[^\w\s\-\[\]]', '', match.group(1).strip())
        return name if name else None
    return None

def extract_old_new_name(caption: str) -> tuple:
    if not caption:
        return None, None
    old_name = new_name = None
    for line in caption.splitlines():
        line = line.strip()
        if line.startswith("Old Name:"):
            old_name = line.replace("Old Name:", "").strip()
        elif line.startswith("New Name:"):
            new_name = line.replace("New Name:", "").strip()
    return old_name, new_name

def extract_names_obtain_bot(caption: str) -> List[str]:
    if not caption:
        return []
    names = []
    lines = caption.splitlines()
    for i, line in enumerate(lines):
        line = line.strip()
        if "🆕 𝗡𝗘𝗪 𝗖𝗔𝗥𝗗 𝗝𝗨𝗦𝗧 𝗗𝗥𝗢𝗣𝗣𝗘𝗗" in line or "🔄 𝗖𝗔𝗥𝗗 𝗨𝗣𝗗𝗔𝗧𝗘𝗗" in line:
            for j in range(i + 1, min(i + 10, len(lines))):
                check_line = lines[j].strip()
                match = re.search(r'Name:\s*(.+)', check_line)
                if match:
                    name = match.group(1).strip()
                    if name:
                        names.append(name)
                    break
                if check_line.startswith("🤵") or check_line.startswith("━━━"):
                    continue
    return names

def extract_names_poll_bot(caption: str) -> List[str]:
    if not caption:
        return []
    names = []
    for line in caption.splitlines():
        line = line.strip()
        if "Character:" in line:
            parts = line.split("Character:", 1)
            if len(parts) == 2 and parts[1].strip():
                names.append(parts[1].strip())
        elif "Name:" in line and "Character" in line:
            parts = line.split("Name:", 1)
            if len(parts) == 2 and parts[1].strip():
                names.append(parts[1].strip())
    return names

def extract_all_names_from_caption(caption: str, source_bot: str = "unknown") -> List[str]:
    names = []
    for fn in (extract_name_catch_bot, extract_name_rarity_change, extract_name_image_update):
        n = fn(caption)
        if n:
            names.append(n)
    names.extend(extract_names_obtain_bot(caption))
    names.extend(extract_names_poll_bot(caption))
    seen, unique_names = set(), []
    for n in names:
        if n not in seen:
            seen.add(n)
            unique_names.append(n)
    return unique_names

def detect_source_bot(caption: str) -> str:
    if not caption:
        return "unknown"
    if "🏖️ Character Name:" in caption: return "catch_bot"
    if "changed rarity for Character" in caption: return "catch_bot"
    if "changed event for Character" in caption: return "catch_bot"
    if "changed anime for Character" in caption: return "catch_bot"
    if "updated image for Character" in caption: return "catch_bot"
    if "changed name" in caption and "Old Name:" in caption: return "catch_bot"
    if "🆕 𝗡𝗘𝗪 𝗖𝗔𝗥𝗗 𝗝𝗨𝗦𝗧 𝗗𝗥𝗢𝗣𝗣𝗘𝗗" in caption: return "obtain_bot"
    if "🔄 𝗖𝗔𝗥𝗗 𝗨𝗣𝗗𝗔𝗧𝗘𝗗" in caption: return "obtain_bot"
    if "𝘊𝘩𝘢𝘳𝘢𝘤𝘵𝘦𝘳 𝘊𝘰𝘭𝘭𝘦𝘤𝘵𝘰𝘳𝘴 𝘉𝘰𝘵:" in caption: return "obtain_bot"
    if "Name:" in caption and "Category:" in caption and "Rarity:" in caption: return "obtain_bot"
    if "Poll" in caption or "Vote" in caption: return "poll_bot"
    return "unknown"

# ==========================================
# 🆕 AUTO-IMPORT NEW CHARACTERS FROM CATCH_BOT — when catch_bot's log channel posts
# "added new Character", we run the equivalent of our OWN /addchar for it automatically:
# same name, same media, same category (as its "Anime"), and its rarity matched 1:1 against
# our own 9 tiers (see RARITY_TIERS above — expanded to match catch_bot's scheme exactly).
# Nothing here touches xbot_hashes_col (that stays a separate lookup db for characters we
# DIDN'T import) — this creates a REAL, spawnable character in characters_base_col, exactly
# as if the owner had typed /addchar by hand.
# ==========================================

# catch_bot's rarity text -> our own RARITY_NUM_MAP key. Now a straight 1:1 lookup (both
# sides use the exact same 9 tier names) via the auto-generated RARITY_TIER_TO_NUM — no
# grouping/compression needed anymore now that RARITY_TIERS matches catch_bot's scheme exactly.
def map_catch_bot_rarity(rarity_raw: str) -> Optional[str]:
    """catch_bot rarity text (e.g. 'CrossVerse', possibly with stray emoji/whitespace) -> our
    own RARITY_NUM_MAP key ('1'-'9'). Returns None for anything unrecognized rather than
    guessing — the caller must treat that as 'don't sync/import this one'."""
    if not rarity_raw:
        return None
    plain = re.sub(r'[^A-Za-z]', '', rarity_raw).upper()
    return RARITY_TIER_TO_NUM.get(plain)

def extract_new_character_info(caption: str) -> Optional[dict]:
    """Parses a catch_bot '... added new Character' post:
        🫧 Anime: CrossVerse
        🏖️ Character Name: Nino Nakano X spider gwen
        ⚡ RARITY: CrossVerse   (or, seen just as often: ⚡ 𝙍𝘼𝙍𝙄𝙏𝙔: CrossVerse)
    Returns {"name", "category", "rarity_raw"} or None if this isn't that kind of post, or a
    required field is missing.
    🩹 FIX: used to look for the literal substring "RARITY:", but catch_bot renders that label
    in a stylized font (𝙍𝘼𝙍𝙄𝙏𝙔) on some posts and plain ASCII on others — those are different
    Unicode codepoints, so the literal check silently failed on every stylized one. Elimination
    against the other two known lines works regardless of which font this particular post uses."""
    if not caption or "added new Character" not in caption:
        return None
    info = {}
    for line in caption.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("🫧 Anime:"):
            info["category"] = line.split(":", 1)[1].strip()
        elif line.startswith("🏖️ Character Name:"):
            info["name"] = line.split(":", 1)[1].strip()
        elif ":" in line and "added new Character" not in line:
            info["rarity_raw"] = line.rsplit(":", 1)[1].strip()
    if info.get("name") and info.get("rarity_raw"):
        info.setdefault("category", "Unknown")
        return info
    return None

async def auto_import_character_from_catchbot(msg, chat_id, source_bot, silent=False):
    """The auto /addchar equivalent. `msg` is the raw message (event.message in the live
    listener, or the message iter_messages() yields during /xbotscan/xbotresync/bulk-import —
    same shape either way). Owner gets a DM per character by default: success with the new
    char_id, or a clear reason it was skipped (unmapped rarity / no media). Pass silent=True
    (used by the bulk-import job below) to suppress those — a DM per character would itself
    flood the owner's DMs across a many-thousand-character bulk run.
    Returns "imported" / "skipped_duplicate" / "skipped_no_media" / "skipped_bad_rarity" /
    "not_a_new_character_post" / "error" — used by the bulk-import job to tally progress."""
    caption = msg.raw_text or ""
    info = extract_new_character_info(caption)
    if not info:
        return "not_a_new_character_post"
    if not (msg.photo or msg.video or msg.document):
        if not silent:
            await bot1.send_message(
                OWNER_ID,
                f"⚠️ <b>Auto-import skipped</b> — no media on the post for "
                f"<code>{escape_html(info['name'])}</code>.",
                parse_mode='html'
            )
        return "skipped_no_media"

    rarity_num = map_catch_bot_rarity(info["rarity_raw"])
    if not rarity_num:
        if not silent:
            await bot1.send_message(
                OWNER_ID,
                f"⚠️ <b>Auto-import skipped</b> — unrecognized catch_bot rarity "
                f"<code>{escape_html(info['rarity_raw'])}</code> for "
                f"<code>{escape_html(info['name'])}</code> — this rarity name isn't one of our 9 tiers "
                f"(RARITY_TIERS / RARITY_DISPLAY_NAME).",
                parse_mode='html'
            )
        return "skipped_bad_rarity"

    # Avoid importing the same character twice. Hash-first (a re-post of the EXACT same
    # "added new Character" event — e.g. a /xbotscan re-run over history it's already imported
    # — has the exact same photo), falling back to name-text matching only among OUR OWN
    # auto-imported characters. 🩹 FIX (per owner report): this used to match by name text
    # against EVERY character regardless of source — if some earlier, unrelated rename (see
    # the whole edit-chain desync class of bug _resolve_imported_character fixes) ever left a
    # DIFFERENT character sitting under this exact display name, a genuinely new character
    # sharing that name would get silently skipped as a "duplicate" of it, forever. Checking
    # the photo first sidesteps that: a different character essentially never has the same
    # picture by coincidence.
    existing = None
    if msg.photo or msg.video or msg.document:
        existing = await _find_imported_character_by_hash(msg)
    if not existing:
        existing = await characters_base_col.find_one({
            "name_normalized": _normalize_catchbot_name(info["name"]),
            "auto_imported_from": {"$exists": True}
        })
    if existing:
        return "skipped_duplicate"  # expected constantly on every re-run — not an error

    try:
        # Store the media in the same storage group /addchar uses. Sent via monitor_userbot
        # (the client that actually received this message) rather than bot1 — a file
        # reference is only valid for the session that fetched it, and monitor_userbot is
        # that session here. bot1 re-reads this storage message fresh (its own valid
        # reference) every time it needs to display the character, exactly like any
        # manually-/addchar'd character — see get_char_display_media above.
        # 🩹 FIX (per owner report): send_safe_message's own FloodWaitError handling gives up
        # and raises past FLOOD_WAIT_RETRY_CAP (15s) — reasonable for a live user-facing
        # call, but neither an auto-import nor a bulk-import run is one: nothing here is
        # blocking a person waiting on a reply, so "wait it out, however long, then keep
        # going" is what's actually wanted. Retried here directly rather than letting it
        # fall through to the generic error handler below.
        while True:
            try:
                forwarded_msg = await asyncio.wait_for(
                    send_safe_message(monitor_userbot, SPECIFIC_CONTROL_GROUP, "", file=msg.media),
                    timeout=240
                )
                break
            except FloodWaitError as e:
                print(f"⏳ [auto-import] FloodWait: sleeping {e.seconds}s...")
                await asyncio.sleep(e.seconds + 1)
        storage_id = forwarded_msg.id
        r_info = RARITY_NUM_MAP[rarity_num]
        char_id = await _generate_new_char_id()
        photo_phash = await compute_phash_for_message(msg)
        character_data = {
            "char_id": char_id,
            "name": info["name"],
            "name_normalized": _normalize_catchbot_name(info["name"]),
            "category": info["category"],
            "rarity": r_info["name"],
            "rarity_tier": classify_rarity(r_info["name"]),
            "storage_msg_id": storage_id,
            "currency_value": r_info["value"],
            "spawn_count": 0,
            "event": "General",
            "spawn_limit": 0,
            "photo_phash": photo_phash,
            "created_at": time.time(),
            "auto_imported_from": source_bot,
            "source_rarity": info["rarity_raw"],
        }
        await characters_base_col.insert_one(character_data)
        await invalidate_character_caches()

        channel_note = ""
        if CHARACTER_CHANNEL_ID:
            try:
                await post_character_to_channel(character_data, is_new=True)
                channel_note = "\n📢 Posted to channel."
            except Exception as ce:
                # 🩹 FIX: if channel posting is genuinely broken (not just the one-time cold
                # entity cache _ensure_character_channel_entity already retries past), a bulk
                # import hitting it on every single character used to alert the owner once
                # PER CHARACTER — hundreds of identical DMs. Rate-limited to once per 10min.
                is_cd, _ = await is_on_cooldown(0, "autoimport_channel_post_error", 600)
                if not is_cd:
                    await report_system_error(f"AutoImport channel post ({char_id})", ce)

        if not silent:
            await bot1.send_message(
                OWNER_ID,
                f"🆕 <b>Auto-imported from {escape_html(source_bot)}</b>\n"
                f"🆔 <b>ID:</b> <code>{char_id}</code>\n"
                f"👤 <b>Name:</b> <code>{escape_html(info['name'])}</code>\n"
                f"🫧 <b>Category:</b> <code>{escape_html(info['category'])}</code>\n"
                f"🏷️ <b>Rarity:</b> {r_info['name']} <i>(from {escape_html(info['rarity_raw'])})</i>"
                f"{channel_note}",
                parse_mode='html'
            )
        return "imported"
    except Exception as e:
        await report_system_error("auto_import_character_from_catchbot", f"{info.get('name')}: {e}")
        return "error"


async def send_xbot_milestone_notification(count: int, last_name: str, chat_id: int):
    try:
        msg = (
            f"🎉 <b>Cross-bot DB: {count} characters indexed</b>\n"
            f"📛 Last added: <code>{escape_html(last_name)}</code>\n"
            f"🆔 Channel: <code>{chat_id}</code>"
        )
        await bot1.send_message(OWNER_ID, msg, parse_mode='html')
    except Exception as e:
        print(f"xbot milestone notification error: {e}")

def _invalidate_xbot_hash_cache(hash_value: str):
    """Removes every cached lookup for this hash, regardless of which source_bot_filter (if
    any) it was cached under — get_cached_xbot_lookup below can cache the SAME hash multiple
    times under different filter-suffixed keys, so a plain single-key pop by hash alone isn't
    enough to actually invalidate it."""
    for key in [k for k in _xbot_hash_cache if k.startswith(f"{hash_value}:")]:
        _xbot_hash_cache.pop(key, None)

async def store_xbot_character_hash(hash_value: str, name: str, full_caption: str, chat_id: int, msg_id: int, source_bot: str = "unknown") -> bool:
    if not hash_value or not name:
        return False
    try:
        existing = await xbot_hashes_col.find_one({"hash": hash_value})
        if existing:
            if existing.get("name") != name or existing.get("source_bot") != source_bot or existing.get("chat_id") != chat_id:
                await xbot_hashes_col.update_one(
                    {"hash": hash_value},
                    {"$set": {
                        "name": name, "full_caption": full_caption, "chat_id": chat_id,
                        "msg_id": msg_id, "source_bot": source_bot, "updated_at": time.time()
                    }}
                )
                _invalidate_xbot_hash_cache(hash_value)
                return True
            return False
        await xbot_hashes_col.insert_one({
            "hash": hash_value, "name": name, "full_caption": full_caption, "chat_id": chat_id,
            "msg_id": msg_id, "source_bot": source_bot, "timestamp": time.time(), "updated_at": time.time()
        })
        total_count = await xbot_hashes_col.count_documents({"chat_id": chat_id})
        if total_count > 0 and total_count % 10 == 0:
            asyncio.create_task(send_xbot_milestone_notification(total_count, name, chat_id))
        return True
    except Exception as e:
        print(f"store_xbot_character_hash error: {e}")
        return False

async def update_xbot_character_name_by_hash(hash_value: str, new_name: str, source_bot: str = "unknown") -> bool:
    if not hash_value or not new_name:
        return False
    try:
        existing = await xbot_hashes_col.find_one({"hash": hash_value})
        if existing:
            if existing.get("name") != new_name:
                await xbot_hashes_col.update_one(
                    {"hash": hash_value},
                    {"$set": {"name": new_name, "source_bot": source_bot, "updated_at": time.time()}}
                )
                _invalidate_xbot_hash_cache(hash_value)
                return True
            return False
        await xbot_hashes_col.insert_one({
            "hash": hash_value, "name": new_name, "full_caption": f"Name: {new_name}",
            "chat_id": 0, "msg_id": 0, "source_bot": source_bot,
            "timestamp": time.time(), "updated_at": time.time()
        })
        return True
    except Exception as e:
        print(f"update_xbot_character_name_by_hash error: {e}")
        return False

async def lookup_xbot_character_by_hash(hash_value: str, source_bot_filter: str = None) -> Optional[dict]:
    if not hash_value:
        return None
    try:
        query = {"hash": hash_value}
        if source_bot_filter:
            query["source_bot"] = source_bot_filter
        return await xbot_hashes_col.find_one(query)
    except Exception as e:
        print(f"lookup_xbot_character_by_hash error: {e}")
        return None

async def get_cached_xbot_lookup(hash_value: str, source_bot_filter: str = None) -> Optional[dict]:
    """🩹 FIX (per owner report): now optionally scoped to a specific source_bot. Without this,
    two different bots happening to use the exact same (or near-identical) artwork for a
    character — e.g. both posting the same stock "Spiderman" image — could hash-collide, and
    whichever entry happened to be stored would win regardless of which bot the spawn actually
    came from. That's fine when we DON'T already know the source (Path B on a bare/reposted
    photo — any match is equally "best guess"), but who_reveal_handler already knows the exact
    source bot when replying to a message from one it has mapped via /xbotsetbot, so in that
    case it hands that bot name in here as source_bot_filter and every match below is
    restricted to just that bot's own entries — no more coincidental cross-bot mixups.
    Cache key includes the filter so a filtered and unfiltered lookup of the same hash never
    return each other's (possibly different-bot) cached result."""
    if not hash_value:
        return None
    now = time.time()
    cache_key = f"{hash_value}:{source_bot_filter or '*'}"
    cached = _xbot_hash_cache.get(cache_key)
    if cached and (now - cached["_cached_at"]) < XBOT_CACHE_TTL:
        return cached["doc"]
    doc = await lookup_xbot_character_by_hash(hash_value, source_bot_filter)
    if doc:
        _xbot_hash_cache[cache_key] = {"doc": doc, "_cached_at": now}
        return doc
    # No exact hash match — fall back to a fuzzy (hamming-distance) scan, same idea as bot1's
    # own find_character_by_media() above, just against the cross-bot collection instead.
    # Scoped to source_bot_filter too, for the same reason as the exact lookup above.
    query = {"source_bot": source_bot_filter} if source_bot_filter else {}
    all_hashes = await xbot_hashes_col.find(query, {"hash": 1, "name": 1, "source_bot": 1, "chat_id": 1}).to_list(length=None)
    best_match, best_distance = None, XBOT_IDENTIFY_HAMMING_THRESHOLD + 1
    for item in all_hashes:
        dist = hamming_distance(hash_value, item.get("hash"))
        if dist < best_distance:
            best_distance, best_match = dist, item
    if best_match and best_distance <= XBOT_IDENTIFY_HAMMING_THRESHOLD:
        _xbot_hash_cache[cache_key] = {"doc": best_match, "_cached_at": now}
        return best_match
    return None

def build_xbot_catch_command(name: str, source_bot: str) -> Optional[str]:
    """Maps a recognized cross-bot character to the exact command that bot works with.
    Returns None for bots with no single catch-style command (e.g. poll_bot) or an
    unrecognized source."""
    label = XBOT_SOURCE_LABELS.get(source_bot)
    if not label or not label[1]:
        return None
    return f"{label[1]} {name}"

async def _xbot_identify_fallback_and_reply(event, media_msg, known_source_bot=None):
    """Called by _identify_media_and_reply (Path B of who_reveal_handler, above) — either
    after our OWN character roster came back with no match, or directly, skipping that check
    entirely, when the caller already knows structurally which bot this spawn is from (see
    known_source_bot below). Checks the cross-bot monitor's hash database and, on a hit,
    replies in the exact same "🔎 Recognized!" reveal-message style bot1 already uses for its
    own characters — just with /catch [name] or /obtain [name] (whichever bot it's actually
    from) in place of /fuck [name].

    known_source_bot, when set, scopes the hash lookup to ONLY that bot's own stored entries
    (see get_cached_xbot_lookup) — otherwise a hash collision between two different bots using
    the same/near-identical artwork for a character could return the wrong bot's entry."""
    hash_val = await compute_phash_for_message(media_msg)
    if not hash_val:
        return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')
    doc = await get_cached_xbot_lookup(hash_val, source_bot_filter=known_source_bot)
    if not doc:
        return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')

    name = doc.get("name") or "?"
    source_bot = doc.get("source_bot", "unknown")
    label = XBOT_SOURCE_LABELS.get(source_bot, (source_bot.replace("_", " ").title(), None))
    final_command = build_xbot_catch_command(name, source_bot)

    reveal_text = (
        f"🔎 <b>Recognized!</b>\n\n"
        f"<b>Name:</b> <b>{escape_html(name)}</b>\n"
        f"🌐 <b>Bot:</b> {escape_html(label[0])}\n\n"
    )
    if final_command:
        reveal_text += f"<code>{escape_html(final_command)}</code>\n\n"
    reveal_text += "📩 <b>Contact:</b> @Comeback_BoD"

    if final_command:
        try:
            # 🩹 Same fix as who_reveal_handler's Path A button above: Telethon's automatic
            # buttons= classifier doesn't recognize KeyboardButtonCopy as inline-only (see
            # LonamiWebs/Telethon#4588), so we build the ReplyInlineMarkup explicitly.
            buttons = types.ReplyInlineMarkup(rows=[
                types.KeyboardButtonRow(buttons=[
                    types.KeyboardButtonCopy(text=f"📋 {final_command}", copy_text=final_command)
                ])
            ])
            return await event.reply(reveal_text, parse_mode='html', buttons=buttons)
        except Exception as button_error:
            await report_system_error("xbot_identify_button_fallback", f"Button error: {button_error}")
    await event.reply(reveal_text, parse_mode='html')

# ---- Userbot event handlers — watch monitored channels for OTHER bots' spawn/log posts.
# Registered on monitor_userbot (below), never on bot1/bot2. ----
def _normalize_catchbot_name(name: str) -> str:
    """🩹 FIX (per owner report — 'updated image for Character Asia Argento [🏖]' style syncs
    silently doing nothing): an emoji can be written with or without an invisible variation
    selector — '🏖' (U+1F3D6) vs '🏖️' (U+1F3D6 + U+FE0F) render identically but are different
    strings. If catch_bot's "added new Character" post used one form and a LATER "updated
    image"/"changed rarity"/etc. post for the same character used the other, an exact-string
    name match would silently fail even though the names look 100% identical to a human.
    Strips variation selectors and zero-width characters, plus normalizes case/whitespace, so
    two visibly-identical names always match regardless of which exact form either post used.
    Every sync/import function below matches on THIS, never the raw name string directly."""
    if not name:
        return ""
    cleaned = re.sub(r'[\uFE0E\uFE0F\u200B\u200C\u200D]', '', name)
    return cleaned.strip().lower()

async def _find_imported_character(name: str):
    """Normalized-name lookup (see _normalize_catchbot_name), restricted to characters we
    auto-imported from a cross-bot source (auto_imported_from set) — never touches a
    manually-/addchar'd character that happens to share a name. Used by every sync function
    below. Falls back to a raw case-insensitive regex match for characters imported before
    name_normalized existed (pre-migration — see _migrate_name_normalized), so this works
    immediately without needing that migration to have already run."""
    normalized = _normalize_catchbot_name(name)
    if not normalized:
        return None
    doc = await characters_base_col.find_one({"name_normalized": normalized, "auto_imported_from": {"$exists": True}})
    if doc:
        return doc
    return await characters_base_col.find_one({
        "name": {"$regex": f"^{re.escape(name)}$", "$options": "i"},
        "auto_imported_from": {"$exists": True}
    })

async def _find_imported_character_by_hash(msg):
    """Resolves an edit post to OUR stored imported character via the ATTACHED photo/video's
    perceptual hash — scoped to auto_imported_from characters only, same as
    _find_imported_character. See _resolve_imported_character's docstring for why this is
    checked FIRST, ahead of name-text matching. Returns None if there's no media on this
    message, or no sufficiently-close hash match."""
    if not (msg.photo or msg.video or msg.document):
        return None
    try:
        hash_val = await compute_phash_for_message(msg)
    except Exception:
        return None
    if not hash_val:
        return None
    candidates = await characters_base_col.find(
        {"auto_imported_from": {"$exists": True}, "photo_phash": {"$exists": True, "$ne": None}}
    ).to_list(length=None)
    best_match, best_distance = None, XBOT_IDENTIFY_HAMMING_THRESHOLD + 1
    for char in candidates:
        dist = hamming_distance(hash_val, char.get("photo_phash"))
        if dist < best_distance:
            best_distance, best_match = dist, char
    return best_match

async def _resolve_imported_character(msg, name_hint):
    """🩹 THE fix (per owner report — a whole chain of edits on one character silently
    desyncing, ending with the final image update never landing): every sync function below
    now resolves 'which of OUR characters is this catch_bot edit post actually about' through
    THIS, instead of matching on name text alone.

    The bug: catch_bot's OWN caption text for later post types (e.g. "changed event for
    Character X [🎒]") already reflects the character's NEW state — including a bracket event
    tag that's only ADDED to the display name once a SEPARATE rename post processes it. If
    that rename post hasn't landed yet (or landed with a slightly different bracket rendering),
    a pure name-text lookup silently comes up empty, and that one sync step is just... skipped,
    with nothing to show for it until someone happens to compare screenshots days later.

    The fix: try the attached photo/video's hash FIRST (see _find_imported_character_by_hash).
    The photo doesn't change just because the name, event, or category does, so hash matching
    sails straight through the same edit chain that broke name matching — rename, event,
    anime/category, rarity, whatever order they arrive in. Name-text matching is now only the
    FALLBACK, for the rare case a post has no media at all.

    This one function is also what makes /xbotresync's full history replay self-healing: since
    every sync function (and the resync loop itself) routes through here, re-running a resync
    after this fix ships will correctly repair characters that already desynced under the old
    name-only matching, not just prevent new desyncs going forward."""
    by_hash = await _find_imported_character_by_hash(msg)
    if by_hash:
        return by_hash
    return await _find_imported_character(name_hint)

async def _create_orphan_imported_character(msg, name, source_bot, category=None, rarity_raw=None, event=None):
    """🩹 SELF-HEALING FALLBACK (per owner report — "make sure the self-bot manages to add it,
    like /addchar would, no matter what"): called by every sync function below when
    _resolve_imported_character comes up completely empty — meaning this character's ORIGINAL
    "added new Character" post was itself somehow never processed (missed while the listener
    was offline, skipped by a bug, posted before monitoring started, etc.), so an EDIT post
    about it has nothing to attach to. Rather than just dropping that edit on the floor, this
    creates the character FROM the edit post itself — same storage/record shape
    auto_import_character_from_catchbot uses for a real "added new Character" post, just with
    defaults filling in whatever this particular edit type doesn't tell us (category, rarity,
    event). The caller is expected to immediately follow this up by setting whichever field
    the edit itself was ABOUT (e.g. the rarity-change sync still applies the new rarity right
    after creating the shell here) — this only needs to cover everything else.
    Returns the new character doc, or None if there's no media to build a character from."""
    if not (msg.photo or msg.video or msg.document):
        return None
    try:
        while True:
            try:
                forwarded_msg = await asyncio.wait_for(
                    send_safe_message(monitor_userbot, SPECIFIC_CONTROL_GROUP, "", file=msg.media),
                    timeout=240
                )
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
        rarity_num = map_catch_bot_rarity(rarity_raw) if rarity_raw else None
        r_info = RARITY_NUM_MAP[rarity_num] if rarity_num else RARITY_NUM_MAP[str(len(RARITY_TIERS))]
        char_id = await _generate_new_char_id()
        photo_phash = await compute_phash_for_message(msg)
        character_data = {
            "char_id": char_id,
            "name": name,
            "name_normalized": _normalize_catchbot_name(name),
            "category": category or "Unknown",
            "rarity": r_info["name"],
            "rarity_tier": classify_rarity(r_info["name"]),
            "storage_msg_id": forwarded_msg.id,
            "currency_value": r_info["value"],
            "spawn_count": 0,
            "event": event or "General",
            "spawn_limit": 0,
            "photo_phash": photo_phash,
            "created_at": time.time(),
            "auto_imported_from": source_bot,
            "source_rarity": rarity_raw or "",
            "auto_healed": True,  # marks this as a reconstructed-from-an-edit record, not a
            # real "added new Character" import — lets a future audit tell the two apart.
        }
        await characters_base_col.insert_one(character_data)
        await invalidate_character_caches()
        return character_data
    except Exception as e:
        await report_system_error("_create_orphan_imported_character", f"{name}: {e}")
        return None

async def _maybe_handle_xbot_rename(msg, caption: str) -> bool:
    """Checked first — in both live listeners AND the /xbotscan and /xbotresync history-replay
    loops further down — before the general 'must have media' gate. A rename post
    ("... changed name / Old Name: X / New Name: Y") comes with the character's own
    photo/video attached right there, same as any other catch_bot post. `msg` is the actual
    message object: event.message in the live listeners, or the message iter_messages()
    yields directly during a scan/resync — same shape either way, so this works for both.

    🩹 FIX: this used to ALSO sweep every other hash entry that happened to share the exact
    old-name string over to the new name. That's unsafe — different cards can legitimately
    share the same base name text (e.g. "Katsuki Bakugo", "Katsuki Bakugo [🎃]",
    "Katsuki Bakugo [🎖️]" turned out to be three separate, unrelated cards in practice), so a
    name-string match can silently relabel a card that was never actually renamed at all. A
    rename must stay scoped to the ONE hash the announcement is actually about — the photo
    attached to THIS post — nothing broader. If that photo is missing, we simply can't safely
    apply the rename and skip it rather than guess.

    Also syncs the rename onto our OWN imported copy of the character, if we have one (see
    _find_imported_character) — keeping it in step with catch_bot going forward, same as the
    event/rarity/image syncs below.

    Returns True if this message WAS a rename announcement (caller should stop processing
    it any further either way, matched or not — it's not a regular character-hash post)."""
    if not ("changed name" in caption and "Old Name:" in caption and "New Name:" in caption):
        return False
    old_name, new_name = extract_old_new_name(caption)
    if old_name and new_name and (msg.photo or msg.video or msg.document):
        hash_val = await compute_phash_for_message(msg)
        if hash_val:
            await update_xbot_character_name_by_hash(hash_val, new_name, detect_source_bot(caption))
        imported = await _resolve_imported_character(msg, old_name)
        if imported:
            await characters_base_col.update_one({"_id": imported["_id"]}, {"$set": {"name": new_name, "name_normalized": _normalize_catchbot_name(new_name)}})
            await invalidate_character_caches()
            await bot1.send_message(
                OWNER_ID,
                f"🔄 <b>Synced rename</b> — <code>{escape_html(imported['char_id'])}</code>\n"
                f"<code>{escape_html(old_name)}</code> → <code>{escape_html(new_name)}</code>",
                parse_mode='html'
            )
        else:
            # 🩹 SELF-HEAL: old_name never existed on our side (its own "added new Character"
            # post was missed somewhere) — create it fresh under the NEW (current, correct)
            # name instead of dropping this rename entirely. See
            # _create_orphan_imported_character's docstring.
            healed = await _create_orphan_imported_character(msg, new_name, detect_source_bot(caption))
            if healed:
                await bot1.send_message(
                    OWNER_ID,
                    f"🩹 <b>Self-healed (rename)</b> — <code>{escape_html(healed['char_id'])}</code>\n"
                    f"Never had <code>{escape_html(old_name)}</code> on record, so created it fresh as "
                    f"<code>{escape_html(new_name)}</code>. Category/rarity are placeholders — "
                    f"check with /editchar.",
                    parse_mode='html'
                )
            else:
                print(f"🔭 [xbot sync] rename: no imported character found matching '{old_name}' — not synced (may just not be one we imported).")
    return True

def extract_event_change(caption: str) -> Optional[tuple]:
    """'... changed event for Character NAME\n\nFrom: X\nTo: Y' -> (name, new_event) or None.
    NAME may itself include a bracket tag (e.g. 'Aglaea [🧪]') — that's fine, it's just
    whatever the character's current full name is, used as-is for the name lookup below."""
    if not caption or "changed event for Character" not in caption:
        return None
    m = re.search(r'changed event for Character\s+(.+)', caption, re.IGNORECASE)
    if not m:
        return None
    name = m.group(1).strip()
    new_event = None
    for line in caption.splitlines():
        line = line.strip()
        if line.startswith("To:"):
            new_event = line.split(":", 1)[1].strip()
    if name and new_event is not None:
        return name, new_event
    return None

async def _maybe_sync_event_change(msg, caption: str) -> bool:
    """Checked alongside the rename check above, same placement/timing."""
    result = extract_event_change(caption)
    if not result:
        return False
    name, new_event = result
    if new_event.strip() in ("None", "-", ""):
        new_event = "General"
    imported = await _resolve_imported_character(msg, name)
    if imported:
        await characters_base_col.update_one({"_id": imported["_id"]}, {"$set": {"event": new_event}})
        await invalidate_character_caches()
        await bot1.send_message(
            OWNER_ID,
            f"🎪 <b>Synced event change</b> — <code>{escape_html(imported['char_id'])}</code>\n"
            f"<code>{escape_html(name)}</code> → event: <code>{escape_html(new_event)}</code>",
            parse_mode='html'
        )
    else:
        healed = await _create_orphan_imported_character(msg, name, detect_source_bot(caption), event=new_event)
        if healed:
            await bot1.send_message(
                OWNER_ID,
                f"🩹 <b>Self-healed (event)</b> — <code>{escape_html(healed['char_id'])}</code>\n"
                f"Never had <code>{escape_html(name)}</code> on record, so created it fresh with "
                f"event: <code>{escape_html(new_event)}</code>. Category/rarity are placeholders — "
                f"check with /editchar.",
                parse_mode='html'
            )
        else:
            print(f"🔭 [xbot sync] event change: no imported character found matching '{name}' — not synced.")
    return True

def extract_anime_change(caption: str) -> Optional[tuple]:
    """'... changed anime for Character NAME\n\nFrom: X\nTo: Y' -> (name, new_category) or
    None. Same shape as extract_event_change — NAME may include a bracket tag, that's fine."""
    if not caption or "changed anime for Character" not in caption:
        return None
    m = re.search(r'changed anime for Character\s+(.+)', caption, re.IGNORECASE)
    if not m:
        return None
    name = m.group(1).strip()
    new_category = None
    for line in caption.splitlines():
        line = line.strip()
        if line.startswith("To:"):
            new_category = line.split(":", 1)[1].strip()
    if name and new_category:
        return name, new_category
    return None

async def _maybe_sync_anime_change(msg, caption: str) -> bool:
    """🩹 NEW (per owner report — this whole change type was silently unhandled before: a
    'changed anime for Character X' post matched none of the other 4 checks, and fell through
    to the generic hash-bookkeeping path, which never touched the character's actual stored
    category at all). Same shape as the event-change sync above."""
    result = extract_anime_change(caption)
    if not result:
        return False
    name, new_category = result
    imported = await _resolve_imported_character(msg, name)
    if imported:
        await characters_base_col.update_one({"_id": imported["_id"]}, {"$set": {"category": new_category}})
        await invalidate_character_caches()
        await bot1.send_message(
            OWNER_ID,
            f"🫧 <b>Synced anime/category change</b> — <code>{escape_html(imported['char_id'])}</code>\n"
            f"<code>{escape_html(name)}</code> → category: <code>{escape_html(new_category)}</code>",
            parse_mode='html'
        )
    else:
        healed = await _create_orphan_imported_character(msg, name, detect_source_bot(caption), category=new_category)
        if healed:
            await bot1.send_message(
                OWNER_ID,
                f"🩹 <b>Self-healed (anime)</b> — <code>{escape_html(healed['char_id'])}</code>\n"
                f"Never had <code>{escape_html(name)}</code> on record, so created it fresh with "
                f"category: <code>{escape_html(new_category)}</code>. Rarity is a placeholder — "
                f"check with /editchar.",
                parse_mode='html'
            )
        else:
            print(f"🔭 [xbot sync] anime change: no imported character found matching '{name}' — not synced.")
    return True

def extract_rarity_change_value(caption: str) -> Optional[str]:
    """From a 'changed rarity for Character X' post's 'To: <emoji> RARITY: <TierName>' line,
    return just the tier name text after the LAST colon (e.g. 'Mystical'). Deliberately does
    NOT check for the literal word "RARITY" on that line — catch_bot renders that label in a
    stylized font (𝙍𝘼𝙍𝙄𝙏𝙔) whose characters don't match plain ASCII "RARITY", so matching on
    the plain "To:" prefix instead is what actually works here."""
    for line in caption.splitlines():
        line = line.strip()
        if line.startswith("To:"):
            return line.rsplit(":", 1)[1].strip()
    return None

async def _maybe_sync_rarity_change(msg, chat_id, caption: str) -> bool:
    """Checked alongside the rename/event checks above. Does two independent jobs on a match:
    (1) xbot_hashes_col bookkeeping (same as before, for characters we haven't imported — this
    is what the /w cross-bot lookup fallback reads), and (2) if we DID import this character,
    sync its rarity onto our own copy too. Needs media for (1) — a hash has to come from
    somewhere — but (2) doesn't strictly need it since we already have a stored copy."""
    if "changed rarity for Character" not in caption:
        return False
    name = extract_name_rarity_change(caption)
    new_rarity_raw = extract_rarity_change_value(caption)
    if not name:
        return True
    source_bot = detect_source_bot(caption)

    if msg.photo or msg.video or msg.document:
        hash_val = await compute_phash_for_message(msg)
        if hash_val:
            doc = await lookup_xbot_character_by_hash(hash_val)
            if doc and doc.get("name") != name:
                await update_xbot_character_name_by_hash(hash_val, name, source_bot)
            else:
                await store_xbot_character_hash(hash_val, name, caption, chat_id, msg.id, source_bot)

    if not new_rarity_raw:
        return True
    imported = await _resolve_imported_character(msg, name)
    if not imported:
        healed = await _create_orphan_imported_character(msg, name, source_bot, rarity_raw=new_rarity_raw)
        if healed:
            await bot1.send_message(
                OWNER_ID,
                f"🩹 <b>Self-healed (rarity)</b> — <code>{escape_html(healed['char_id'])}</code>\n"
                f"Never had <code>{escape_html(name)}</code> on record, so created it fresh at "
                f"<code>{healed['rarity']}</code>. Category is a placeholder — check with /editchar.",
                parse_mode='html'
            )
        else:
            print(f"🔭 [xbot sync] rarity change: no imported character found matching '{name}' — not synced.")
        return True
    rarity_num = map_catch_bot_rarity(new_rarity_raw)
    if not rarity_num:
        await bot1.send_message(
            OWNER_ID,
            f"⚠️ <b>Rarity sync skipped</b> — <code>{escape_html(imported['char_id'])}</code> "
            f"<code>{escape_html(name)}</code>: unrecognized rarity <code>{escape_html(new_rarity_raw)}</code>.",
            parse_mode='html'
        )
        return True
    r_info = RARITY_NUM_MAP[rarity_num]
    await characters_base_col.update_one(
        {"_id": imported["_id"]},
        {"$set": {"rarity": r_info["name"], "rarity_tier": RARITY_TIERS[int(rarity_num) - 1], "source_rarity": new_rarity_raw}}
    )
    await invalidate_character_caches()
    await bot1.send_message(
        OWNER_ID,
        f"🏷️ <b>Synced rarity change</b> — <code>{escape_html(imported['char_id'])}</code>\n"
        f"<code>{escape_html(name)}</code> → {r_info['name']}",
        parse_mode='html'
    )
    return True

async def _maybe_sync_image_update(msg, chat_id, caption: str) -> bool:
    """Checked alongside the checks above. Does two independent jobs on a match: (1)
    xbot_hashes_col bookkeeping (same as before, for characters we haven't imported), and (2)
    if we DID import this character, re-store the new media as its own copy's media too — via
    monitor_userbot (the session that actually has a valid file reference for it — see
    auto_import_character_from_catchbot for why bot1 can't be handed this media object
    directly). Both need the post's own media — that's the whole point of an image update.
    🩹 Note: _resolve_imported_character's hash-first lookup will almost always MISS here and
    fall back to name matching — the attached photo IS the new one, so it usually won't match
    our still-old stored photo_phash yet. That's fine and expected; it only helps in the (rarer)
    case the "update" is a near-identical recompression/touch-up of the same art, where hash
    matching can resolve it directly without needing the name to already be correct."""
    if "updated image for Character" not in caption:
        return False
    name = extract_name_image_update(caption)
    if not name:
        return True
    if not (msg.photo or msg.video or msg.document):
        return True
    source_bot = detect_source_bot(caption)
    hash_val = await compute_phash_for_message(msg)
    if hash_val:
        await store_xbot_character_hash(hash_val, name, caption, chat_id, msg.id, source_bot)
        _invalidate_xbot_hash_cache(hash_val)

    imported = await _resolve_imported_character(msg, name)
    if not imported:
        # 🩹 SELF-HEAL — this is the exact reported scenario: an "updated image for Character
        # X" post about a character we never actually have on record (its own "added new
        # Character" post was missed somewhere upstream). _create_orphan_imported_character
        # already does everything needed here (forwards the media, stores photo_phash) —
        # no separate forwarding step required in this branch.
        healed = await _create_orphan_imported_character(msg, name, source_bot)
        if healed:
            await bot1.send_message(
                OWNER_ID,
                f"🩹 <b>Self-healed (image)</b> — <code>{escape_html(healed['char_id'])}</code>\n"
                f"Never had <code>{escape_html(name)}</code> on record at all, so created it fresh "
                f"from this image. Category/rarity are placeholders — check with /editchar.",
                parse_mode='html'
            )
        else:
            print(f"🔭 [xbot sync] image update: no imported character found matching '{name}' — not synced.")
        return True
    try:
        forwarded_msg = await asyncio.wait_for(
            send_safe_message(monitor_userbot, SPECIFIC_CONTROL_GROUP, "", file=msg.media),
            timeout=240
        )
        new_hash = await compute_phash_for_message(msg)
        await characters_base_col.update_one(
            {"_id": imported["_id"]},
            {"$set": {"storage_msg_id": forwarded_msg.id, "photo_phash": new_hash}}
        )
        _CHAR_PHOTO_CACHE.pop(imported["char_id"], None)
        await invalidate_character_caches()
        await bot1.send_message(
            OWNER_ID,
            f"🖼️ <b>Synced image update</b> — <code>{escape_html(imported['char_id'])}</code>\n"
            f"<code>{escape_html(name)}</code>",
            parse_mode='html'
        )
    except Exception as e:
        await report_system_error("_maybe_sync_image_update", f"{name}: {e}")
    return True

async def _maybe_sync_catchbot_character_change(msg, chat_id, caption: str) -> bool:
    """Single entry point for ALL the 'keep an already-imported character in sync with
    catch_bot' checks — rename, event change, anime/category change, rarity change, image
    update — called from BOTH listeners before their generic/fallback handling.
    Short-circuits on the first match, since a post is only ever one of these kinds. Returns
    True if any of them handled this message."""
    if await _maybe_handle_xbot_rename(msg, caption):
        return True
    if await _maybe_sync_event_change(msg, caption):
        return True
    if await _maybe_sync_anime_change(msg, caption):
        return True
    if await _maybe_sync_rarity_change(msg, chat_id, caption):
        return True
    if await _maybe_sync_image_update(msg, chat_id, caption):
        return True
    return False

async def userbot_channel_listener(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    if chat_id not in monitored_chat_ids:
        return
    caption = event.raw_text or ""
    # 🩹 FIX: catch_bot posts ALL of these (rename, event change, rarity change, image
    # update) as brand-new messages, not edits — checked here, before the "needs media" gate
    # below, since event-change/rarity-change syncs don't need media at all.
    if await _maybe_sync_catchbot_character_change(event.message, chat_id, caption):
        return
    if not (event.photo or event.video or event.document):
        return
    source_bot = detect_source_bot(caption)
    # 🆕 "added new Character" posts get a REAL character created in our own DB (see
    # auto_import_character_from_catchbot above) — checked before the generic xbot-hash
    # storage path below, since this is a fully different, much bigger action than just
    # remembering a hash->name lookup.
    if "added new Character" in caption:
        asyncio.create_task(auto_import_character_from_catchbot(event.message, chat_id, source_bot))
        return
    names = extract_all_names_from_caption(caption, source_bot)
    if not names:
        return
    hash_val = await compute_phash_for_message(event.message)
    if not hash_val:
        return
    for name in names:
        await store_xbot_character_hash(hash_val, name, caption, chat_id, event.id, source_bot)

async def userbot_edit_listener(event):
    if event.is_private:
        return
    chat_id = event.chat_id
    if chat_id not in monitored_chat_ids:
        return
    new_caption = event.raw_text or ""
    # Same dispatcher as userbot_channel_listener above, kept here too in case catch_bot ever
    # posts (or edits into) any of these formats as an edit instead of a fresh message.
    if await _maybe_sync_catchbot_character_change(event.message, chat_id, new_caption):
        return
    if not (event.photo or event.video or event.document):
        return
    source_bot = detect_source_bot(new_caption)

    if "🆕 𝗡𝗘𝗪 𝗖𝗔𝗥𝗗 𝗝𝗨𝗦𝗧 𝗗𝗥𝗢𝗣𝗣𝗘𝗗" in new_caption or "🔄 𝗖𝗔𝗥𝗗 𝗨𝗣𝗗𝗔𝗧𝗘𝗗" in new_caption:
        names = extract_names_obtain_bot(new_caption)
        if names:
            hash_val = await compute_phash_for_message(event.message)
            if hash_val:
                for name in names:
                    await store_xbot_character_hash(hash_val, name, new_caption, chat_id, event.id, source_bot)
                    _invalidate_xbot_hash_cache(hash_val)
        return

def register_userbot_handlers(client):
    client.add_event_handler(userbot_channel_listener, events.NewMessage(incoming=True))
    client.add_event_handler(userbot_edit_listener, events.MessageEdited(incoming=True))

# ---- The monitor userbot itself — a REAL Telegram account (not a bot token), logged in via
# a StringSession the owner supplies with /xbotsetsession. Stays None until that happens, or
# until load_and_start_monitor_userbot() finds a previously-saved session at boot. ----
monitor_userbot: Optional[TelegramClient] = None

async def load_and_start_monitor_userbot():
    global monitor_userbot
    doc = await bot_settings_col.find_one({"_id": "xbot_monitor_session"})
    if not doc or not doc.get("session"):
        # 🔁 One-time migration: the old standalone monitor script saved its session under
        # _id "userbot_session" (same "bot_settings" collection, different key — see
        # settings_col in the original script). If that's there, adopt it under our new key
        # so the owner doesn't have to run /xbotsetsession again after the merge.
        old_doc = await bot_settings_col.find_one({"_id": "userbot_session"})
        if old_doc and old_doc.get("session"):
            await bot_settings_col.update_one(
                {"_id": "xbot_monitor_session"},
                {"$set": {"session": old_doc["session"]}},
                upsert=True
            )
            doc = old_doc
            print("🔁 [xbot monitor] Migrated session from the pre-merge script's old key.")
    if not doc or not doc.get("session"):
        print("⚠️ [xbot monitor] No saved userbot session yet — owner can set one with /xbotsetsession.")
        return
    try:
        client = TelegramClient(StringSession(doc["session"]), APP_ID, APP_HASH)
        await client.start()
        me = await client.get_me()
        register_userbot_handlers(client)
        asyncio.create_task(client.run_until_disconnected())
        monitor_userbot = client
        print(f"✅ [xbot monitor] Userbot connected as @{me.username if me.username else me.id}")

        # 📦 Resume an interrupted bulk import automatically — this is the whole point of
        # persisting its checkpoint to bot_settings_col instead of just memory: a bot restart
        # mid-run (deploy, crash, host restart) shouldn't lose progress OR need the owner to
        # notice and manually re-trigger it. See _run_bulk_import further down.
        bulk_state = await bot_settings_col.find_one({"_id": "xbot_bulk_import_state"})
        if bulk_state and bulk_state.get("active") and bulk_state.get("chat_ids"):
            print(f"📦 [xbot monitor] Resuming interrupted bulk import ({bulk_state.get('checked', 0)} already checked)...")
            asyncio.create_task(_run_bulk_import(bulk_state["chat_ids"], status_chat_id=OWNER_ID, status_msg_id=None))
    except Exception as e:
        print(f"❌ [xbot monitor] Userbot failed to start: {e}")

# ==========================================
# 🔧 OWNER COMMANDS — cross-bot monitor admin panel (bot1, owner-only). Old standalone-script
# command name -> new namespaced name, for anyone used to the original script:
#   /addchannel -> /xbotaddchannel   /removechannel -> /xbotremovechannel
#   /channellist -> /xbotchannels    /setbot -> /xbotsetbot
#   /listbots -> /xbotbots           /removebot -> /xbotremovebot
#   /set -> /xbotsetsession          /scanchannel -> /xbotscan
#   /setchannel -> /xbotresync       /status -> /xbotstatus
# ==========================================
XBOT_VALID_SOURCE_TYPES = ["catch_bot", "obtain_bot", "poll_bot", "unknown"]

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotaddchannel\s+(-?\d+)\s+(\w+)$', 'bot1')))
async def xbot_add_channel_command(event):
    if event.sender_id != OWNER_ID:
        return
    chat_id = int(event.pattern_match.group(1))
    source_bot = event.pattern_match.group(2)
    if source_bot not in XBOT_VALID_SOURCE_TYPES:
        return await event.reply(f"❌ Invalid bot type. Choose: {', '.join(XBOT_VALID_SOURCE_TYPES)}")
    await monitored_channels_col.update_one(
        {"chat_id": chat_id},
        {"$set": {"source_bot": source_bot, "added_at": time.time()}},
        upsert=True
    )
    monitored_chat_ids.add(chat_id)
    monitored_chat_map[chat_id] = source_bot
    await event.reply(f"✅ Channel <code>{chat_id}</code> added (type: {source_bot})", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotremovechannel\s+(-?\d+)$', 'bot1')))
async def xbot_remove_channel_command(event):
    if event.sender_id != OWNER_ID:
        return
    chat_id = int(event.pattern_match.group(1))
    await monitored_channels_col.delete_one({"chat_id": chat_id})
    monitored_chat_ids.discard(chat_id)
    monitored_chat_map.pop(chat_id, None)
    await event.reply(f"✅ Channel <code>{chat_id}</code> removed", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotchannels$', 'bot1')))
async def xbot_channel_list_command(event):
    if event.sender_id != OWNER_ID:
        return
    docs = await monitored_channels_col.find({}).to_list(length=None)
    if not docs:
        return await event.reply("📭 No channels monitored yet. Use /xbotaddchannel")
    text = "📋 <b>Monitored Channels</b>\n\n"
    for doc in docs:
        added = datetime.fromtimestamp(doc.get("added_at", time.time())).strftime("%Y-%m-%d")
        text += f"• <code>{doc.get('chat_id')}</code> → {doc.get('source_bot', 'unknown')} (added: {added})\n"
    await event.reply(text, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotsetbot\s+(\d+)\s+(\w+)$', 'bot1')))
async def xbot_set_bot_mapping_command(event):
    if event.sender_id != OWNER_ID:
        return
    bot_id = int(event.pattern_match.group(1))
    source_bot = event.pattern_match.group(2)
    if source_bot not in ("catch_bot", "obtain_bot", "poll_bot"):
        return await event.reply("❌ Invalid bot type. Choose: catch_bot, obtain_bot, poll_bot")
    await set_bot_mapping(bot_id, source_bot)
    await event.reply(f"✅ Bot <code>{bot_id}</code> → {source_bot}", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotbots$', 'bot1')))
async def xbot_list_bots_command(event):
    if event.sender_id != OWNER_ID:
        return
    docs = await bot_mapping_col.find({}).to_list(length=None)
    if not docs:
        return await event.reply("📭 No bots mapped yet. Use /xbotsetbot")
    text = "🤖 <b>Bot ID Mapping</b>\n\n"
    for doc in docs:
        updated = datetime.fromtimestamp(doc.get("updated_at", time.time())).strftime("%Y-%m-%d")
        text += f"• <code>{doc.get('bot_id')}</code> → {doc.get('source_bot', 'unknown')} (updated: {updated})\n"
    await event.reply(text, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotremovebot\s+(\d+)$', 'bot1')))
async def xbot_remove_bot_mapping_command(event):
    if event.sender_id != OWNER_ID:
        return
    bot_id = int(event.pattern_match.group(1))
    await bot_mapping_col.delete_one({"bot_id": bot_id})
    bot_mapping_cache.pop(bot_id, None)
    await event.reply(f"✅ Bot <code>{bot_id}</code> removed from mapping", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotsetsession\s+(.+)$', 'bot1')))
async def xbot_set_session_handler(event):
    global monitor_userbot
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this command in DM only — it carries a login session string.")
    session_str = event.pattern_match.group(1).strip()
    if len(session_str) < 10:
        return await event.reply("❌ That doesn't look like a valid String Session.")
    await bot_settings_col.update_one(
        {"_id": "xbot_monitor_session"},
        {"$set": {"session": session_str}},
        upsert=True
    )
    await event.reply("✅ Session saved. Restarting the monitor userbot...")
    try:
        if monitor_userbot and monitor_userbot.is_connected():
            await monitor_userbot.disconnect()
        client = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
        await client.start()
        me = await client.get_me()
        register_userbot_handlers(client)
        asyncio.create_task(client.run_until_disconnected())
        monitor_userbot = client
        await event.reply(f"✅ Monitor userbot connected as @{me.username if me.username else me.id}")
    except Exception as e:
        await event.reply(f"❌ Couldn't start the monitor userbot: {escape_html(str(e))}", parse_mode='html')

# ==========================================
# 📦 BULK HISTORICAL IMPORT — /xbotimportall walks a channel's ENTIRE history (not just new
# posts going forward) and auto-imports every "added new Character" found, same as the live
# listener does. Built deliberately SLOW and RESUMABLE (per owner request):
#   • Paced with BULK_IMPORT_DELAY_SECONDS between every message, however many thousand
#     characters this ends up being — gentle on Telegram, Mongo, and bot1's own
#     responsiveness to everyone else the whole time. Taking most of a day is expected, not a
#     problem.
#   • Progress is checkpointed to bot_settings_col after every message. If the bot process
#     restarts for ANY reason mid-run (deploy, crash, host restart), load_and_start_monitor_
#     userbot() below notices the unfinished job at startup and resumes it automatically from
#     the checkpoint — the owner never has to notice or re-trigger it by hand.
#   • Runs as a background asyncio task the whole time — bot1 keeps handling every other
#     command normally throughout, this never blocks the event loop.
# ==========================================
BULK_IMPORT_DELAY_SECONDS = 1  # 🩹 CHANGED (per owner request): was 3s — lowered since
# auto_import_character_from_catchbot now waits out a FloodWaitError properly (however long
# Telegram actually asks for) instead of just relying on a conservative fixed gap to avoid
# one. If real flooding does happen at this pace, it's handled by waiting, not by erroring.
_bulk_import_active = False  # in-memory guard against starting a second overlapping run
_bulk_import_cancel_requested = False  # checked inside the loop below — see xbot_import_cancel_command

def _bulk_import_counts_lines(counts: dict) -> str:
    """🩹 FIX (per owner report — 'characters get skipped and I don't know why, maybe flood?'):
    skipped_no_media and skipped_bad_rarity used to not be counted ANYWHERE in the bulk
    import's progress/summary — checked went up, but if a character fell into either of those
    buckets it just silently vanished from every visible total, with no way to tell it had
    even happened let alone why. Every possible outcome is shown now, so a real, systemic skip
    reason (e.g. a rarity name that isn't in our 9 tiers) is now visible immediately instead of
    being mistaken for random flakiness."""
    lines = [
        f"📨 Checked: {counts.get('checked', 0)}",
        f"🆕 Imported: {counts.get('imported', 0)}",
        f"⏭️ Already had: {counts.get('skipped_duplicate', 0)}",
    ]
    if counts.get('skipped_no_media'):
        lines.append(f"🖼️ Skipped (no media): {counts['skipped_no_media']}")
    if counts.get('skipped_bad_rarity'):
        lines.append(f"🏷️ Skipped (unrecognized rarity): {counts['skipped_bad_rarity']}")
    if counts.get('errors'):
        lines.append(f"⚠️ Errors: {counts['errors']}")
    return "\n".join(lines)

async def _run_bulk_import(chat_ids, status_chat_id=None, status_msg_id=None):
    global _bulk_import_active, _bulk_import_cancel_requested
    if _bulk_import_active:
        return  # a run is already in progress (e.g. resumed at startup) — never overlap two
    _bulk_import_active = True
    _bulk_import_cancel_requested = False
    state = await bot_settings_col.find_one({"_id": "xbot_bulk_import_state"}) or {}
    counts = {
        "checked": state.get("checked", 0), "imported": state.get("imported", 0),
        "skipped_duplicate": state.get("skipped_duplicate", 0),
        "skipped_no_media": state.get("skipped_no_media", 0),
        "skipped_bad_rarity": state.get("skipped_bad_rarity", 0),
        "errors": state.get("errors", 0)
    }
    await bot_settings_col.update_one(
        {"_id": "xbot_bulk_import_state"},
        {"$set": {"active": True, "chat_ids": chat_ids, "started_at": state.get("started_at", time.time()), **counts}},
        upsert=True
    )
    try:
        for chat_id in chat_ids:
            if _bulk_import_cancel_requested:
                break
            source_bot = monitored_chat_map.get(chat_id, "unknown")
            state = await bot_settings_col.find_one({"_id": "xbot_bulk_import_state"})
            resume_id = state.get("last_processed_msg_id") if state and state.get("current_chat_id") == chat_id else None
            await bot_settings_col.update_one({"_id": "xbot_bulk_import_state"}, {"$set": {"current_chat_id": chat_id}})
            kwargs = {"reverse": True}  # oldest first — same reasoning as /xbotresync
            if resume_id:
                kwargs["min_id"] = resume_id
            async for msg in monitor_userbot.iter_messages(chat_id, **kwargs):
                if _bulk_import_cancel_requested:
                    break
                counts["checked"] += 1
                caption = msg.raw_text or ""
                if "added new Character" in caption:
                    result = await auto_import_character_from_catchbot(msg, chat_id, source_bot, silent=True)
                    if result == "imported":
                        counts["imported"] += 1
                    elif result == "skipped_duplicate":
                        counts["skipped_duplicate"] += 1
                    elif result == "skipped_no_media":
                        counts["skipped_no_media"] += 1
                    elif result == "skipped_bad_rarity":
                        counts["skipped_bad_rarity"] += 1
                    elif result == "error":
                        counts["errors"] += 1
                await bot_settings_col.update_one(
                    {"_id": "xbot_bulk_import_state"},
                    {"$set": {"last_processed_msg_id": msg.id, **counts}}
                )
                if status_chat_id and status_msg_id and counts["checked"] % 25 == 0:
                    try:
                        await bot1.edit_message(
                            status_chat_id, status_msg_id,
                            f"⏳ <b>Bulk import running…</b> (paced — this can take a while, that's expected)\n"
                            f"{_bulk_import_counts_lines(counts)}",
                            parse_mode='html'
                        )
                    except Exception:
                        pass
                await asyncio.sleep(BULK_IMPORT_DELAY_SECONDS)
    except Exception as e:
        await report_system_error("_run_bulk_import", str(e))
    finally:
        was_cancelled = _bulk_import_cancel_requested
        _bulk_import_active = False
        await bot_settings_col.update_one({"_id": "xbot_bulk_import_state"}, {"$set": {"active": False}})
    if was_cancelled:
        summary = (
            f"🛑 <b>Bulk import stopped</b> (checkpoint saved — /xbotimportall will resume from here)\n"
            f"{_bulk_import_counts_lines(counts)}"
        )
    else:
        summary = (
            f"✅ <b>Bulk import complete!</b>\n"
            f"{_bulk_import_counts_lines(counts)}"
        )
    try:
        if status_chat_id and status_msg_id:
            await bot1.edit_message(status_chat_id, status_msg_id, summary, parse_mode='html')
        else:
            await bot1.send_message(OWNER_ID, summary, parse_mode='html')
    except Exception:
        await bot1.send_message(OWNER_ID, summary, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotimportall(?:\s+(-?\d+))?$', 'bot1')))
async def xbot_import_all_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not monitor_userbot or not monitor_userbot.is_connected():
        return await event.reply("❌ Monitor userbot isn't connected. Use /xbotsetsession first.")
    if _bulk_import_active:
        return await event.reply("⏳ A bulk import is already running. Use /xbotimportstatus to check progress.")
    target_chat_id = event.pattern_match.group(1)
    if target_chat_id:
        target_chat_id = int(target_chat_id)
        if target_chat_id not in monitored_chat_ids:
            return await event.reply(f"❌ Channel <code>{target_chat_id}</code> isn't monitored. Use /xbotaddchannel first.", parse_mode='html')
        chat_ids = [target_chat_id]
    else:
        if not monitored_chat_ids:
            return await event.reply("❌ No channels monitored yet. Use /xbotaddchannel first.")
        chat_ids = list(monitored_chat_ids)
    # Fresh start (not a resume) — clear any stale checkpoint from a previous completed/different run.
    await bot_settings_col.update_one(
        {"_id": "xbot_bulk_import_state"},
        {"$set": {"active": True, "chat_ids": chat_ids, "current_chat_id": None, "last_processed_msg_id": None,
                   "checked": 0, "imported": 0, "skipped_duplicate": 0, "errors": 0, "started_at": time.time()}},
        upsert=True
    )
    status_msg = await event.reply(
        f"⏳ <b>Starting bulk import</b> across {len(chat_ids)} channel(s)...\n"
        f"Paced at {BULK_IMPORT_DELAY_SECONDS}s/message — this is expected to take a while "
        f"(hours, possibly most of a day for a large history). If the bot restarts for any "
        f"reason, it'll pick back up right where it left off automatically.",
        parse_mode='html'
    )
    asyncio.create_task(_run_bulk_import(chat_ids, status_chat_id=event.chat_id, status_msg_id=status_msg.id))

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotimportstatus$', 'bot1')))
async def xbot_import_status_command(event):
    if event.sender_id != OWNER_ID:
        return
    state = await bot_settings_col.find_one({"_id": "xbot_bulk_import_state"})
    if not state:
        return await event.reply("📭 No bulk import has been run yet.")
    running = "🟢 running" if _bulk_import_active else ("🟡 marked active (will resume on next restart)" if state.get("active") else "⚪ finished")
    await event.reply(
        f"📦 <b>Bulk Import Status</b>\n"
        f"Status: {running}\n"
        f"{_bulk_import_counts_lines(state)}\n"
        f"📍 Current channel: <code>{state.get('current_chat_id')}</code>",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotimportcancel$', 'bot1')))
async def xbot_import_cancel_command(event):
    global _bulk_import_cancel_requested
    if event.sender_id != OWNER_ID:
        return
    if not _bulk_import_active:
        return await event.reply("📭 No bulk import is currently running.")
    _bulk_import_cancel_requested = True
    await event.reply(
        "🛑 Marked for stop. It'll finish its current message (within "
        f"{BULK_IMPORT_DELAY_SECONDS}s) and then stop — the checkpoint is saved, so "
        "/xbotimportall will resume from here next time you run it."
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotscan(?:\s+(-?\d+))?$', 'bot1')))
async def xbot_scan_channel_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM.")
    if not monitor_userbot or not monitor_userbot.is_connected():
        return await event.reply("❌ Monitor userbot isn't connected. Use /xbotsetsession first.")
    target_chat_id = event.pattern_match.group(1)
    if target_chat_id:
        target_chat_id = int(target_chat_id)
        if target_chat_id not in monitored_chat_ids:
            return await event.reply(f"❌ Channel <code>{target_chat_id}</code> isn't monitored. Use /xbotaddchannel first.", parse_mode='html')
        chat_ids_to_scan = [target_chat_id]
        status = await event.reply(f"⏳ Scanning channel <code>{target_chat_id}</code>...", parse_mode='html')
    else:
        if not monitored_chat_ids:
            return await event.reply("❌ No channels monitored yet. Use /xbotaddchannel first.")
        chat_ids_to_scan = list(monitored_chat_ids)
        status = await event.reply(f"⏳ Scanning all {len(chat_ids_to_scan)} channels...")
    total_checked = total_found = 0
    for chat_id in chat_ids_to_scan:
        source_bot = monitored_chat_map.get(chat_id, "unknown")
        checked = found = 0
        try:
            # reverse=True: oldest first — matters when a character's been renamed more than
            # once, so the LAST rename processed is the actually-current name.
            async for msg in monitor_userbot.iter_messages(chat_id, reverse=True):
                checked += 1
                total_checked += 1
                if checked % 50 == 0:
                    try:
                        await status.edit(f"⏳ Scanning <code>{chat_id}</code>...\n📨 Checked: {checked}\n✅ Found: {found}", parse_mode='html')
                    except Exception:
                        pass
                caption = msg.raw_text or ""
                # 🩹 FIX: rename/event/rarity/image-update posts used to be invisible to
                # /xbotscan entirely — it only ever called extract_all_names_from_caption,
                # which doesn't parse any of those formats. Checked here now, same as the
                # live listeners. Deliberately NOT auto-importing brand-new characters here
                # (see auto_import_character_from_catchbot's own call site) — a bulk scan
                # replaying catch_bot's ENTIRE history would otherwise mass-import its whole
                # roster the moment anyone runs a routine /xbotscan.
                if await _maybe_sync_catchbot_character_change(msg, chat_id, caption):
                    found += 1
                    total_found += 1
                    continue
                if not (msg.photo or msg.video):
                    continue
                names = extract_all_names_from_caption(caption, source_bot)
                if not names:
                    continue
                hash_val = await compute_phash_for_message(msg)
                if not hash_val:
                    continue
                for name in names:
                    if await store_xbot_character_hash(hash_val, name, caption, chat_id, msg.id, source_bot):
                        found += 1
                        total_found += 1
                await asyncio.sleep(0.1)
        except Exception as e:
            print(f"xbot scan error for {chat_id}: {e}")
    await status.edit(f"✅ <b>Scan Complete!</b>\n📨 Checked: {total_checked}\n🎯 Found: {total_found}", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotresync(?:\s+(-?\d+))?$', 'bot1')))
async def xbot_resync_channel_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM.")
    if not monitor_userbot or not monitor_userbot.is_connected():
        return await event.reply("❌ Monitor userbot isn't connected. Use /xbotsetsession first.")
    target_chat_id = event.pattern_match.group(1)
    if target_chat_id:
        target_chat_id = int(target_chat_id)
        if target_chat_id not in monitored_chat_ids:
            return await event.reply(f"❌ Channel <code>{target_chat_id}</code> isn't monitored.", parse_mode='html')
        chat_ids_to_scan = [target_chat_id]
        status = await event.reply(f"⏳ Resetting channel <code>{target_chat_id}</code>...", parse_mode='html')
    else:
        if not monitored_chat_ids:
            return await event.reply("❌ No channels monitored yet.")
        chat_ids_to_scan = list(monitored_chat_ids)
        status = await event.reply(f"⏳ Resetting all {len(chat_ids_to_scan)} channels...")
    total_checked = total_updated = 0
    for chat_id in chat_ids_to_scan:
        source_bot = monitored_chat_map.get(chat_id, "unknown")
        checked = updated = 0
        try:
            await xbot_hashes_col.delete_many({"chat_id": chat_id})
            # reverse=True: oldest first — matters when a character's been renamed more than
            # once, so the LAST rename processed is the actually-current name.
            async for msg in monitor_userbot.iter_messages(chat_id, reverse=True):
                checked += 1
                total_checked += 1
                if checked % 50 == 0:
                    try:
                        await status.edit(f"⏳ Resetting <code>{chat_id}</code>...\n📨 Checked: {checked}\n✅ Updated: {updated}", parse_mode='html')
                    except Exception:
                        pass
                caption = msg.raw_text or ""
                # 🩹 FIX: same gap as /xbotscan — rename/event/rarity/image-update posts were
                # invisible here before. Same no-auto-import-during-bulk-replay reasoning too.
                if await _maybe_sync_catchbot_character_change(msg, chat_id, caption):
                    updated += 1
                    total_updated += 1
                    continue
                if not (msg.photo or msg.video):
                    continue
                names = extract_all_names_from_caption(caption, source_bot)
                if not names:
                    continue
                hash_val = await compute_phash_for_message(msg)
                if not hash_val:
                    continue
                for name in names:
                    await store_xbot_character_hash(hash_val, name, caption, chat_id, msg.id, source_bot)
                    updated += 1
                    total_updated += 1
                await asyncio.sleep(0.1)
        except Exception as e:
            print(f"xbot resync error for {chat_id}: {e}")
    await status.edit(f"✅ <b>Resync Complete!</b>\n📨 Checked: {total_checked}\n🔄 Re-indexed: {total_updated}", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotstatus$', 'bot1')))
async def xbot_status_command(event):
    if event.sender_id != OWNER_ID:
        return
    total = await xbot_hashes_col.count_documents({})
    chat_stats = await xbot_hashes_col.aggregate([{"$group": {"_id": "$chat_id", "count": {"$sum": 1}}}]).to_list(length=None)
    bot_stats = await xbot_hashes_col.aggregate([{"$group": {"_id": "$source_bot", "count": {"$sum": 1}}}]).to_list(length=None)
    text = f"📊 <b>Cross-Bot Monitor Status</b>\n📦 Total: <code>{total}</code>\n\n📋 <b>By Channel:</b>\n"
    for stat in chat_stats:
        text += f"  • <code>{stat.get('_id') or 'unknown'}</code>: {stat.get('count', 0)}\n"
    text += "\n🤖 <b>By Bot Type:</b>\n"
    for stat in bot_stats:
        text += f"  • {stat.get('_id') or 'unknown'}: {stat.get('count', 0)}\n"
    text += f"\n🔌 Userbot connected: {'✅' if (monitor_userbot and monitor_userbot.is_connected()) else '❌'}"
    await event.reply(text, parse_mode='html')


# ---- CATCH LOGIC (with daily limit and spawn_count increment on success) ----
DAILY_CATCH_LIMIT = 22  # flat cap for everyone — single source of truth, used by both the
# limit check in catch_handler and the /today "who hit the limit first" ranking below.

async def perform_catch(chat_id, user_id, spawn_data, event, reply_to_msg=None, is_callback=False, temp_msg_id=None):
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    try:
        updated_user = await users_catcher_col.find_one_and_update(
            {"user_id": user_id},
            {
                "$push": {
                    "harem": {
                        "char_id": spawn_data['char_id'],
                        "caught_date": time.time(),
                        "rarity": spawn_data['rarity'],
                        "status": "vault",
                        "chat_id": chat_id
                    }
                },
                "$inc": {
                    "total_caught": 1,
                    f"group_catches.{str(chat_id)}": 1,
                    "daily_catches": 1
                },
                "$set": {"fullname": plain_name, "last_catch_date": datetime.now(TZ)}
            },
            upsert=True,
            return_document=ReturnDocument.AFTER
        )
        effective_limit = DAILY_CATCH_LIMIT
        if updated_user and updated_user.get("daily_catches") == effective_limit:
            await users_catcher_col.update_one(
                {"user_id": user_id, "daily_limit_hit_at": {"$exists": False}},
                {"$set": {"daily_limit_hit_at": datetime.now(TZ)}}
            )
        await characters_base_col.update_one(
            {"char_id": spawn_data['char_id']},
            {"$inc": {"spawn_count": 1}}
        )
        # ✅ New code: get category stats
        category = spawn_data.get('category', 'Unknown')
        cat_char_ids = await characters_base_col.distinct("char_id", {"category": category})
        owned_harem_set = {item.get("char_id") for item in updated_user.get("harem", []) if isinstance(item, dict) and item.get("char_id")}
        owned_in_cat = sum(1 for cid in cat_char_ids if cid in owned_harem_set)
        total_in_cat = len(cat_char_ids)
        cat_display = f"🏖️ Aɴɪᴍᴇ: {escape_html(category)} ({owned_in_cat}/{total_in_cat})"

        # ✅ New message format
        character_name = spawn_data['name']
        rarity_tier = classify_rarity(spawn_data['rarity'])
        rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
        # Remove 'No.X' from rarity display
        rarity_display = strip_rarity_number(spawn_data['rarity'])

        success_msg = (
            f"🪷 {mention}, ʏᴏᴜ ꜰᴜᴄᴋᴇᴅ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!\n\n"
            f"🫧 Nᴀᴍᴇ: {escape_html(character_name)} | 🐧 {display_char_id(spawn_data['char_id'])}\n"
            f"{rarity_emoji} {RARITY_LABEL_STYLED}: {rarity_display}\n"
            f"{cat_display}\n\n"
            f"👒 ᴄʜᴇᴄᴋ ʏᴏᴜʀ /harem!"
        )

        # ✅ အောင်မြင်မှုဆုတွေ ရှိရင် ထည့်ပေးမယ်
        newly_earned = await check_and_award_achievements(user_id)
        if newly_earned:
            success_msg += format_achievement_unlocks(newly_earned)

        success_buttons = [[
            Button.switch_inline("🤍 harem", query=f"harem.{user_id}", same_peer=True),
            Button.inline("◈ profile", data=f"catchprofile_{user_id}")
        ]]

        if chat_id in active_group_spawns: 
            del active_group_spawns[chat_id]
        if chat_id in spawn_locks: 
            del spawn_locks[chat_id]

        if is_callback:
            await bot1.send_message(chat_id, success_msg, reply_to=reply_to_msg or event.message_id, parse_mode='html', buttons=success_buttons)
        elif temp_msg_id:
            try:
                await bot1.edit_message(chat_id, temp_msg_id, success_msg, parse_mode='html', buttons=success_buttons)
            except errors.MessageNotModifiedError:
                pass
            except Exception:
                await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
        else:
            await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
        return True
    except Exception as e:
        if chat_id in active_group_spawns: 
            del active_group_spawns[chat_id]
        if chat_id in spawn_locks: 
            del spawn_locks[chat_id]
        error_msg = f"❌ <b>Catch Logic Fault:</b> {e}"
        if is_callback:
            await bot1.send_message(chat_id, error_msg, parse_mode='html')
        else:
            await event.reply(error_msg, parse_mode='html')
        return False

CATCH_USAGE_TEXT = (
    "📌 <b>Usage:</b> <code>/fuck [Character Name]</code>\n"
    "<i>◈ say my name exactly, or whisper /who and I'll tell you… "
    "or just tap the button.</i>"
)

# 🩹 CHANGED (per owner request): /obtain renamed to /fuck for the bot's cute-anime-wifey
# tone. /obtain (and the .obtain dot-form) still work as a legacy alias, and /collect is
# still retired (a different, unrelated bot in the same groups uses that name — see below).
# /morgan stays as its own separate fun alias, unrelated to this rename.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:morgan|fuck|fuck)(?:@\w+)?\s+(.*)$', 'bot1')))
async def catch_handler(event):
    if event.is_private: return
    user_id = event.sender_id
    chat_id = event.chat_id
    # Check spam mute — GLOBALLY, across every group.
    # 🩹 FIX (per owner report — "the biggest bug"): same fix as /who above — no repeated
    # "you're muted" reply on every retry, just silence. spam_detection_and_mute already sent
    # the one real notice when the mute first triggered.
    if user_id in user_mute_until and time.time() < user_mute_until[user_id]:
        return
    
    catch_name = event.pattern_match.group(1).strip()
    if not catch_name:
        return await event.reply(CATCH_USAGE_TEXT, parse_mode='html')

    # ==========================================
    # 🛸 NORMAL SPAWN CATCH LOGIC
    # ==========================================
    if chat_id not in active_group_spawns:
        return await event.reply(f"🛸 <b>…there's no one here for you right now.</b>", parse_mode='html')
    
    spawn_data = active_group_spawns[chat_id]
    if spawn_data["claimed"]:
        return await _reply_already_caught(event, spawn_data)
    
    if time.time() - spawn_data["spawn_time"] > 300:
        if chat_id in active_group_spawns: 
            del active_group_spawns[chat_id]
        return await event.reply(f"⏱️ <b>…too late. I already slipped away.</b>", parse_mode='html')
    
    if normalize_name(catch_name) != normalize_name(spawn_data["name"]):
        return await event.reply(f"❌ <b>…that's not my name. whisper /who and try again.</b>", parse_mode='html')

    # Daily limit check — done BEFORE the claim below, so a user who's already capped out
    # doesn't burn the community spawn on themselves; it stays up for someone who can catch it.
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if user_doc:
        today = datetime.now(TZ).date()
        last_catch_date = user_doc.get("last_catch_date")
        if last_catch_date:
            last_date = last_catch_date.date() if isinstance(last_catch_date, datetime) else last_catch_date
            if last_date != today:
                await users_catcher_col.update_one(
                    {"user_id": user_id},
                    {"$set": {"daily_catches": 0, "last_catch_date": datetime.now(TZ)},
                     "$unset": {"daily_limit_hit_at": ""}}
                )
                user_doc["daily_catches"] = 0
        daily_catches = user_doc.get("daily_catches", 0)
        daily_limit = DAILY_CATCH_LIMIT
        if daily_catches >= daily_limit:
            mention = await get_html_mention(event, user_id)
            return await event.reply(
                f"<b>…</b> {mention}, you've had enough of me for today — {daily_limit} is your limit. "
                f"come back tomorrow 🤍",
                parse_mode='html'
            )

    # 🔒 Claim the spawn atomically — check-and-set with no await in between, under the
    # per-chat lock — BEFORE replying to anyone. This is what fixes the freeze: no matter
    # how many people type the right name in the same second, only ONE coroutine ever gets
    # past this point. Everyone else bounces off right here with one cheap message — no
    # placeholder, no 2.5s wait, no daily-limit read, no DB writes — so a burst of racers
    # no longer turns into a wall of messages and a pile of simultaneous catch attempts.
    async with spawn_locks[chat_id]:
        spawn_data = active_group_spawns.get(chat_id)
        if not spawn_data or spawn_data.get("claimed"):
            return await _reply_already_caught(event, spawn_data)
        spawn_data["claimed"] = True
        spawn_data["claimed_by"] = user_id

    # 🐛→🦋 catching animation: one message, edited in place frame-by-frame — no extra
    # replies sent, and perform_catch() below edits this same message into the final result
    # (instead of deleting it and sending a new one).
    # 🩹 CHANGED (per owner request): this used to be event.reply("💫") — a REPLY to the
    # racer's own /obtain message, which meant onlookers could see (via the reply preview)
    # who was in the running before the result was ever revealed. Sent as a plain message now,
    # so nobody knows who's even attempting it until the final edit reveals the winner.
    temp_msg = await bot1.send_message(chat_id, "⚡️")
    await asyncio.sleep(1)
    try:
        await temp_msg.edit("💥")
    except errors.MessageNotModifiedError:
        pass
    await asyncio.sleep(1)
    await perform_catch(chat_id, user_id, spawn_data, event, reply_to_msg=event.id, is_callback=False, temp_msg_id=temp_msg.id)

async def _reply_already_caught(event, spawn_data):
    """Short, English, tells whoever lost the race exactly who beat them — replaces the old
    generic 'Already caught!' which left everyone guessing."""
    winner_id = (spawn_data or {}).get("claimed_by")
    if winner_id:
        mention = await get_html_mention(event, winner_id)
        text = f"…too late. {mention} already made me theirs."
    else:
        text = "❌ <b>…someone already claimed me.</b>"
    return await event.reply(text, parse_mode='html')
# ---- /refillcatch: recompute spawn_count from what's ACTUALLY in players' vaults ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]refillcatch(?:@\w+)?(?:\s+([a-zA-Z0-9_]+))?$', 'bot1')))
async def refillcatch_handler(event):
    if event.sender_id != OWNER_ID:
        return
    char_id_arg = event.pattern_match.group(1)
    status_msg = await event.reply("⏳ <b>Recalculating catch counts from real vault data...</b>", parse_mode='html')
    if char_id_arg:
        char_id_arg = char_id_arg.upper()
        char_doc = await characters_base_col.find_one({"char_id": char_id_arg})
        if not char_doc:
            return await status_msg.edit(f"❌ No character found with ID <code>{escape_html(char_id_arg)}</code>.", parse_mode='html')
        pipeline = [
            {"$unwind": "$harem"},
            {"$match": {"harem.char_id": char_id_arg}},
            {"$count": "total"}
        ]
        result = await users_catcher_col.aggregate(pipeline).to_list(length=1)
        real_count = result[0]["total"] if result else 0
        await characters_base_col.update_one({"char_id": char_id_arg}, {"$set": {"spawn_count": real_count}})
        await invalidate_character_caches()
        await status_msg.edit(
            f"✅ <b>{escape_html(char_doc['name'])}</b> (<code>{char_id_arg}</code>) synced!\n"
            f"📈 <b>Global Catches (real):</b> <code>{real_count}</code>",
            parse_mode='html'
        )
    else:
        pipeline = [
            {"$unwind": "$harem"},
            {"$group": {"_id": "$harem.char_id", "count": {"$sum": 1}}}
        ]
        results = await users_catcher_col.aggregate(pipeline).to_list(length=None)
        counts_map = {r["_id"]: r["count"] for r in results if r.get("_id")}
        all_chars = await characters_base_col.find({}, {"char_id": 1}).to_list(length=None)
        ops = [
            UpdateOne({"char_id": c["char_id"]}, {"$set": {"spawn_count": counts_map.get(c["char_id"], 0)}})
            for c in all_chars
        ]
        if ops:
            await characters_base_col.bulk_write(ops)
        await invalidate_character_caches()
        await status_msg.edit(
            f"✅ <b>Full Resync Complete!</b>\n"
            f"🔁 <code>{len(ops)}</code> characters' Global Catch counts now match players' real vaults.",
            parse_mode='html'
        )

# ==========================================
# 🎯 HMODE – RARITY FILTER
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]hmode(?:@\w+)?$', 'bot1')))
async def set_rarity_filter_handler(event):
    user_id = event.sender_id
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    current_filter = user_doc.get("rarity_filter") if user_doc else None
    # 🩹 FIX: was 9 full-width rows (one per rarity), each showing the whole fancy-font name
    # like "🎞 𝖴𝖫𝖳𝖱𝖠𝖲𝖳𝖠𝖱 𝖭𝗈.𝟣" — ate a huge amount of vertical space in the chat. Now a
    # compact 2x2 grid, emoji-only per button; the current selection still gets a ✅ prefix
    # so it stays recognizable even without the text label.
    buttons = []
    row = []
    for num, data in RARITY_NUM_MAP.items():
        tier = RARITY_TIERS[int(num) - 1]
        emoji = RARITY_EMOJI[tier]
        rarity_name = data["name"]
        label = f"✅{emoji}" if current_filter == rarity_name else emoji
        row.append(Button.inline(label, data=f"hfilter_{num}_{user_id}"))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    clear_label = "🔓 Clear Filter" if current_filter else "🔒 No Filter"
    buttons.append([Button.inline(clear_label, data=f"hfilter_clear_{user_id}")])
    buttons.append([Button.inline("🔙 Back", data="nav_back_home")])
    await event.reply(
        f"◈ <b>who do you want to see in /harem?</b>\n"
        f"Current: {current_filter if current_filter else 'None (Show All)'}\n\n"
        f"…tap a rarity to filter, or clear to see everyone\n"
        f"<i>🔐 Only you can use these buttons.</i>",
        buttons=buttons,
        parse_mode='html'
    )

@bot1.on(events.CallbackQuery(pattern=r'^hfilter_(\d+|clear)_(\d+)$'))
async def rarity_filter_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    owner_user_id = int(event.pattern_match.group(2))
    if event.sender_id != owner_user_id:
        return await event.answer("⚠️ ဒါက သင့်ရဲ့ Rarity Filter မဟုတ်ပါ။ /hmode ကို ကိုယ်တိုင်နှိပ်ပါ။", alert=True)
    user_id = owner_user_id
    if action == "clear":
        await users_catcher_col.update_one(
            {"user_id": user_id},
            {"$set": {"rarity_filter": None}},
            upsert=True
        )
        await event.answer("…filter cleared. I'll show you everyone~")
        await event.edit("✅ Filter cleared. Use /harem to see everyone again.")
        return
    rarity_num = action
    rarity_data = RARITY_NUM_MAP.get(rarity_num)
    if not rarity_data:
        await event.answer("❌ Invalid rarity.")
        return
    rarity_name = rarity_data["name"]
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$set": {"rarity_filter": rarity_name}},
        upsert=True
    )
    await event.answer(f"…now showing {rarity_name} first")
    await event.edit(f"✅ Filter set to {rarity_name}. Use /harem to see them.")

# ==========================================
# 🎒 INVENTORY / HAREM
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]harem(?:@\w+)?(?:\s+(.*))?$', 'bot1')))
async def show_harem_vault(event):
    # 🩹 CHANGED (per owner request): /harem used to let anyone view someone ELSE's vault by
    # replying to their message or passing @username/user_id — that's removed now. /harem
    # always shows the sender's own vault, full stop. Any argument/reply is simply ignored.
    user_id = event.sender_id
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    await send_paginated_harem(bot1, event.chat_id, user_id, page=1, viewer_id=user_id)

# ---- /fav bare usage ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]fav(?:@\w+)?$', 'bot1')))
async def fav_bare_usage_handler(event):
    await event.reply(
        "📌 <b>Usage:</b> <code>/fav [CharID]</code>\n"
        "<i>Example:</i> <code>/fav 1234</code>\n"
        "◈ pick your favorite of us to show off on <code>/harem</code>…",
        parse_mode='html'
    )

# ---- /fav with inline confirmation ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]fav(?:@\w+)?\s+([a-zA-Z0-9_]+)$', 'bot1')))
async def set_favorite_card(event):
    user_id = event.sender_id
    raw_input = event.pattern_match.group(1).strip()
    char_id_input = normalize_char_id_input(raw_input)
    
    # ✅ Case-Insensitive ရှာဖို့
    card = await characters_base_col.find_one({
        "char_id": {"$regex": f"^{char_id_input}$", "$options": "i"}
    })
    
    if not card:
        # ✅ အနီးဆုံး ID တွေကို ပြပေးမယ် (raw input သုံးမယ် — BOD ကို prepend လုပ်ထားတဲ့ char_id_input သုံးရင် အကုန် "BOD" နဲ့ စတော့ fuzzy match အလုပ်မလုပ်တော့ဘူး)
        similar = await characters_base_col.find(
            {"char_id": {"$regex": re.escape(raw_input[:3]), "$options": "i"}}
        ).limit(5).to_list(length=5)
        reply = f"❌ <b>…I don't know anyone with that ID.</b>\n\n"
        if similar:
            reply += "💡 <b>Did you mean:</b>\n"
            for s in similar:
                reply += f"• <code>{display_char_id(s['char_id'])}</code> - {s.get('name', 'Unknown')}\n"
        else:
            reply += "📭 …couldn't find anyone close to that."
        return await event.reply(reply, parse_mode='html')
    
    # ✅ Card ကိုတွေ့ရင် ဆက်လုပ်ပါ
    actual_char_id = card["char_id"]  # Database ထဲက အတိအကျ ID
    
    if user_id == OWNER_ID or user_id in added_owner_ids:
        # 👑 Unlimited vault — every character counts as owned, no harem lookup needed.
        owns_card = True
    else:
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        user_harem = user_doc.get("harem", []) if user_doc else []
        owns_card = any(isinstance(x, dict) and x.get("char_id").upper() == actual_char_id.upper() for x in user_harem)
    
    if not owns_card:
        return await event.reply(f"❌ <b>…she's not yours yet. catch her first.</b>", parse_mode='html')
    
    # ✅ Confirmation Buttons
    confirm_text = (
        f"◈ <b>pick her as your favorite?</b>\n\n"
        f"🦢 <b>Character:</b> <code>{card['name']}</code> (<code>{display_char_id(actual_char_id)}</code>)\n"
        f" <b>Rarity:</b> {card.get('rarity', 'Unknown')}\n"
        f"{artist_line(card)}\n"
        f"…she'd be the one showing up in your /harem"
    )
    buttons = [
        [
            Button.inline("🤍 yes, her", data=f"fav_confirm_{user_id}_{actual_char_id}"),
            Button.inline("…not yet", data=f"fav_cancel_{user_id}_{actual_char_id}")
        ]
    ]
    await event.reply(confirm_text, buttons=buttons, parse_mode='html') 

# ---- Helper functions for harem ----
async def remove_one_harem_copy(user_id, char_id, status):
    """Atomically removes exactly ONE harem copy matching (char_id, status) from user_id's
    vault — safe even when they own several copies of the same char_id (duplicates of common
    cards are normal and expected). Uses the positional $ operator (which only ever matches
    the FIRST array element that fits the filter) to null that one slot out, then a cheap
    $pull sweep to actually drop the null.
    🩹 FIX: this replaces the old pattern used by marketplace-buy and /trade-confirm — find_one
    the whole harem array, remove(item) in plain Python, then $set the WHOLE array back. That
    read-modify-write had no atomicity at all: if the same account did anything else to their
    harem (a gift, another sale, another trade) in the gap between the read and the write, that
    other change was silently overwritten by this stale full-array write — a classic lost-update
    race, and a plausible way for cards to duplicate or vanish under concurrent use. There's no
    such gap here: both updates below are single-document atomic operations."""
    await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": {"char_id": char_id, "status": status}}},
        {"$unset": {"harem.$": 1}}
    )
    await users_catcher_col.update_one({"user_id": user_id}, {"$pull": {"harem": None}})

async def clear_stale_favorite(user_id, char_id, remaining_harem):
    """Call this right after removing char_id from user_id's harem (gift / sell-and-bought /
    trade / scrap). If that was their LAST copy and it happened to be their /fav card, unset
    fav_card so /harem and /profile stop showing a card they no longer own."""
    still_owns_it = any(isinstance(it, dict) and it.get("char_id") == char_id for it in remaining_harem)
    if still_owns_it:
        return
    await users_catcher_col.update_one(
        {"user_id": user_id, "fav_card": char_id},
        {"$unset": {"fav_card": ""}}
    )

CARD_RANK_CACHE_TTL = 600  # 10 minutes — ranks don't need to be perfectly real-time, a bit of staleness is fine

def _rank_from_owners(owners, user_id):
    for idx, o in enumerate(owners, start=1):
        if o.get("user_id") == user_id:
            return idx
    return None

async def get_user_rank_for_card(user_id, char_id):
    """Single-card lookup — kept for any other call site that only needs one rank.
    /harem itself no longer uses this (see get_user_ranks_for_cards below), since
    calling this once per owned card was the N+1 query pattern that bogged it down."""
    ranks = await get_user_ranks_for_cards(user_id, [char_id])
    return ranks.get(char_id)

async def get_user_ranks_for_cards(user_id, char_ids):
    """Batched, cached replacement for calling get_user_rank_for_card once per card.
    Returns {char_id: rank_or_None} for every char_id in char_ids.

    Two layers make this cheap even under heavy concurrent /harem traffic:
    1. Each card's top-10 ownership leaderboard is cached in Redis (CARD_RANK_CACHE_TTL).
       This cache is *shared across every user* — a popular card's leaderboard is the
       same list no matter whose /harem is asking, so cache hit rate is high.
    2. Whatever isn't cached gets resolved in ONE aggregation call covering every
       missing char_id at once (relies on the harem.char_id index), instead of the
       old approach of one full aggregation per card."""
    if not char_ids:
        return {}
    ranks = {}
    missing = []
    # Batched into a single MGET round-trip instead of one GET per char_id in a loop — the
    # old loop meant len(char_ids) sequential network round-trips (up to 500 for a full
    # /harem before the page-scoped fix above), and if Redis was unreachable each of those
    # had to time out individually instead of failing once.
    try:
        cached_values = await redis_client.mget([f"cardrank:{cid}" for cid in char_ids])
    except Exception:
        cached_values = [None] * len(char_ids)
    for cid, cached in zip(char_ids, cached_values):
        if cached is not None:
            ranks[cid] = _rank_from_owners(json.loads(cached), user_id)
        else:
            missing.append(cid)
    if not missing:
        return ranks
    pipeline = [
        {"$match": {"harem.char_id": {"$in": missing}}},
        {"$project": {
            "user_id": 1,
            "harem": {"$filter": {"input": "$harem", "as": "item", "cond": {"$in": ["$$item.char_id", missing]}}}
        }},
        {"$unwind": "$harem"},
        {"$group": {"_id": {"char_id": "$harem.char_id", "user_id": "$user_id"}, "count": {"$sum": 1}}},
        {"$sort": {"_id.char_id": 1, "count": -1}},
        {"$group": {"_id": "$_id.char_id", "owners": {"$push": {"user_id": "$_id.user_id", "count": "$count"}}}},
        {"$project": {"owners": {"$slice": ["$owners", 10]}}}
    ]
    try:
        results = await users_catcher_col.aggregate(pipeline).to_list(length=None)
    except Exception as e:
        logging.error(f"⚠️ get_user_ranks_for_cards aggregation error: {e}")
        results = []
    found_ids = set()
    for doc in results:
        cid = doc["_id"]
        owners = doc.get("owners", [])
        found_ids.add(cid)
        ranks[cid] = _rank_from_owners(owners, user_id)
        try:
            await redis_client.setex(f"cardrank:{cid}", CARD_RANK_CACHE_TTL, json.dumps(owners))
        except Exception:
            pass
    # Cards nobody owns yet never show up in the aggregation output — cache an empty
    # list for those too, otherwise they'd re-trigger the aggregation on every call.
    for cid in missing:
        if cid not in found_ids:
            ranks[cid] = None
            try:
                await redis_client.setex(f"cardrank:{cid}", CARD_RANK_CACHE_TTL, json.dumps([]))
            except Exception:
                pass
    return ranks

async def send_paginated_harem(client, chat_id, user_id, page=1, edit_msg_id=None, viewer_id=None):
    if viewer_id is None:
        viewer_id = user_id
    is_own_vault = (viewer_id == user_id)
    # 👑 The owner's vault is unlimited: every character ever added via /addchar (and any
    # added in the future) counts as owned, always exactly one copy each — computed live from
    # characters_base_col rather than stored, so it needs no migration and always reflects the
    # current roster automatically. The owner's REAL personal /collect catches stay in their
    # actual harem array untouched and are shown separately (see the "📥 My Real Catches"
    # button below and the "collected.<id>" inline gallery) rather than mixed into this view.
    is_unlimited_vault = (user_id == OWNER_ID or user_id in added_owner_ids)
    # Projected — this function only ever reads harem/rarity_filter/fav_card off the user doc,
    # no need to pull wallet_balance, cooldowns, msg_history, etc. too.
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"harem": 1, "rarity_filter": 1, "fav_card": 1, "_id": 0}) or {}
    raw_harem = user_doc.get("harem", [])
    raw_owned_id_set = {item.get("char_id") for item in raw_harem if isinstance(item, dict) and item.get("char_id")}
    rarity_filter = user_doc.get("rarity_filter")

    if is_unlimited_vault:
        all_chars = await get_all_characters_cached()  # already invalidated on /addchar etc.
        if rarity_filter:
            all_chars = [c for c in all_chars if classify_rarity(c.get("rarity")) == classify_rarity(rarity_filter)]
        if not all_chars:
            msg = (f"⚔️ <b>…nobody matches that, quietly.</b>\nUse <code>/hmode</code> to change or clear it."
                   if rarity_filter else "<b>No characters exist yet — add some with /addchar.</b>")
            if edit_msg_id: await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html')
            else: await client.send_message(chat_id, msg, parse_mode='html')
            return
        harem_counts = {c["char_id"]: {"normal": 1, "market": 0} for c in all_chars}
        owned_ids = list(harem_counts.keys())
        filtered_harem = [{"char_id": cid} for cid in owned_ids]  # stand-in so len() below stays accurate
    else:
        if not raw_harem:
            msg = "<b>…your harem is empty. come find some of us</b>" if is_own_vault else "<b>…their harem is empty</b>"
            if edit_msg_id: await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html')
            else: await client.send_message(chat_id, msg, parse_mode='html')
            return
        filtered_harem = []
        if rarity_filter:
            for item in raw_harem:
                if isinstance(item, dict) and classify_rarity(item.get("rarity")) == classify_rarity(rarity_filter):
                    filtered_harem.append(item)
        else:
            filtered_harem = raw_harem
        if not filtered_harem:
            msg = f"⚔️ <b>…nobody matches that, quietly.</b>\n"
            msg += f"Use <code>/hmode</code> to change or clear it."
            if edit_msg_id: await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html')
            else: await client.send_message(chat_id, msg, parse_mode='html')
            return
        harem_counts = {}
        for item in filtered_harem:
            if isinstance(item, dict) and "char_id" in item:
                cid = item["char_id"]
                is_market = item.get("status") == "market"
                if cid not in harem_counts:
                    harem_counts[cid] = {"normal": 0, "market": 0}
                if is_market:
                    harem_counts[cid]["market"] += 1
                else:
                    harem_counts[cid]["normal"] += 1
        owned_ids = list(harem_counts.keys())
        if not owned_ids:
            msg = f"⚔️ <b>…nothing valid in here right now.</b>"
            if edit_msg_id: await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html')
            else: await client.send_message(chat_id, msg, parse_mode='html')
            return
    db_chars = await characters_base_col.find({"char_id": {"$in": owned_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "event": 1, "_id": 0}).to_list(length=None)
    category_totals = await get_category_totals_cached()
    def get_rarity_weight(rarity_str):
        return rarity_rank_value(rarity_str)
    from collections import defaultdict
    by_category = defaultdict(list)
    for card in db_chars:
        by_category[card.get("category") or "Unknown Series"].append(card)
    # 🎨 UI REDESIGN (matches catch_bot's own /harem layout): cards are grouped back under a
    # per-category header — "☘️ <Anime> (<owned>/<total>)" then a dashed divider — with every
    # owned card underneath as its own single "<id> | <rarity emoji> | <name> [<event>] (xN)"
    # line. Groups are packed onto pages greedily; if a category's remaining cards don't fit
    # on the current page, its header is simply repeated at the top of the next page so every
    # page still reads correctly standalone.
    CATEGORY_SEP = "⚋⚋⚋⚋⚋⚋⚋⚋"
    groups = []  # [(cat, owned_in_cat, total_in_cat, [(char_id, card_line), ...]), ...]
    for cat in sorted(by_category.keys(), key=lambda c: c.lower()):
        cat_cards = sorted(
            by_category[cat],
            key=lambda x: (-get_rarity_weight(x.get("rarity", "")), x.get("name", "").lower())
        )
        owned_in_cat = len(cat_cards)
        total_in_cat = category_totals.get(cat, owned_in_cat)
        cat_lines = []
        for card in cat_cards:
            cid = card["char_id"]
            counts = harem_counts.get(cid, {"normal": 0, "market": 0})
            normal_qty, market_qty = counts["normal"], counts["market"]
            if normal_qty > 0 and market_qty > 0:
                status_str = f"x{normal_qty} | {market_qty} 🛒"
            elif market_qty > 0:
                status_str = f"{market_qty} 🛒"
            else:
                status_str = f"x{normal_qty}"
            tier = classify_rarity(card.get("rarity", ""))
            rarity_emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
            evt_tag = event_emoji_tag(card.get("event"))
            evt_str = f" [{evt_tag}]" if evt_tag else ""
            card_line = (
                f"<code>{display_char_id(cid)}</code> | {rarity_emoji} | "
                f"{escape_html(card['name'])}{evt_str} ({status_str})"
            )
            cat_lines.append((cid, card_line))
        groups.append((cat, owned_in_cat, total_in_cat, cat_lines))
    # PAGE_CHAR_BUDGET is deliberately set so that EVERY page — not just page 1 — stays within
    # Telegram's 1024-char photo CAPTION limit even after adding the mention/label line, filter
    # line, and footer. That's what lets the fav-card photo stay attached for the whole vault,
    # any size: since every single page is guaranteed caption-safe, Next/Previous can keep
    # editing that same photo message's caption forever without ever risking
    # "MediaCaptionTooLongError" — no need to fall back to plain text or a bigger vault at all.
    PAGE_CHAR_BUDGET = 500
    pages = []                    # each page: [(cat, owned_in_cat, total_in_cat, [(char_id, card_line), ...]), ...]
    page_char_ids_per_page = []   # parallel: just the char_ids shown on each page (for rank lookups)
    current_page, current_len, current_page_ids = [], 0, []

    def _flush_page():
        nonlocal current_page, current_len, current_page_ids
        if current_page:
            pages.append(current_page)
            page_char_ids_per_page.append(current_page_ids)
        current_page, current_len, current_page_ids = [], 0, []

    for cat, owned_in_cat, total_in_cat, cat_lines in groups:
        header_len = utf16_len(f"☘️ {cat} ({owned_in_cat}/{total_in_cat})\n{CATEGORY_SEP}") + 1
        idx = 0
        while idx < len(cat_lines):
            fresh_on_page = (not current_page) or (current_page[-1][0] != cat)
            # 🩹 FIX (real bug — "Message was too long", crashing /harem entirely for large,
            # many-category vaults): a NEW category always forced through at least its header +
            # one line below (see the `if not chunk` fallback), even when remaining_budget was
            # already negative — and nothing ever flushed the page for THAT reason, only when a
            # category's OWN second-or-later line didn't fit. A page could accumulate an
            # unbounded number of small categories this way, each adding "at least one more
            # header+line" with no cap — for a harem spread across many categories, that let a
            # single page balloon straight past even Telegram's 4096-char plain-text limit, not
            # just the 1024 caption budget. Flushing here, BEFORE starting a new category on an
            # already-full page, closes the gap: every page can now overshoot
            # PAGE_CHAR_BUDGET by at most one category's worth, never an unbounded number of them.
            if fresh_on_page and current_page and (current_len + header_len) >= PAGE_CHAR_BUDGET:
                _flush_page()
                fresh_on_page = True
            this_header_len = header_len if fresh_on_page else 0
            remaining_budget = PAGE_CHAR_BUDGET - current_len - this_header_len
            chunk, chunk_len = [], 0
            while idx < len(cat_lines):
                cid, line = cat_lines[idx]
                line_len = utf16_len(line) + 1 + 4  # +4 reserves room for a rank badge suffix
                if chunk and chunk_len + line_len > remaining_budget:
                    break
                chunk.append((cid, line))
                chunk_len += line_len
                idx += 1
            if not chunk:
                if current_page:
                    _flush_page()
                    continue
                # pathological edge case (a single line bigger than the whole budget on an
                # already-empty page) — force it through alone rather than looping forever.
                cid, line = cat_lines[idx]
                chunk, chunk_len, idx = [(cid, line)], utf16_len(line) + 5, idx + 1
            current_page.append((cat, owned_in_cat, total_in_cat, chunk))
            current_page_ids.extend(cid for cid, _ in chunk)
            current_len += this_header_len + chunk_len
        current_len += 1  # blank spacer line after this category's block
    _flush_page()
    total_pages = len(pages) or 1
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    page_groups = pages[page - 1] if pages else []
    # Only now do we know exactly which cards are visible on this page — look up ranks for
    # just those instead of the whole vault.
    page_char_ids = page_char_ids_per_page[page - 1] if page_char_ids_per_page else []
    ranks_map = await get_user_ranks_for_cards(viewer_id, page_char_ids)
    page_lines = []
    for cat, owned_in_cat, total_in_cat, chunk in page_groups:
        page_lines.append(f"☘️ {escape_html(cat)} (<code>{owned_in_cat}/{total_in_cat}</code>)")
        page_lines.append(CATEGORY_SEP)
        for cid, line in chunk:
            rank = ranks_map.get(cid)
            rank_str = ""
            if rank == 1:
                rank_str = " 🥇"
            elif rank == 2:
                rank_str = " 🥈"
            elif rank == 3:
                rank_str = " 🥉"
            page_lines.append(f"{line}{rank_str}")
        page_lines.append("")  # blank spacer between category groups
    try:
        sender_ent = await client.get_entity(user_id)
        first = getattr(sender_ent, 'first_name', '') or ''
        last = getattr(sender_ent, 'last_name', '') or ''
        fullname = f"{first} {last}".strip() or getattr(sender_ent, 'username', '') or "Hunter"
    except: fullname = "Hunter"
    mention = f"<a href='tg://user?id={user_id}'><b>{escape_html(fullname)}</b></a>"
    output_text = f"{mention}'s {small_caps('Recent Characters')} - {small_caps('Page')}: <code>{page}/{total_pages}</code>\n"
    if rarity_filter:
        output_text += f"🔍 <b>Filter:</b> {rarity_filter}\n"
    output_text += "\n"
    for l in page_lines:
        output_text += l + "\n"
    output_text += "\n"
    if is_unlimited_vault:
        output_text += f"👑Owner Mode"
    if rarity_filter:
        output_text += f"\n<i>🔍 Filter active — use /hmode to change or clear.</i>"
    buttons = []
    # 🩹 FIX: this used to be len(filtered_harem), so setting an /hmode rarity filter (e.g.
    # Blossom) made the button count drop to just that rarity's count (e.g. 10 instead of the
    # true 100). The button should always reflect the whole vault's total, regardless of
    # whatever rarity filter happens to be active.
    # 🩹 FIX: this used to be len(raw_harem), which counts EVERY raw array element — including
    # any corrupted/invalid entries (non-dict items, or dicts missing "char_id") that a user
    # would never actually see rendered as a card. That silently inflated the count (e.g.
    # showing 19 when only 17 were real, displayable cards), same class of bug as the /stats
    # total-vs-breakdown mismatch. Count only entries that would actually show up as a card.
    total_cards = len(owned_ids) if is_unlimited_vault else sum(
        1 for item in raw_harem if isinstance(item, dict) and item.get("char_id")
    )
    # 🎨 UI REDESIGN: down to a single inline-query (switch_inline) button instead of two —
    # the separate "My Real Catches" button for the unlimited vault was cluttering the row
    # alongside Next/Previous and the rarity-filter toggle. If the owner still wants to browse
    # their real /collect catches separately, that's reachable another way (e.g. re-add a
    # button here with query=f"collected.{user_id}") — dropped here to keep just one.
    buttons.append([Button.switch_inline(f"Wifeyys ♥ ({total_cards})", query=f"harem.{user_id}", same_peer=True)])
    nav_buttons = []
    if page > 1:
        nav_buttons.append(Button.inline("← Previous", data=f"harem_{page-1}_{user_id}_{viewer_id}"))
    if page < total_pages:
        nav_buttons.append(Button.inline("Next ➡", data=f"harem_{page+1}_{user_id}_{viewer_id}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    if is_own_vault:
        if rarity_filter:
            buttons.append([Button.inline("Clean Filter", data=f"hfilter_clear_{user_id}")])
        buttons.append([Button.inline("Change Filter", data="nav_hmode")])
    if not buttons:
        buttons = None
    fav_card_id = user_doc.get("fav_card")
    if fav_card_id and not is_unlimited_vault and fav_card_id not in raw_owned_id_set:
        # Owner gifted/sold/traded/scrapped away their last copy of this card since favouriting
        # it — stop treating it as the favourite (both for display here and going forward).
        # (Skipped for the unlimited vault — every card is always "owned" there, so a
        # favourite never goes stale.)
        await users_catcher_col.update_one({"user_id": user_id, "fav_card": fav_card_id}, {"$unset": {"fav_card": ""}})
        fav_card_id = None
    fav_media = None
    target_display_id = fav_card_id
    if not target_display_id and owned_ids:
        target_display_id = random.choice(owned_ids)
    if target_display_id:
        fav_card_data = await characters_base_col.find_one({"char_id": target_display_id})
        if fav_card_data:
            fav_media = await get_char_display_media(client, target_display_id, fav_card_data["storage_msg_id"])
    # 🩹 FIX: attach the fav-card photo whenever it fits, for a vault of ANY size — not just
    # when everything happens to fit on a single page. This works now because PAGE_CHAR_BUDGET
    # above guarantees every page (not only page 1) stays within Telegram's 1024-char caption
    # limit, so Next/Previous can keep editing that same photo message's caption on ANY page
    # without ever risking "MediaCaptionTooLongError". The length check below still runs (using
    # page 1's text) as the actual go/no-go signal — if it ever comes out true, every later page
    # is guaranteed true too, by construction.
    CAPTION_SAFE_LIMIT = 1024
    can_attach_photo = bool(fav_media) and utf16_len(output_text) <= CAPTION_SAFE_LIMIT
    try:
        if edit_msg_id:
            try:
                await client.edit_message(chat_id, edit_msg_id, output_text, parse_mode='html', buttons=buttons)
            except errors.MessageNotModifiedError:
                pass
            except Exception:
                # Should never trigger given the PAGE_CHAR_BUDGET guarantee above — kept only
                # as a last-resort safety net (e.g. an unusually long display name we didn't
                # account for) so a genuine edge case degrades to a fresh message instead of an
                # error page.
                try:
                    await client.delete_messages(chat_id, edit_msg_id)
                except Exception:
                    pass
                await client.send_message(chat_id, output_text, parse_mode='html', buttons=buttons)
        else:
            if can_attach_photo:
                async def _send_harem_photo(media):
                    return await client.send_message(chat_id, output_text, file=media, parse_mode='html', buttons=buttons)
                sent = await send_with_char_media(target_display_id, fav_card_data["storage_msg_id"], _send_harem_photo)
                if sent is None:
                    await client.send_message(chat_id, output_text, parse_mode='html', buttons=buttons)
            else:
                await client.send_message(chat_id, output_text, parse_mode='html', buttons=buttons)
    except Exception as main_err:
        try:
            await client.send_message(chat_id, f"❌ <b>Vault Display Error:</b> <code>{escape_html(str(main_err))}</code>", parse_mode='html')
        except: pass

# ---- Inline Query for harem ----
def _rarity_weight_for_sort(rarity_str):
    return rarity_rank_value(rarity_str)

def _inline_media_result(builder, media, cid, title, caption):
    """Builds an inline result for a photo or video. Videos use type='gif' so Telegram
    renders them in the same side-by-side grid as photos, instead of a tall vertical list.
    No title is passed — a visible title/description on a document-type result is what makes
    it render as a text row instead of a clean grid tile on some clients; omitting it (it's
    optional) keeps every tile a plain thumbnail. The name still shows up in the caption once
    a result is actually selected and sent.
    Takes the raw media object (not a full Message) so this works equally with a freshly
    fetched message's .media or a cached one from get_char_display_media[_batch]."""
    if isinstance(media, types.MessageMediaPhoto):
        return builder.photo(file=media, id=cid, text=caption, parse_mode='html')
    return builder.document(
        file=media,
        type='gif',
        id=cid,
        text=caption,
        parse_mode='html'
    )

# ---- harem.<user_id> : shows a user's own vault as an inline gallery.
# collected.<user_id> routes here too (see unified_inline_query_handler) with
# force_real_harem=True, which is what lets the owner's REAL /collect catches be viewed
# separately from their unlimited vault below. ----
async def handle_harem_inline_query(event, query_text, force_real_harem=False):
    builder = event.builder
    try:
        target_user_id = int(query_text.split(".", 1)[1])
    except (ValueError, IndexError):
        return await event.answer(
            [], cache_time=0,
            switch_pm="⚠️ Couldn't read that request — try tapping the button again.", switch_pm_param="start"
        )
    user_doc = await users_catcher_col.find_one({"user_id": target_user_id})
    rarity_filter = user_doc.get("rarity_filter") if user_doc else None
    # 🎯 Unlike /harem's own text listing (where the rarity_filter genuinely restricts what's
    # shown), this visual gallery always shows EVERY owned card's photo/video — an active
    # /hmode rarity filter only makes cards of that rarity appear FIRST, as a sort preference
    # rather than an exclusion. Hiding most of someone's actual card art behind a filter here
    # would be a jarring surprise for a feature that's meant purely for browsing.
    filter_tier = classify_rarity(rarity_filter) if rarity_filter else None
    # 👑 Same unlimited-vault rule as /harem itself (see send_paginated_harem) — every
    # character that exists counts as owned, one copy each, computed live so /addchar never
    # needs a sync step. force_real_harem (the "collected." entry point) opts back into the
    # owner's REAL harem array, for viewing their actual personal catches.
    is_unlimited_vault = (target_user_id == OWNER_ID or target_user_id in added_owner_ids) and not force_real_harem

    if is_unlimited_vault:
        all_chars = await get_all_characters_cached()  # already invalidated on /addchar etc.
        if not all_chars:
            return await event.answer([], cache_time=0, switch_pm="❌ No characters found.", switch_pm_param="start")
        harem_counts = {c["char_id"]: 1 for c in all_chars}
        owned_ids = list(harem_counts.keys())
        total_cards = len(owned_ids)
    else:
        if not user_doc or not user_doc.get("harem"):
            return await event.answer(
                [], cache_time=0,
                switch_pm="…nobody's been caught yet", switch_pm_param="start"
            )
        raw_harem = [item for item in user_doc.get("harem", []) if isinstance(item, dict) and "char_id" in item]
        if not raw_harem:
            return await event.answer([], cache_time=0, switch_pm="…nothing here yet", switch_pm_param="start")
        harem_counts = {}
        for item in raw_harem:
            cid = item["char_id"]
            harem_counts[cid] = harem_counts.get(cid, 0) + 1
        owned_ids = list(harem_counts.keys())
        total_cards = len(raw_harem)
    db_chars = await characters_base_col.find({"char_id": {"$in": owned_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "storage_msg_id": 1, "artist": 1, "event": 1, "_id": 0}).to_list(length=None)
    # Filter-matching cards sort first (priority, not exclusion — see filter_tier note above);
    # within each group, same anime is now kept together too — see send_paginated_harem's own
    # fix for the same underlying issue.
    db_chars = sorted(db_chars, key=lambda x: (
        0 if (filter_tier and classify_rarity(x.get("rarity", "")) == filter_tier) else 1,
        (x.get("category") or "Unknown Series").lower(),
        -_rarity_weight_for_sort(x.get("rarity", "")),
        x.get("name", "").lower()
    ))
    # Per-category "(owned/total)" stats for the card caption below — owned counts unique
    # cards from THIS vault, total is however many exist in that series overall (same source
    # as /harem's own category line — see send_paginated_harem).
    category_totals = await get_category_totals_cached()
    cat_owned_counts = {}
    for c in db_chars:
        cname = c.get("category") or "Unknown Series"
        cat_owned_counts[cname] = cat_owned_counts.get(cname, 0) + 1
    try:
        owner_ent = await bot1.get_entity(target_user_id)
        first = getattr(owner_ent, 'first_name', '') or ''
        last = getattr(owner_ent, 'last_name', '') or ''
        owner_name = f"{first} {last}".strip() or getattr(owner_ent, 'username', '') or f"User {target_user_id}"
    except Exception:
        owner_name = f"User {target_user_id}"
    # ✅ FULL PAGINATION: Telegram hard-caps a single inline answer at 50 results (more raises
    # ResultsTooMuchError) — that's a platform limit, not a choice. To actually show the
    # WHOLE vault instead of freezing at the first 50, we page through db_chars using
    # next_offset: the client automatically re-queries us with the offset once the person
    # scrolls near the end of the current batch, so scrolling reveals every unique card.
    PAGE_SIZE = 50
    try:
        start_idx = int(event.query.offset) if event.query.offset else 0
    except (ValueError, AttributeError):
        start_idx = 0
    page_chars = db_chars[start_idx:start_idx + PAGE_SIZE]
    # Batch-fetch every storage message for this page in ONE call instead of one
    # get_messages() per card. The old per-card loop meant up to 50 sequential API
    # round-trips for a single inline answer — slow enough to risk Telegram's ~10s
    # inline-query timeout and occasional flood-wait, so whichever cards hadn't finished
    # fetching yet (or hit an error) just got silently skipped via `continue`. That's why the
    # set of visible cards looked "random" and capped around ~100 for a 500-card vault: it
    # wasn't a hard limit, it was fetches failing to finish in time, differently each query.
    # get_char_display_media_batch further only hits Telegram for whatever's missing from the
    # in-process cache, so a page anyone's already browsed once is free the next time.
    try:
        media_by_cid = await get_char_display_media_batch(bot1, page_chars)
    except Exception as e:
        print(f"Inline gallery batch fetch error: {e}")
        media_by_cid = {}
    results = []
    for card in page_chars:
        cid = card["char_id"]
        qty = harem_counts.get(cid, 0)
        storage_media = media_by_cid.get(cid)
        if not storage_media:
            continue
        try:
            tier = classify_rarity(card.get("rarity", ""))
            rarity_emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
            rarity_plain = RARITY_DISPLAY_NAME.get(tier, tier.title() if tier != "OTHER" else "Unknown")
            qty_note = f" (x{qty})" if not is_unlimited_vault else ""
            evt_tag = event_emoji_tag(card.get("event"))
            evt_str = f" [{evt_tag}]" if evt_tag else ""
            cat_name = card.get("category") or "Unknown Series"
            owned_in_cat = cat_owned_counts.get(cat_name, 1)
            total_in_cat = category_totals.get(cat_name, owned_in_cat)
            caption = (
                f"🧃OᴡO! ᴄʜᴇᴄᴋ ᴏᴜᴛ {escape_html(owner_name)} sᴀɴ ᴄʜᴀʀᴀᴄᴛᴇʀ!\n\n"
                f"{escape_html(cat_name)} ({owned_in_cat}/{total_in_cat})\n"
                f"{display_char_id(cid)}: {escape_html(card['name'])}{evt_str}{qty_note}\n"
                f"{rarity_emoji} {RARITY_LABEL_STYLED}: {rarity_plain}"
            )
            results.append(_inline_media_result(builder, storage_media, cid, card['name'], caption))
        except Exception as e:
            print(f"Inline gallery error for {cid}: {e}")
            continue
    next_start = start_idx + PAGE_SIZE
    # 🩹 FIX: next_offset used to be "" (explicit empty string) when there was no further page.
    # That reads fine per the Bot API docs, but Telegram's raw API can reject an
    # explicitly-set-but-empty next_offset outright with NextOffsetInvalidError — the field
    # needs to be OMITTED (None) to signal "no more results", not set to an empty value.
    next_offset = str(next_start) if next_start < len(db_chars) else None
    filter_note = f"🎯 {classify_rarity(rarity_filter)} shown first" if rarity_filter else "All rarities"
    mode_note = " · 👑 Unlimited Vault" if is_unlimited_vault else (" · 📥 Real Collect" if force_real_harem else "")
    try:
        await event.answer(
            results, cache_time=0,
            gallery=True,  # ✅ side-by-side grid, no gaps — instead of a tall one-per-row list
            next_offset=next_offset,
            switch_pm=f"{filter_note} · Total: {total_cards}{mode_note}",
            switch_pm_param="start"
        )
    except errors.NextOffsetInvalidError:
        # Last-resort safety net: whatever Telegram didn't like about next_offset, retry
        # without it (no further-page continuation) so the person still sees these results
        # instead of the whole inline query silently failing.
        await event.answer(
            results, cache_time=0,
            gallery=True,
            switch_pm=f"{filter_note} · Total: {total_cards}{mode_note}",
            switch_pm_param="start"
        )

# ---- dex.<category> : shows every character (caught or not) in a series, image gallery style ----
async def handle_dex_inline_query(event, query_text):
    builder = event.builder
    cat_name = query_text.split(".", 1)[1].strip() if "." in query_text else ""
    if not cat_name:
        return await event.answer([], cache_time=0)
    all_categories = await get_all_categories_cached()
    matched_cat = next((c for c in all_categories if c and c.lower() == cat_name.lower()), None)
    if not matched_cat:
        return await event.answer([], cache_time=0)
    user_id = getattr(event, 'sender_id', None)
    if not user_id:
        try:
            user_id = event.query.user_id
        except Exception:
            user_id = None
    owned_ids = set()
    if user_id:
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        if user_doc:
            owned_ids = {c.get("char_id") for c in user_doc.get("harem", []) if isinstance(c, dict) and c.get("char_id")}
    cat_chars = [c for c in await get_all_characters_cached() if c.get("category") == matched_cat]
    cat_chars.sort(key=lambda x: (-_rarity_weight_for_sort(x.get("rarity", "")), x.get("name", "").lower()))
    results = []
    page_chars = cat_chars[:50]
    # Batch-fetch (see handle_harem_inline_query for why this matters — one call instead of
    # up to 50 sequential ones); further reduced to only-the-misses by the cache inside
    # get_char_display_media_batch.
    try:
        media_by_cid = await get_char_display_media_batch(bot1, page_chars)
    except Exception as e:
        print(f"Dex inline gallery batch fetch error: {e}")
        media_by_cid = {}
    for card in page_chars:
        cid = card["char_id"]
        owned = cid in owned_ids
        storage_media = media_by_cid.get(cid)
        if not storage_media:
            continue
        try:
            caption = (
                f"Character Name🐇<b>{escape_html(card['name'])}</b>\n"
                f"ID <code>{display_char_id(cid)}</code>\n"
                f"🏞️<b>Category:</b> {escape_html(matched_cat)}\n"
                f" <b>Rarity:</b> {card.get('rarity', '')}\n"
                f"{artist_line(card)}"
                f"{'✅ You caught this!' if owned else '❓ Not caught yet'}"
            )
            results.append(_inline_media_result(builder, storage_media, cid, card['name'], caption))
        except Exception as e:
            print(f"Dex inline gallery error for {cid}: {e}")
            continue
    await event.answer(results, cache_time=0)

# ---- /fuck <name> : lets the /who reveal button's switch_inline query actually send a
# message. Accepts legacy "/obtain ", "/collect " and "/catch " prefixes too, so any
# switch_inline buttons already sent to chats before the /obtain → /fuck rename still work —
# but always emits the new "/fuck <name>" text going forward. ----
async def handle_collect_inline_query(event, query_text):
    for legacy_prefix in ("/fuck ", "/obtain ", "/collect ", "/catch "):
        if query_text.startswith(legacy_prefix):
            prefix = legacy_prefix
            break
    else:
        prefix = "/fuck "
    char_name = query_text[len(prefix):].strip()
    if not char_name:
        return await event.answer([], cache_time=0)
    builder = event.builder
    result = builder.article(
        title=f"🤍 it's {char_name}",
        description="…tap here, and I'm yours",
        text=f"/fuck {char_name}",
        id=f"collect_{abs(hash(char_name)) % (10 ** 12)}"
    )
    await event.answer([result], cache_time=0)

@bot1.on(events.InlineQuery)
async def unified_inline_query_handler(event):
    query_text = (event.text or "").strip()
    if query_text.startswith("harem."):
        await handle_harem_inline_query(event, query_text)
    elif query_text.startswith("collected."):
        # Owner's REAL /collect catches, kept separate from their unlimited vault above —
        # see handle_harem_inline_query and send_paginated_harem's "📥 My Real Catches" button.
        await handle_harem_inline_query(event, "harem." + query_text[len("collected."):], force_real_harem=True)
    elif query_text.startswith("dex."):
        await handle_dex_inline_query(event, query_text)
    elif query_text.startswith(("/fuck ", "/obtain ", "/collect ", "/catch ")):
        await handle_collect_inline_query(event, query_text)
    else:
        await event.answer([], cache_time=0)

# ---- Callback for view_all_cards ----
@bot1.on(events.CallbackQuery(pattern=r'^view_all_cards_(\d+)$'))
async def view_all_cards_callback(event):
    user_id = int(event.pattern_match.group(1))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc or not user_doc.get("harem"):
        return await event.answer("📭 This vault is empty!", alert=True)
    raw_harem = user_doc.get("harem", [])
    rarity_filter = user_doc.get("rarity_filter")
    filtered_harem = []
    if rarity_filter:
        for item in raw_harem:
            if isinstance(item, dict) and classify_rarity(item.get("rarity")) == classify_rarity(rarity_filter):
                filtered_harem.append(item)
    else:
        filtered_harem = raw_harem
    if not filtered_harem:
        return await event.answer("❌ No cards found with current filter!", alert=True)
    unique_cards = {}
    for item in filtered_harem:
        if isinstance(item, dict) and "char_id" in item:
            cid = item["char_id"]
            if cid not in unique_cards:
                unique_cards[cid] = {"count": 0, "item": item}
            unique_cards[cid]["count"] += 1
    if not unique_cards:
        return await event.answer("❌ No valid cards found!", alert=True)
    card_ids = list(unique_cards.keys())
    page = 1
    per_page = 5
    total_pages = (len(card_ids) + per_page - 1) // per_page
    await send_gallery_page(event, user_id, card_ids, unique_cards, page, per_page, total_pages)

async def send_gallery_page(event, user_id, card_ids, unique_cards, page, per_page, total_pages):
    start_idx = (page - 1) * per_page
    end_idx = min(start_idx + per_page, len(card_ids))
    page_card_ids = card_ids[start_idx:end_idx]
    try:
        owner_ent = await bot1.get_entity(user_id)
        first = getattr(owner_ent, 'first_name', '') or ''
        last = getattr(owner_ent, 'last_name', '') or ''
        owner_name = f"{first} {last}".strip() or getattr(owner_ent, 'username', '') or "Hunter"
    except Exception:
        owner_name = "Hunter"
    gallery_text = f"👀 <b>{escape_html(owner_name)}'s Card Gallery</b>\n"
    filter_doc = await users_catcher_col.find_one({"user_id": user_id})
    rarity_filter = filter_doc.get("rarity_filter") if filter_doc else None
    if rarity_filter:
        gallery_text += f"🔍 <b>Filter:</b> {rarity_filter}\n"
    gallery_text += f"📑 <b>Page {page}/{total_pages}</b> · <b>Total Cards:</b> {len(card_ids)}\n\n"
    gallery_text += f"<i>✨ Tap a card below to see its details</i>\n"
    buttons = []
    row = []
    for idx, cid in enumerate(page_card_ids):
        card_data = await characters_base_col.find_one({"char_id": cid})
        if not card_data:
            continue
        card_name = card_data.get("name", "Unknown")
        emoji = card_data.get("rarity", RARITY_DEFAULT_EMOJI)[0] if card_data.get("rarity") else RARITY_DEFAULT_EMOJI
        count = unique_cards[cid]["count"]
        label = f"{emoji} {card_name} x{count}"
        row.append(Button.inline(label, data=f"card_detail_{cid}_{user_id}"))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    nav_row = []
    if page > 1:
        nav_row.append(Button.inline("⬅️ Prev", data=f"gallery_page_{page-1}_{user_id}"))
    if page < total_pages:
        nav_row.append(Button.inline("Next ➡️", data=f"gallery_page_{page+1}_{user_id}"))
    if nav_row:
        buttons.append(nav_row)
    buttons.append([Button.inline("🔙 Back to Vault", data=f"harem_1_{user_id}")])
    await event.edit(gallery_text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^gallery_page_(\d+)_(\d+)$'))
async def gallery_page_callback(event):
    page = int(event.pattern_match.group(1))
    user_id = int(event.pattern_match.group(2))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc or not user_doc.get("harem"):
        return await event.answer("📭 This vault is empty!", alert=True)
    raw_harem = user_doc.get("harem", [])
    rarity_filter = user_doc.get("rarity_filter")
    filtered_harem = []
    if rarity_filter:
        for item in raw_harem:
            if isinstance(item, dict) and classify_rarity(item.get("rarity")) == classify_rarity(rarity_filter):
                filtered_harem.append(item)
    else:
        filtered_harem = raw_harem
    unique_cards = {}
    for item in filtered_harem:
        if isinstance(item, dict) and "char_id" in item:
            cid = item["char_id"]
            if cid not in unique_cards:
                unique_cards[cid] = {"count": 0, "item": item}
            unique_cards[cid]["count"] += 1
    card_ids = list(unique_cards.keys())
    per_page = 5
    total_pages = (len(card_ids) + per_page - 1) // per_page
    await send_gallery_page(event, user_id, card_ids, unique_cards, page, per_page, total_pages)

@bot1.on(events.CallbackQuery(pattern=r'^card_detail_([a-zA-Z0-9_]+)_(\d+)$'))
async def card_detail_callback(event):
    char_id = event.pattern_match.group(1)
    if isinstance(char_id, bytes):
        char_id = char_id.decode('utf-8')
    user_id = int(event.pattern_match.group(2))
    card = await characters_base_col.find_one({"char_id": char_id})
    if not card:
        return await event.answer("❌ Card not found!", alert=True)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        return await event.answer("❌ User not found!", alert=True)
    harem = user_doc.get("harem", [])
    count = 0
    for item in harem:
        if isinstance(item, dict) and item.get("char_id") == char_id:
            count += 1
    try:
        owner_ent = await bot1.get_entity(user_id)
        first = getattr(owner_ent, 'first_name', '') or ''
        last = getattr(owner_ent, 'last_name', '') or ''
        owner_name = f"{first} {last}".strip() or getattr(owner_ent, 'username', '') or "Hunter"
    except Exception:
        owner_name = "Hunter"
    owner_mention = f"<a href='tg://user?id={user_id}'><b>{escape_html(owner_name)}</b></a>"
    detail_text = (
        f" <b>Card Details</b>\n"
        f" <b>This Charater Card Owner:</b> {owner_mention}\n\n"
        f" <b>Name:</b> <code>{escape_html(card['name'])}</code>\n"
        f" <b>ID:</b> <code>{display_char_id(card['char_id'])}</code>\n"
        f" <b>Category:</b> <code>{escape_html(card['category'])}</code>\n"
        f" <b>Rarity:</b> {card['rarity']}\n"
        f"{artist_line(card)}"
        f"📦 <b>Owned:</b> <code>{count} copies</code>\n"
        f" <b>Value:</b> <code>{card['currency_value']} USD</code>\n\n"
        f"<i>✨ Tap the image to close</i>"
    )

    async def _send_detail(media):
        return await bot1.send_file(
            event.chat_id,
            media,
            caption=detail_text,
            parse_mode='html',
            reply_to=event.message_id
        )

    media_preview = await get_char_display_media(bot1, card["char_id"], card["storage_msg_id"])
    if media_preview:
        await event.answer("🃏 Loading card...", alert=False)
        sent = await send_with_char_media(card["char_id"], card["storage_msg_id"], _send_detail)
        if sent:
            await event.answer("✅ Card sent!", alert=True)
        else:
            await event.edit(detail_text, parse_mode='html')
    else:
        await event.edit(detail_text, parse_mode='html')

# ---- UNIFIED CALLBACK HANDLER (extended) ----
@bot1.on(events.CallbackQuery)
async def unified_callback_handler(event):
    if not event.data: return
    try: data_str = event.data.decode('utf-8')
    except: return
    data_parts = data_str.split('_')
    action_type = data_parts[0]

    if action_type == "harem":
        page = int(data_parts[1])
        target_user_id = int(data_parts[2])
        viewer_id = event.sender_id
        await send_paginated_harem(bot1, event.chat_id, target_user_id, page=page, edit_msg_id=event.message_id, viewer_id=viewer_id)
    elif action_type == "ach":
        page = int(data_parts[1])
        target_user_id = int(data_parts[2])
        if event.sender_id != target_user_id:
            return await event.answer("⚠️ These are not your achievements!", alert=True)
        mention = await get_html_mention(event, target_user_id)
        await send_achievements_page(bot1, event.chat_id, target_user_id, mention, page=page, edit_msg_id=event.message_id)
    # ==========================================
    # 🎁 Gift-history pagination (from /myinfo, /profile)
    # ==========================================
    elif action_type == "gh":
        owner_user_id = int(data_parts[1])
        page = int(data_parts[2])
        if event.sender_id != owner_user_id:
            return await event.answer("⚠️ ဒါက သင့်ရဲ့ history မဟုတ်ပါ။", alert=True)
        text, buttons = await render_gift_history_page(owner_user_id, page)
        try:
            await event.edit(text, parse_mode='html', buttons=buttons)
        except Exception:
            pass
        await event.answer()

    # ==========================================
    # 📊 Profile view (legacy pf_stats_/pf_main_ buttons on old, already-sent messages route
    # here too — there's no more separate stats page to toggle to, so both sub-actions just
    # re-render the same combined view now)
    # ==========================================
    elif action_type == "pf":
        owner_user_id = int(data_parts[2])
        if event.sender_id != owner_user_id:
            return await event.answer("⚠️ ဒါက သင့်ရဲ့ Profile မဟုတ်ပါ။", alert=True)
        mention = await get_html_mention(event, owner_user_id)
        text, buttons = await render_profile_full(event, owner_user_id, mention)
        try:
            await event.edit(text, parse_mode='html', buttons=buttons)
        except Exception:
            pass
        await event.answer()

    # ==========================================
    # 🏆 Leaderboard tab/page switching
    # ==========================================
    elif action_type == "lb":
        mode = data_parts[1]
        page = int(data_parts[2])
        text, buttons = await render_leaderboard_page(mode, page)
        try:
            await event.edit(text, parse_mode='html', buttons=buttons)
        except Exception:
            pass
        await event.answer()

    # ==========================================
    # ⭐ /fav confirm / cancel callbacks
    # ==========================================
    elif action_type == "fav":
        if len(data_parts) < 4:
            return await event.answer("❌ Invalid request.", alert=True)
        sub_action = data_parts[1]
        target_user_id = int(data_parts[2])
        char_id = "_".join(data_parts[3:])
        if event.sender_id != target_user_id:
            return await event.answer("⚠️ ဒါက သင့်ရွေးချယ်မှုမဟုတ်ပါ။", alert=True)
        if sub_action == "cancel":
            await event.answer("❌ Cancelled.")
            try:
                await event.edit("❌ <b>Favourite ထည့်ခြင်းကို ပယ်ဖျက်လိုက်ပါပြီ။</b>", parse_mode='html', buttons=None)
            except Exception:
                pass
            return
        if sub_action == "confirm":
            card = await characters_base_col.find_one({"char_id": char_id})
            if not card:
                return await event.answer("❌ ဒီကတ်ကို ရှာမတွေ့ပါ။", alert=True)
            # 🩹 FIX (per owner report): this callback — fired when the "🤍 yes, her" button is
            # tapped — had its OWN separate ownership check that never got the OWNER_ID /
            # added_owner_ids unlimited-vault bypass set_favorite_card above already has. It's
            # a completely different code path (this lives in unified_callback_handler), so
            # fixing the command handler alone missed it entirely — even OWNER_ID itself would
            # silently fail here on any character they hadn't actually, really caught.
            if target_user_id == OWNER_ID or target_user_id in added_owner_ids:
                owns_card = True
            else:
                user_doc = await users_catcher_col.find_one({"user_id": target_user_id})
                user_harem = user_doc.get("harem", []) if user_doc else []
                owns_card = any(
                    isinstance(x, dict) and (x.get("char_id") or "").upper() == char_id.upper()
                    for x in user_harem
                )
            if not owns_card:
                return await event.answer("❌ …she's not yours anymore.", alert=True)
            await users_catcher_col.update_one({"user_id": target_user_id}, {"$set": {"fav_card": card["char_id"]}})
            await event.answer("🤍 she's your favorite now~")
            try:
                await event.edit(
                    f"🍬 <b>{escape_html(card['name'])}</b> (<code>{display_char_id(card['char_id'])}</code>) ကို "
                    f"favourite ကတ်အဖြစ် သတ်မှတ်လိုက်ပြီ! ✨ /harem မှာ ဒီကတ်ပေါ်လာမယ်။",
                    parse_mode='html', buttons=None
                )
            except Exception:
                pass
            return
# 🛡️ Guard Bot (bot3) has been merged into bot1, so all outgoing game messages (cardjoin,
# hilo, etc.) are now sent by bot1 too — the @bot1.on(events.CallbackQuery) registration
# above already covers every callback, no second registration needed.

# ==========================================
# 🏆 LEADERBOARD (Daily / All-Time, paginated)
# ==========================================
LEADERBOARD_PAGE_SIZE = 15
LB_MEDALS = {0: "🥇", 1: "🥈", 2: "🥉"}

async def render_leaderboard_page(mode, page):
    """Generate leaderboard text and buttons for a given mode and page."""
    today_str = datetime.now(TZ).strftime("%Y-%m-%d") if mode == "daily" else None
    data = await get_cached_leaderboard(mode, today_str)
    
    total = len(data)
    start = page * LEADERBOARD_PAGE_SIZE
    page_rows = data[start:start + LEADERBOARD_PAGE_SIZE]
    field_map = {"daily": "daily_catches", "all": "total_caught"}
    title_map = {"daily": "📅 <b>Today's Top Catchers</b>", "all": "🏆 <b>All-Time Top Catchers</b>"}
    field = field_map.get(mode, "total_caught")
    title = title_map.get(mode, title_map["all"])
    
    if not page_rows:
        body = "<i>Nobody's caught anything yet — be the first! 🐟</i>" if page == 0 else "<i>No more entries.</i>"
    else:
        lines = []
        for i, row in enumerate(page_rows):
            rank = start + i
            medal = LB_MEDALS.get(rank, f"<code>#{rank + 1}</code>")
            name = escape_html(clean_display_name(row.get("fullname"), fallback=f"User {row.get('user_id')}"))
            val = row.get(field, 0)
            lines.append(f"{medal}  {name} — <code>{val}</code>")
        body = "\n".join(lines)
    
    text = f"{title}\n{body}"
    
    # Tab buttons
    tab_rows = [
        [
            Button.inline(("🔘 " if mode == "daily" else "") + "📅 Daily", data="lb_daily_0"),
            Button.inline(("🔘 " if mode == "all" else "") + "🏆 All-Time", data="lb_all_0")
        ]
    ]
    
    # Navigation buttons
    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Prev", data=f"lb_{mode}_{page - 1}"))
    if start + LEADERBOARD_PAGE_SIZE < total:
        nav_row.append(Button.inline("Next ▶", data=f"lb_{mode}_{page + 1}"))
    
    buttons = list(tab_rows)
    if nav_row:
        buttons.append(nav_row)
    
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](leaderboard|lb)(?:@\w+)?$', 'bot1')))
async def leaderboard_handler(event):
    """Handle /leaderboard and /lb commands."""
    text, buttons = await render_leaderboard_page("all", 0)
    await event.reply(text, parse_mode='html', buttons=buttons)

# ---- Callback handler for leaderboard navigation ----
@bot1.on(events.CallbackQuery(pattern=r'^lb_(daily|all)_(\d+)$'))
async def leaderboard_callback_handler(event):
    """Handle leaderboard page/tab switching via inline buttons."""
    mode = event.pattern_match.group(1)  # "daily" or "all"
    if isinstance(mode, bytes):
        mode = mode.decode('utf-8')
    page = int(event.pattern_match.group(2))
    
    text, buttons = await render_leaderboard_page(mode, page)
    
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer("✅ Updated!")
    except errors.MessageNotModifiedError:
        # Message content hasn't changed, just acknowledge the click
        await event.answer()
    except Exception as e:
        await event.answer(f"❌ Error: {e}", alert=True)

LEADERBOARD_CACHE_TTL = 60  # a full minute of staleness is fine for a top-50 board

async def get_cached_leaderboard(mode, today_str=None):
    """mode: 'daily' or 'all'. Leaderboard staleness of up to a minute is harmless, so this
    caches the whole top-50 snapshot instead of hitting Mongo on every /leaderboard tap."""
    cache_key = f"cache:leaderboard:{mode}:{today_str or 'x'}"
    try:
        cached = await redis_client.get(cache_key)
        if cached:
            return json.loads(cached)
    except Exception as e:
        print(f"⚠️ Redis leaderboard cache error: {e}")
        # Redis မရရင် DB ကို တိုက်ရိုက်ရှာမယ်
    
    # Fetch from database
    if mode == "daily":
        today_start = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0)
        cursor = users_catcher_col.find(
            {"last_catch_date": {"$gte": today_start}, "daily_catches": {"$gt": 0}},
            {"_id": 0, "user_id": 1, "fullname": 1, "daily_catches": 1}
        ).sort("daily_catches", -1).limit(50)
    else:
        cursor = users_catcher_col.find(
            {"total_caught": {"$gt": 0}},
            {"_id": 0, "user_id": 1, "fullname": 1, "total_caught": 1}
        ).sort("total_caught", -1).limit(50)
    
    data = await cursor.to_list(length=50)
    
    # Try to cache it
    try:
        await redis_client.setex(cache_key, LEADERBOARD_CACHE_TTL, json.dumps(data, default=str))
    except Exception as e:
        print(f"⚠️ Redis leaderboard cache write error: {e}")
    
    return data

# ==========================================
# 📊 PROFILE
# ==========================================
# 🎨 UI REDESIGN (per owner request — replicating a reference screenshot's boxed, small-caps
# layout): what used to be two separate pages (an overview page + a "tap for Rarity Vault"
# page) are now ONE combined view, in 4 box-drawn sections — header/level, rarity breakdown,
# extra stats, global position. "Experience Level" didn't exist as a concept before this — see
# get_experience_level's docstring for the (purely cosmetic, catches-based) formula behind it.
async def render_profile_full(event, user_id, mention):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    total_caught = user_doc.get("total_caught", 0) if user_doc else 0
    streak = user_doc.get("daily_streak", 0) if user_doc else 0
    referrals = user_doc.get("referral_count", 0) if user_doc else 0
    badge_count = len(user_doc.get("achievements", [])) if user_doc else 0
    raw_harem = user_doc.get("harem", []) if user_doc else []
    fav_card_id = user_doc.get("fav_card") if user_doc else None
    total_gifted = user_doc.get("total_gifted", 0) if user_doc else 0
    total_gift_received = user_doc.get("total_gift_received", 0) if user_doc else 0
    gifted_by_tier = (user_doc.get("gifted_by_rarity", {}) if user_doc else {}) or {}
    unique_ids = {item["char_id"] for item in raw_harem if isinstance(item, dict) and "char_id" in item}
    base_total = await characters_base_col.count_documents({})
    unique_owned = len(unique_ids)
    rank = await users_catcher_col.count_documents({"total_caught": {"$gt": total_caught}}) + 1

    chat_rank_line = ""
    if not event.is_private:
        chat_id_str = str(event.chat_id)
        my_chat_catches = (user_doc.get("group_catches", {}) if user_doc else {}).get(chat_id_str, 0)
        if my_chat_catches > 0:
            chat_rank = await users_catcher_col.count_documents({f"group_catches.{chat_id_str}": {"$gt": my_chat_catches}}) + 1
            chat_rank_line = f"├─➩ 🍁 {small_caps('Chat Rank')}: <code>#{chat_rank}</code>\n"

    fav_line = ""
    if fav_card_id and fav_card_id not in unique_ids:
        # Owner no longer has any copy of this card — clear the stale favourite.
        await users_catcher_col.update_one({"user_id": user_id, "fav_card": fav_card_id}, {"$unset": {"fav_card": ""}})
        fav_card_id = None
    if fav_card_id:
        fav_doc = await characters_base_col.find_one({"char_id": fav_card_id})
        if fav_doc:
            fav_line = f"├─➩ ⭐ {small_caps('Favourite')}: {escape_html(fav_doc.get('name'))} (<code>{fav_card_id}</code>)\n"

    pct = (unique_owned / base_total * 100) if base_total else 0
    level, level_progress, level_span = get_experience_level(total_caught)
    giver_title = get_giver_title(total_gifted)
    receiver_title = get_receiver_title(total_gift_received)
    giver_rank_str = f" ({giver_title[0]} {giver_title[1]})" if giver_title else ""
    receiver_rank_str = f" ({receiver_title[0]} {receiver_title[1]})" if receiver_title else ""

    # ---- Box 1: header + level ----
    box1 = (
        f"╭──「 🎗️ {small_caps('Catcher Profile')} 🎗 」\n"
        f"├─➩ 👤 {small_caps('User')}: {mention}\n"
        f"├─➩ 🔩 {small_caps('User ID')}: <code>{user_id}</code>\n"
        f"├─➩ ⚡ {small_caps('Total Character')}: <code>{total_caught}</code> (<code>{unique_owned}</code>)\n"
        f"├─➩ 🫧 {small_caps('Harem')}: <code>{unique_owned}/{base_total}</code> (<code>{pct:.3f}%</code>)\n"
        f"├─➩ ℹ️ {small_caps('Experience Level')}: <code>{level}</code>\n"
        f"├─➩ 📈 {small_caps('Progress Bar')}:\n"
        f"╰         {build_block_progress_bar(level_progress, level_span)}"
    )

    # ---- Box 2: rarity breakdown — same "current (ever obtained)" pairing the old stats
    # page used, tiers with nothing caught AND nothing ever gifted away are skipped entirely.
    tier_counts = {t: 0 for t in RARITY_TIERS}
    for item in raw_harem:
        if isinstance(item, dict):
            tier = classify_rarity(item.get("rarity", ""))
            if tier in tier_counts:
                tier_counts[tier] += 1
    tier_lines = []
    for tier in RARITY_TIERS:
        cnt = tier_counts[tier]
        gifted = gifted_by_tier.get(tier, 0)
        if cnt == 0 and gifted == 0:
            continue
        ever_total = cnt + gifted
        tier_lines.append(
            f"├─➩ {RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)} {small_caps('Rarity')}: "
            f"{small_caps(tier.title())}: <code>{cnt}</code> (<code>{ever_total}</code>)"
        )
    box2 = "╭───────────────────\n" + (
        "\n".join(tier_lines) if tier_lines else f"├─➩ <i>{small_caps('No characters caught yet')}</i>"
    ) + "\n╰───────────────────"

    # ---- Box 3: everything else ----
    box3 = (
        f"╭───────────────────\n"
        f"├─➩ 🔥 {small_caps('Streak')}: <code>{streak}d</code>   🤝 {small_caps('Referrals')}: <code>{referrals}</code>\n"
        f"├─➩ 🏅 {small_caps('Badges')}: <code>{badge_count}/{len(ACHIEVEMENTS)}</code>\n"
        f"├─➩ 🎁 {small_caps('Gifted')}: <code>{total_gifted}</code>{giver_rank_str}\n"
        f"├─➩ 🎀 {small_caps('Received')}: <code>{total_gift_received}</code>{receiver_rank_str}\n"
        f"{fav_line}"
        f"{chat_rank_line}"
        f"╰───────────────────"
    )

    # ---- Box 4: global position ----
    box4 = (
        f"╭───────────────────\n"
        f"├─➩ 🌍 {small_caps('Global Position')}: <code>{rank}</code>\n"
        f"╰───────────────────"
    )

    text = f"{box1}\n\n{box2}\n\n{box3}\n\n{box4}"
    buttons = [[Button.inline("🎁 Gift History", data=f"gh_{user_id}_0")]] if total_gifted else None
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](profile|myinfo)(?:@\w+)?$', 'bot1')))
async def profile_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    text, buttons = await render_profile_full(event, user_id, mention)
    # 🩹 FIX (same class of bug as /harem's "Message was too long" crash): a profile photo
    # caption is capped at 1024 UTF-16 units, but this view can run past that for a user with
    # many rarity tiers represented, a long display name, a long favourite name, etc. — with
    # no upper bound otherwise. Falling back to a plain (photo-less) reply, which only has to
    # fit under the much higher 4096-char message limit, means a big profile degrades
    # gracefully instead of throwing an error.
    if utf16_len(text) <= 1024:
        photo_stream = None
        try:
            photo_bytes = await bot1.download_profile_photo(user_id, file=bytes)
            if photo_bytes:
                photo_stream = io.BytesIO(photo_bytes)
                photo_stream.name = "profile.jpg"
        except Exception:
            photo_stream = None
        if photo_stream:
            try:
                await bot1.send_file(
                    event.chat_id, photo_stream, caption=text,
                    parse_mode='html', reply_to=event.id, buttons=buttons
                )
                return
            except Exception:
                pass
    await event.reply(text, parse_mode='html', buttons=buttons)






ACH_ENTRIES_PER_PAGE = 7

async def send_achievements_page(client, chat_id, user_id, mention, page=1, edit_msg_id=None):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    earned_ids = set(user_doc.get("achievements", [])) if user_doc else set()
    entries = []
    for ach in ACHIEVEMENTS:
        tick = "✅" if ach["id"] in earned_ids else "🔒"
        entries.append(f"{tick} {ach['emoji']} <b>{ach['name']}</b>\n<i>{ach['desc']}</i>")
    total_pages = max(1, (len(entries) + ACH_ENTRIES_PER_PAGE - 1) // ACH_ENTRIES_PER_PAGE)
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    start_idx = (page - 1) * ACH_ENTRIES_PER_PAGE
    page_entries = entries[start_idx:start_idx + ACH_ENTRIES_PER_PAGE]
    header = (
        f"🏅 <b>ACHIEVEMENTS</b> — {mention}\n"
        f"📊 <b>Unlocked:</b> <code>{len(earned_ids)}/{len(ACHIEVEMENTS)}</code>\n"
        f"📑 <b>Page:</b> <code>{page}/{total_pages}</code>\n"
    )
    output_text = header + "\n" + "\n".join(page_entries)
    buttons = []
    nav_buttons = []
    if page > 1:
        nav_buttons.append(Button.inline("🔵 ⬅️ Prev", data=f"ach_{page-1}_{user_id}"))
    if page < total_pages:
        nav_buttons.append(Button.inline("🔴 Next ➡️", data=f"ach_{page+1}_{user_id}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    if not buttons:
        buttons = None
    if edit_msg_id:
        try:
            await client.edit_message(chat_id, edit_msg_id, output_text, parse_mode='html', buttons=buttons)
        except errors.MessageNotModifiedError:
            pass
    else:
        await client.send_message(chat_id, output_text, parse_mode='html', buttons=buttons)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]achievements(?:@\w+)?$', 'bot1')))
async def achievements_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    await check_and_award_achievements(user_id)
    await send_achievements_page(bot1, event.chat_id, user_id, mention, page=1)

# ==========================================
# 🔗 REFERRAL
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]referral(?:@\w+)?$', 'bot1')))
async def referral_info_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    ref_count = user_doc.get("referral_count", 0) if user_doc else 0
    bot_me = await bot1.get_me()
    ref_link = f"https://t.me/{bot_me.username}?start=ref_{user_id}"
    msg = f"🔗 <b>YOUR REFERRAL LINK</b>\n⚡ ━━━━━━━━━━━━━━━ ⚡\nShare this link! Friends who join through it count toward your referral total.\n\n🔗 <code>{ref_link}</code>\n\n👥 <b>Total Invited:</b> <code>{ref_count} Friends</code>"
    share_url = f"https://t.me/share/url?url={ref_link}&text=Join%20the%20Bot%20now!"
    await event.reply(msg, parse_mode='html', buttons=[[Button.url("📤 Share Link", share_url)]])

# ==========================================
# 🔍 CHECK CHARACTER (Updated: spawn_count now reflects actual catches)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]check(?:@\w+)?$', 'bot1')))
async def check_bare_usage_handler(event):
    await event.reply(
        "📌 <b>Usage:</b> <code>/check [CharID]</code>\n"
        "<i>Example:</i> <code>/check 1234</code>",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]check(?:@\w+)?\s+([a-zA-Z0-9_]+)$', 'bot1')))
async def check_character_id_handler(event):
    char_id_input = normalize_char_id_input(event.pattern_match.group(1))
    
    # ✅ Case-Insensitive ရှာဖို့
    character = await characters_base_col.find_one({
        "char_id": {"$regex": f"^{char_id_input}$", "$options": "i"}
    })
    
    if not character:
        return await event.reply(f"<b>✗ Character ID not found!</b>", parse_mode='html')
    
    # ✅ spawn_count က catch အရေအတွက်ကိုပြတယ်
    spawn_count = character.get("spawn_count", 0)
    limit = character.get("spawn_limit", 0)
    
    # ✅ ပြသပုံ
    if limit == 0:
        spawns_line = f"<code>{spawn_count}</code> (♾️ Infinite)"
    else:
        remaining = max(0, limit - spawn_count)
        spawns_line = f"<code>{spawn_count}/{limit}</code> (<code>{remaining} left</code>)"
    
    # ✅ Top 10 Collectors — ranked by catch count first, then by whoever caught it
    # EARLIEST (lowest caught_date) as the tiebreaker, so the first person to ever land
    # this card shows up as #1 instead of wherever Mongo's tie order happens to place them.
    pipeline = [
        {"$match": {"harem.char_id": character['char_id']}},
        {"$project": {
            "fullname": "$fullname",
            "user_id": "$user_id",
            "matches": {"$filter": {
                "input": "$harem",
                "as": "item",
                "cond": {"$eq": ["$$item.char_id", character['char_id']]}
            }}
        }},
        {"$project": {
            "fullname": 1,
            "user_id": 1,
            "count": {"$size": "$matches"},
            "first_caught": {"$min": "$matches.caught_date"}
        }},
        {"$sort": {"count": -1, "first_caught": 1}},
        {"$limit": 10}
    ]
    top_hunters = await users_catcher_col.aggregate(pipeline).to_list(length=10)
    
    leaderboard_str = ""
    for idx, u in enumerate(top_hunters, start=1):
        uname = escape_html(clean_display_name(u.get("fullname"), fallback=f"Agent {u['user_id']}"))
        # ✅ Mention ပါစေ — tg://user deep link works off the stored user_id alone (no extra
        # get_entity round-trip needed), so tapping a name opens that collector's account.
        mention = f"<a href='tg://user?id={u['user_id']}'>{uname}</a>"
        leaderboard_str += f" <b>{idx}.</b> {mention} — <code>x{u['count']}</code>\n"
    
    info_text = (
        f"🎒 <b>Here's the record on this one</b>\n\n"
        f"🍬 <b>Asset ID:</b> <code>{display_char_id(character['char_id'])}</code>\n"
        f"☃️ <b>Name:</b> <code>{character['name']}</code>\n"
        f"🫧 <b>Category:</b> <code>{character['category']}</code>\n"
        f"🦋 <b>Rarity:</b> {character['rarity']}\n"
        f"{artist_line(character)}"
        f"🎡 <b>Event:</b> <code>{escape_html(character.get('event', 'General'))}</code>\n"
        f"📈 <b>Global Catches:</b> {spawns_line}\n\n"
        f"🏆 <b>TOP 10 COLLECTORS</b>\n"
        f"{leaderboard_str if leaderboard_str else 'No collectors yet.'}"
    )

    async def _send_check(media):
        return await event.reply(info_text, parse_mode='html', file=media)

    sent = await send_with_char_media(character["char_id"], character["storage_msg_id"], _send_check)
    if sent is None:
        await event.reply(info_text, parse_mode='html')
# ==========================================
# ==========================================
# 📖 DEX (Fixed - No Redis Dependency)
# ==========================================
DEX_CATEGORIES_PER_PAGE = 15
DEX_CARDS_PER_PAGE = 15

def _dex_rarity_weight(rarity_str):
    return rarity_rank_value(rarity_str)

async def _dex_get_all_characters():
    """Get all characters directly from DB (bypass Redis cache for reliability)."""
    return await characters_base_col.find({}, {"_id": 0}).to_list(length=None)

async def _dex_get_all_categories():
    """Get all categories directly from DB."""
    return await characters_base_col.distinct("category")

async def _dex_get_owned_ids(user_id):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        return set()
    return {c.get("char_id") for c in user_doc.get("harem", []) if isinstance(c, dict) and c.get("char_id")}

# ---- /dex : Show all categories with pagination ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]dex(?:@\w+)?$', 'bot1')))
async def dex_categories_handler(event):
    user_id = event.sender_id
    owned_ids = await _dex_get_owned_ids(user_id)
    all_categories = await _dex_get_all_categories()
    
    if not all_categories:
        return await event.reply("📭 <b>No categories found!</b>", parse_mode='html')
    
    all_categories = sorted(all_categories, key=lambda x: x.lower())
    all_chars = await _dex_get_all_characters()
    
    category_data = []
    for cat in all_categories:
        total = sum(1 for c in all_chars if c.get("category") == cat)
        owned = sum(1 for c in all_chars if c.get("category") == cat and c["char_id"] in owned_ids)
        category_data.append((cat, total, owned))
    
    total_pages = (len(category_data) + DEX_CATEGORIES_PER_PAGE - 1) // DEX_CATEGORIES_PER_PAGE
    await _dex_send_categories_page(event, category_data, 0, total_pages, owned_ids, all_chars)

async def _dex_send_categories_page(event, category_data, page, total_pages, owned_ids, all_chars, edit_msg_id=None):
    start = page * DEX_CATEGORIES_PER_PAGE
    end = min(start + DEX_CATEGORIES_PER_PAGE, len(category_data))
    page_data = category_data[start:end]
    
    total_all = len(all_chars)
    owned_all = len(owned_ids & {c["char_id"] for c in all_chars})
    
    text = f"📖 <b>CHARACTER DEX</b>\n"
    text += f"🧩 <b>Total:</b> <code>{owned_all}/{total_all}</code> caught\n"
    text += f"📑 <b>Page {page + 1}/{total_pages}</b> · <b>Categories:</b> <code>{len(category_data)}</code>\n\n"
    text += f"<i>👇 Tap a category to see all cards</i>\n\n"
    
    for idx, (cat, total, owned) in enumerate(page_data, start=start + 1):
        marker = "🟩" if owned == total else ("🟨" if owned > 0 else "⬜")
        text += f"{marker} <b>{idx}.</b> <code>{escape_html(cat)}</code> — <b>{owned}/{total}</b>\n"
    
    buttons = []
    nav_buttons = []
    if page > 0:
        nav_buttons.append(Button.inline("◀ Prev", data=f"dex_cat_page_{page - 1}"))
    if page < total_pages - 1:
        nav_buttons.append(Button.inline("Next ▶", data=f"dex_cat_page_{page + 1}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    
    if edit_msg_id:
        try:
            await bot1.edit_message(event.chat_id, edit_msg_id, text, parse_mode='html', buttons=buttons)
        except errors.MessageNotModifiedError:
            pass
    else:
        await event.reply(text, parse_mode='html', buttons=buttons)

# ---- /search [Category] ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]search(?:@\w+)?\s+(.+)$', 'bot1')))
async def dex_search_handler(event):
    user_id = event.sender_id
    category_query = event.pattern_match.group(1).strip()
    owned_ids = await _dex_get_owned_ids(user_id)
    
    all_categories = await _dex_get_all_categories()
    matched_cat = next((c for c in all_categories if c and c.lower() == category_query.lower()), None)
    
    if not matched_cat:
        return await event.reply(
            f"❌ <b>No category named '{escape_html(category_query)}'</b>\n"
            f"💡 Use <code>/dex</code> to see all categories.",
            parse_mode='html'
        )
    
    all_chars = await _dex_get_all_characters()
    cat_chars = [c for c in all_chars if c.get("category") == matched_cat]
    cat_chars.sort(key=lambda x: (-_dex_rarity_weight(x.get("rarity", "")), x.get("name", "").lower()))
    
    total_pages = (len(cat_chars) + DEX_CARDS_PER_PAGE - 1) // DEX_CARDS_PER_PAGE
    await _dex_send_category_detail(event, matched_cat, cat_chars, owned_ids, 0, total_pages)

async def _dex_send_category_detail(event, category, cat_chars, owned_ids, page, total_pages, edit_msg_id=None):
    start = page * DEX_CARDS_PER_PAGE
    end = min(start + DEX_CARDS_PER_PAGE, len(cat_chars))
    page_chars = cat_chars[start:end]
    
    total_n = len(cat_chars)
    owned_n = sum(1 for c in cat_chars if c["char_id"] in owned_ids)
    pct = int((owned_n / total_n) * 100) if total_n else 0
    
    rarity_counter = Counter(classify_rarity(c.get("rarity", "")) for c in cat_chars)
    breakdown_lines = " | ".join(
        f"{RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)}{tier[:3]} <code>{rarity_counter[tier]}</code>"
        for tier in RARITY_TIERS if rarity_counter.get(tier)
    )
    
    text = f"📖 <b>{escape_html(category)}</b> ({owned_n}/{total_n} · {pct}%)\n"
    text += f"📑 <b>Page {page + 1}/{total_pages}</b>\n"
    text += f"{breakdown_lines}\n\n"
    
    for idx, card in enumerate(page_chars, start=start + 1):
        char_id = card["char_id"]
        owned = "✅" if char_id in owned_ids else "❌"
        rarity_display = card.get("rarity", "➖")
        event_text = card.get("event", "General")
        if event_text == "General":
            event_text = "➖"
        text += f"{owned} <b>{idx}.</b> {rarity_display} <code>{escape_html(card['name'])}</code> [<code>{display_char_id(char_id)}</code>]\n"
        text += f"   🎪 {escape_html(event_text)}\n"
    
    buttons = []
    nav_buttons = []
    if page > 0:
        nav_buttons.append(Button.inline("◀ Prev", data=f"dex_detail_{category}_{page - 1}"))
    if page < total_pages - 1:
        nav_buttons.append(Button.inline("Next ▶", data=f"dex_detail_{category}_{page + 1}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    buttons.append([Button.inline("🔙 Back to Categories", data="dex_back_categories")])
    buttons.append([Button.switch_inline(f"👀 View {category} Gallery", query=f"dex.{category}", same_peer=True)])
    
    if edit_msg_id:
        try:
            await bot1.edit_message(event.chat_id, edit_msg_id, text, parse_mode='html', buttons=buttons)
        except errors.MessageNotModifiedError:
            pass
    else:
        await event.reply(text, parse_mode='html', buttons=buttons)

# ---- Callback handlers ----
@bot1.on(events.CallbackQuery(pattern=r'^dex_cat_page_(\d+)$'))
async def dex_cat_page_callback(event):
    page = int(event.pattern_match.group(1))
    user_id = event.sender_id
    owned_ids = await _dex_get_owned_ids(user_id)
    all_categories = sorted(await _dex_get_all_categories(), key=lambda x: x.lower())
    all_chars = await _dex_get_all_characters()
    
    category_data = []
    for cat in all_categories:
        total = sum(1 for c in all_chars if c.get("category") == cat)
        owned = sum(1 for c in all_chars if c.get("category") == cat and c["char_id"] in owned_ids)
        category_data.append((cat, total, owned))
    
    total_pages = (len(category_data) + DEX_CATEGORIES_PER_PAGE - 1) // DEX_CATEGORIES_PER_PAGE
    await _dex_send_categories_page(event, category_data, page, total_pages, owned_ids, all_chars, edit_msg_id=event.message_id)
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^dex_detail_([^_]+)_(\d+)$'))
async def dex_detail_page_callback(event):
    category = event.pattern_match.group(1)
    if isinstance(category, bytes):
        category = category.decode('utf-8')
    page = int(event.pattern_match.group(2))
    user_id = event.sender_id
    owned_ids = await _dex_get_owned_ids(user_id)
    all_chars = await _dex_get_all_characters()
    
    cat_chars = [c for c in all_chars if c.get("category") == category]
    cat_chars.sort(key=lambda x: (-_dex_rarity_weight(x.get("rarity", "")), x.get("name", "").lower()))
    total_pages = (len(cat_chars) + DEX_CARDS_PER_PAGE - 1) // DEX_CARDS_PER_PAGE
    
    await _dex_send_category_detail(event, category, cat_chars, owned_ids, page, total_pages, edit_msg_id=event.message_id)
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^dex_back_categories$'))
async def dex_back_categories_callback(event):
    user_id = event.sender_id
    owned_ids = await _dex_get_owned_ids(user_id)
    all_categories = sorted(await _dex_get_all_categories(), key=lambda x: x.lower())
    all_chars = await _dex_get_all_characters()
    
    category_data = []
    for cat in all_categories:
        total = sum(1 for c in all_chars if c.get("category") == cat)
        owned = sum(1 for c in all_chars if c.get("category") == cat and c["char_id"] in owned_ids)
        category_data.append((cat, total, owned))
    
    total_pages = (len(category_data) + DEX_CATEGORIES_PER_PAGE - 1) // DEX_CATEGORIES_PER_PAGE
    await _dex_send_categories_page(event, category_data, 0, total_pages, owned_ids, all_chars, edit_msg_id=event.message_id)
    await event.answer()

# ---- /dex [Category] - shortcut ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]dex(?:@\w+)?\s+(.+)$', 'bot1')))
async def dex_with_category_handler(event):
    # Same as /search
    user_id = event.sender_id
    category_query = event.pattern_match.group(1).strip()
    owned_ids = await _dex_get_owned_ids(user_id)
    
    all_categories = await _dex_get_all_categories()
    matched_cat = next((c for c in all_categories if c and c.lower() == category_query.lower()), None)
    
    if not matched_cat:
        return await event.reply(
            f"❌ <b>No category named '{escape_html(category_query)}'</b>\n"
            f"💡 Use <code>/dex</code> to see all categories.",
            parse_mode='html'
        )
    
    all_chars = await _dex_get_all_characters()
    cat_chars = [c for c in all_chars if c.get("category") == matched_cat]
    cat_chars.sort(key=lambda x: (-_dex_rarity_weight(x.get("rarity", "")), x.get("name", "").lower()))
    
    total_pages = (len(cat_chars) + DEX_CARDS_PER_PAGE - 1) // DEX_CARDS_PER_PAGE
    await _dex_send_category_detail(event, matched_cat, cat_chars, owned_ids, 0, total_pages)
TOP_MEDALS = {0: "🥇", 1: "🥈", 2: "🥉"}

async def _resolve_one_top_mention(client, user_id, stored_fullname):
    """Best-effort LIVE clickable mention (tg://user?id=...) for a leaderboard row, so /top
    and /gtop always point at the actual current account instead of a possibly-stale stored
    name. Falls back to the safely-sanitized stored fullname if the entity can't be resolved
    (e.g. the bot has genuinely never seen that user) — never breaks the leaderboard."""
    try:
        entity = await client.get_entity(user_id)
        first = getattr(entity, 'first_name', '') or ''
        last = getattr(entity, 'last_name', '') or ''
        live_name = f"{first} {last}".strip() or getattr(entity, 'username', '') or f"User {user_id}"
        display = clean_display_name(live_name, fallback=f"User {user_id}")
    except Exception:
        display = clean_display_name(stored_fullname, fallback=f"User {user_id}")
    return f"<a href='tg://user?id={user_id}'><b>{escape_html(display)}</b></a>"

async def _resolve_top_mentions(client, users):
    # ⚡ PERFORMANCE: resolving 10 rows one-at-a-time meant 10 sequential Telegram round-trips
    # before /top or /gtop could reply — easily a couple of seconds, and the sort of thing
    # that reads as "the bot got heavier". Resolving all of them concurrently turns that into
    # a single parallel batch instead.
    return await asyncio.gather(*(
        _resolve_one_top_mention(client, u["user_id"], u.get("fullname")) for u in users
    ))

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]top(?:@\w+)?$', 'bot1')))
async def local_group_top_handler(event):
    if event.is_private: return
    chat_id = event.chat_id
    cursor = users_catcher_col.find({f"group_catches.{str(chat_id)}": {"$gt": 0}}).sort(f"group_catches.{str(chat_id)}", -1).limit(10)
    top_users = await cursor.to_list(length=10)
    if not top_users:
        return await event.reply(f"🏆 <b>No rank data in this group yet.</b>\n<i>Catch a card to get on the board!</i>", parse_mode='html')
    mentions = await _resolve_top_mentions(event.client, top_users)
    lines = []
    for i, (u, mention) in enumerate(zip(top_users, mentions)):
        count = u["group_catches"][str(chat_id)]
        rank_tag = TOP_MEDALS.get(i, f"<code>#{i + 1}</code>")
        lines.append(f"{rank_tag}  {mention} — <code>{count:,} cards</code>")
    msg = (
        f"🏆 <b>TOP 10 HUNTERS IN THIS GROUP</b>\n"
        f"{chr(10).join(lines)}"
    )
    await event.reply(msg, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]gtop(?:@\w+)?$', 'bot1')))
async def global_top_handler(event):
    cursor = users_catcher_col.find({"total_caught": {"$gt": 0}}).sort("total_caught", -1).limit(10)
    top_users = await cursor.to_list(length=10)
    if not top_users:
        return await event.reply(f"🌐 <b>No global ranking yet.</b>\n<i>Catch a card to get on the board!</i>", parse_mode='html')
    mentions = await _resolve_top_mentions(event.client, top_users)
    lines = []
    for i, (u, mention) in enumerate(zip(top_users, mentions)):
        count = u.get("total_caught", 0)
        rank_tag = TOP_MEDALS.get(i, f"<code>#{i + 1}</code>")
        lines.append(f"{rank_tag}  {mention} — <code>{count:,} cards</code>")
    msg = (
        f"🌐 <b>GLOBAL TOP 10 HUNTERS</b>\n"
        f"{chr(10).join(lines)}"
    )
    await event.reply(msg, parse_mode='html')
# ==========================================
# 💰 BALANCE (Inline Buttons - ၂x၂ ပုံစံ)
# ==========================================


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftranks(?:@\w+)?$', 'bot1')))
async def gift_ranks_handler(event):
    giver_lines = "\n".join(f"{emoji} <b>{title}</b> — <code>{th}+</code> gifts" for th, emoji, title in reversed(GIFT_GIVER_TITLES))
    receiver_lines = "\n".join(f"{emoji} <b>{title}</b> — <code>{th}+</code> gifts" for th, emoji, title in reversed(GIFT_RECEIVER_TITLES))
    text = (
        f"🎖️ <b>GIFT RANKS</b>\n"
        f"<i>/gift ကတ်တွေ ပေး/ရ အရေအတွက်အလိုက် Rank အဆင့်ဆင့် အလိုအလျောက် ရရှိနိုင်ပါတယ်</i>\n\n"
        f"📤 <b>Giver Rank</b> <i>(/gift ပေးသမျှ အရေအတွက်)</i>\n"
        f"{giver_lines}\n"
        f"📥 <b>Receiver Rank</b> <i>(/gift လက်ခံရသမျှ အရေအတွက်)</i>\n"
        f"{receiver_lines}\n"
        f"<code>/profile</code> <i>မှာ ကိုယ့် Rank လက်ရှိကို ကြည့်နိုင်ပါတယ်။</i>"
    )
    await event.reply(text, parse_mode='html')



# ==========================================
# 🎖️ GIFT RANK TITLES — 6 escalating Burmese titles for GIVING (total_gifted) and a separate
# 6 for RECEIVING (total_gift_received). Purely a cosmetic badge computed live off the two
# counters already tracked on every /gift — nothing extra to keep in sync. Sorted descending
# by threshold so the first match in a scan is always the highest tier reached.
# ==========================================
GIFT_TIER_THRESHOLDS = (10, 30, 50, 100, 200, 300)  # 300+ is the open-ended top tier

GIFT_GIVER_TITLES = [  # (threshold, emoji, title) — "the one who gives cards away"
    (300, "🏆", "ကဒ်ဘုရင်"),        # Card King
    (200, "👑", "ကဒ်မင်းလေး"),          # Card Prince
    (100, "⚔️", "ကဒ်သခင်"),         # Card Lord
    (50, "📜", "ကဒ်ဆရာ"),           # Card Master
    (30, "🎗️", "ကဒ်ရက်ရောရှင်"),    # Generous Card-Giver
    (10, "🎁", "ကဒ်အလှူရှင်"),        # Card Donor
]
GIFT_RECEIVER_TITLES = [  # (threshold, emoji, title) — "the one showered with cards"
    (300, "👑", "ကဒ်ဘုန်းရှင်"),     # The Glorious One
    (200, "🌺", "ကဒ်ဂုဏ်ရှင်"),      # The Honored One
    (100, "💎", "ကဒ်မြတ်နိုးရှင်"),   # The Cherished One
    (50, "🌟", "ကဒ်ကျော်စောရှင်"),   # The Renowned One
    (30, "💝", "ကဒ်နှစ်လိုရှင်"),     # The Beloved One
    (10, "🎀", "ကဒ်ကံရှင်"),         # Fortune's Chosen
]

def _gift_title_for_count(count, titles_desc):
    """titles_desc must be sorted descending by threshold. Returns (emoji, title) for the
    highest tier `count` qualifies for, or None if below every threshold."""
    for threshold, emoji, title in titles_desc:
        if count >= threshold:
            return emoji, title
    return None

def get_giver_title(total_gifted):
    return _gift_title_for_count(total_gifted, GIFT_GIVER_TITLES)

def get_receiver_title(total_gift_received):
    return _gift_title_for_count(total_gift_received, GIFT_RECEIVER_TITLES)

# ==========================================
# 🎁 GIFT HISTORY (used by the /profile, /myinfo "Gift History" button)
# ==========================================
GIFT_HISTORY_PAGE_SIZE = 5

async def render_gift_history_page(user_id, page):
    skip = page * GIFT_HISTORY_PAGE_SIZE
    total = await gift_history_col.count_documents({"sender_id": user_id})
    rows = await gift_history_col.find({"sender_id": user_id}).sort("timestamp", -1).skip(skip).limit(GIFT_HISTORY_PAGE_SIZE).to_list(length=GIFT_HISTORY_PAGE_SIZE)
    if not rows:
        body = "<i>No gifts sent yet.</i>" if page == 0 else "<i>No more entries.</i>"
    else:
        lines = []
        for r in rows:
            char_doc = await characters_base_col.find_one({"char_id": r["char_id"]})
            char_name = escape_html(char_doc["name"]) if char_doc else r["char_id"]
            receiver_doc = await users_catcher_col.find_one({"user_id": r["receiver_id"]})
            receiver_name = escape_html(clean_display_name(receiver_doc.get("fullname") if receiver_doc else None, fallback=f"User {r['receiver_id']}"))
            when = datetime.fromtimestamp(r["timestamp"], TZ).strftime("%Y-%m-%d")
            lines.append(f"🎁 <b>{char_name}</b> → {receiver_name} <i>({when})</i>")
        body = "\n".join(lines)
    text = f"🎁 <b>Your Gift History</b> ({total} total)\n{body}"
    nav = []
    if page > 0:
        nav.append(Button.inline("◀ Prev", data=f"gh_{user_id}_{page - 1}"))
    if skip + GIFT_HISTORY_PAGE_SIZE < total:
        nav.append(Button.inline("Next ▶", data=f"gh_{user_id}_{page + 1}"))
    buttons = [nav] if nav else None
    return text, buttons


# ==========================================
# 🎁 GIFT (fixed)
# ==========================================
ADDED_OWNER_GIFT_LIMIT_PER_CARD = 3  # /addowner grantees: like OWNER_ID, can gift ANY
# character with no real catch needed — max N times per card, tracked per (user, char_id).
# card can be gifted before it's exhausted — see gift_asset_handler/gift_callback_handler.

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]gift(?:@\w+)?\s+(.+)$', 'bot1')))
async def gift_asset_handler(event):
    if not event.is_reply:
        return await event.reply("❌ <b>…reply to the person you want to gift her to.</b>", parse_mode='html')

    char_id = normalize_char_id_input(event.pattern_match.group(1))
    sender_id = event.sender_id
    reply_msg = await event.get_reply_message()
    receiver_id = reply_msg.sender_id

    if sender_id == receiver_id:
        return await event.reply("❌ <b>…can't gift yourself.</b>", parse_mode='html')

    # 🩹 FIX (moved to gift_callback_handler below, per owner report): the 1000 USD gift fee
    # used to be charged RIGHT HERE — before checking whether char_id even exists or the sender
    # actually owns it. A typo'd/nonexistent char_id (e.g. /gift 21345), or trying to gift a
    # card you don't have, still cost 1000 USD every single time, with zero refund — even
    # hitting Cancel on the confirmation didn't give it back. It's now only charged once
    # validation has passed AND the gift is confirmed.
    char_data = await characters_base_col.find_one({"char_id": char_id})
    if not char_data:
        return await event.reply("❌ <b>…I don't know anyone with that ID.</b>", parse_mode='html')

    if sender_id == OWNER_ID:
        pass  # 👑 unlimited vault — no ownership check needed, see gift_callback_handler
    elif sender_id in added_owner_ids:
        # 👑 Added owner (see /addowner): gifts like the real owner does — ANY character,
        # no real catch needed at all (char_data above already confirms it exists, that's
        # enough) — the only difference from OWNER_ID is the ADDED_OWNER_GIFT_LIMIT_PER_CARD
        # cap per card, tracked via added_owner_gift_count. See gift_callback_handler for
        # where that quota is actually enforced/incremented.
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        gift_count_used = ((sender_doc or {}).get("added_owner_gift_count") or {}).get(char_id, 0)
        if gift_count_used >= ADDED_OWNER_GIFT_LIMIT_PER_CARD:
            return await event.reply(
                f"❌ <b>…you've already gifted this card its max {ADDED_OWNER_GIFT_LIMIT_PER_CARD} times.</b>",
                parse_mode='html'
            )
    else:
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        sender_harem = sender_doc.get("harem", []) if sender_doc else []
        char_item = next((x for x in sender_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") != "market"), None)
        if not char_item:
            return await event.reply(f"❌ <b>…she's not yours to give.</b>", parse_mode='html')

    r_mention = await get_html_mention(event, receiver_id)
    confirm_text = (
        f"◈ <b>let her go?</b>\n\n"
        f"🐇 <b>Character:</b> <code>{char_data['name']}</code> (<code>{display_char_id(char_id)}</code>)\n"
        f"🦋 <b>Rarity:</b> {char_data.get('rarity', 'Unknown')}\n"
        f"{artist_line(char_data)}"
        f"🎯 <b>To:</b> {r_mention}\n\n"
        f"…she'll belong to {r_mention} instead"
    )

    buttons = [
        [
            Button.inline("🤍 yes, send her", data=f"gift_confirm_{sender_id}_{receiver_id}_{char_id}"),
            Button.inline("…not yet", data=f"gift_cancel_{sender_id}_{receiver_id}_{char_id}")
        ]
    ]

    async def _send_gift_confirm(media):
        return await event.reply(confirm_text, file=media, buttons=buttons, parse_mode='html')

    sent = await send_with_char_media(char_data["char_id"], char_data["storage_msg_id"], _send_gift_confirm)
    if sent is None:
        await event.reply(confirm_text, buttons=buttons, parse_mode='html')

@bot1.on(events.CallbackQuery(pattern=r'^gift_(confirm|cancel)_(\d+)_(\d+)_([a-zA-Z0-9_]+)$'))
async def gift_callback_handler(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    char_id_raw = event.pattern_match.group(4)
    if isinstance(char_id_raw, bytes):
        char_id = char_id_raw.decode('utf-8').upper()
    else:
        char_id = char_id_raw.upper()
    if event.sender_id != sender_id:
        return await event.answer("❌ This action is not for you!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    if action == "cancel":
        await event.edit(
            f"…<b>changed your mind.</b>\n\n"
            f"Card <code>{display_char_id(char_id)}</code> stays with you.\n"
            f"🐇 maybe next time",
            parse_mode='html',
            buttons=None
        )
        await event.answer("Gift cancelled.", alert=True)
        return
    # confirm
    if sender_id == OWNER_ID:
        # 👑 Unlimited vault: nothing to remove — this card stays available for every future
        # gift too. Rarity comes straight from the character record instead of a harem item
        # (the owner may never have actually caught this one for real). Gift stats are still
        # tracked for visibility, they just don't touch the owner's real harem array.
        char_data = await characters_base_col.find_one({"char_id": char_id})
        if not char_data:
            await event.edit(
                f"❌ <b>…she's gone.</b>\n\n"
                f"Character <code>{display_char_id(char_id)}</code> no longer exists.",
                parse_mode='html',
                buttons=None
            )
            await event.answer("Card not found.", alert=True)
            return
        char_rarity = char_data.get("rarity", "Unknown")
        gift_tier = classify_rarity(char_rarity)
        await users_catcher_col.update_one(
            {"user_id": sender_id},
            {"$inc": {"total_gifted": 1, f"gifted_by_rarity.{gift_tier}": 1}},
            upsert=True
        )
    elif sender_id in added_owner_ids:
        # 👑 Added owner (see /addowner): gifts like OWNER_ID above — nothing to remove, this
        # card stays available for future gifts too, rarity comes straight from the character
        # record (they may never have actually caught this one for real). The ONLY difference
        # from OWNER_ID is the ADDED_OWNER_GIFT_LIMIT_PER_CARD cap, tracked per (user, char_id)
        # via added_owner_gift_count.
        char_data = await characters_base_col.find_one({"char_id": char_id})
        if not char_data:
            await event.edit(
                f"❌ <b>…she's gone.</b>\n\n"
                f"Character <code>{display_char_id(char_id)}</code> no longer exists.",
                parse_mode='html',
                buttons=None
            )
            await event.answer("Card not found.", alert=True)
            return
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        gift_count_used = ((sender_doc or {}).get("added_owner_gift_count") or {}).get(char_id, 0)
        if gift_count_used >= ADDED_OWNER_GIFT_LIMIT_PER_CARD:
            await event.edit(
                f"❌ <b>…you've already gifted this card its max {ADDED_OWNER_GIFT_LIMIT_PER_CARD} times.</b>",
                parse_mode='html',
                buttons=None
            )
            await event.answer("Gift limit reached.", alert=True)
            return
        char_rarity = char_data.get("rarity", "Unknown")
        gift_tier = classify_rarity(char_rarity)
        await users_catcher_col.update_one(
            {"user_id": sender_id},
            {"$inc": {"total_gifted": 1, f"gifted_by_rarity.{gift_tier}": 1, f"added_owner_gift_count.{char_id}": 1}},
            upsert=True
        )
    else:
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        sender_harem = sender_doc.get("harem", []) if sender_doc else []
        char_item = next((x for x in sender_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") != "market"), None)
        if not char_item:
            await event.edit(
                f"❌ <b>…she's already gone.</b>\n\n"
                f"you no longer have card <code>{display_char_id(char_id)}</code>.\n"
                f"☄️ luck played a little trick on you",
                parse_mode='html',
                buttons=None
            )
            await event.answer("Card not found.", alert=True)
            return
        # 🩹 FIX: atomic $pull-based removal (see remove_one_harem_copy) instead of the old
        # find_one → sender_harem.remove() → $set the whole array back — same lost-update
        # race risk as marketplace/trade/sell fixed earlier.
        char_rarity = char_item.get("rarity", "Unknown")
        gift_tier = char_item.get("rarity_tier") or classify_rarity(char_rarity)
        await remove_one_harem_copy(sender_id, char_id, char_item.get("status", "vault"))
        await users_catcher_col.update_one(
            {"user_id": sender_id},
            {"$inc": {"total_gifted": 1, f"gifted_by_rarity.{gift_tier}": 1}}
        )
        sender_doc_after = await users_catcher_col.find_one({"user_id": sender_id}, {"harem": 1})
        await clear_stale_favorite(sender_id, char_id, (sender_doc_after or {}).get("harem", []))

    r_mention = await get_html_mention(event, receiver_id)
    r_plain_name = await get_plain_name(event, receiver_id)
    await users_catcher_col.update_one(
        {"user_id": receiver_id},
        {
            "$push": {"harem": {"char_id": char_id, "caught_date": time.time(), "rarity": char_rarity, "status": "vault"}},
            "$inc": {"total_caught": 1, "total_gift_received": 1},
            "$set": {"fullname": r_plain_name}
        },
        upsert=True
    )
    try:
        await gift_history_col.insert_one({
            "sender_id": sender_id,
            "receiver_id": receiver_id,
            "char_id": char_id,
            "rarity_tier": gift_tier,
            "timestamp": time.time()
        })
    except Exception as e:
        print(f"gift_history log error: {e}")

    # 🎖️ Gift Rank: pull the sender's fresh post-gift count and work out (a) their current
    # title, and (b) whether THIS gift is the exact moment that crossed them into a new tier
    # (count lands precisely on a threshold — safe since each gift only ever moves a counter
    # up by 1) — that's the promotion banner moment, shown once, right when it happens.
    sender_after = await users_catcher_col.find_one({"user_id": sender_id}, {"total_gifted": 1})
    sender_gift_count = (sender_after or {}).get("total_gifted", 0)
    giver_title = get_giver_title(sender_gift_count)
    giver_promoted = sender_gift_count in GIFT_TIER_THRESHOLDS
    giver_rank_line = f"🎖️ <b>Your Rank:</b> {giver_title[0]} <code>{giver_title[1]}</code>\n" if giver_title else ""
    giver_promo_line = f"\n🎉 <b>ဂုဏ်ယူပါတယ်! Rank အသစ် {giver_title[0]} <code>{giver_title[1]}</code> ရရှိသွားပါပြီ!</b> <i>(Gift {sender_gift_count} ကြိမ်ပြည့်ပါပြီ)</i>" if giver_promoted and giver_title else ""

    # 🎨 A designed confirmation where the gift happened.
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    char_name_display = escape_html(char_doc.get("name", "?")) if char_doc else char_id
    rarity_emoji = RARITY_EMOJI.get(gift_tier, RARITY_DEFAULT_EMOJI)
    s_mention = await get_html_mention(event, sender_id)

    await event.edit(
        f"◈ <b>…she's gone to someone new</b>\n"
        f""
        f"📤 <b>From:</b> {s_mention}\n"
        f"📥 <b>To:</b> {r_mention}\n"
        f"{rarity_emoji} <b>Card:</b> <code>{char_name_display}</code> (<code>{display_char_id(char_id)}</code>)\n"
        f"🦋 <b>Rarity:</b> {char_rarity}\n"
        f"{giver_rank_line}"
        f"\n"
        f"🍔 <i>…all done</i>"
        f"{giver_promo_line}",
        parse_mode='html',
        buttons=None
    )
    await event.answer("Gift sent successfully!", alert=True)
    # 🩹 CHANGED (per owner request): a DM to the receiver used to be sent here too — removed,
    # the in-chat confirmation above is enough now.






# 🩹 FIX: /introduce used to build its whole reply as a single <pre style='...'> block.
# Two separate bugs made it fail completely (silently — no reply, no error visible to the
# user, looked "disappeared"):
#   1. Telegram's HTML parse mode does NOT support a `style` attribute on <pre> (or any
#      tag) — only a bare <pre> or <pre><code class="language-x">. Sending it raised a
#      "can't parse entities" error from Telegram, which the reply call never caught.
#   2. Even with that fixed, the text itself is ~4280 characters — over Telegram's hard
#      4096-char message limit — so it would still have failed to send on length alone.
# This splits the body across as many plain <pre> messages as needed, breaking only on
# line boundaries, so it always sends regardless of how long the list of commands grows.
def _chunk_text_by_lines(text, max_chunk=3900):
    lines = text.split('\n')
    chunks, current, current_len = [], [], 0
    for line in lines:
        added_len = len(line) + 1
        if current and current_len + added_len > max_chunk:
            chunks.append('\n'.join(current))
            current, current_len = [], 0
        current.append(line)
        current_len += added_len
    if current:
        chunks.append('\n'.join(current))
    return chunks

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]introduce(?:@\w+)?$', 'bot1')))
async def introduce_bot_handler(event):
    intro_body = (
        "ဟိုက်  –  YOUR ALL-IN-ONE TELEGRAM BOT\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "\n"
        "    I am a multi‑functional Telegram bot built to keep this group running smoothly.\n"
        "    I combine a character-catching game and group management — all in one place.\n"
        "\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "📌  WHAT I CAN DO FOR YOU (complete list)\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "\n"
        "🛡️  MODERATION\n"
        "    • /info [Reply/@username]  –  user profile card (ID, badges, etc.)\n"
        "    • Auto‑spam detection for stickers & short messages (auto‑mutes repeat offenders)\n"
        "\n"
        "🎮  CATCHING GAME (CHARACTER COLLECTION)\n"
        "    • /who (/w, /waifu) –  reveal the spawned character\n"
        "    • /fuck [name]     –  capture the character\n"
        "    • /harem          –  view your vault (paginated inventory)\n"
        "    • /fav [ID]       –  set a favourite card\n"
        "    • /profile, /myinfo –  check your stats and collection\n"
        "    • /top /gtop      –  local and global leaderboards\n"
        "    • /check [ID]     –  detailed character info & top collectors\n"
        "\n"
        "🎁  SOCIAL\n"
        "    • /gift [cardID]   –  gift a card to someone (reply)\n"
        "    • /referral        –  get your unique invite link\n"
        "\n"
        "🌦️  WEATHER\n"
        "    • /weather         –  live weather for Myanmar & Thailand\n"
        "                         (choose country, then city)\n"
        "\n"
        "📚  HELP & NAVIGATION\n"
        "    • /help            –  detailed command reference\n"
        "    • /introduce       –  you are reading this!\n"
        "\n"
        "⚙️  OWNER‑ONLY (hidden from normal users)\n"
        "    • /addchar, /delchar, /editchar, /setchar, /addartist,\n"
        "      /change CharID (reply to new photo/video)  –  swap a character's media\n"
        "                         (e.g. upgrade a blurry upload) without affecting anyone's catches,\n"
        "      /exportchars      –  send the full character database as a CSV file,\n"
        "      /changeallrarity confirm  –  rebrand all rarity names/emoji DB-wide,\n"
        "      /linkartist, /unlinkartist  –  link an /addartist name to a real Telegram\n"
        "                         account,\n"
        "      /cr CharID no&lt;N&gt;  –  force-change ONE character's rarity tier,\n"
        "      /cr no&lt;N&gt; (as a reply)  –  bulk-change MANY CharIDs at once,\n"
        "      /fspawn, /haitime, /resetstats, /mau, /stealth, etc.\n"
        "\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "💡  Everything is designed to be fun, fair, and easy to follow.\n"
        "    For any help, type /help or ask me directly.\n"
        "\n"
        "📢  Join our community: https://t.me/Comeback_BoD\n"
        "Glad to have you here.\n"
    )
    chunks = _chunk_text_by_lines(intro_body)
    for i, chunk in enumerate(chunks):
        is_last = (i == len(chunks) - 1)
        html_chunk = f"<pre>{chunk}</pre>"
        if is_last:
            await event.reply(html_chunk, parse_mode='html', buttons=[[Button.inline("🏠 Open Menu", data="nav_back_home")]])
        else:
            await event.reply(html_chunk, parse_mode='html')







# ==========================================
# 👑 /addowner — reply to a user's message to grant them the SAME unlimited-vault privilege
# OWNER_ID has: every character counts as "owned" for browsing (/harem, the inline gallery),
# for /fav, AND for /gift — no real /collect catch needed for any of them. The one difference
# from OWNER_ID: gifting is capped at ADDED_OWNER_GIFT_LIMIT_PER_CARD times per card (OWNER_ID
# has no cap at all). See gift_asset_handler/gift_callback_handler for where that's enforced.
# (Card trading — /trade, /buy, /sell, /market — no longer exists in this bot at all, so
# there's nothing left to restrict there; /gift is the only transfer command remaining.)
# ==========================================

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addowner$', 'bot1')))
async def add_owner_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_reply:
        return await event.reply("❌ <b>Reply to the user's message with /addowner.</b>", parse_mode='html')
    replied = await event.get_reply_message()
    target_id = replied.sender_id
    if target_id == OWNER_ID:
        return await event.reply("❌ That's already you.")
    if getattr(await replied.get_sender(), 'bot', False):
        return await event.reply("❌ Can't add a bot as an owner.")
    if target_id in added_owner_ids:
        mention = await get_html_mention(event, target_id)
        return await event.reply(f"❌ {mention} is already an added owner.", parse_mode='html')
    await added_owners_col.update_one(
        {"user_id": target_id},
        {"$set": {"added_by": OWNER_ID, "added_at": time.time()}},
        upsert=True
    )
    added_owner_ids.add(target_id)
    mention = await get_html_mention(event, target_id)
    await event.reply(
        f"👑 <b>Added Owner:</b> {mention}\n"
        f"Character အားလုံးကို ပိုင်ဆိုင်ထားသလို ကြည့်နိုင်ပါပြီ — <code>/harem</code>, gallery, "
        f"<code>/fav</code> အားလုံး အလုပ်လုပ်ပါမယ်။\n"
        f"🎁 <b>Gift</b> လည်း ကဒ်ဘယ်ဟာမဆို ပေးလို့ရပါပြီ (real catch မလိုပါ) — "
        f"ဒါပေမဲ့ ကဒ်တစ်ခုစီကို <b>{ADDED_OWNER_GIFT_LIMIT_PER_CARD} ကြိမ်ထိပဲ</b> ပေးလို့ရပါမယ်။",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]removeowner$', 'bot1')))
async def remove_owner_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_reply:
        return await event.reply("❌ <b>Reply to the user's message with /removeowner.</b>", parse_mode='html')
    replied = await event.get_reply_message()
    target_id = replied.sender_id
    if target_id not in added_owner_ids:
        return await event.reply("❌ That user isn't an added owner.")
    await added_owners_col.delete_one({"user_id": target_id})
    added_owner_ids.discard(target_id)
    mention = await get_html_mention(event, target_id)
    await event.reply(f"✅ Removed added-owner status from {mention}.", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]listowners$', 'bot1')))
async def list_owners_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not added_owner_ids:
        return await event.reply("📭 No added owners yet — use /addowner (as a reply) to add one.")
    lines = []
    for uid in added_owner_ids:
        mention = await get_html_mention(event, uid)
        lines.append(f"• {mention} (<code>{uid}</code>)")
    await event.reply("👑 <b>Added Owners:</b>\n" + "\n".join(lines), parse_mode='html')

# ==========================================
# 🗑️ HAITIME / RESETSTATS / GIFTALL / STEALTH
# ==========================================

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]resetstats(?:@\w+)?$', 'bot1')))
async def reset_group_counters_by_owner(event):
    if event.sender_id != OWNER_ID: return
    try:
        # group_spawn_counters (in-memory) is the source of truth for spawn decisions now —
        # clearing only the Mongo copy would do nothing (the next periodic flush would just
        # overwrite it right back with whatever's still live in memory).
        group_spawn_counters.clear()
        await groups_counters_col.update_many({}, {"$set": {"counter": 0}})
        await event.reply(f"⚙️ <b>All counters reset to 0.</b>", parse_mode='html')
    except Exception as e:
        await event.reply(f"❌ Error: <code>{e}</code>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]haitime(?:@\w+)?$', 'bot1')))
async def show_spawn_target_status(event):
    if event.sender_id != OWNER_ID: return
    global_config = await groups_config_col.find_one({"chat_id": GLOBAL_SPAWN_CHAT_KEY})
    global_target = global_config.get("spawn_target", 50) if global_config else 50
    overrides = await groups_config_col.find(
        {"chat_id": {"$ne": GLOBAL_SPAWN_CHAT_KEY}, "spawn_target": {"$exists": True}}
    ).to_list(length=None)
    text = (
        f"<b>SPAWN THRESHOLD STATUS</b>\n"
        f"🌐 <b>Global (default for all groups):</b> <code>{global_target}</code> messages\n"
    )
    if overrides:
        text += f"\n📌 <b>{len(overrides)} group(s) currently have their own override:</b>\n"
        for doc in overrides[:20]:
            text += f"  • <code>{doc['chat_id']}</code> → <code>{doc.get('spawn_target')}</code>\n"
        if len(overrides) > 20:
            text += f"  … and {len(overrides) - 20} more\n"
        text += "<i>Setting a new global value with /haitime [count] clears all of these automatically.</i>"
    else:
        text += "\n📌 No group has its own override — every group follows the global value above."
    text += (
        f"\n\n📖 <b>Usage:</b>\n"
        f"<code>/haitime [count]</code> — set the global default\n"
        f"<code>/haitime [chat_id] [count]</code> — override one specific group"
    )
    await event.reply(text, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]haitime(?:@\w+)?\s+(-?\d+)(?:\s+(-?\d+))?$', 'bot1')))
async def change_spawn_target_handler(event):
    if event.sender_id != OWNER_ID: return
    args = event.pattern_match.groups()
    try:
        val1 = int(args[0])
        val2 = int(args[1]) if args[1] else None
    except (ValueError, TypeError):
        return await event.reply("⚠️ <b>Invalid format.</b>\nUsage: <code>/haitime <count></code> or <code>/haitime <chat_id> <count></code>", parse_mode='html')
    if val2 is not None:
        target_chat_id = val1
        new_target = val2
        scope_text = f"Group ID: <code>{target_chat_id}</code>"
    else:
        target_chat_id = GLOBAL_SPAWN_CHAT_KEY
        new_target = val1
        scope_text = "Global (default for every group without its own override)"
    if new_target <= 0: return await event.reply("❌ <b>Count must be > 0.</b>", parse_mode='html')
    await groups_config_col.update_one({"chat_id": target_chat_id}, {"$set": {"spawn_target": new_target}}, upsert=True)
    cleared_count = 0
    if target_chat_id == GLOBAL_SPAWN_CHAT_KEY:
        # 🩹 FIX: setting the global value used to leave every per-group override untouched,
        # so those groups silently kept ignoring it — the owner had to hunt down and clear each
        # one by hand. /haitime [count] (no chat_id) now means "this is the value, everywhere,
        # no exceptions": every other group's override is cleared in the same call.
        clear_result = await groups_config_col.update_many(
            {"chat_id": {"$ne": GLOBAL_SPAWN_CHAT_KEY}, "spawn_target": {"$exists": True}},
            {"$unset": {"spawn_target": ""}}
        )
        cleared_count = clear_result.modified_count
    # A global-default change affects every chat that falls back to it, and we can't tell
    # from here which cached entries that includes — clearing the whole cache is cheap
    # (it's just a dict) and guarantees no group keeps running on a stale value.
    _spawn_target_cache.clear()
    # Verify the write actually persisted before confirming to the owner
    confirm_doc = await groups_config_col.find_one({"chat_id": target_chat_id})
    confirmed_value = confirm_doc.get("spawn_target") if confirm_doc else None
    if confirmed_value != new_target:
        return await event.reply(
            f"❌ <b>Notice:</b> The update didn't save correctly. Please try again.\n"
            f"<code>Expected {new_target}, found {confirmed_value}</code>",
            parse_mode='html'
        )
    extra_note = f"\n✅ <i>{cleared_count} group override(s) cleared — every group now follows this value.</i>" if cleared_count else ""
    await event.reply(
        f"⚙️ <b>SPAWN THRESHOLD UPDATED</b>\n"
        f"New spawn count for {scope_text} set to <code>{new_target}</code> messages."
        f"{extra_note}",
        parse_mode='html'
    )

async def ghost_spawn_cleaner():
    while True:
        try:
            current_time = time.time()
            expired_chats = []
            for chat_id, data in active_group_spawns.items():
                if current_time - data.get("spawn_time", 0) > 1800:
                    expired_chats.append(chat_id)
            for chat_id in expired_chats:
                if chat_id in active_group_spawns: del active_group_spawns[chat_id]
                if chat_id in spawn_locks: del spawn_locks[chat_id]
            # 🛡️ RELIABILITY: pending_rarity_quiz entries are normally cleaned up by
            # rarity_gate_quiz_timeout_watcher a few minutes after posting. This is a
            # belt-and-suspenders safety net — if that watcher task ever died without running
            # its cleanup, a leftover entry here would silently block ALL future auto-spawns
            # in that chat forever (see the guard at the top of global_message_counter_handler).
            expired_quizzes = [
                cid for cid, quiz in pending_rarity_quiz.items()
                if current_time - quiz.get("quiz_time", 0) > RARITY_GATE_TIMEOUT_SECONDS + 60
            ]
            for cid in expired_quizzes:
                if cid in pending_rarity_quiz: del pending_rarity_quiz[cid]
        except Exception as e:
            logging.error(f"Cleaner Error: {e}")
        await asyncio.sleep(300)

# ==========================================
# 🚨 STEALTH CONTROLLER
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]stealth(?:@\w+)?(?:\s+(on|off))?$', 'bot1')))
async def toggle_stealth(event):
    global STEALTH_MAU_MODE
    if event.sender_id != OWNER_ID: return
    args = event.pattern_match.group(1)
    if not args:
        status = "🟢 ACTIVE" if STEALTH_MAU_MODE else "🔴 INACTIVE"
        return await event.reply(f"<b>Stealth MAU Status:</b> {status}\n📌 <code>/stealth on</code> or <code>/stealth off</code>", parse_mode='html')
    if args.lower() == "on":
        STEALTH_MAU_MODE = True
        await event.reply("🟢 <b>Stealth MAU Engine: ACTIVATED!</b>", parse_mode='html')
    elif args.lower() == "off":
        STEALTH_MAU_MODE = False
        await event.reply("🔴 <b>Stealth MAU Engine: DEACTIVATED!</b>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=r'(?i)^(play|/|\.|p|harem|h|vault|v|waifu|w|daily|claim)$'))
async def stealth_mau_handler(event):
    global STEALTH_MAU_MODE
    if not STEALTH_MAU_MODE or event.is_private: return
    user_id = event.sender_id
    try:
        await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    except Exception:
        pass

# ==========================================
# 📡 WEATHER ENGINE (Fixed)
# ==========================================
def fetch_live_weather(city_id="Yangon"):
    try:
        search_query = city_id.replace("_", " ")
        url = f"https://wttr.in/{search_query}?format=j1"
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req, timeout=7) as response:
            data = json.loads(response.read().decode())
            current = data['current_condition'][0]
            temp_c = current['temp_C']
            weather_desc = current['weatherDesc'][0]['value'].strip()
            humidity = current['humidity']
            wind_speed = current['windspeedKmph']
            translations = {
                "Sunny": "☀️ Sunny", "Clear": "🌌 Clear", "Partly cloudy": "⛅ Partly cloudy",
                "Cloudy": "☁️ Cloudy", "Overcast": "☁️ Overcast", "Mist": "🌫️ Mist",
                "Fog": "🌫️ Fog", "Patchy rain nearby": "🌦️ Patchy rain",
                "Light rain": "🌧️ Light rain", "Moderate rain": "🌧️ Moderate rain",
                "Heavy rain": "⛈️ Heavy rain", "Thunderstorm": "⛈️ Thunderstorm",
                "Torrential rain shower": "⛈️ Torrential rain"
            }
            translated = translations.get(weather_desc, weather_desc)
            return {"success": True, "temp": temp_c, "desc": translated, "humidity": humidity, "wind": wind_speed, "city": search_query.upper()}
    except Exception as e:
        print(f"Weather Fetch Error: {e}")
        return {"success": False}

@bot1.on(events.NewMessage(pattern=r"(?i)^[/.]weather$"))
async def weather_cmd_handler(event):
    buttons = [[Button.inline("🇲🇲 Myanmar", data="w_country_mm"), Button.inline("🇹🇭 Thailand", data="w_country_th")]]
    await event.reply("🌍 <b>Select Country</b>\nChoose a country.", parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r"^w_(.+)$"))
async def weather_callback_engine(event):
    # ✅ Handle both string and bytes data
    raw_data = event.data.decode('utf-8') if isinstance(event.data, bytes) else event.data
    action = raw_data.replace("w_", "")
    
    if action == "main_menu":
        buttons = [[Button.inline("🇲🇲 Myanmar", data="w_country_mm"), Button.inline("🇹🇭 Thailand", data="w_country_th")]]
        await event.edit("🌍 <b>Select Country</b>", parse_mode='html', buttons=buttons)
        await event.answer()
        return
    elif action == "country_mm":
        buttons = [
            [Button.inline("Yangon", data="w_city_Yangon"), Button.inline("Mandalay", data="w_city_Mandalay")],
            [Button.inline("Naypyidaw", data="w_city_Naypyidaw"), Button.inline("Taunggyi", data="w_city_Taunggyi")],
            [Button.inline("Bago", data="w_city_Bago"), Button.inline("Mawlamyine", data="w_city_Mawlamyine")],
            [Button.inline("⬅️ Back", data="w_main_menu")]
        ]
        await event.edit("🇲🇲 <b>Myanmar Regions</b>", parse_mode='html', buttons=buttons)
        await event.answer()
        return
    elif action == "country_th":
        buttons = [
            [Button.inline("Bangkok", data="w_city_Bangkok"), Button.inline("Chiang Mai", data="w_city_Chiang_Mai")],
            [Button.inline("Phuket", data="w_city_Phuket"), Button.inline("Pattaya", data="w_city_Pattaya")],
            [Button.inline("Hat Yai", data="w_city_Hat_Yai"), Button.inline("Khon Kaen", data="w_city_Khon_Kaen")],
            [Button.inline("⬅️ Back", data="w_main_menu")]
        ]
        await event.edit("🇹🇭 <b>Thai Provinces</b>", parse_mode='html', buttons=buttons)
        await event.answer()
        return
    elif action.startswith("city_"):
        city_name = action.replace("city_", "")
        await event.edit(f"📡 <i>Fetching weather for {city_name}...</i>", parse_mode='html')
        loop = asyncio.get_event_loop()
        w_data = await loop.run_in_executor(None, fetch_live_weather, city_name)
        mm_cities = ["Yangon", "Mandalay", "Naypyidaw", "Taunggyi", "Bago", "Mawlamyine"]
        back_target = "w_country_mm" if city_name in mm_cities else "w_country_th"
        control_buttons = [[Button.inline("🔄 Refresh", data=f"w_city_{city_name}")], [Button.inline("⬅️ Back", data=back_target)]]
        
        if w_data["success"]:
            response_text = (
                f"🌍 <b>LIVE WEATHER</b>\n"
                f"📍 <b>Location:</b> <code>{w_data['city']}</code>\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"🌡️ <b>Temp:</b> <code>{w_data['temp']}°C</code>\n"
                f"💧 <b>Humidity:</b> <code>{w_data['humidity']}%</code>\n"
                f"💨 <b>Wind:</b> <code>{w_data['wind']} Km/h</code>\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"🌤️ <b>Condition:</b> <code>{w_data['desc']}</code>"
            )
        else:
            response_text = f"❌ <b>ERROR:</b> Could not retrieve data for {city_name}."
        
        await event.edit(response_text, parse_mode='html', buttons=control_buttons)
        await event.answer()
async def run_bot1_forever():
    global BOT1_USERNAME
    while True:
        try:
            print("🚀 Connecting Main Bot (bot1)...")
            await bot1.start(bot_token=MAIN_BOT_TOKEN)
            me_main = await bot1.get_me()
            print(f"✅ Main Bot connected as @{me_main.username}")
            if me_main.username: BOT1_USERNAME = me_main.username.lower()
            if me_main.id not in bot_ids: bot_ids.append(me_main.id)
            await load_rarity_weight_cache()
            await load_added_owners_cache()
            await load_group_spawn_counters_cache()
            asyncio.create_task(ghost_spawn_cleaner())
            asyncio.create_task(group_counter_flush_loop())
            print("📅 Background tasks started.")
            await bot1.run_until_disconnected()
        except Exception as system_fault:
            print(f"⚠️ Main Bot disconnected: {system_fault}")
            print("⏳ Restarting Main Bot in 30 seconds...")
            await asyncio.sleep(30)


async def _create_indexes_background():
    """Runs create_indexes() without blocking bot startup — index creation is a MongoDB round
    trip per index (~35 of them), which used to make bot1/bot2 sit disconnected from Telegram
    for however long that took. Indexes are a pure performance optimization (queries still
    work without one, just slower), so there's no correctness reason to wait on them."""
    try:
        await create_indexes()
    except Exception as e:
        print(f"Index creation error: {e}")

async def start_bot_state_cleanup_loop():
    """Sweeps BotState's expired cache entries every 10 minutes for the life of the process."""
    while True:
        await asyncio.sleep(600)
        try:
            removed = bot_state.cleanup_expired()
            if removed:
                print(f"🧹 BotState cleanup: removed {removed} stale entries")
        except Exception as e:
            print(f"BotState cleanup error: {e}")

async def start_system():
    threading.Thread(target=run_flask, daemon=True).start()
    print("Bot System Starting...")
    asyncio.create_task(_create_indexes_background())
    asyncio.create_task(start_bot_state_cleanup_loop())
    asyncio.create_task(daily_report_scheduler())
    # 🔭 Cross-bot monitor: load its small config tables, then — if a login session was
    # already saved via /xbotsetsession on a previous run — reconnect the monitor userbot in
    # the background. A failure or simply "no session yet" here should never block bot1/bot2
    # from starting; the owner can always (re)connect it later with /xbotsetsession.
    await load_monitored_channels()
    await load_bot_mappings()
    asyncio.create_task(load_and_start_monitor_userbot())
    await asyncio.gather(run_bot1_forever())

if __name__ == "__main__":
    try:
        asyncio.run(start_system())
    except (KeyboardInterrupt, SystemExit):
        print("Bot System Shutting Down.")
        
