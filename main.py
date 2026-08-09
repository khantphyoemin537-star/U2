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
        self.pending_sell_offers = {}         # sell_id -> {"expiry": ts, "seller_id", "char_id", "char_name", "offer"} — /sell Owner-buyback confirm flow
        self.pending_premium_gifts = {}       # gift_id -> {"expiry": ts, "user_id", "star_amount"} — Premium daily Star gift confirm flow

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
        self.active_card_games = {}
        self.active_haido_events = {}
        self.active_mines_games = {}
        self.active_box_games = {}
        self.pending_rarity_quiz = {}
        # 🏰 Squad-founding flow (/create): user_id -> {"stage": "name"/"photo", "name",
        # "chat_id", "prompt_msg_id", "deadline"}. Has its own dedicated timeout+refund
        # watchdog (_squad_setup_timeout_watchdog), same reasoning as the games above.
        self.pending_squad_setup = {}
        # 🚨 Comedic "AML bust" jail (see try_deduct_bet_bot3 / AML_BUST_THRESHOLD below):
        # user_id -> unix timestamp the jail expires. Satire flavor only, not a real ban —
        # but it doubles as the enforcement point for bot3's actual max-single-bet ceiling.
        self.aml_jail = {}

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
        for d in (self.admin_cache, self.pending_sell_offers, self.pending_premium_gifts):
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

async def ensure_user_registered(user_id, fullname):
    global_system = await groups_config_col.find_one({"chat_id": "global_system"})
    welcome_bonus = global_system.get("default_welcome_bonus", 0) if global_system else 0
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {
            "$setOnInsert": {
                "wallet_balance": welcome_bonus,
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
                "force_sub_rewarded": False,
                "star_balance": 0.0
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
async def try_deduct_balance(user_id, amount):
    """Attempts to atomically deduct `amount` USD from a user's wallet.
    Returns True if the deduction succeeded (they had enough), False if they didn't
    (or amount <= 0). Safe to call concurrently — never overdraws a wallet."""
    if amount <= 0:
        return False
    result = await users_catcher_col.update_one(
        {"user_id": user_id, "wallet_balance": {"$gte": amount}},
        {"$inc": {"wallet_balance": -amount}}
    )
    return result.modified_count > 0

async def try_deduct_star(user_id, amount):
    """Same atomic check-and-deduct pattern as try_deduct_balance, but for ⭐ Star balance —
    used everywhere a user spends Star (Owner Shop purchases, peer card trades)."""
    if amount <= 0:
        return False
    result = await users_catcher_col.update_one(
        {"user_id": user_id, "star_balance": {"$gte": amount}},
        {"$inc": {"star_balance": -amount}}
    )
    return result.modified_count > 0

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
# Rank 1 (rarest) -> Rank 4 (most common). All 4 tiers accept photo or video media — no
# tier is restricted to a specific media type.
RARITY_TIERS = ["SWEETIE", "BLOSSOM", "FLUFFY", "KAWAII"]
# ⚠️ SINGLE SOURCE OF TRUTH for rarity emoji (Rarity No.1 = SWEETIE ... No.4 = KAWAII).
# Change emoji here ONLY — RARITY_NUM_MAP below is generated from this, so spawns, /who,
# the /addchar legend, achievements, stats and /changeallrarity all stay in sync automatically.
RARITY_EMOJI = {
    "SWEETIE": "🍯", "BLOSSOM": "🌸", "FLUFFY": "☁️", "KAWAII": "🎀"
}
RARITY_DEFAULT_EMOJI = "❓"  # fallback shown only when a tier truly can't be classified
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
    try:
        if msg.photo:
            media_bytes = await msg.download_media(file=bytes)
        elif msg.video or msg.document:
            media_bytes = await msg.download_media(thumb=-1, file=bytes)
        else:
            return None
        if not media_bytes:
            return None
        return compute_dhash(media_bytes)
    except Exception as e:
        print(f"compute_phash_for_message error: {e}")
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

def star_price_for_char(char_doc):
    """⭐ OWNER SHOP PRICE — fixed by rarity, No.1 (rarest) = 400⭐ ... No.4 (most common) = 100⭐.
    This is exactly rarity_rank_value, kept as its own named function so the pricing rule
    reads clearly at every /buy [char id] / /show call site."""
    if not char_doc:
        return 0
    return rarity_rank_value(char_doc.get("rarity_tier") or char_doc.get("rarity", "")) * 100

def catch_star_reward(rarity_str):
    """⭐ Star bonus paid out (on top of the usual USD wallet reward) when a spawn is actually
    CAUGHT from the wild — not bought from the Owner Shop. A quarter of the Owner Shop Star
    price (e.g. Blossom No.2 → 75⭐)."""
    return rarity_rank_value(rarity_str) * 25
# ==========================================
# 💵 USD / ⭐ STAR DISPLAY FORMATTING
# ==========================================
# 💵 2026-07: the bot's whole economy was migrated off the old uncapped MMK currency onto a
# fixed USD peg (see "USD ECONOMY" note near MMK_PER_USD) — this is the standard formatter
# for any USD balance/value shown to a player. ⭐ Star remains the separate second currency
# used for card trading and is untouched by this migration.
def format_usd(amount):
    """'$8,000.00' — the standard way any USD balance/value should be displayed."""
    try:
        return f"${amount:,.2f}"
    except Exception:
        return f"${amount}"

def format_usd_compact(amount):
    """'$8,000.00' below 1 Million; '$2.35 Million' / '$1.10 Billion' / '$3.40 Trillion' at or
    above it. Used specifically for /balance so very large wallet_balance values (e.g. from
    Squad invite fees or casino wins) stay readable instead of a long string of digits — every
    other USD display in the bot keeps using plain format_usd() unchanged."""
    try:
        amount = float(amount)
    except Exception:
        return f"${amount}"
    negative = amount < 0
    abs_amount = abs(amount)
    if abs_amount >= 1_000_000_000_000:
        text = f"${abs_amount / 1_000_000_000_000:,.2f} Trillion"
    elif abs_amount >= 1_000_000_000:
        text = f"${abs_amount / 1_000_000_000:,.2f} Billion"
    elif abs_amount >= 1_000_000:
        text = f"${abs_amount / 1_000_000:,.2f} Million"
    else:
        text = f"${abs_amount:,.2f}"
    return f"-{text}" if negative else text

def format_star_plain(star_amount):
    """Clean Star display — whole numbers show with no decimals, fractional Star (e.g. quiz
    rewards of 0.2-1⭐) show up to 2 decimal places."""
    try:
        amount = float(star_amount)
    except Exception:
        return f"{star_amount} ⭐"
    if amount.is_integer():
        return f"{int(amount):,} ⭐"
    return f"{amount:,.2f} ⭐"

# ==========================================
# RARITY SPAWN WEIGHT — a single GLOBAL "level" dial (via /spawnweight) that boosts how often
# Sweetie (No.1 — RARITY_GATE_TIERS, the quiz-gated tier, defined further down) spawns,
# relative to its own default below. Blossom/Fluffy/Kawaii (No.2-4) are never touched by
# this — only the quiz-gated tier scales. "Global" means exactly that: one setting, shared by
# every chat, regardless of which chat the owner happens to type the command in.
DEFAULT_RARITY_WEIGHTS = dict(zip(RARITY_TIERS, [5, 15, 35, 70]))
# No.1 Sweetie=5 ... No.4 Kawaii=70 — a 14x gap between rarest and most common by default.
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

# 🚫 OWNER SHOP "SOLD OUT" TOGGLE — lets the Owner temporarily stop a rarity tier from being
# purchasable via /buy [char_id] and the /show gallery's 🛒 Buy button (catching it from a live
# spawn is completely unaffected). Starts with Sweetie (No.1) disabled by default; toggle any
# tier on/off with /buytoggle no1 .. no4 (persisted in bot_settings_col so it survives restarts).
_cached_disabled_buy_tiers = {"SWEETIE"}
SOLD_OUT_CONTACT_LINK = "https://t.me/Comeback_BoD/1300786"  # where buyers can reply to reach
# the owner directly and negotiate/buy manually while a tier is closed in the Owner Shop

async def load_disabled_buy_tiers_cache():
    global _cached_disabled_buy_tiers
    try:
        doc = await bot_settings_col.find_one({"_id": "disabled_buy_tiers"})
        if doc is not None:
            tiers = doc.get("tiers")
            if isinstance(tiers, list):
                _cached_disabled_buy_tiers = {t for t in tiers if t in RARITY_TIERS}
    except Exception as e:
        print(f"load_disabled_buy_tiers_cache error: {e}")

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
    balance_targets = [round(v / MMK_PER_USD, 2) for v in [1000, 10000, 50000, 100000, 500000, 1000000]]
    balance_emojis = ["🪙", "💰", "💵", "💳", "🏦", "💎"]
    for i, target in enumerate(balance_targets):
        achievements.append({
            "id": f"wealth_{target}",
            "emoji": balance_emojis[i],
            "name": f"Hold {target:,} USD",
            "desc": f"Amass {target:,} USD in your wallet",
            "check": lambda u, t=target: u.get("wallet_balance", 0) >= t
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
marketplace_col = db["marketplace_data"]
guilds_col = db["guilds_data"]
# 🏰 SQUAD SYSTEM — deliberately its OWN collection, not guilds_col. guilds_col already has an
# older, never-actually-wired-up "Guild XP/Level" mechanic (see the guild_levelup_msg block in
# catch_handler) that assumes every doc there has "xp"/"level" fields. Squad docs don't have
# those, and nothing currently ever inserts into guilds_col — so reusing it here would leave a
# latent KeyError crash sitting in every future catch for anyone in a Squad. Keeping Squad data
# in its own collection sidesteps that entirely without needing to touch the old dormant code.
squads_col = db["squads_data"]
gift_history_col = db["gift_history"]
haido_history_col = db["haido_history"] # records each person-to-person /gift for profile stats
artists_col = db["artists"]  # 🎨 artist_name (lowercased) -> linked Telegram user_id, for Guard Bot collect rewards — see /linkartist
wealth_compression_log_col = db["wealth_compression_log"] # 🐋 audit trail — one doc per /compresswealth confirm run
force_sub_reclaim_log_col = db["force_sub_reclaim_log"] # 🧾 audit trail — one doc per /reclaimforcesub confirm run
rarity_quiz_bank_col = db["rarity_quiz_bank"] # 🔐 owner-authored Rarity 1-4 gate quiz questions
bot_settings_col = db["bot_settings"] # ⚙️ single-document global settings
star_market_col = db["star_market"] # ⭐ single global Star <-> USD exchange rate doc
# 🏦 bot3's own "house" ledger — single global doc (key="bot3"), seeded once with a large
# starting bankroll and then updated in lockstep with every bet/refund/fee/payout across every
# bot3-hosted casino game (see bot3_treasury_adjust below). Lets anyone check /bot3balance to
# see exactly how much bot3 has won or lost overall, instead of that being uncountable.
bot3_treasury_col = db["bot3_treasury"]
star_purchase_log_col = db["star_purchase_log"] # 🧾 every /buy [char id] Owner Shop purchase, for /buylist
star_sell_log_col = db["star_sell_log"] # 🧾 every /sell [char id] Owner buyback (Star paid to the player), for /starlist
star_exchange_log_col = db["star_exchange_log"] # 🧾 every /buystar & /sellstar USD<->Star exchange, for /starlist
debts_col = db["debts"]  # 💰 အကြွေးစာရင်း
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


async def get_or_create_star_market():
    """Lazily creates the single global ⭐ Star <-> USD exchange rate doc on first touch, and
    rolls its 'day open' price forward once a new Yangon calendar day begins."""
    market = await star_market_col.find_one({"key": "STAR"})
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    if not market:
        market = {
            "key": "STAR", "price": STAR_STARTING_PRICE, "day_open_price": STAR_STARTING_PRICE,
            "day_open_date": today_str, "prev_tick_price": STAR_STARTING_PRICE,
            "history": [STAR_STARTING_PRICE], "buy_volume_today": 0.0, "sell_volume_today": 0.0,
            "updated_at": time.time(),
        }
        try:
            await star_market_col.insert_one(dict(market))
        except Exception:
            refetched = await star_market_col.find_one({"key": "STAR"})
            if refetched:
                market = refetched
    if market.get("day_open_date") != today_str:
        await star_market_col.update_one(
            {"key": "STAR"},
            {"$set": {"day_open_price": market["price"], "day_open_date": today_str,
                      "buy_volume_today": 0.0, "sell_volume_today": 0.0}}
        )
        market["day_open_price"] = market["price"]
        market["day_open_date"] = today_str
    return market

async def _write_star_price(market, new_price, extra_fields=None):
    new_price = round(max(new_price, STAR_MIN_PRICE), 2)
    history = (market.get("history", []))[-(STAR_HISTORY_MAX - 1):] + [new_price]
    fields = {"prev_tick_price": market["price"], "price": new_price,
               "history": history, "updated_at": time.time()}
    if extra_fields:
        fields.update(extra_fields)
    await star_market_col.update_one({"key": "STAR"}, {"$set": fields})
    return new_price

async def get_or_create_bot3_treasury():
    """Lazily creates the single global bot3 'house' ledger doc on first touch, seeded with
    BOT3_SEED_STAR_BALANCE / BOT3_SEED_WALLET_BALANCE. The seed values are also frozen onto the
    doc (seed_star_balance / seed_wallet_balance) so /bot3balance can always show original vs
    current and compute a real profit/loss, no matter how much wallet_balance/star_balance
    have since moved."""
    treasury = await bot3_treasury_col.find_one({"key": "bot3"})
    if not treasury:
        treasury = {
            "key": "bot3",
            "star_balance": BOT3_SEED_STAR_BALANCE,
            "wallet_balance": BOT3_SEED_WALLET_BALANCE,
            "seed_star_balance": BOT3_SEED_STAR_BALANCE,
            "seed_wallet_balance": BOT3_SEED_WALLET_BALANCE,
            "created_at": time.time(),
        }
        try:
            await bot3_treasury_col.insert_one(dict(treasury))
        except Exception:
            refetched = await bot3_treasury_col.find_one({"key": "bot3"})
            if refetched:
                treasury = refetched
    return treasury

async def bot3_treasury_adjust(usd=0, star=0):
    """The single choke point every bot3 casino game's money movement passes through, so the
    bot3_treasury_col doc stays a real-time, exact mirror of bot3's own win/loss — separate
    from and in ADDITION to the player's own wallet_balance/star_balance change.
    Sign convention: positive = bot3 GAINS (a player's bet, burn fee, or cashout tax being
    taken); negative = bot3 PAYS OUT (a player's win, or a refund reversing an earlier bet).
    Call this immediately alongside — never instead of — the normal users_catcher_col update,
    with the exact opposite of whatever amount just moved into/out of the player's balance."""
    if not usd and not star:
        return
    await get_or_create_bot3_treasury()  # ensure the doc exists before the very first $inc
    try:
        await bot3_treasury_col.update_one(
            {"key": "bot3"},
            {"$inc": {"wallet_balance": usd, "star_balance": star}},
            upsert=True
        )
    except Exception as e:
        logging.error(f"❌ bot3_treasury_adjust failed (usd={usd}, star={star}): {e}")

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

async def check_aml_jail(event, user_id):
    """Returns True (caller must abort, bet NOT taken) if this user is still serving out a
    previous AML 'bust'. Call this before even asking for/accepting a bet amount."""
    until = aml_jail.get(user_id)
    if not until:
        return False
    remaining = int(until - time.time())
    if remaining <= 0:
        aml_jail.pop(user_id, None)
        return False
    mention = await get_html_mention(event, user_id)
    await _out(
        event,
        f"🚨 <b>{mention} — လက်ရှိ ငွေကြေးခဝါချမှု စုံစမ်းစစ်ဆေးမှု အောက်ရောက်နေပါတယ်။</b>\n"
        f"⏳ <code>{remaining}</code> စက္ကန့်အကြာမှ ဂိမ်းများ ပြန်ကစားနိုင်ပါမယ်။\n"
        f"<i>😂 (Simulation ပါ — တကယ့်အရေးယူမှု မဟုတ်ပါ)</i>",
        parse_mode='html'
    )
    return True

async def try_deduct_bet_bot3(event, user_id, bet):
    """Drop-in replacement for try_deduct_balance(user_id, bet), used specifically for the
    INITIAL stake on every bot3 casino game. Same True/False contract, but first runs the AML
    jail + bust checks above — so this is also where AML_BUST_THRESHOLD is actually enforced
    as a real ceiling, not just flavor text."""
    if await check_aml_jail(event, user_id):
        return False
    if bet >= AML_BUST_THRESHOLD:
        aml_jail[user_id] = time.time() + AML_JAIL_SECONDS
        mention = await get_html_mention(event, user_id)
        await _out(
            event,
            f"🚨🚔 <b>ငွေကြေးခဝါချမှု စုံစမ်းရေးအဖွဲ့</b> 🚔🚨\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"{mention} — <code>{format_usd_compact(bet)}</code> ဆိုတဲ့ လောင်းကြေးက "
            f"သံသယဖြစ်ဖွယ် ငွေလွှဲပြောင်းမှုအဖြစ် တွေ့ရှိရပါတယ်။ 🕵️‍♂️\n\n"
            f"🔒 <b>Account ကို {AML_JAIL_SECONDS // 60} မိနစ် ယာယီ စစ်ဆေးမှု ခံရပါတော့မယ်</b>\n"
            f"<i>😂 (Simulation ပါ — တကယ့်အရေးယူမှု မဟုတ်ပါ)</i>",
            parse_mode='html'
        )
        return False
    return await try_deduct_balance(user_id, bet)


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
    await users_catcher_col.create_index("wallet_balance")
    await users_catcher_col.create_index([("group_catches.$**", 1)])
    await users_catcher_col.create_index([("wallet_balance", -1)])
    await users_catcher_col.create_index([("total_caught", -1)])
    await users_catcher_col.create_index([("total_gifted", -1)])
    await users_catcher_col.create_index([("total_buys", -1)])
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
    # ⭐ Star exchange + Owner Shop purchase log
    await star_market_col.create_index("key", unique=True)
    await bot3_treasury_col.create_index("key", unique=True)
    await users_catcher_col.create_index([("star_balance", -1)])
    await star_purchase_log_col.create_index([("timestamp", -1)])
    await star_purchase_log_col.create_index([("buyer_id", 1), ("timestamp", -1)])
    await star_sell_log_col.create_index([("timestamp", -1)])
    await star_sell_log_col.create_index([("seller_id", 1), ("timestamp", -1)])
    await star_exchange_log_col.create_index([("timestamp", -1)])
    await star_exchange_log_col.create_index([("user_id", 1), ("timestamp", -1)])
    # ⚡ groups_msg_counters is read+written on almost EVERY group message (the spawn-trigger
    # counter) — it had no index at all, meaning every single message did a full collection
    # scan. This is the single hottest query path in the whole bot.
    await groups_counters_col.create_index("chat_id", unique=True)
    # ⚡ marketplace_data had no indexes at all despite being looked up by listing_id on
    # every purchase attempt, and by char_id/seller_id when browsing or cancelling a listing.
    await marketplace_col.create_index("listing_id", unique=True)
    await marketplace_col.create_index("char_id")
    await marketplace_col.create_index([("seller_id", 1), ("char_id", 1)])
    await marketplace_col.create_index([("timestamp", -1)])
    await artists_col.create_index("artist_name", unique=True)
    # 🏰 Squad system — squad_id is looked up on every /squad, /invite, and page-nav callback;
    # members is queried via {"members": user_id} on every catch/command to find "my squad".
    await squads_col.create_index("squad_id", unique=True)
    await squads_col.create_index("members")
    # ❌ REMOVED: gotu_pairs_col, gotu_games_col, gotu_players_col, quiz_questions_col, quiz_msg_counters_col
    await _migrate_rarity_tiers()
    print("Database Indexes synchronized! ✔️")
try:
    asyncio.get_event_loop()
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH, flood_sleep_threshold=10)

# 🔐 bot2 — dedicated owner-control bot. Handles ONLY /addchar, /ktr, /ktrr, /rtclean,
# /shadow, /unshadow. Everything else stays on bot1.
bot2 = TelegramClient('bot_owner_session', APP_ID, APP_HASH, flood_sleep_threshold=10)
# 🛡️ bot3 — Guard Bot has been retired as a separate client and fully merged into bot1.
# Everything it used to do (artist payouts, Premium daily Star gift, force-join-room game
# cleanup, the casino games) now runs on bot1. Kept as a permanent `None` — rather than
# deleting the name outright — so any leftover `bot3 is None` / `bot3 is not None` check
# elsewhere still resolves safely instead of raising a NameError.
bot3 = None
bot_ids = bot_state.bot_ids
active_group_spawns = bot_state.active_group_spawns
active_card_games = bot_state.active_card_games
STEALTH_MAU_MODE = False
spawn_locks = bot_state.spawn_locks
pending_editchar_prompt_ids = bot_state.pending_editchar_prompt_ids
sticker_spam_data = bot_state.sticker_spam_data
char_spam_data = bot_state.char_spam_data
admin_cache = bot_state.admin_cache
pending_sell_offers = bot_state.pending_sell_offers
pending_premium_gifts = bot_state.pending_premium_gifts
dark_passenger_targets = bot_state.dark_passenger_targets
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

# ---- Sweetie (No.1, the rarest tier) spawns are gated behind a quiz: chosen_char is picked
# as usual, but instead of spawning immediately, a question + 4 inline buttons is posted. Only
# the FIRST correct tap actually releases the spawn (normal /who + /collect flow after that).
# chat_id -> {"char", "options", "correct_index", "question", "msg_id", "quiz_time", "solved"}
pending_rarity_quiz = bot_state.pending_rarity_quiz
pending_squad_setup = bot_state.pending_squad_setup  # 🏰 /create Squad-founding flow — see BotState
aml_jail = bot_state.aml_jail  # 🚨 comedic AML "bust" — see try_deduct_bet_bot3 below
RARITY_GATE_TIERS = {RARITY_TIERS[0]}  # rarity No.1 (Sweetie) only
RARITY_GATE_TIMEOUT_SECONDS = 360
RARITY_QUIZ_BANK = [
    {"question": "၅ + ၃ ဘယ်လောက်လဲ?", "options": ["၇", "၈", "၉", "၁၀"], "correct_index": 1},
    {"question": "၁၀ - ၄ ဘယ်လောက်လဲ?", "options": ["၄", "၅", "၆", "၇"], "correct_index": 2},
    {"question": "၃ x ၄ ဘယ်လောက်လဲ?", "options": ["၁၀", "၁၁", "၁၂", "၁၃"], "correct_index": 2},
    {"question": "၂၀ ÷ ၅ ဘယ်လောက်လဲ?", "options": ["၃", "၄", "၅", "၆"], "correct_index": 1},
    {"question": "၁၅ + ၇ ဘယ်လောက်လဲ?", "options": ["၂၀", "၂၁", "၂၂", "၂၃"], "correct_index": 2},
    {"question": "၈ x ၉ ဘယ်လောက်လဲ?", "options": ["၆၂", "၇၂", "၈၂", "၉၂"], "correct_index": 1},
    {"question": "၁၀၀ - ၃၇ ဘယ်လောက်လဲ?", "options": ["၆၁", "၆၂", "၆၃", "၆၄"], "correct_index": 2},
    {"question": "၂၄ ÷ ၃ ဘယ်လောက်လဲ?", "options": ["၆", "၇", "၈", "၉"], "correct_index": 2},
    {"question": "၇ + ၈ ဘယ်လောက်လဲ?", "options": ["၁၃", "၁၄", "၁၅", "၁၆"], "correct_index": 2},
    {"question": "၅ x ၅ ဘယ်လောက်လဲ?", "options": ["၂၀", "၂၄", "၂၅", "၃၀"], "correct_index": 2},
    {"question": "၅၀ - ၂၃ ဘယ်လောက်လဲ?", "options": ["၂၅", "၂၆", "၂၇", "၂၈"], "correct_index": 2},
    {"question": "၃၆ ÷ ၆ ဘယ်လောက်လဲ?", "options": ["၄", "၅", "၆", "၇"], "correct_index": 2},
    {"question": "၉ + ၁၁ ဘယ်လောက်လဲ?", "options": ["၁၈", "၁၉", "၂၀", "၂၁"], "correct_index": 2},
    {"question": "၁၂ x ၃ ဘယ်လောက်လဲ?", "options": ["၃၀", "၃၄", "၃၆", "၃၈"], "correct_index": 2},
    {"question": "၈၀ - ၄၅ ဘယ်လောက်လဲ?", "options": ["၃၃", "၃၄", "၃၅", "၃၆"], "correct_index": 2},
    {"question": "၄၉ ÷ ၇ ဘယ်လောက်လဲ?", "options": ["၅", "၆", "၇", "၈"], "correct_index": 2},
    {"question": "၈ x ၇ ဘယ်လောက်လဲ?", "options": ["၄၆", "၅၆", "၆၆", "၇၆"], "correct_index": 1},
    {"question": "၁၁ + ၁၃ ဘယ်လောက်လဲ?", "options": ["၂၂", "၂၃", "၂၄", "၂၅"], "correct_index": 2},
    {"question": "၃ x ၉ ဘယ်လောက်လဲ?", "options": ["၂၅", "၂၆", "၂၇", "၂၈"], "correct_index": 2},
    {"question": "၉၀ - ၆၈ ဘယ်လောက်လဲ?", "options": ["၂၀", "၂၁", "၂၂", "၂၃"], "correct_index": 2},
    {"question": "၇၂ ÷ ၈ ဘယ်လောက်လဲ?", "options": ["၇", "၈", "၉", "၁၀"], "correct_index": 2},
    {"question": "၁၄ + ၁၅ ဘယ်လောက်လဲ?", "options": ["၂၇", "၂၈", "၂၉", "၃၀"], "correct_index": 2},
    {"question": "၄ x ၁၃ ဘယ်လောက်လဲ?", "options": ["၄၂", "၅၂", "၆၂", "၇၂"], "correct_index": 1},
    {"question": "၅၀ - ၁၂ ဘယ်လောက်လဲ?", "options": ["၃၆", "၃၇", "၃၈", "၃၉"], "correct_index": 2},
    {"question": "၆၀ ÷ ၅ ဘယ်လောက်လဲ?", "options": ["၁၀", "၁၁", "၁၂", "၁၃"], "correct_index": 2},
    {"question": "၁ + ၇ ဘယ်လောက်လဲ?", "options": ["၆", "၇", "၈", "၉"], "correct_index": 2},
    {"question": "၂၀ x ၄ ဘယ်လောက်လဲ?", "options": ["၇၀", "၈၀", "၉၀", "၁၀၀"], "correct_index": 1},
    {"question": "၉၉ - ၂၀ ဘယ်လောက်လဲ?", "options": ["၇၇", "၇၈", "၇၉", "၈၀"], "correct_index": 2},
    {"question": "၅၆ ÷ ၇ ဘယ်လောက်လဲ?", "options": ["၆", "၇", "၈", "၉"], "correct_index": 2},
    {"question": "၁၀၀ + ၂၅ ဘယ်လောက်လဲ?", "options": ["၁၁၅", "၁၂၀", "၁၂၅", "၁၃၀"], "correct_index": 2},
    {"question": "၆ x ၁၁ ဘယ်လောက်လဲ?", "options": ["၅၆", "၆၆", "၇၆", "၈၆"], "correct_index": 1},
    {"question": "၇၃ - ၄၈ ဘယ်လောက်လဲ?", "options": ["၂၃", "၂၄", "၂၅", "၂၆"], "correct_index": 2},
    {"question": "၄၅ ÷ ၉ ဘယ်လောက်လဲ?", "options": ["၄", "၅", "၆", "၇"], "correct_index": 1},
    {"question": "၂ + ၈ ဘယ်လောက်လဲ?", "options": ["၈", "၉", "၁၀", "၁၁"], "correct_index": 2},
    {"question": "၃ x ၁၅ ဘယ်လောက်လဲ?", "options": ["၄၀", "၄၅", "၅၀", "၅၅"], "correct_index": 1},
    {"question": "၈၀ - ၃၃ ဘယ်လောက်လဲ?", "options": ["၄၅", "၄၆", "၄၇", "၄၈"], "correct_index": 2},
    {"question": "၈၄ ÷ ၄ ဘယ်လောက်လဲ?", "options": ["၁၉", "၂၀", "၂၁", "၂၂"], "correct_index": 2},
    {"question": "၆၆ + ၁၂ ဘယ်လောက်လဲ?", "options": ["၇၆", "၇၇", "၇၈", "၇၉"], "correct_index": 2},
    {"question": "၇ x ၈ ဘယ်လောက်လဲ?", "options": ["၄၆", "၅၆", "၆၆", "၇၆"], "correct_index": 1},
    {"question": "၁၀၀ - ၅၆ ဘယ်လောက်လဲ?", "options": ["၄၂", "၄၃", "၄၄", "၄၅"], "correct_index": 2},
    {"question": "၉၀ ÷ ၁၀ ဘယ်လောက်လဲ?", "options": ["၇", "၈", "၉", "၁၀"], "correct_index": 2},
    {"question": "၁၂ + ၂၃ ဘယ်လောက်လဲ?", "options": ["၃၃", "၃၄", "၃၅", "၃၆"], "correct_index": 2},
    {"question": "၆ x ၆ ဘယ်လောက်လဲ?", "options": ["၃၀", "၃၄", "၃၆", "၃၈"], "correct_index": 2},
    {"question": "၇၅ - ၂၆ ဘယ်လောက်လဲ?", "options": ["၄၇", "၄၈", "၄၉", "၅၀"], "correct_index": 2},
    {"question": "၄၈ ÷ ၆ ဘယ်လောက်လဲ?", "options": ["၆", "၇", "၈", "၉"], "correct_index": 2},
    {"question": "၅ + ၁၀ ဘယ်လောက်လဲ?", "options": ["၁၃", "၁၄", "၁၅", "၁၆"], "correct_index": 2},
    {"question": "၉ x ၄ ဘယ်လောက်လဲ?", "options": ["၃၀", "၃၄", "၃၆", "၃၈"], "correct_index": 2},
    {"question": "၅၀ - ၁၉ ဘယ်လောက်လဲ?", "options": ["၂၉", "၃၀", "၃၁", "၃၂"], "correct_index": 2},
    {"question": "၃၆ ÷ ၄ ဘယ်လောက်လဲ?", "options": ["၇", "၈", "၉", "၁၀"], "correct_index": 2},
    {"question": "၈ + ၇ ဘယ်လောက်လဲ?", "options": ["၁၃", "၁၄", "၁၅", "၁၆"], "correct_index": 2},
]
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
    "SWEETIE": 400, "BLOSSOM": 200, "FLUFFY": 100, "KAWAII": 50
}
# ⚠️ Display name for each tier, English only (no Burmese in the rarity name).
# classify_rarity() still matches on the bare RARITY_TIERS token (e.g. "SWEETIE"), which is
# always the English display name here too, so this is safe to change freely without touching
# classification/sorting/weights.
RARITY_DISPLAY_NAME = {
    "SWEETIE": "Sweetie", "BLOSSOM": "Blossom", "FLUFFY": "Fluffy", "KAWAII": "Kawaii"
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
# ⭐ Star is the currency used to buy cards (Owner Shop + Owner /sell buyback). Its USD exchange
# rate is a FIXED PEG — it never moves on its own from trading volume or background drift.
# It only ever changes when the Owner explicitly runs /setstarrate. (Previously this rate
# rate stays fully predictable at all times.)
STAR_STARTING_PRICE = 1_000_000.0 / MMK_PER_USD   # USD per 1 ⭐ Star — the fixed rate, until /setstarrate changes it
STAR_MIN_PRICE = 100000.0 / MMK_PER_USD  # safety floor for /setstarrate — guards against a fat-fingered near-zero rate
STAR_HISTORY_MAX = 24
# 🏦 bot3's starting bankroll — set once, the first time get_or_create_bot3_treasury() runs.
# Large enough that ordinary payouts across every bot3 game never need bot3 to "go negative";
# from then on the balance only moves via bot3_treasury_adjust() as real bets/payouts happen.
BOT3_SEED_STAR_BALANCE = 100_000_000          # ⭐ 100 Million
BOT3_SEED_WALLET_BALANCE = 10_000_000_000.0   # 💵 10 Billion USD
QUIZ_STAR_REWARD_MIN = 3  # ⭐ reward range for correctly answering a Rarity 1-4 gate quiz
QUIZ_STAR_REWARD_MAX = 7

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

async def handle_gift_fee(sender_id):
    """
    sender ဆီက 1000 USD ကောက်ခံပြီး မရရင် အကြွေးတင်မယ်။
    bot3 balance ကိုလည်း update လုပ်မယ်။
    """
    fee = 1000.0

    # 1️⃣ အရင်ဆုံး sender မှာ အကြွေးရှိမရှိ စစ်မယ်
    debt_doc = await debts_col.find_one({"user_id": sender_id})
    if debt_doc:
        debt_amount = debt_doc.get("amount", 0)
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        balance = sender_doc.get("wallet_balance", 0) if sender_doc else 0

        if balance > 0:
            deduct = min(debt_amount, balance)
            await users_catcher_col.update_one(
                {"user_id": sender_id},
                {"$inc": {"wallet_balance": -deduct}}
            )
            await bot3_treasury_adjust(usd=deduct)  # bot3 မှာ ပေါင်းထည့်

            new_debt = debt_amount - deduct
            if new_debt <= 0:
                await debts_col.delete_one({"user_id": sender_id})
            else:
                await debts_col.update_one(
                    {"user_id": sender_id},
                    {"$set": {"amount": new_debt}}
                )

    # 2️⃣ ဒီ gift အတွက် fee ကောက်မယ်
    if not await try_deduct_balance(sender_id, fee):
        # မရရင် အကြွေးတင်မယ်
        await debts_col.update_one(
            {"user_id": sender_id},
            {"$inc": {"amount": fee}},
            upsert=True
        )
        await bot3_treasury_adjust(usd=fee)
        return False  # fee မရဘူး (အကြွေးတင်ထားတယ်)

    return True  # fee ရတယ်
    
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

GAME_FOOTER = "\n\n🪙 <code>/balance</code>, 🙎 တခြားဂိမ်းတွေ ဆော့မယ်ဆို /game လို့ရိုက်"
async def _delete_after_delay(client, chat_id, msg_id, delay=10):
    try:
        await asyncio.sleep(delay)
        await client.delete_messages(chat_id, msg_id)
    except Exception:
        pass

def schedule_game_cleanup(client, chat_id, msg, delay=10):
    # 🛡️ Guard Bot (bot3) has been merged into bot1 — there's no separate client to split
    # cleanup load across anymore, so this just always uses whichever client is passed in.
    msg_id = getattr(msg, 'id', msg)
    asyncio.create_task(_delete_after_delay(client, chat_id, msg_id, delay))

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
        schedule_game_cleanup(event.client, event.chat_id, msg, delay=FORCE_SUB_PROMPT_TTL)
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

@bot1.on(events.NewMessage(pattern=r'^[/.]'))
async def guard_bot_game_throttle(event):
    user_id = event.sender_id
    if not user_id or user_id == OWNER_ID or user_id in bot_ids: return
    m = _FORCE_SUB_CMD_RE.match(event.raw_text or "")
    if not m: return
    cmd_word = m.group(1).split('@')[0].lower()
    if cmd_word not in GUARD_GAME_COMMANDS: return
    on_cooldown, remaining = await is_on_cooldown(user_id, "guard_game_spam", GUARD_GAME_COOLDOWN_SECONDS)
    if not on_cooldown: return
    notifier = event.client
    try:
        warn = await notifier.send_message(
            event.chat_id,
            f" <b>ခဏစောင့်ပါ!</b> Game တွေ မကြာခဏ မဆော့ပါနဲ့ — <code>{remaining}s</code> လောက် စောင့်ပြီးမှ ထပ်ကစားပါ။",
            parse_mode='html'
        )
        schedule_game_cleanup(notifier, event.chat_id, warn, delay=5)
    except Exception:
        pass
    try:
        await event.delete()
    except Exception:
        pass
    raise events.StopPropagation

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
                NEW_USER_BONUS = round(1000 / MMK_PER_USD, 2)
                REFERRER_BONUS = round(2000 / MMK_PER_USD, 2)
                await users_catcher_col.update_one(
                    {"user_id": user_id},
                    {"$set": {"referred_by": referrer_id}, "$inc": {"wallet_balance": NEW_USER_BONUS}}
                )
                await users_catcher_col.update_one(
                    {"user_id": referrer_id},
                    {"$inc": {"wallet_balance": REFERRER_BONUS, "referral_count": 1}}
                )
                await check_and_award_achievements(referrer_id, notify_chat_id=referrer_id)
                referral_note = (
                    f"\n\n🎉 <b>Referral Bonus!</b> You got <code>+{NEW_USER_BONUS} USD</code> welcome gift, "
                    f"and your friend got <code>+{REFERRER_BONUS} USD</code> for inviting you! 🎁"
                )
    bot_me = await bot1.get_me()
    welcome_msg = (
        f"👑 <b>Morgan Bot</b> ကနေ ကြိုဆိုပါတယ်!\n\n"
        f"ကျွန်တော်က <b>Character Collector Bot</b> တစ်ခုပါ — ဒီ Group ထဲမှာ Character အသစ်တွေ "
        f"အခါအားလျော်စွာ ပေါ်လာမှာဖြစ်ပြီး၊ ဖော်ထုတ်ဖမ်းဆီးစုဆောင်းရတဲ့ <b>Collector Game</b> ကို "
        f"အဓိကထားပါတယ်။ အပြင် <b>Casino ဂိမ်းများ</b> (Slot, Roulette, Mines, Plinko, စသည်) နဲ့ "
        f"<b>Group အုပ်ချုပ်ရေး</b> လုပ်ဆောင်ချက်တွေကိုပါ တစ်နေရာတည်း ပေါင်းစပ်ပေးထားပါတယ်။\n\n"
        f"Group ထဲမှာ Character များကို ဖမ်းဆီးရင်း 💵 USD နဲ့ ⭐ Star ရရှိနိုင်ပြီး၊ Casino ဂိမ်းတွေ "
        f"ဆော့ကစားပြီးလည်း ⭐ Star ထပ်ရယူနိုင်ပါတယ်။\n\n"
        f"အောက်က Button များ နှိပ်ပြီး ဘာတွေ ရနိုင်လဲ ကြည့်လိုက်ပါ။ 🙂"
        f"{referral_note}"
    )
    buttons = [
        [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("💰 Economy", data="nav_game_main")],
        [Button.inline("🎰 Casino", data="nav_casino_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
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

def get_game_text():
    return (
        f"🎮 <b><u>Game Console</u></b>\n\n"
        f"⭐ <code>/balance</code>\nCheck your USD and ⭐ Star balance.\n\n"
        f"⭐ <code>/daily</code>\nClaim your daily bonus (streak rewards!).\n\n"
        f"⭐ <code>/hunt</code>\nGo on a hunting adventure for extra cash.\n\n"
        f"⭐ <code>/gift [char_id]</code> (reply to a user)\nSend a caught character to another player — you'll both get a nicely designed confirmation, and they'll get a DM too. Every gift given/received counts toward a Gift Rank — see /giftranks.\n\n"
        f"💵 <code>/giftusd [amount]</code> (reply to a user)\nSend USD straight from your wallet to theirs.\n\n"
        f"⭐ <code>/giftstar [amount]</code> (reply to a user)\nSend ⭐ Star straight from your balance to theirs.\n\n"
        f"👑 <code>/giftpremium [months]</code> (reply to a user)\nBuy them Bot Premium with your own ⭐ Star, at the same rate as /buypremium — <code>1, 2, 3, 6, 12</code> months.\n\n"
        f"🎁 <code>/topgift</code>\nTop 10 most generous gifters.\n\n"
        f"🎖️ <code>/giftranks</code>\nSee the full Giver and Receiver rank ladders — titles unlock automatically as your gift counts climb.\n\n"
        f"🏪 <code>/market</code>\nYour balance + a shortcut to buy cards or buy ⭐ Star.\n\n"
        f"🛍️ <code>/buy</code>\nChoose between browsing cards (via /show in DM) or buying ⭐ Star.\n\n"
        f"🛍️ <code>/buy [char_id]</code>\nBuy a fresh copy of that character straight from the Owner Shop, priced by rarity (Sweetie = 400⭐, Blossom = 300⭐, Fluffy = 200⭐, Kawaii = 100⭐). Capped at {DAILY_BUY_LIMIT}/day, {LIFETIME_BUY_PER_CHAR_LIMIT} copies of the same character ever, and Sweetie/Blossom/Fluffy share {TOP_RARITY_WEEKLY_BUY_LIMIT} combined per week.\n\n"
        f"🏷️ <code>/sell [char_id]</code>\nOwner buys the card back with ⭐ Star — a random offer between 0.5x and 1.5x its Owner Shop price, yours to accept or decline.\n\n"
        f"🤝 <code>/trade [your ID] [their ID]</code> (reply to the user)\nPropose a direct card swap with another player — they confirm or cancel it.\n\n"
        f"💱 <code>/buystar [⭐]</code> / <code>/sellstar [⭐]</code>\nExchange ⭐ Star for USD (or back) at the fixed rate.\n\n"
        f"👑 <code>/buypremium</code>\nBuy Bot Premium User status with ⭐ Star — shorter spam cooldown, a higher daily catch limit, bonus cards, a daily Star gift, and more. (Or earn it free — spend/buy {PREMIUM_AUTO_STAR_THRESHOLD}⭐ in one day for {PREMIUM_AUTO_GRANT_DAYS} free day.)"
    )

def get_casino_text():
    return (
        f"🎰 <b><u>Casino Floor</u></b>\n\n"
        f"🎰 <code>/slot [amount]</code>\nSpin the 7-symbol slot machine.\n\n"
        f"🃏 <code>/cardgame [amount]</code>\nCreate a multiplayer card game lobby.\n\n"
        f"▶️ <code>/startgame</code> / <code>/cancelgame</code>\nStart or cancel the lobby you created.\n\n"
        f"🪙 <code>/flip [heads/tails] [amount]</code>\nCoin flip — 50/50 odds.\n\n"
        f"🎲 <code>/dice [amount]</code>\nRoll a dice, win on 4-6.\n\n"
        f"🂡 <code>/hilo [amount]</code>\nHigher/lower card game.\n\n"
        f"🎯 <code>/gamble [amount]</code>\nDouble or nothing — 50% chance.\n\n"
        f"💣 <code>/mines [amount]</code>\nReveal safe tiles in a 5x5 grid, cash out anytime — hit a bomb and lose it all.\n\n"
        f"📦 <code>/box [amount]</code>\nDeal or No Deal — 30 boxes, keep one, open the rest, take Morgan's offer whenever you want.\n\n"
        f"🎡 <code>/roulette [amount]</code> (<code>/r</code>)\nBet on a color or number, then spin the wheel.\n\n"
        f"🔴 <code>/plinko [amount]</code> (<code>/p</code>)\nDrop a ball through the pegs for a random multiplier.\n\n"
        f"🛞 <code>/wheel [amount]</code>\nSpin the fortune wheel for a random multiplier.\n\n"
        f"✂️ <code>/rps [amount]</code>\nRock-paper-scissors against the bot — winning doubles your bet."
    )

def get_collection_text():
    return (
        f"🎒 <b><u>Collection Desk</u></b>\n\n"
        f"🎒 <code>/harem</code>\nView your vault — paginated inventory of everyone you've caught.\n\n"
        f"⭐ <code>/fav [ID]</code>\nSet a favourite card to pin at the top.\n\n"
        f"📊 <code>/profile</code>, <code>/myinfo</code>\nCheck your stats, balance, and collection at a glance.\n\n"
        f"🏆 <code>/top</code> / <code>/gtop</code>\nLocal and global leaderboards.\n\n"
        f"🔎 <code>/check [ID]</code>\nDetailed character info and its top collectors.\n\n"
        f"🖼 <code>/show</code>\nPick a rarity (2x2 button grid) and browse every character in it, full quality, with ⬅️ Prev / ➡️ Next and a 🛒 Buy button. DM only.\n\n"
        f"🔗 <code>/referral</code>\nGet your invite link — you get 0.50 USD, your friend gets 0.25 USD."
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'(?i)^[/.]help(?:@\w+)?$', 'bot1')))
async def help_command_handler(event):
    await event.reply(bq(get_help_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])

@bot1.on(events.NewMessage(pattern=own_pattern(r'(?i)^[/.]game(?:@\w+)?$', 'bot1')))
async def game_command_handler(event):
    # 🩹 FIX: this used to call get_game_text(), which — despite the name — is actually the
    # ECONOMY menu (balance/daily/hunt/gifts...). The real games list (slot, cardgame,
    # flip, dice, hilo, gamble) lives in get_casino_text(). /game was showing the wrong menu.
    await event.reply(bq(get_casino_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])

@bot1.on(events.CallbackQuery())
async def system_callback_router(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    if data == "nav_back_home":
        bot_me = await bot1.get_me()
        welcome_msg = (
            f"<b>🎮 Character Collector Bot</b>\n"
            f"Characters spawn in your groups for you to catch and collect — that's my main game. "
            f"I also run Casino games, an in-bot economy (💵 USD &amp; ⭐ Star), and basic group "
            f"management on the side."
        )
        buttons = [
            [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("💰 Economy", data="nav_game_main")],
            [Button.inline("🎰 Casino", data="nav_casino_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
            [Button.url("Add Me To Your Group", f"https://t.me/{bot_me.username}?startgroup=true")],
            [Button.url("Join Our Circle", "https://t.me/Comeback_BoD")]
        ]
        return await event.edit(bq(welcome_msg), parse_mode='html', buttons=buttons)
    elif data == "nav_help_main":
        return await event.edit(bq(get_help_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_game_main":
        return await event.edit(bq(get_game_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_casino_main":
        return await event.edit(bq(get_casino_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_collection_main":
        return await event.edit(bq(get_collection_text()), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_hmode":
        await set_rarity_filter_handler(event)
    elif data.startswith("catchprofile_"):
        target_user_id = int(data.split("_", 1)[1])
        if user_id != target_user_id:
            return await event.answer("⚠️ This isn't your profile button!", alert=True)
        mention = await get_html_mention(event, user_id)
        text, buttons = await render_profile_main_page(event, user_id, mention)
        await event.respond(text, parse_mode='html', buttons=buttons)
        await event.answer()
    elif data.startswith("pf_stats_"):
        target_user_id = int(data.split("_", 2)[2])
        if user_id != target_user_id:
            return await event.answer("⚠️ This isn't your profile button!", alert=True)
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        raw_harem = user_doc.get("harem", []) if user_doc else []
        owned_copies = {tier: 0 for tier in RARITY_TIERS}
        owned_unique = {tier: set() for tier in RARITY_TIERS}
        for item in raw_harem:
            if not isinstance(item, dict):
                continue
            tier = classify_rarity(item.get("rarity", ""))
            if tier in owned_copies:
                owned_copies[tier] += 1
                if item.get("char_id"):
                    owned_unique[tier].add(item["char_id"])
        tier_totals_cursor = characters_base_col.aggregate([
            {"$group": {"_id": "$rarity_tier", "count": {"$sum": 1}}}
        ])
        tier_totals = {doc["_id"]: doc["count"] async for doc in tier_totals_cursor}
        lines = []
        for tier in RARITY_TIERS:
            emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
            copies = owned_copies[tier]
            unique = len(owned_unique[tier])
            total = tier_totals.get(tier, 0)
            lines.append(f"{emoji} <b>{tier}:</b> <code>{copies}</code> owned <i>({unique}/{total} unique)</i>")
        text = (
            f"📊 <b>RARITY BREAKDOWN</b>\n"
            f"" + "\n".join(lines) + "\n"
            f"<i>Ordered from rarest (top) to most common (bottom).</i>"
        )
        buttons = [[Button.inline("🔙 Back to Profile", data=f"pf_back_{user_id}")]]
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    elif data.startswith("pf_back_"):
        target_user_id = int(data.split("_", 2)[2])
        if user_id != target_user_id:
            return await event.answer("⚠️ This isn't your profile button!", alert=True)
        mention = await get_html_mention(event, user_id)
        text, buttons = await render_profile_main_page(event, user_id, mention)
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
        premium_tag = " 👑 [Premium User]" if is_premium_active(u) else ""
        hit_at = u.get("daily_limit_hit_at")
        if hit_at:
            time_str = hit_at.astimezone(TZ).strftime("%H:%M") if isinstance(hit_at, datetime) else "?"
            lines.append(f"{medal}  {mention} — 🏁 hit their daily limit at <code>{time_str}</code>{premium_tag}")
        else:
            lines.append(f"{medal}  {mention} — <code>{u['daily_catches']} catches</code>{premium_tag}")

    text = f"📅 <b>Today's Catchers</b> <i>(Top {TODAY_TOP_LIMIT})</i>\n"
    text += f"🏁 Ranked by who reached their daily catch limit first (👑 Premium: {PREMIUM_DAILY_CATCH_LIMIT}, others: {DAILY_CATCH_LIMIT})\n\n"
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
                    f"အပြင် Casino ဂိမ်းအမျိုးမျိုးကိုလည်း ဒီ Group ထဲမှာ ဆော့ကစားနိုင်ပါပြီ — "
                    f"ဂိမ်းတွေ ဆော့ပြီး 💵 USD &amp; ⭐ Star ကို တကယ် ရယူနိုင်ပါတယ်။\n\n"
                    f"📌 <b>စတင်ကြည့်ရှုရန်:</b>\n"
                    f"   • <code>/introduce</code> - ကျွန်တော် လုပ်ဆောင်ပေးနိုင်တာတွေ အသေးစိတ် ကြည့်ရန်\n"
                    f"   • <code>/help</code> - Command အားလုံး ကြည့်ရန်\n\n"
                    f"🎮 ဂိမ်းဆော့ပြီး ⭐ Star &amp; 💵 USD ရယူနိုင်တာမို့၊ သင့် Group ကိုယ်ပိုင်မှာလည်း ဒီအကျိုးခံစားချက်တွေ "
                    f"ရစေချင်ရင် <b>@{bot_me.username}</b> ကို Add လုပ်ထားနိုင်ပါတယ်။\n\n"
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
        mute_seconds = PREMIUM_SPAM_MUTE_SECONDS if await check_premium(user_id) else SPAM_CATCH_MUTE_SECONDS
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
    worth = format_usd(char_doc.get('currency_value', 0))
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
        f"💎 {worth}   │   🔁 {limit_text}\n"
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
        char_id = f"BOD{random.randint(1, 9999)}"
        while await characters_base_col.find_one({"char_id": char_id}):
            char_id = f"BOD{random.randint(1, 9999)}"
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
    if char_doc and char_doc.get("char_id"):
        tier = RARITY_TIERS[int(tier_num) - 1]
        if tier in _cached_disabled_buy_tiers:
            # 🩹 CHANGED (per owner request): a dead "sold out" button used to just show an
            # alert and go nowhere. Now it's a URL button straight to the owner's pinned
            # message — buyers can reply there directly to negotiate/buy manually while the
            # tier is closed in the Owner Shop.
            rows.append([Button.url("🚫 အရောင်းကုန်ပါပြီ — ဝယ်ရန်ဆက်သွယ်ပါ", SOLD_OUT_CONTACT_LINK)])
        else:
            price = star_price_for_char(char_doc)
            rows.append([Button.inline(f"🛒 {price}⭐ ဖြင့်ဝယ်မယ်", data=f"shopbuy_{char_doc['char_id']}")])
    rows.append([Button.inline("🔢 Rarity List", data="showgrid_back")])
    return rows

def _build_show_caption(char_doc, tier_num, idx, total):
    rarity_display = char_doc.get("rarity") or RARITY_NUM_MAP.get(tier_num, {}).get("name", "Unknown")
    limit = char_doc.get("spawn_limit", 0)
    spawned = char_doc.get("spawn_count", 0)
    caught_text = "♾️ <b>Infinite</b>" if not limit else f"<code>{spawned}/{limit}</code>"
    price = star_price_for_char(char_doc)
    return (
        f"🖼️ <b>Rarity Gallery</b> — <code>{idx + 1}/{total}</code>\n"
        f""
        f"✨ <b>Name:</b> <code>{escape_html(char_doc.get('name',''))}</code>\n"
        f"🆔 <b>ID:</b> <code>{display_char_id(char_doc.get('char_id',''))}</code>\n"
        f"{rarity_display}\n"
        f"🫧 <b>Category:</b> <code>{escape_html(char_doc.get('category','') or 'Unknown')}</code>\n"
        f"{artist_line(char_doc)}"
        f"🔁 <b>Caught:</b> {caught_text}\n"
        f"⭐ <b>Shop Price:</b> <code>{price}⭐</code>"
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

async def _maybe_reward_artist_for_collect(artist_name, catcher_mention, character_name):
    """Fire-and-forget: if `artist_name` (from a caught card's 'artist' field) is linked to a
    Telegram account via /linkartist, credits that account a random ⭐ Star reward and
    announces it in the force-join group through the Guard Bot. Does nothing — silently and
    cheaply — if there's no artist credit on the card or no link registered for it yet."""
    if not artist_name or not str(artist_name).strip():
        return
    try:
        link = await artists_col.find_one({"artist_name": str(artist_name).strip().lower()})
        if not link or not link.get("user_id"):
            return
        artist_user_id = link["user_id"]
        star_amount = round(random.uniform(GUARD_ARTIST_REWARD_MIN, GUARD_ARTIST_REWARD_MAX), 2)
        await users_catcher_col.update_one({"user_id": artist_user_id}, {"$inc": {"star_balance": star_amount}}, upsert=True)
        artist_mention = f"<a href='tg://user?id={artist_user_id}'>{escape_html(link.get('display_name') or str(artist_name))}</a>"
        await bot1.send_message(
            FORCE_SUB_CHAT_ID,
            f"🎨 <b>Artist Reward!</b>\n{catcher_mention} collected <b>{escape_html(character_name)}</b>, drawn by "
            f"{artist_mention} — <code>+{star_amount}⭐</code> sent their way!",
            parse_mode='html'
        )
    except Exception as e:
        print(f"⚠️ Artist reward failed for '{artist_name}': {e}")

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
    # 🔒 Two messages can cross the spawn_target threshold within milliseconds of each other —
    # both would pass the check above since neither active_group_spawns nor pending_rarity_quiz
    # has been written yet. Serialize on the same per-chat lock the quiz-solve callback already
    # uses, and re-check once inside it, so only the first caller actually spawns anything.
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
                # spawn_count now represents number of catches, so compare against limit
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
            # ⚖️ Configurable via /spawnweight (groups 1-3 / 4-6 / 7-9); falls back to
            # DEFAULT_RARITY_WEIGHTS for any group left unset.
            RARITY_WEIGHTS = get_effective_rarity_weights()

            # 🛡️ RELIABILITY: a character whose storage media has gone missing (deleted from
            # the control group, corrupted forward, etc.) used to silently swallow the ENTIRE
            # spawn attempt — trigger_dynamic_spawn would just quietly return and the group
            # would have to rack up a whole new spawn_target's worth of messages before getting
            # another chance. Now we retry with a different character (excluding whichever ones
            # just failed) a few times before giving up, so one bad entry can't stall a group.
            candidates = list(eligible_characters)
            max_attempts = min(5, len(candidates))
            for attempt in range(max_attempts):
                weights = [
                    RARITY_WEIGHTS.get(c.get("rarity_tier") or classify_rarity(c.get("rarity", "")), 20)
                    for c in candidates
                ]
                chosen_char = random.choices(candidates, weights=weights, k=1)[0]
                tier = chosen_char.get("rarity_tier") or classify_rarity(chosen_char.get("rarity", ""))
                if tier in RARITY_GATE_TIERS:
                    # Rarity No.1-4 — don't spawn directly, gate it behind a quiz first.
                    ok = await start_rarity_gate_quiz(chat_id, chosen_char)
                    if not ok:
                        # Quiz couldn't be posted (e.g. no quiz questions configured) — release
                        # directly rather than silently stalling the whole group.
                        ok = await release_spawn(chat_id, chosen_char)
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
        artist_display = escape_html(str(artist_raw).strip()) if artist_raw and str(artist_raw).strip() else "-"
        # Spelled out step-by-step on purpose — players were missing that /who has to be a
        # REPLY to this exact message, and that there's a second /fuck step after that.
        spawn_text = (
            f"𓂃 ⋆｡˚ <i>someone slipped in and doesn't want to be found yet…</i>\n"
            f"◈ whisper <code>/w</code> if you're curious, or guess with <code>/fuck [ NAME ]</code>\n"
            f"✒️ Artist: {artist_display}"
        )

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
            f"◈ <b>not just anyone gets to find me…</b>\n"
            f"<b>Rarity:</b> {rarity_display}\n\n"
            f"❓ <b>{escape_html(q['question'])}</b>\n\n"
            f"⏱ <b>{RARITY_GATE_TIMEOUT_SECONDS} seconds</b> — answer first, and I'm yours\n"
            f"🧨 <i>မှားဖြေမိရင် အခွင့်အရေး ထပ်မရနိုင်ပါ.</i>"
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
    # ⭐ Rarity 1-4 gate quizzes reward a small random Star bonus for the correct answer,
    # separate from and in addition to the spawn itself being released. 👑 Premium winners get
    # PREMIUM_QUIZ_REWARD_MULTIPLIER extra on top of the usual roll.
    star_reward = round(random.uniform(QUIZ_STAR_REWARD_MIN, QUIZ_STAR_REWARD_MAX), 2)
    winner_is_premium = await check_premium(winner_id)
    if winner_is_premium:
        star_reward = round(star_reward * PREMIUM_QUIZ_REWARD_MULTIPLIER, 2)
    try:
        await users_catcher_col.update_one({"user_id": winner_id}, {"$inc": {"star_balance": star_reward}}, upsert=True)
    except Exception as e:
        print(f"Quiz star reward error: {e}")
    try:
        await event.edit(
            f"◈ <b>{mention} found the answer… I'm yours now</b>\n"
            f"✔ <b>Correct answer:</b> {escape_html(quiz['options'][quiz['correct_index']])}\n"
            f"⭐ <b>Bonus:</b> +<code>{star_reward}⭐</code>{' 👑' if winner_is_premium else ''}\n\n"
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

async def _identify_media_and_reply(event, media_msg):
    user_id = event.sender_id
    is_cd, _ = await is_on_cooldown(user_id, "identify_repost", IDENTIFY_COOLDOWN_SECONDS)
    if is_cd:
        return
    best_match = await find_character_by_media(media_msg)
    if not best_match:
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
            f"<i>Only catchable if this one is actually live right now — this is just a lookup.</i>"
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
    if event.is_reply:
        replied_msg = await event.get_reply_message()
        if not replied_msg:
            return
        bot_me = await bot1.get_me()
        if replied_msg.sender_id != bot_me.id:
            replied_sender = await replied_msg.get_sender()
            if getattr(replied_sender, 'bot', False):
                return

    # ---- Path A: replying to the CURRENT live spawn message in this group — original,
    # unchanged flow (expiry/claimed guards, catch button, etc.) ----
    if not event.is_private and chat_id in active_group_spawns:
        spawn_data = active_group_spawns[chat_id]
        if event.is_reply and event.reply_to_msg_id == spawn_data["spawn_msg_id"]:
            if time.time() - spawn_data["spawn_time"] > 300:
                del active_group_spawns[chat_id]
                return await event.reply(
                    "…too late. I already wandered off. wait for the next one",
                    parse_mode='html'
                )
            try:
                char_name = spawn_data['name']
                rarity_tier = classify_rarity(spawn_data.get('rarity', ''))
                rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
                reveal_text = (
                    f"◈ found me, huh?\n\n"
                    f"{rarity_emoji} <code>/fuck {escape_html(char_name)}</code>\n\n"
                    f"…say it, and I'm yours."
                )
                try:
                    buttons = [
                        [types.KeyboardButtonCopy(
                            text=f"🤍 it's me, {char_name}",
                            copy_text=f"/fuck {char_name}"
                        )]
                    ]
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
        return await _identify_media_and_reply(event, media_msg)

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

# ---- CATCH LOGIC (with daily limit and spawn_count increment on success) ----
DAILY_CATCH_LIMIT = 22  # flat cap for everyone — single source of truth, used by both the
# limit check in catch_handler and the /today "who hit the limit first" ranking below.

async def perform_catch(chat_id, user_id, spawn_data, event, reply_to_msg=None, is_callback=False, temp_msg_id=None):
    """Grants the catch reward. IMPORTANT: by the time this is called, catch_handler has
    already atomically marked spawn_data['claimed'] = True under spawn_locks[chat_id] —
    that's the actual "who wins" decision. This function no longer re-checks or re-locks
    that; it assumes the caller already won and just needs the reward + message sent.
    (This split is what fixes the freeze/spam under simultaneous catches — see catch_handler.)"""
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    try:
        # Update user: add card, increment total, balance, group catches, and daily catches.
        # find_one_and_update (not update_one) so we get the POST-increment daily_catches
        # back atomically, with no separate read that could race against another catch.
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
                    "wallet_balance": spawn_data["value"],
                    "star_balance": catch_star_reward(spawn_data['rarity']),
                    f"group_catches.{str(chat_id)}": 1,
                    "daily_catches": 1
                },
                "$set": {"fullname": plain_name, "last_catch_date": datetime.now(TZ)}
            },
            upsert=True,
            return_document=ReturnDocument.AFTER
        )
        # Record exactly when this user's daily_catches first reached today's cap — this is
        # what /today's leaderboard sorts by ("who hit the limit first"). daily_catches only
        # ever moves up by 1 and is reset to 0 (with daily_limit_hit_at unset) at the start of
        # each new day — see the day-rollover check in catch_handler below — so the update
        # that brings it to exactly the user's own cap (PREMIUM_DAILY_CATCH_LIMIT for Premium,
        # DAILY_CATCH_LIMIT otherwise) is the one and only moment that happens today, and the
        # $exists guard makes the write itself idempotent too.
        effective_limit = PREMIUM_DAILY_CATCH_LIMIT if is_premium_active(updated_user) else DAILY_CATCH_LIMIT
        if updated_user and updated_user.get("daily_catches") == effective_limit:
            await users_catcher_col.update_one(
                {"user_id": user_id, "daily_limit_hit_at": {"$exists": False}},
                {"$set": {"daily_limit_hit_at": datetime.now(TZ)}}
            )
        # ✅ Increment spawn_count ONLY on successful catch
        await characters_base_col.update_one(
            {"char_id": spawn_data['char_id']},
            {"$inc": {"spawn_count": 1}}
        )
        guild_levelup_msg = ""
        user_guild = await guilds_col.find_one({"members": user_id})
        if user_guild:
            new_xp = user_guild["xp"] + 10
            current_level = user_guild["level"]
            if new_xp >= (current_level * 500):
                await guilds_col.update_one({"_id": user_guild["_id"]}, {"$set": {"xp": 0}, "$inc": {"level": 1}})
                guild_levelup_msg = f"\n\n🏰 <b>Guild Level Up!</b> 👑\nYour guild <b>[{escape_html(user_guild['name'])}]</b> is now Level <b>{current_level + 1}</b>! 🎉"
            else:
                await guilds_col.update_one({"_id": user_guild["_id"]}, {"$inc": {"xp": 10}})
        character_name = spawn_data['name']
        asyncio.create_task(_maybe_reward_artist_for_collect(spawn_data.get('artist'), mention, character_name))
        newly_earned = await check_and_award_achievements(user_id)
        raw_event_name = spawn_data.get('event')
        event_display = escape_html(raw_event_name) if raw_event_name and raw_event_name != "General" else ""
        rarity_tier = classify_rarity(spawn_data['rarity'])
        rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
        # 👑 Premium catchers get a flashier catch card than everyone else — a banner up top,
        # a crown next to their name, and the 🎃🐢 pair — so a Premium catch visibly stands out
        # in the group.
        is_catcher_premium = is_premium_active(updated_user)
        premium_banner = "◈ premium darling ◈\n" if is_catcher_premium else ""
        premium_crown = " 👑" if is_catcher_premium else ""

        success_msg = (
            f"{premium_banner}"
            f"◈ caught.\n\n"
            f"<b>{mention}</b>{premium_crown}, {escape_html(character_name)}'s heart is yours now{' (' + event_display + ')' if event_display else ''} 🤍\n"
            f""
            f"{rarity_emoji} {strip_rarity_number(spawn_data['rarity'])} · #{display_char_id(spawn_data['char_id'])}\n"
            f"{artist_line(spawn_data.get('artist'))}"
            f"+{format_usd(spawn_data['value'])} · +{format_star_plain(catch_star_reward(spawn_data['rarity']))}⭐\n"
            f"\n"
            f"<code>/harem</code> to see who else is waiting for you…"
        )

        if guild_levelup_msg:
            success_msg += guild_levelup_msg
        success_msg += format_achievement_unlocks(newly_earned)
        success_buttons = [[
            Button.switch_inline("🤍 my harem", query=f"harem.{user_id}", same_peer=True),
            Button.inline("◈ profile", data=f"catchprofile_{user_id}")
        ]]
        if chat_id in active_group_spawns: del active_group_spawns[chat_id]
        if chat_id in spawn_locks: del spawn_locks[chat_id]
        if is_callback:
            await bot1.send_message(chat_id, success_msg, reply_to=reply_to_msg or event.message_id, parse_mode='html', buttons=success_buttons)
        elif temp_msg_id:
            # 🩹 Edit the 🐛→🦋 catching-animation message into the final result in place,
            # instead of deleting it and sending a brand new message — one message, no flicker.
            try:
                await bot1.edit_message(chat_id, temp_msg_id, success_msg, parse_mode='html', buttons=success_buttons)
            except errors.MessageNotModifiedError:
                pass
            except Exception:
                # Edit failed for some other reason (e.g. message too old) — make sure the
                # player still sees their result rather than silently losing it.
                await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
        else:
            await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
        return True
    except Exception as e:
        # NOTE: we deliberately do NOT reset claimed=False here. This spawn was already
        # atomically handed to this user in catch_handler — reopening it after a failure
        # (e.g. a Telegram flood-wait mid-flow) is exactly how two people could end up
        # winning the same character. Instead we clear the spawn out so the game doesn't
        # get stuck, log the fault, and let the next spawn come normally.
        if chat_id in active_group_spawns: del active_group_spawns[chat_id]
        if chat_id in spawn_locks: del spawn_locks[chat_id]
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
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:morgan|fuck|obtain)(?:@\w+)?\s+(.*)$', 'bot1')))
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
        daily_limit = PREMIUM_DAILY_CATCH_LIMIT if is_premium_active(user_doc) else DAILY_CATCH_LIMIT
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
    await asyncio.sleep(0.5)
    try:
        await temp_msg.edit("💥")
    except errors.MessageNotModifiedError:
        pass
    await asyncio.sleep(0.5)
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
    
    if user_id == OWNER_ID:
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
    is_unlimited_vault = (user_id == OWNER_ID)
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
    db_chars = await characters_base_col.find({"char_id": {"$in": owned_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "_id": 0}).to_list(length=None)
    category_totals = await get_category_totals_cached()
    def get_rarity_weight(rarity_str):
        return rarity_rank_value(rarity_str)
    from collections import defaultdict
    by_category = defaultdict(list)
    for card in db_chars:
        by_category[card.get("category") or "Unknown Series"].append(card)
    # 🎨 UI REDESIGN: cards are no longer grouped under a per-category header — each card is
    # its own 2-line block (name/id/rarity/qty, then an "Anime" line carrying the category +
    # owned/total for that series), sorted flat by rarity then name. Simpler than the old
    # category-block/continuation-header scheme since there's no group to keep together
    # across a page break anymore — every block is independent.
    sorted_cards = sorted(db_chars, key=lambda x: (-get_rarity_weight(x.get("rarity", "")), x.get("name", "").lower()))
    card_blocks = []  # [(char_id, line1_without_rank_badge, line2), ...]
    for card in sorted_cards:
        cid = card["char_id"]
        counts = harem_counts.get(cid, {"normal": 0, "market": 0})
        normal_qty = counts["normal"]
        market_qty = counts["market"]
        if normal_qty > 0 and market_qty > 0:
            status_str = f"x{normal_qty} | {market_qty} 🛒"
        elif market_qty > 0:
            status_str = f"{market_qty} 🛒"
        else:
            status_str = f"x{normal_qty}"
        tier = classify_rarity(card.get("rarity", ""))
        rarity_emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
        cat = card.get("category") or "Unknown Series"
        owned_in_cat = len(by_category[cat])
        total_in_cat = category_totals.get(cat, owned_in_cat)
        line1 = f"☘️ {escape_html(card['name'])} : <code>{display_char_id(cid)}</code> : {rarity_emoji} | ({status_str})"
        line2 = f"⚜️ Anime: {escape_html(cat)} (<code>{owned_in_cat}/{total_in_cat}</code>)"
        card_blocks.append((cid, line1, line2))
    # PAGE_CHAR_BUDGET is deliberately set so that EVERY page — not just page 1 — stays within
    # Telegram's 1024-char photo CAPTION limit even after adding the mention/label line, filter
    # line, and footer. That's what lets the fav-card photo stay attached for the whole vault,
    # any size: since every single page is guaranteed caption-safe, Next/Previous can keep
    # editing that same photo message's caption forever without ever risking
    # "MediaCaptionTooLongError" — no need to fall back to plain text or a bigger vault at all.
    PAGE_CHAR_BUDGET = 450
    pages = []          # each page: [(char_id, line1, line2), ...]
    current_page, current_len = [], 0

    def _flush_page():
        nonlocal current_page, current_len
        if current_page:
            pages.append(current_page)
        current_page, current_len = [], 0

    for cid, line1, line2 in card_blocks:
        block_len = utf16_len(line1) + 1 + 4 + utf16_len(line2) + 1 + 1  # +4 reserves room for a rank badge suffix on line1; final +1 is the blank spacer after this card
        if current_page and current_len + block_len > PAGE_CHAR_BUDGET:
            _flush_page()
        current_page.append((cid, line1, line2))
        current_len += block_len
    _flush_page()
    total_pages = len(pages) or 1
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    page_items = pages[page - 1] if pages else []
    # Only now do we know exactly which cards are visible on this page — look up ranks for
    # just those instead of the whole vault.
    page_char_ids = [cid for cid, _, _ in page_items]
    ranks_map = await get_user_ranks_for_cards(viewer_id, page_char_ids)
    page_lines = []
    for cid, line1, line2 in page_items:
        rank = ranks_map.get(cid)
        rank_str = ""
        if rank == 1:
            rank_str = " 🥇"
        elif rank == 2:
            rank_str = " 🥈"
        elif rank == 3:
            rank_str = " 🥉"
        page_lines.append(f"{line1}{rank_str}")
        page_lines.append(line2)
        page_lines.append("")  # blank spacer between cards
    try:
        sender_ent = await client.get_entity(user_id)
        first = getattr(sender_ent, 'first_name', '') or ''
        last = getattr(sender_ent, 'last_name', '') or ''
        fullname = f"{first} {last}".strip() or getattr(sender_ent, 'username', '') or "Hunter"
    except: fullname = "Hunter"
    mention = f"<a href='tg://user?id={user_id}'><b>{escape_html(fullname)}</b></a>"
    vault_owner_doc = await users_catcher_col.find_one({"user_id": user_id}, {"premium_until": 1})
    premium_badge = " 👑" if (not is_unlimited_vault and is_premium_active(vault_owner_doc)) else ""
    output_text = f"{mention}'s{premium_badge} <b>Recent Waifus</b> - Page: <code>{page}/{total_pages}</code>\n"
    if rarity_filter:
        output_text += f"🔍 <b>Filter:</b> {rarity_filter}\n"
    output_text += "\n"
    for l in page_lines:
        output_text += l + "\n"
    output_text += "\n"
    if is_own_vault:
        output_text += f"🏪 <i>/market ဖြင့် ⭐ Star &amp; ကဒ်များ ဝယ်နိုင်ပါတယ်</i>\n"
    if is_unlimited_vault:
        output_text += f"👑Userများကို ကဒ်ဂေ့ရန်အတွက်ပါနော်​ဗျ"
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
            buttons.append([Button.inline("Filterမထားဘူး", data=f"hfilter_clear_{user_id}")])
        buttons.append([Button.inline("Rarity Filterချိန်းမယ်", data="nav_hmode")])
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
    is_unlimited_vault = (target_user_id == OWNER_ID) and not force_real_harem

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
    # within each group, same rarity-weight-then-name order as before.
    db_chars = sorted(db_chars, key=lambda x: (
        0 if (filter_tier and classify_rarity(x.get("rarity", "")) == filter_tier) else 1,
        -_rarity_weight_for_sort(x.get("rarity", "")),
        x.get("name", "").lower()
    ))
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
            qty_note = f" (x{qty})" if not is_unlimited_vault else ""
            event_text = card.get("event") or "General"
            caption = (
                f"Wow, check {escape_html(owner_name)}'s character card!\n"
                f"🆔 Id- <code>{display_char_id(cid)}</code>\n"
                f"🌟 Name- <b>{escape_html(card['name'])}</b>{qty_note}\n"
                f"⚜️ Anime- {escape_html(card.get('category', ''))}\n"
                f"🎡 Event- {escape_html(event_text)}\n"
                f"{rarity_emoji} Rarity- {card.get('rarity', '')}"
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
    elif action_type == "mktpg":
        page = int(data_parts[1])
        await send_market_page(bot1, event.chat_id, page=page, edit_msg_id=event.message_id)
    elif action_type == "mktbuy":
        listing_id = data_parts[1]
        buyer_id = event.sender_id
        listing = await marketplace_col.find_one({"listing_id": listing_id})
        if not listing: return await event.answer("❌ This listing no longer exists.", alert=True)
        price = listing["price"]
        seller_id = listing["seller_id"]
        char_id = listing["char_id"]
        if buyer_id == seller_id: return await event.answer("⚠️ You cannot buy your own item!", alert=True)
        claim = await marketplace_col.delete_one({"listing_id": listing_id})
        if claim.deleted_count == 0:
            return await event.answer("❌ This listing no longer exists.", alert=True)
        char_data = await characters_base_col.find_one({"char_id": char_id})
        char_rarity = char_data.get("rarity", "Unknown") if char_data else "Unknown"
        res = await users_catcher_col.update_one(
            {"user_id": buyer_id, "wallet_balance": {"$gte": price}},
            {
                "$inc": {"wallet_balance": -price, "total_caught": 1},
                "$push": {"harem": {"char_id": char_id, "caught_date": time.time(), "rarity": char_rarity, "status": "vault"}}
            }
        )
        if res.modified_count == 0:
            await marketplace_col.insert_one(listing)
            return await event.answer("❌ Insufficient balance!", alert=True)
        # 🩹 FIX: atomic $pull-based removal (see remove_one_harem_copy) instead of the old
        # find_one → seller_harem.remove() → $set the whole array back — that read-modify-write
        # had a race window where a concurrent gift/sale/trade on the seller's account could get
        # silently clobbered by this stale full-array write.
        await remove_one_harem_copy(seller_id, char_id, "market")
        await users_catcher_col.update_one({"user_id": seller_id}, {"$inc": {"wallet_balance": price}})
        seller_doc_after = await users_catcher_col.find_one({"user_id": seller_id}, {"harem": 1})
        await clear_stale_favorite(seller_id, char_id, (seller_doc_after or {}).get("harem", []))
        await event.answer("🎉 Purchase successful!", alert=True)
        await event.edit(f"🤝 <b>DEAL SECURED</b>\n\nYou successfully bought the card.", parse_mode='html')
    elif action_type == "tr":
        sub_action = data_parts[1]
        sender_id = int(data_parts[2])
        target_id = int(data_parts[3])
        if sub_action == "canc":
            if event.sender_id in [sender_id, target_id]:
                await event.answer("❌ Transaction cancelled")
                await event.edit(f"❌ <b>Trade contract voided.</b>", parse_mode='html')
            else: await event.answer("⚠️ You are not involved in this trade.", alert=True)
            return
        if sub_action == "conf":
            if event.sender_id != target_id: return await event.answer("⚠️ You are not the recipient.", alert=True)
            if not claim_single_tap(event):
                return await event.answer("⏳ Already processing...", alert=False)
            await event.answer("⚡ Finalising trade...")
            my_char_id, their_char_id = data_parts[4], data_parts[5]
            s_doc = await users_catcher_col.find_one({"user_id": sender_id})
            t_doc = await users_catcher_col.find_one({"user_id": target_id})
            s_harem = s_doc.get("harem", []) if s_doc else []
            t_harem = t_doc.get("harem", []) if t_doc else []
            s_item = next((x for x in s_harem if isinstance(x, dict) and x.get("char_id") == my_char_id and x.get("status") != "market"), None)
            t_item = next((x for x in t_harem if isinstance(x, dict) and x.get("char_id") == their_char_id and x.get("status") != "market"), None)
            if not s_item or not t_item: return await event.edit(f"❌ <b>Trade failed – card unavailable.</b>", parse_mode='html')
            # 🩹 FIX: same atomic swap as marketplace-buy above — $pull exactly one matching
            # copy off each side, then $push the new one on, instead of read-modify-write-back
            # the whole harem array (which raced against any other concurrent change on either
            # account and could silently duplicate or erase cards).
            await remove_one_harem_copy(sender_id, my_char_id, s_item.get("status", "vault"))
            await remove_one_harem_copy(target_id, their_char_id, t_item.get("status", "vault"))
            await users_catcher_col.update_one(
                {"user_id": sender_id},
                {"$push": {"harem": {"char_id": their_char_id, "caught_date": time.time(), "rarity": t_item.get("rarity", "Unknown"), "status": "vault"}}}
            )
            await users_catcher_col.update_one(
                {"user_id": target_id},
                {"$push": {"harem": {"char_id": my_char_id, "caught_date": time.time(), "rarity": s_item.get("rarity", "Unknown"), "status": "vault"}}}
            )
            s_doc_after = await users_catcher_col.find_one({"user_id": sender_id}, {"harem": 1})
            t_doc_after = await users_catcher_col.find_one({"user_id": target_id}, {"harem": 1})
            await clear_stale_favorite(sender_id, my_char_id, (s_doc_after or {}).get("harem", []))
            await clear_stale_favorite(target_id, their_char_id, (t_doc_after or {}).get("harem", []))
            await event.edit(f"🤝 <b>Trade concluded successfully!</b>", parse_mode='html')
    elif action_type == "cardjoin":
        g_chat_id = int(data_parts[1])
        p_id = event.sender_id
        if not claim_single_tap(event):
            return await event.answer("⏳ Already processing...", alert=False)
        if g_chat_id not in active_card_games: return await event.answer("❌ This game lobby no longer exists.", alert=True)
        game = active_card_games[g_chat_id]
        if game["status"] != "lobby": return await event.answer("❌ Game started!", alert=True)
        if p_id in game["players"]: return await event.answer("⚠️ Already in game.", alert=True)
        if not await try_deduct_bet_bot3(event, p_id, game["bet"]):
            return await event.answer(f"❌ Insufficient balance! Need {game['bet']} USD", alert=True)
        await bot3_treasury_adjust(usd=game["bet"])
        if p_id in game["players"]:
            await users_catcher_col.update_one({"user_id": p_id}, {"$inc": {"wallet_balance": game["bet"]}})
            await bot3_treasury_adjust(usd=-(game["bet"]))
            return await event.answer("⚠️ Already in game.", alert=True)
        try:
            p_ent = await event.client.get_entity(p_id)
            f_n = getattr(p_ent, 'first_name', '') or ''
            l_n = getattr(p_ent, 'last_name', '') or ''
            fullname = f"{f_n} {l_n}".strip() or getattr(p_ent, 'username', '') or f"Agent {p_id}"
        except: fullname = f"Agent {p_id}"
        game["players"][p_id] = fullname
        host_mention = f"<a href='tg://user?id={game['host_id']}'><b>{escape_html(game['players'][game['host_id']])}</b></a>"
        lobby_text = f"🃏 <b>HIGH CARD DRAW</b>\n👑 <b>Host:</b> {host_mention}\n💵 <b>Bet:</b> <code>{game['bet']} USD</code>\n\n👥 <b>Players ({len(game['players'])}):</b>\n"
        for idx, (pid, name) in enumerate(game["players"].items(), start=1):
            p_mention = f"<a href='tg://user?id={pid}'><b>{escape_html(name)}</b></a>"
            lobby_text += f" {idx}. {p_mention}\n"
        lobby_text += f"\n📌 <i>Host: <code>/startgame</code></i>"
        buttons = [[Button.inline("🃏 Join", data=f"cardjoin_{g_chat_id}")]]
        await event.edit(lobby_text, parse_mode='html', buttons=buttons)
        await event.answer("🎉 You joined the game!")
    
    # ==========================================
    # 🃏 HI-LO (ပြင်ဆင်ပြီး ဗားရှင်း)
    # ==========================================
    elif action_type == "hilo":
        choice = data_parts[1]
        base_card = int(data_parts[2])
        bet_amount = float(data_parts[3])
        target_user_id = int(data_parts[4])
        
        if event.sender_id != target_user_id:
            return await event.answer("⚠️ This is not your game.", alert=True)
        if not claim_single_tap(event):
            return await event.answer("⏳ Already processing...", alert=False)
        
        new_card = random.randint(1, 13)
        while new_card == base_card:
            new_card = random.randint(1, 13)
        
        card_map = {1: "A", 11: "J", 12: "Q", 13: "K"}
        base_display = base_card if base_card <= 10 else card_map.get(base_card, str(base_card))
        new_display = new_card if new_card <= 10 else card_map.get(new_card, str(new_card))
        
        is_win = (choice == "HIGH" and new_card > base_card) or (choice == "LOW" and new_card < base_card)
        mention = await get_html_mention(event, target_user_id)
        
        # 🐋 Whale Check
        user_doc = await users_catcher_col.find_one({"user_id": target_user_id})
        whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
        is_whale = whale_balance > WEALTH_THRESHOLD
        
        result_text = ""
        payout = 0
        whale_text = ""
        
        if is_win:
            raw_win = bet_amount * 2
            if is_whale:
                raw_win, whale_text = apply_whale_tax(whale_balance, raw_win)
            payout = raw_win
            await users_catcher_col.update_one({"user_id": target_user_id}, {"$inc": {"wallet_balance": payout}})
            await bot3_treasury_adjust(usd=-(payout))
            result_text = f"🎉 <b>သင်နိုင်သည်!</b> <code>+{format_usd(payout)}</code>"
            
        elif new_card == base_card:
            # 🤝 အပြိုင် - လောင်းငွေ ပြန်အမ်းမယ်
            refund = bet_amount
            await users_catcher_col.update_one({"user_id": target_user_id}, {"$inc": {"wallet_balance": refund}})
            await bot3_treasury_adjust(usd=-(refund))
            result_text = f"🤝 <b>အပြိုင်</b> (လောင်းငွေ <code>{format_usd(bet_amount)}</code> ပြန်ရမယ်)"
        else:
            result_text = f"💸 <b>သင်ရှုံးသည်</b> <code>-{format_usd(bet_amount)}</code>"
        
        final_message = (
            f"🃏 <b>HI-LO ရလဒ်</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>ကစားသမား:</b> {mention}\n"
            f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet_amount)}</code>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🎴 <b>မူလကတ်:</b> <code>[ {base_display} ]</code>\n"
            f"🆕 <b>ကျသွားသောကတ်:</b> <code>[ {new_display} ]</code>\n"
            f"🎯 <b>သင်ရွေး:</b> <code>{'📈 Higher' if choice == 'HIGH' else '📉 Lower'}</code>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{result_text}"
            f"{whale_text}"
            f"{GAME_FOOTER}"
        )
        
        await event.edit(final_message, parse_mode='html')
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id)
    
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
    # 📊 Profile main/stats page toggle
    # ==========================================
    elif action_type == "pf":
        sub_action = data_parts[1]
        owner_user_id = int(data_parts[2])
        if event.sender_id != owner_user_id:
            return await event.answer("⚠️ ဒါက သင့်ရဲ့ Profile မဟုတ်ပါ။", alert=True)
        mention = await get_html_mention(event, owner_user_id)
        if sub_action == "stats":
            text, buttons = await render_profile_stats_page(owner_user_id, mention)
        else:
            text, buttons = await render_profile_main_page(event, owner_user_id, mention)
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
async def render_profile_main_page(event, user_id, mention):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    total_caught = user_doc.get("total_caught", 0) if user_doc else 0
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    streak = user_doc.get("daily_streak", 0) if user_doc else 0
    referrals = user_doc.get("referral_count", 0) if user_doc else 0
    badge_count = len(user_doc.get("achievements", [])) if user_doc else 0
    raw_harem = user_doc.get("harem", []) if user_doc else []
    fav_card_id = user_doc.get("fav_card") if user_doc else None
    total_gifted = user_doc.get("total_gifted", 0) if user_doc else 0
    total_gift_received = user_doc.get("total_gift_received", 0) if user_doc else 0
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
            chat_rank_line = f"➤ 🍁 <b>Chat Rank:</b> <code>#{chat_rank}</code>\n"
    fav_line = ""
    if fav_card_id and fav_card_id not in unique_ids:
        # Owner no longer has any copy of this card — clear the stale favourite.
        await users_catcher_col.update_one({"user_id": user_id, "fav_card": fav_card_id}, {"$unset": {"fav_card": ""}})
        fav_card_id = None
    if fav_card_id:
        fav_doc = await characters_base_col.find_one({"char_id": fav_card_id})
        if fav_doc:
            fav_line = f"➤ ⭐ <b>Favourite:</b> <code>{escape_html(fav_doc.get('name'))}</code> (<code>{fav_card_id}</code>)\n"
    pct = (unique_owned / base_total * 100) if base_total else 0
    premium_line = ""
    if is_premium_active(user_doc):
        expiry_str = datetime.fromtimestamp(user_doc["premium_until"], TZ).strftime("%Y-%m-%d")
        premium_line = f"➤ 👑 <b>Bot Premium User</b> — <code>{expiry_str}</code> အထိ\n"
    giver_title = get_giver_title(total_gifted)
    receiver_title = get_receiver_title(total_gift_received)
    giver_rank_str = f" ({giver_title[0]} {giver_title[1]})" if giver_title else ""
    receiver_rank_str = f" ({receiver_title[0]} {receiver_title[1]})" if receiver_title else ""
    cosmetic_prefix = get_equipped_cosmetics_prefix(user_doc)
    cosmetic_line = f"➤ ✨ <b>{escape_html(cosmetic_prefix)}</b>\n" if cosmetic_prefix else ""
    frame_border = get_equipped_frame_border(user_doc)
    header_line = f"{frame_border} <b>This is your account</b> {frame_border}" if frame_border else "<b>This is your account</b>"
    text = (
        f"{header_line}\n"
        f""
        f"➤ 🫅 <b>Collector:</b> {mention}\n"
        f"{cosmetic_line}"
        f"{premium_line}"
        f"➤ 🔖 <b>Your ID:</b> <code>{user_id}</code>\n"
        f"➤ 🏆 <b>Global Rank:</b> <code>#{rank}</code>\n"
        f"{chat_rank_line}"
        f"➤ 🎒 <b>Total Caught:</b> <code>{total_caught}</code>\n"
        f"➤ 🧬 <b>Unique Owned:</b> <code>{unique_owned}/{base_total}</code> (<code>{pct:.1f}%</code>)\n"
        f"<code>{build_progress_bar(unique_owned, base_total)}</code>\n"
        f"➤ 🪙 <b>Balance:</b> <code>{format_usd(balance)}</code>\n"
        f"➤ ⭐ <b>Star:</b> <code>{format_star_plain(star_balance)}</code>\n"
        f"➤ 🔥 <b>Streak:</b> <code>{streak}d</code>   🤝 <b>Referrals:</b> <code>{referrals}</code>\n"
        f"➤ 🏅 <b>Badges:</b> <code>{badge_count}/{len(ACHIEVEMENTS)}</code>\n"
        f"➤ 🎁 <b>Gifted:</b> <code>{total_gifted}</code>{giver_rank_str}\n"
        f"➤ 🎀 <b>Received:</b> <code>{total_gift_received}</code>{receiver_rank_str}\n"
        f"{fav_line}"
        f"\n"
        f"🏪 <i>/market ဖြင့် ⭐ Star &amp; ကဒ်များ ဝယ်နိုင်ပါတယ်</i>\n"
        f"🎭 <i>/shop ဖြင့် Title, Emblem, Frame ဝယ်နိုင်ပါတယ်</i>\n"
        f"<i>Tap below to open your Rarity Vault breakdown!</i>"
    )
    buttons = [[Button.inline("ရထားတဲ့ကဒ်များ", data=f"pf_stats_{user_id}")]]
    if total_gifted:
        buttons.append([Button.inline("🎁 Gift History", data=f"gh_{user_id}_0")])
    return text, buttons

async def render_profile_stats_page(user_id, mention):
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    total_caught = user_doc.get("total_caught", 0) if user_doc else 0
    raw_harem = user_doc.get("harem", []) if user_doc else []
    gifted_by_tier = (user_doc.get("gifted_by_rarity", {}) if user_doc else {}) or {}
    total_gifted = user_doc.get("total_gifted", 0) if user_doc else 0
    tier_counts = {t: 0 for t in RARITY_TIERS}
    for item in raw_harem:
        if isinstance(item, dict):
            tier = classify_rarity(item.get("rarity", ""))
            if tier in tier_counts:
                tier_counts[tier] += 1
    tier_block = []
    for tier in RARITY_TIERS:
        cnt = tier_counts[tier]
        gifted = gifted_by_tier.get(tier, 0)
        if cnt == 0 and gifted == 0:
            continue
        ever_total = cnt + gifted
        tier_block.append(
            f"{RARITY_EMOJI[tier]} <b>{tier}</b> — <code>{cnt}</code> (<code>{ever_total}</code>)\n"
            f"<code>{build_progress_bar(cnt, total_caught)}</code>"
        )
    body = "\n".join(tier_block) if tier_block else "<i>No characters caught yet.</i>"
    text = (
        f"📊 <b>RARITY VAULT</b> — {mention}\n"
        f"<i>current (total ever obtained, including gifted-away cards)</i>\n"
        f"{body}"
    )
    if total_gifted:
        text += f"\n🎁 <b>Total Gifted Away:</b> <code>{total_gifted}</code>"
    buttons = [[Button.inline("🔙 Back to Profile", data=f"pf_main_{user_id}")]]
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](profile|myinfo)(?:@\w+)?$', 'bot1')))
async def profile_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    text, buttons = await render_profile_main_page(event, user_id, mention)
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

# ==========================================
# 🎭 COSMETICS SHOP — /shop (Title, Emblem, Frame — USD money sink, purely cosmetic)
# ==========================================
# Owned forever once bought (kept in users_catcher_col.owned_cosmetics), but only ONE item per
# category can be equipped at a time (equipped_title / equipped_emblem / equipped_frame).
# Equipped title+emblem show as a line on /profile; equipped frame decorates the card header.
# No gameplay effect whatsoever — this exists purely as another place to spend USD.
COSMETICS_CATALOG = {
    "title": [
        {"id": "title_newcomer",     "label": "🌱 Newcomer",      "price": 5},
        {"id": "title_adventurer",   "label": "⚔️ Adventurer",    "price": 25},
        {"id": "title_veteran",      "label": "🔥 Veteran",       "price": 100},
        {"id": "title_highroller",   "label": "💎 High Roller",   "price": 500},
        {"id": "title_dragonmaster", "label": "🐉 Dragon Master", "price": 2500},
        {"id": "title_legend",       "label": "👑 Legend",        "price": 10000},
        {"id": "title_mythic",       "label": "🌌 Mythic",        "price": 50000},
    ],
    "emblem": [
        {"id": "emblem_lucky",        "label": "🍀 Lucky",         "price": 10},
        {"id": "emblem_swift",        "label": "⚡ Swift",         "price": 50},
        {"id": "emblem_sharpshooter", "label": "🎯 Sharpshooter",  "price": 250},
        {"id": "emblem_elite",        "label": "🦅 Elite",         "price": 1000},
        {"id": "emblem_champion",     "label": "🔱 Champion",      "price": 5000},
    ],
    "frame": [
        {"id": "frame_silver",  "label": "🥈 Silver Frame",  "price": 200,   "border": "🥈"},
        {"id": "frame_gold",    "label": "🥇 Gold Frame",    "price": 1000,  "border": "🥇"},
        {"id": "frame_diamond", "label": "💠 Diamond Frame", "price": 5000,  "border": "💠"},
        {"id": "frame_prism",   "label": "🌈 Prism Frame",   "price": 20000, "border": "🌈"},
    ],
}
COSMETIC_CATEGORY_LABELS = {"title": "🏷️ Title", "emblem": "🎖️ Emblem", "frame": "🖼️ Frame"}
COSMETIC_EQUIP_FIELD = {"title": "equipped_title", "emblem": "equipped_emblem", "frame": "equipped_frame"}

def _find_cosmetic(cosmetic_id):
    for cat, items in COSMETICS_CATALOG.items():
        for item in items:
            if item["id"] == cosmetic_id:
                return cat, item
    return None, None

def get_equipped_cosmetics_prefix(user_doc):
    """Equipped Title + Emblem as one short line for the profile card. '' if neither equipped."""
    if not user_doc:
        return ""
    parts = []
    for field in ("equipped_title", "equipped_emblem"):
        cid = user_doc.get(field)
        if cid:
            _, item = _find_cosmetic(cid)
            if item:
                parts.append(item["label"])
    return " ".join(parts)

def get_equipped_frame_border(user_doc):
    cid = user_doc.get("equipped_frame") if user_doc else None
    if not cid:
        return None
    _, item = _find_cosmetic(cid)
    return item.get("border") if item else None

def _render_shop_category(user_doc, category):
    items = COSMETICS_CATALOG[category]
    owned = set((user_doc or {}).get("owned_cosmetics", []))
    equipped = (user_doc or {}).get(COSMETIC_EQUIP_FIELD[category])
    lines = [f"🎭 <b>COSMETICS SHOP — {COSMETIC_CATEGORY_LABELS[category]}</b>", "<i>ဒီဟာတွေက Cosmetic ပဲဖြစ်ပြီး Gameplay ပေါ် ဘာမှသက်ရောက်မှုမရှိပါ — Profile ကို လှပအောင် လုပ်ဖို့ပဲ ဖြစ်ပါတယ်။</i>", ""]
    rows = []
    for item in items:
        tag = "✅ Equipped" if equipped == item["id"] else ("🔓 Owned" if item["id"] in owned else f"💰 {format_usd_compact(item['price'])}")
        lines.append(f"{item['label']} — {tag}")
        if equipped == item["id"]:
            rows.append([Button.inline(f"↩️ Unequip {item['label']}", data=f"shop_uneq_{category}")])
        elif item["id"] in owned:
            rows.append([Button.inline(f"👕 Equip {item['label']}", data=f"shop_equip_{item['id']}")])
        else:
            rows.append([Button.inline(f"💰 Buy {item['label']} — {format_usd_compact(item['price'])}", data=f"shop_buy_{item['id']}")])
    cat_row = [Button.inline(("• " if c == category else "") + lbl, data=f"shop_cat_{c}") for c, lbl in COSMETIC_CATEGORY_LABELS.items()]
    rows.append(cat_row)
    return "\n".join(lines), rows

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]shop(?:@\w+)?$', 'bot1')))
async def cosmetics_shop_command(event):
    user_id = event.sender_id
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    text, rows = _render_shop_category(user_doc, "title")
    await _out(event, text, parse_mode='html', buttons=rows)

@bot1.on(events.CallbackQuery(pattern=r'^shop_cat_(title|emblem|frame)$'))
async def shop_category_callback(event):
    category = event.pattern_match.group(1)
    if isinstance(category, bytes):
        category = category.decode('utf-8')
    if event.sender_id is None:
        return
    user_doc = await users_catcher_col.find_one({"user_id": event.sender_id})
    text, rows = _render_shop_category(user_doc, category)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^shop_buy_(\w+)$'))
async def shop_buy_callback(event):
    cosmetic_id = event.pattern_match.group(1)
    if isinstance(cosmetic_id, bytes):
        cosmetic_id = cosmetic_id.decode('utf-8')
    user_id = event.sender_id
    if not claim_single_tap(event):
        return await event.answer()
    category, item = _find_cosmetic(cosmetic_id)
    if not item:
        return await event.answer("⚠️ ဒီ Item မရှိပါ။", alert=True)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if item["id"] in (user_doc or {}).get("owned_cosmetics", []):
        return await event.answer("✅ ဒါကို ရှိပြီးသားပါ။", alert=True)
    if not await try_deduct_balance(user_id, item["price"]):
        return await event.answer(f"❌ Balance မလုံလောက်ပါ — {format_usd_compact(item['price'])} လိုအပ်ပါတယ်။", alert=True)
    await users_catcher_col.update_one({"user_id": user_id}, {"$addToSet": {"owned_cosmetics": item["id"]}})
    await event.answer(f"🎉 {item['label']} ဝယ်ယူပြီးပါပြီ!")
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    text, rows = _render_shop_category(user_doc, category)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass

@bot1.on(events.CallbackQuery(pattern=r'^shop_equip_(\w+)$'))
async def shop_equip_callback(event):
    cosmetic_id = event.pattern_match.group(1)
    if isinstance(cosmetic_id, bytes):
        cosmetic_id = cosmetic_id.decode('utf-8')
    user_id = event.sender_id
    if not claim_single_tap(event):
        return await event.answer()
    category, item = _find_cosmetic(cosmetic_id)
    if not item:
        return await event.answer("⚠️ ဒီ Item မရှိပါ။", alert=True)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if item["id"] not in (user_doc or {}).get("owned_cosmetics", []):
        return await event.answer("❌ ဒါကို မဝယ်ရသေးပါ။", alert=True)
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {COSMETIC_EQUIP_FIELD[category]: item["id"]}})
    await event.answer(f"👕 {item['label']} ဝတ်ဆင်လိုက်ပါပြီ!")
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    text, rows = _render_shop_category(user_doc, category)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass

@bot1.on(events.CallbackQuery(pattern=r'^shop_uneq_(title|emblem|frame)$'))
async def shop_unequip_callback(event):
    category = event.pattern_match.group(1)
    if isinstance(category, bytes):
        category = category.decode('utf-8')
    user_id = event.sender_id
    if not claim_single_tap(event):
        return await event.answer()
    await users_catcher_col.update_one({"user_id": user_id}, {"$unset": {COSMETIC_EQUIP_FIELD[category]: ""}})
    await event.answer("↩️ ချွတ်လိုက်ပါပြီ။")
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    text, rows = _render_shop_category(user_doc, category)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass

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
    msg = f"🔗 <b>YOUR REFERRAL LINK</b>\n⚡ ━━━━━━━━━━━━━━━ ⚡\nShare this link! You get <code>+0.50 USD</code>, friend gets <code>+0.25 USD</code>.\n\n🔗 <code>{ref_link}</code>\n\n👥 <b>Total Invited:</b> <code>{ref_count} Friends</code>"
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
# ==========================================
# 🛍️ /buy [char_id] — DAILY & LIFETIME PURCHASE LIMITS (Owner exempt from both)
# ==========================================
DAILY_BUY_LIMIT = 3  # Owner Shop purchases (/buy [char_id]) per player per day
LIFETIME_BUY_PER_CHAR_LIMIT = 1  # max copies of the SAME character a player can EVER buy via /buy
TOP_RARITY_WEEKLY_TIERS = {"SWEETIE", "BLOSSOM", "FLUFFY"}  # Rarity No.1, No.2, No.3
TOP_RARITY_WEEKLY_BUY_LIMIT = 2  # combined cap across ALL THREE tiers together, per rolling week
TOP_RARITY_WEEK_SECONDS = 7 * 86400
# 🔒 NEW CARD PROTECTION — a freshly /addchar'd character can't be bought outright via
# /buy for this long after creation; it can only be obtained by actually catching it from a
# live spawn. Stops a deep-pocketed player from insta-sniping every new card the moment it's
# added, before anyone else even gets a chance to see it spawn. Keyed off characters_base_col's
# "created_at" (set at /addchar time — see add_character()); characters added before this
# feature shipped have no created_at, default to 0, and are correctly treated as long past
# the window (so nothing already in the roster gets retroactively locked).
NEW_CARD_PROTECTION_SECONDS = 86400  # 24 hours

# ==========================================
# 👑 BOT PREMIUM USER — tuning constants
# ==========================================
PREMIUM_AUTO_STAR_THRESHOLD = 100  # ⭐ spent (via /buy) OR bought (via /buystar) in one day auto-grants Premium
PREMIUM_AUTO_GRANT_DAYS = 1  # length of the auto-grant, from the moment the threshold is crossed
PREMIUM_TIERS = [  # (months, price in ⭐, days credited) — the 5 /buypremium tiers
    (1, 9000, 30),
    (2, 17500, 60),
    (3, 25500, 90),
    (6, 48000, 180),
    (12, 90000, 365),
]
PREMIUM_DAILY_CATCH_LIMIT = 25  # vs DAILY_CATCH_LIMIT (22) for everyone else
PREMIUM_SPAM_MUTE_SECONDS = 180  # 3 minutes, vs SPAM_CATCH_MUTE_SECONDS (8 min / 480s)
PREMIUM_QUIZ_REWARD_MULTIPLIER = 1.5  # Premium winners' rarity-gate quiz Star bonus is scaled by this
PREMIUM_PURCHASE_BONUS_TIER = "KAWAII"  # Rarity No.4 (🎀 Kawaii) — free cards on every /buypremium purchase
PREMIUM_PURCHASE_BONUS_COUNT = 2

def is_premium_active(user_doc):
    """True if user_doc's premium_until is still in the future. Safe to call with None."""
    return bool(user_doc) and user_doc.get("premium_until", 0) > time.time()

async def check_premium(user_id):
    doc = await users_catcher_col.find_one({"user_id": user_id}, {"premium_until": 1})
    return is_premium_active(doc)

async def grant_premium_days(user_id, days):
    """Extends premium_until by `days`. Stacks on top of any time already remaining —
    buying/earning more while already Premium adds to what's left instead of overwriting it."""
    now = time.time()
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"premium_until": 1})
    current_until = (user_doc or {}).get("premium_until", 0)
    base = current_until if current_until > now else now
    new_until = base + days * 86400
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"premium_until": new_until}}, upsert=True)
    return new_until

async def _track_star_activity_and_maybe_grant_premium(user_id, kind, amount):
    """kind: 'spent' (⭐ spent on /buy Owner Shop purchases) or 'bought' (⭐ bought via
    /buystar). Tracks a per-day running total for each and, the moment either total FIRST
    crosses PREMIUM_AUTO_STAR_THRESHOLD in a single Yangon calendar day, grants
    PREMIUM_AUTO_GRANT_DAYS of Premium. Returns the new premium_until timestamp if a grant
    just happened, else None."""
    field = "star_spent_today" if kind == "spent" else "star_bought_today"
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"star_activity_date": 1, field: 1})
    if not user_doc or user_doc.get("star_activity_date") != today_str:
        await users_catcher_col.update_one(
            {"user_id": user_id},
            {"$set": {"star_activity_date": today_str, "star_spent_today": 0.0, "star_bought_today": 0.0}},
            upsert=True
        )
        before = 0.0
    else:
        before = user_doc.get(field, 0.0)
    updated = await users_catcher_col.find_one_and_update(
        {"user_id": user_id}, {"$inc": {field: amount}}, return_document=ReturnDocument.AFTER
    )
    after = updated.get(field, before + amount) if updated else before + amount
    if before < PREMIUM_AUTO_STAR_THRESHOLD <= after:
        return await grant_premium_days(user_id, PREMIUM_AUTO_GRANT_DAYS)
    return None

# ==========================================
async def execute_star_shop_purchase(buyer_id, char_id):
    """⭐ OWNER SHOP — core purchase logic shared by the /buy [char id] command and the
    "🛒 Buy" button inside the /show gallery. Any character in the database can be bought
    directly (a fresh copy, independent of catching) at its fixed rarity Star price; the
    Star spent goes straight to the Owner's balance, and every purchase is logged for
    /buylist. Capped at DAILY_BUY_LIMIT/day and LIFETIME_BUY_PER_CHAR_LIMIT copies of the
    same character ever, per player — PLUS Rarity No.1-3 (SWEETIE/BLOSSOM/FLUFFY) share a combined
    TOP_RARITY_WEEKLY_BUY_LIMIT across all three tiers together, per rolling
    TOP_RARITY_WEEK_SECONDS window, PLUS a brand new character can't be bought at all for its
    first NEW_CARD_PROTECTION_SECONDS (spawn-only during that window) (Owner is exempt from
    every cap here). Returns (ok: bool, message_html: str)."""
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        return False, "❌ <b>ဒီ Character ID ကို ရှာမတွေ့ပါ။</b>"
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    now = time.time()
    char_tier = char_doc.get("rarity_tier")
    # 🚫 SOLD OUT — owner has temporarily disabled Owner Shop purchases for this tier via
    # /buytoggle. Catching it from a live spawn is unaffected; only the direct buy is blocked.
    if buyer_id != OWNER_ID and char_tier in _cached_disabled_buy_tiers:
        return False, (
            f"🚫 <b>{RARITY_EMOJI.get(char_tier, '')} {char_tier} ကို Owner Shop ကနေ "
            f"ခဏပိတ်ထားပါတယ် — အရောင်းကုန်နေပါတယ်။</b>\n"
            f"🎯 <i>Spawn ကနေပဲ ဖမ်းလို့ရပါမယ်။</i>\n"
            f"☎️ <a href='{SOLD_OUT_CONTACT_LINK}'>ဒီမှာနှိပ်ပြီး Owner ကို Reply လုပ်ကာ ဝယ်ယူနိုင်ပါတယ်</a>"
        )
    # 🔒 NEW CARD PROTECTION — block outright Owner Shop purchase for the first
    # NEW_CARD_PROTECTION_SECONDS after /addchar. Owner is exempt (same as every other cap
    # below) so they can still test-buy their own newly added character immediately.
    if buyer_id != OWNER_ID:
        card_age = now - char_doc.get("created_at", 0)
        if card_age < NEW_CARD_PROTECTION_SECONDS:
            remaining = NEW_CARD_PROTECTION_SECONDS - card_age
            hrs, rem_secs = divmod(int(remaining), 3600)
            mins = rem_secs // 60
            return False, (
                f"🔒 <b>ဒီကတ်က အသစ်ထည့်ထားတာဖြစ်လို့ ပထမ 24 နာရီအတွင်း Owner Shop ကနေ "
                f"<code>/buy</code> နဲ့ မဝယ်ရသေးပါဘူး။</b>\n"
                f"🎯 ဒီကတ်ကို Spawn ကနေပဲ ဖမ်းလို့ရပါမယ်။\n"
                f"⏳ <b>ကျန်ချိန်:</b> <code>{hrs}h {mins}m</code>"
            )
    if buyer_id != OWNER_ID:
        limit_doc = await users_catcher_col.find_one(
            {"user_id": buyer_id},
            {"buy_date": 1, "daily_buy_count": 1, "lifetime_char_buys": 1, "top_rarity_week_start": 1, "top_rarity_buys_this_week": 1}
        )
        daily_count = (limit_doc or {}).get("daily_buy_count", 0) if limit_doc and limit_doc.get("buy_date") == today_str else 0
        if daily_count >= DAILY_BUY_LIMIT:
            return False, f"❌ <b>ယနေ့အတွက် Owner Shop ဝယ်ယူခွင့် ပြည့်သွားပါပြီ။</b> <i>(တစ်ရက်လျှင် {DAILY_BUY_LIMIT} ကြိမ်သာ ဝယ်လို့ရပါတယ် — မနက်ဖြန် ပြန်လာပါ)</i>"
        lifetime_count = ((limit_doc or {}).get("lifetime_char_buys") or {}).get(char_id, 0)
        if lifetime_count >= LIFETIME_BUY_PER_CHAR_LIMIT:
            return False, f"❌ <b>ဒီ Character ကို Owner Shop ကနေ တစ်သက်တာအတွက် {LIFETIME_BUY_PER_CHAR_LIMIT} ကြိမ်အထိပဲ ဝယ်လို့ရပါတယ် — ပြည့်သွားပါပြီ။</b>"
        if char_tier in TOP_RARITY_WEEKLY_TIERS:
            week_start = (limit_doc or {}).get("top_rarity_week_start", 0)
            week_count = (limit_doc or {}).get("top_rarity_buys_this_week", 0)
            if now - week_start >= TOP_RARITY_WEEK_SECONDS:
                week_count = 0  # rolling week has elapsed — fresh allowance
            if week_count >= TOP_RARITY_WEEKLY_BUY_LIMIT:
                reset_at = datetime.fromtimestamp(week_start + TOP_RARITY_WEEK_SECONDS, TZ).strftime("%Y-%m-%d %H:%M")
                return False, (
                    f"❌ <b>🍯🌸☁️ Sweetie/Blossom/Fluffy ကို တစ်ပတ်လျှင် "
                    f"{TOP_RARITY_WEEKLY_BUY_LIMIT} ကတ် ပေါင်းစပ်၍သာ Owner Shop ကနေ ဝယ်နိုင်ပါတယ် — ပြည့်သွားပါပြီ။</b>\n"
                    f"⏳ <i>{reset_at} မှ ပြန်ဝယ်နိုင်ပါမယ်။</i>"
                )
    price = star_price_for_char(char_doc)
    if not await try_deduct_star(buyer_id, price):
        buyer_doc = await users_catcher_col.find_one({"user_id": buyer_id})
        have = buyer_doc.get("star_balance", 0) if buyer_doc else 0
        return False, (
            f"❌ <b>Star မလုံလောက်ပါ။</b>\n"
            f"လိုအပ်: <code>{price}⭐</code> | လက်ရှိရှိ: <code>{format_star_plain(have)}</code>\n"
            f"💡 <code>/buystar [Star amount]</code> ဖြင့် Star ဝယ်နိုင်ပါတယ်။"
        )
    await users_catcher_col.update_one(
        {"user_id": buyer_id},
        {"$inc": {"total_caught": 1, "total_buys": 1},  # total_buys feeds Squad Points
         "$push": {"harem": {"char_id": char_id, "caught_date": time.time(), "rarity": char_doc.get("rarity", "Unknown"), "status": "vault"}}},
        upsert=True
    )
    premium_note = ""
    if buyer_id != OWNER_ID:
        # Roll the daily buy counter over first if it's a new day, then increment both it and
        # the lifetime per-character counter.
        await users_catcher_col.update_one(
            {"user_id": buyer_id, "buy_date": {"$ne": today_str}},
            {"$set": {"buy_date": today_str, "daily_buy_count": 0}}
        )
        await users_catcher_col.update_one(
            {"user_id": buyer_id},
            {"$inc": {"daily_buy_count": 1, f"lifetime_char_buys.{char_id}": 1}}
        )
        if char_tier in TOP_RARITY_WEEKLY_TIERS:
            # Roll the weekly window over first if it has elapsed, then increment.
            await users_catcher_col.update_one(
                {"user_id": buyer_id, "$or": [
                    {"top_rarity_week_start": {"$exists": False}},
                    {"top_rarity_week_start": {"$lte": now - TOP_RARITY_WEEK_SECONDS}}
                ]},
                {"$set": {"top_rarity_week_start": now, "top_rarity_buys_this_week": 0}}
            )
            await users_catcher_col.update_one(
                {"user_id": buyer_id},
                {"$inc": {"top_rarity_buys_this_week": 1}}
            )
        newly_premium_until = await _track_star_activity_and_maybe_grant_premium(buyer_id, "spent", price)
        if newly_premium_until:
            premium_note = f"\n\n👑 <b>⭐ သုံးစွဲမှု များပြားလို့ Bot Premium User {PREMIUM_AUTO_GRANT_DAYS}ရက် အပိုရရှိပါပြီ!</b>"
    # Owner owns every Star that gets paid for a shop purchase.
    await users_catcher_col.update_one({"user_id": OWNER_ID}, {"$inc": {"star_balance": price}}, upsert=True)
    await star_purchase_log_col.insert_one({
        "buyer_id": buyer_id, "char_id": char_id, "char_name": char_doc.get("name", "?"),
        "rarity": char_doc.get("rarity", "Unknown"), "stars_paid": price, "timestamp": time.time()
    })
    return True, (
        f"🎉 <b>ဝယ်ယူမှု အောင်မြင်ပါတယ်!</b>\n"
        f""
        f"✨ <b>Name:</b> <code>{escape_html(char_doc.get('name',''))}</code>\n"
        f"🆔 <b>ID:</b> <code>{display_char_id(char_id)}</code>\n"
        f"{char_doc.get('rarity','')}\n"
        f"💸 <b>ပေးချေ:</b> <code>{price}⭐</code>"
        f"\n"
        f"<code>/harem</code> <i>ဖြင့် ကြည့်နိုင်ပါတယ်။</i>"
        f"{premium_note}"
    )

# ---- /buytoggle: owner switches a rarity tier's Owner Shop purchase on/off ("sold out").
# Blocks BOTH /buy [char_id] and the /show gallery's 🛒 Buy button for that tier — catching it
# from a live spawn is never affected. Bare /buytoggle shows current status of all 4 tiers. ----
def _buytoggle_status_text():
    lines = ["🛍️ <b>Owner Shop — Rarity On/Off Status</b>\n"]
    for tier in RARITY_TIERS:
        num = RARITY_TIER_TO_NUM[tier]
        emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
        state = "🚫 <b>ပိတ်ထား</b> (Sold out)" if tier in _cached_disabled_buy_tiers else "✅ <b>ဖွင့်ထား</b>"
        lines.append(f"No.{num} {emoji} {tier} — {state}")
    lines.append("\n<b>Usage:</b> <code>/buytoggle no1</code> <i>(No.1..No.4 တစ်ခုချင်းစီကို ပိတ်/ဖွင့် Toggle)</i>")
    return "\n".join(lines)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buytoggle(?:@\w+)?(?:\s+(?:no)?([1-4]))?$', 'bot1')))
async def buy_tier_toggle_handler(event):
    if event.sender_id != OWNER_ID: return
    global _cached_disabled_buy_tiers
    arg = event.pattern_match.group(1)
    if not arg:
        return await event.reply(_buytoggle_status_text(), parse_mode='html')
    tier = RARITY_TIERS[int(arg) - 1]
    if tier in _cached_disabled_buy_tiers:
        _cached_disabled_buy_tiers.discard(tier)
        action = "✅ <b>ပြန်ဖွင့်လိုက်ပါပြီ</b> — ဝယ်လို့ရပါပြီ"
    else:
        _cached_disabled_buy_tiers.add(tier)
        action = "🚫 <b>ပိတ်လိုက်ပါပြီ</b> — အရောင်းကုန် ဖြစ်သွားပါပြီ"
    await bot_settings_col.update_one(
        {"_id": "disabled_buy_tiers"},
        {"$set": {"tiers": sorted(_cached_disabled_buy_tiers)}},
        upsert=True
    )
    emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
    await event.reply(
        f"{emoji} <b>{tier}</b> (No.{arg}) — {action}\n\n" + _buytoggle_status_text(),
        parse_mode='html'
    )

# ==========================================
# 🏷️ /sell [char_id] — OWNER BUYBACK ONLY. Player-to-player card trading has been disabled
# entirely — the Owner is now the only counterparty. The bot proposes a randomized offer
# between SELL_OFFER_MIN_MULT and SELL_OFFER_MAX_MULT of that character's fixed Owner Shop
# price (star_price_for_char) — the player can never name their own price — and nothing
# changes hands until the player confirms with an inline button. Identical flow whether run
# in a group chat or in the bot's DM.
# ==========================================
SELL_OFFER_MIN_MULT = 0.05
SELL_OFFER_MAX_MULT = 0.35
# 🩹 CHANGED (per owner request): this used to randomize between 10% and 100% of the FULL
# Owner Shop buy price — up to a full refund just for selling a card back, which handed out
# way more Stars than intended and made buy→sell-back loops attractive. Now 5%–35%, keeping a
# healthy spread between what a card costs to buy and what it's worth selling back.
SELL_OFFER_TIMEOUT = 300  # seconds an offer stays open before it silently expires

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]sell(?:@\w+)?$', 'bot1')))
async def sell_bare_usage_handler(event):
    await event.reply(
        "📌 <b>Usage:</b> <code>/sell [CharID]</code>\n"
        "<i>Example:</i> <code>/sell 1234</code>\n"
        "Owner ကနေ ⭐ Star ဖြင့် ပြန်ဝယ်ပေးပါမယ် — စျေးနှုန်းကို Owner ကသာ ကမ်းလှမ်းပါမယ်။",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]sell(?:@\w+)?\s+([a-zA-Z0-9_]+)\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def sell_legacy_price_handler(event):
    """Catches the OLD '/sell [char_id] [price]' syntax so people typing it out of habit get
    a clear explanation instead of silence — manual pricing/P2P listings no longer exist."""
    await event.reply(
        "⚠️ <b>Card ရောင်းစျေးကို ကိုယ်တိုင်သတ်မှတ်လို့ မရတော့ပါ။</b>\n"
        "📌 <code>/sell [CharID]</code> ဟုသာ ရိုက်ပါ — Owner ကနေ ကမ်းလှမ်းငွေကို အလိုအလျောက် ပြသပေးပါမယ်။",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]sell(?:@\w+)?\s+([a-zA-Z0-9_]+)$', 'bot1')))
async def sell_offer_handler(event):
    user_id = event.sender_id
    char_id = normalize_char_id_input(event.pattern_match.group(1))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    user_harem = user_doc.get("harem", []) if user_doc else []
    char_item = next((x for x in user_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") != "market"), None)
    if not char_item: return await event.reply(f"❌ <b>You don’t have this card available.</b>", parse_mode='html')
    char_data = await characters_base_col.find_one({"char_id": char_id})
    if not char_data: return await event.reply(f"❌ <b>Character ID not found.</b>", parse_mode='html')
    base_price = star_price_for_char(char_data)
    offer = round(random.uniform(SELL_OFFER_MIN_MULT, SELL_OFFER_MAX_MULT) * base_price, 2)
    sell_id = f"S{random.randint(100000, 999999)}"
    pending_sell_offers[sell_id] = {
        "expiry": time.time() + SELL_OFFER_TIMEOUT,
        "seller_id": user_id, "char_id": char_id, "char_name": char_data.get("name", "?"),
        "offer": offer,
    }
    buttons = [[
        Button.inline("✅ ရောင်းမယ်", data=f"sellconf_{sell_id}"),
        Button.inline("❌ မရောင်းသေးဘူး", data=f"sellcanc_{sell_id}")
    ]]
    await event.reply(
        f"🏷️ <b>OWNER OFFER</b>\n"
        f""
        f"👤 <b>Card:</b> <code>{escape_html(char_data.get('name','?'))}</code> [<code>{display_char_id(char_id)}</code>]\n"
        f"☎️ <b>ကမ်းလှမ်းငွေ:</b> <code>{format_star_plain(offer)}</code>"
        f"\n"
        f"<i>ဒီစျေးနှုန်းနဲ့ ရောင်းမလား?</i>",
        parse_mode='html', buttons=buttons
    )

@bot1.on(events.CallbackQuery(pattern=r'^sellconf_(\S+)$'))
async def sell_offer_confirm_callback(event):
    sell_id = event.pattern_match.group(1)
    if isinstance(sell_id, bytes): sell_id = sell_id.decode('utf-8')
    offer_data = pending_sell_offers.get(sell_id)
    if not offer_data or time.time() > offer_data["expiry"]:
        pending_sell_offers.pop(sell_id, None)
        return await event.answer("⏳ This offer has expired. Run /sell again.", alert=True)
    if event.sender_id != offer_data["seller_id"]:
        return await event.answer("⚠️ This isn't your offer!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    seller_id, char_id, offer = offer_data["seller_id"], offer_data["char_id"], offer_data["offer"]
    user_doc = await users_catcher_col.find_one({"user_id": seller_id})
    user_harem = user_doc.get("harem", []) if user_doc else []
    char_item = next((x for x in user_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") != "market"), None)
    if not char_item:
        pending_sell_offers.pop(sell_id, None)
        await event.answer("❌ Card no longer available.", alert=True)
        return await event.edit("❌ <b>ဒီကဒ်ကို ရှာမတွေ့တော့ပါ။</b>", parse_mode='html', buttons=None)
    if not await try_deduct_star(OWNER_ID, offer):
        # Owner's Star reserve can't cover this offer right now — leave the player's card
        # untouched and let them retry later rather than pay out Star from nowhere.
        pending_sell_offers.pop(sell_id, None)
        await event.answer("❌ Offer unavailable right now.", alert=True)
        return await event.edit("❌ <b>ယခုအချိန် Owner ဆီတွင် Star မလုံလောက်သေးပါ။ ခဏနေမှ ပြန်ကြိုးစားပါ။</b>", parse_mode='html', buttons=None)
    # 🩹 FIX: same atomic $pull-based removal as marketplace-buy/trade — see
    # remove_one_harem_copy for why the old find_one → .remove() → $set-the-whole-array-back
    # pattern was a lost-update race risk.
    await remove_one_harem_copy(seller_id, char_id, char_item.get("status", "vault"))
    await users_catcher_col.update_one({"user_id": seller_id}, {"$inc": {"star_balance": offer}}, upsert=True)
    seller_doc_after = await users_catcher_col.find_one({"user_id": seller_id}, {"harem": 1})
    await clear_stale_favorite(seller_id, char_id, (seller_doc_after or {}).get("harem", []))
    await star_sell_log_col.insert_one({
        "seller_id": seller_id, "char_id": char_id, "char_name": offer_data["char_name"],
        "stars_paid": offer, "timestamp": time.time()
    })
    pending_sell_offers.pop(sell_id, None)
    await event.answer("✅ Sold!", alert=True)
    await event.edit(
        f"✅ <b>ရောင်းချမှု အောင်မြင်ပါတယ်!</b>\n"
        f""
        f"👤 <b>Card:</b> <code>{escape_html(offer_data['char_name'])}</code>\n"
        f"⭐ <b>ရရှိ:</b> <code>{format_star_plain(offer)}</code>"
        f"",
        parse_mode='html', buttons=None
    )

@bot1.on(events.CallbackQuery(pattern=r'^sellcanc_(\S+)$'))
async def sell_offer_cancel_callback(event):
    sell_id = event.pattern_match.group(1)
    if isinstance(sell_id, bytes): sell_id = sell_id.decode('utf-8')
    offer_data = pending_sell_offers.get(sell_id)
    if offer_data and event.sender_id != offer_data["seller_id"]:
        return await event.answer("⚠️ This isn't your offer!", alert=True)
    pending_sell_offers.pop(sell_id, None)
    await event.answer("👍 Kept.")
    await event.edit("🙅 <b>ရောင်းခြင်းကို ပယ်ဖျက်လိုက်ပါပြီ — ကဒ်ကို ဆက်ထားနိုင်ပါတယ်။</b>", parse_mode='html', buttons=None)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buy(?:@\w+)?$', 'bot1')))
async def buy_bare_usage_handler(event):
    user_id = event.sender_id
    buttons = [
        [Button.inline("🎴 ကဒ်များ", data=f"buyhub_cards_{user_id}")],
        [Button.inline("⭐ ကဒ်ဝယ်ဖို့ Star ဝယ်မယ်", data=f"buyhub_star_{user_id}")],
        [Button.inline("👑 Premium ဝယ်မယ်", data=f"buyhub_premium_{user_id}")],
    ]
    await event.reply(
        "🛍️ <b>ဘာကိုဝယ်ချင်ပါသလဲ?</b>",
        parse_mode='html',
        buttons=buttons
    )

@bot1.on(events.CallbackQuery(pattern=r'^buyhub_(cards|star|premium)_(\d+)$'))
async def buy_hub_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes): action = action.decode('utf-8')
    owner_uid = int(event.pattern_match.group(2))
    if event.sender_id != owner_uid:
        return await event.answer("⚠️ This isn't your menu!", alert=True)
    await event.answer()
    if action == "cards":
        await event.edit(
            "🎴 <b>ကဒ်များ ဝယ်ရန်</b>\n"
            "📩 Bot DM မှာ <code>/show</code> ကိုနှိပ်ပြီး Rarity ရွေးပြီး ကဒ်တွေ့ကြည့်နိုင်ပါတယ်။\n"
            "ကြိုက်တဲ့ကဒ်တွေ့ရင် <code>/buy [char id]</code> နဲ့ Star ဖြင့်ဝယ်နိုင်ပါတယ်။",
            parse_mode='html', buttons=None
        )
    elif action == "premium":
        text, buttons = render_premium_tiers_text_and_buttons(owner_uid)
        await event.edit(text, parse_mode='html', buttons=buttons)
    else:
        market = await get_or_create_star_market()
        await event.edit(
            f"⭐ <b>Star ဝယ်ရန်</b>\n"
            f"💱 <b>လက်ရှိစျေးနှုန်း:</b> <code>1⭐ = {market['price']:,.0f} USD</code>\n"
            f"📌 <code>/buystar [Star amount]</code> ဟုရိုက်ပြီး Star ဝယ်နိုင်ပါတယ်။\n"
            f"<i>Example:</i> <code>/buystar 1</code>",
            parse_mode='html', buttons=None
        )

@bot1.on(events.CallbackQuery(pattern=r'^shopbuy_([a-zA-Z0-9_]+)$'))
async def shop_buy_gallery_callback(event):
    char_id = event.pattern_match.group(1)
    if isinstance(char_id, bytes): char_id = char_id.decode('utf-8')
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    ok, msg = await execute_star_shop_purchase(event.sender_id, char_id)
    await event.answer("🎉 Purchased!" if ok else "❌ Failed", alert=True)
    await bot1.send_message(event.sender_id if event.is_private else event.chat_id, msg, parse_mode='html')

# ---- /buy [char id] — Owner Shop purchase: buy a fresh copy of any character directly with
# ⭐ Star, priced by rarity (see star_price_for_char). ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buy(?:@\w+)?\s+([a-zA-Z0-9_]+)$', 'bot1')))
async def buy_shop_handler(event):
    char_id = normalize_char_id_input(event.pattern_match.group(1))
    ok, msg = await execute_star_shop_purchase(event.sender_id, char_id)
    await event.reply(msg, parse_mode='html')

# ---- /buy [char id] [seller id] — DISABLED. Peer-to-peer card trading no longer exists
# (see /sell, which is now an Owner-only buyback); this old pattern is kept solely so anyone
# still typing it out of habit gets a clear explanation instead of silence. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buy(?:@\w+)?\s+([a-zA-Z0-9_]+)\s+(\d+)$', 'bot1')))
async def buy_market_handler(event):
    await event.reply(
        "⚠️ <b>Player အချင်းချင်း ကဒ်ရောင်းဝယ်ခြင်းကို ရပ်ဆိုင်းလိုက်ပါပြီ။</b>\n"
        "📌 <code>/buy [CharID]</code> ဖြင့် Owner Shop ကနေ တိုက်ရိုက်ဝယ်ပါ။",
        parse_mode='html'
    )

# ==========================================
# 👑 /buypremium — buy Bot Premium User status with ⭐ Star, across 5 duration tiers.
# Premium can ALSO be earned automatically (see _track_star_activity_and_maybe_grant_premium)
# by spending/buying PREMIUM_AUTO_STAR_THRESHOLD⭐ in a single day.
# ==========================================
def _premium_tier_label(months):
    return "1 နှစ်" if months == 12 else f"{months} လ"

def render_premium_tiers_text_and_buttons(user_id):
    lines = [f"• {_premium_tier_label(m)} — <code>{p}⭐</code>" for m, p, _ in PREMIUM_TIERS]
    buttons = [[Button.inline(f"👑 {_premium_tier_label(m)} — {p}⭐", data=f"prembuy_{m}_{user_id}")] for m, p, _ in PREMIUM_TIERS]
    text = (
        f"👑 <b>BOT PREMIUM USER</b>\n"
        f"{chr(10).join(lines)}\n"
        f"✨ <b>အကျိုးခံစားခွင့်များ:</b>\n"
        f"• 🕒 Spam Cooldown <code>8 min → 3 min</code>\n"
        f"• 🎯 Daily Catch <code>22 → 25</code> ကြိမ်\n"
        f"• 🎁 ဝယ်ဝယ်ချင်း 🎀 <b>Kawaii</b> ကဒ် <code>{PREMIUM_PURCHASE_BONUS_COUNT}</code> ကဒ် အခမဲ့\n"
        f"• ⭐ <b>နေ့စဉ်</b> Star <code>{PREMIUM_DAILY_GIFT_MIN}~{PREMIUM_DAILY_GIFT_MAX}⭐</code> Random လက်ဆောင်\n"
        f"• 🧠 Quiz Star ဆု ပိုများ\n"
        f"• 👑 Premium Badge — <code>/harem</code>, <code>/profile</code>, <code>/fuck</code> တွေမှာ ပြပေးမယ်\n"
        f"👇 <i>သက်တမ်း ရွေးချယ်ပါ</i>"
    )
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buypremium(?:@\w+)?$', 'bot1')))
async def buypremium_handler(event):
    user_id = event.sender_id
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    text, buttons = render_premium_tiers_text_and_buttons(user_id)
    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^prembuy_(\d+)_(\d+)$'))
async def premium_purchase_callback(event):
    months = int(event.pattern_match.group(1))
    owner_uid = int(event.pattern_match.group(2))
    if event.sender_id != owner_uid:
        return await event.answer("⚠️ This isn't your menu!", alert=True)
    tier = next((t for t in PREMIUM_TIERS if t[0] == months), None)
    if not tier:
        return await event.answer("❌ Invalid tier.", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    _, price, days = tier
    if not await try_deduct_star(owner_uid, price):
        buyer_doc = await users_catcher_col.find_one({"user_id": owner_uid})
        have = buyer_doc.get("star_balance", 0) if buyer_doc else 0
        return await event.answer(f"❌ Star မလုံလောက်ပါ။ လိုအပ်: {price}⭐ | ရှိ: {format_star_plain(have)}", alert=True)
    new_until = await grant_premium_days(owner_uid, days)
    # Owner receives the Star paid for Premium too, same as every other Star sink in this economy.
    await users_catcher_col.update_one({"user_id": OWNER_ID}, {"$inc": {"star_balance": price}}, upsert=True)
    
    expiry_str = datetime.fromtimestamp(new_until, TZ).strftime("%Y-%m-%d %H:%M")
    await event.answer("👑 Premium Activated!", alert=True)
    await event.edit(
        f"👑 <b>BOT PREMIUM ACTIVATED!</b>\n"
        f""
        f"⏳ <b>သက်တမ်း:</b> <code>{expiry_str}</code> အထိ"
        f"\n"
        f"🎉 <i>Premium အကျိုးခံစားခွင့်များ ချက်ချင်း စတင်အသုံးပြုနိုင်ပါပြီ!</i>",
        parse_mode='html', buttons=None
    )

# ==========================================
# 🎁 PREMIUM DAILY STAR GIFT — Guard Bot's job has been merged into bot1. Runs across every
# group bot1 is in: once per day, the FIRST /collect attempt or @mention a Premium user sends,
# they're offered a small random ⭐ Star gift right there. Public and visible on purpose — this
# is what makes Premium's perks obvious to everyone else watching, not just the Premium user.
# ==========================================
PREMIUM_DAILY_GIFT_MIN = 100  # ⭐
PREMIUM_DAILY_GIFT_MAX = 200  # ⭐

async def _maybe_offer_premium_daily_gift(event, user_id):
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"premium_until": 1, "premium_gift_date": 1})
    if not is_premium_active(user_doc):
        return
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    if user_doc.get("premium_gift_date") == today_str:
        return  # already offered today
    # Atomic claim on today's slot — a burst of qualifying messages in the same moment can't
    # send this twice; only the update that actually flips premium_gift_date wins.
    claimed = await users_catcher_col.find_one_and_update(
        {"user_id": user_id, "premium_gift_date": {"$ne": today_str}},
        {"$set": {"premium_gift_date": today_str}}
    )
    if not claimed:
        return
    star_amount = round(random.uniform(PREMIUM_DAILY_GIFT_MIN, PREMIUM_DAILY_GIFT_MAX), 2)
    gift_id = f"G{random.randint(100000, 999999)}"
    pending_premium_gifts[gift_id] = {"expiry": time.time() + 86400, "user_id": user_id, "star_amount": star_amount}
    buttons = [[
        Button.inline("✅ ယူမယ်", data=f"premgift_take_{gift_id}"),
        Button.inline("❌ မယူဘူး", data=f"premgift_skip_{gift_id}")
    ]]
    try:
        await event.reply(
            f"👑 <b>ရော့! မင်းက Bot Premium ဝယ်ထားတဲ့ User မို့ Bot Creator က မင်းကို နေ့တိုင်း Star ပေးခိုင်းထားတယ်</b>\n"
            f"⭐ <b>ဒီနေ့ မင်းရမှာ:</b> <code>{star_amount}⭐</code>",
            parse_mode='html', buttons=buttons
        )
    except Exception:
        pass

async def premium_daily_gift_trigger_handler(event):
    if event.is_private: return
    # Guard Bot (bot3) has been merged into bot1 — always use the original bot1 trigger:
    # any group, only on a collect attempt or a direct mention (so it doesn't fire on
    # every single message bot1 ever sees).
    text = event.raw_text or ""
    if not text: return
    is_collect_attempt = bool(re.match(r'^[/.](?:collect|morgan)\b', text, re.IGNORECASE))
    mentions_bot = bool(BOT1_USERNAME) and f"@{BOT1_USERNAME}" in text.lower()
    if not (is_collect_attempt or mentions_bot):
        return
    try:
        await _maybe_offer_premium_daily_gift(event, event.sender_id)
    except Exception as e:
        print(f"Premium daily gift trigger error: {e}")

async def premium_gift_take_callback(event):
    gift_id = event.pattern_match.group(1)
    if isinstance(gift_id, bytes): gift_id = gift_id.decode('utf-8')
    gift = pending_premium_gifts.get(gift_id)
    if not gift or time.time() > gift["expiry"]:
        pending_premium_gifts.pop(gift_id, None)
        return await event.answer("⏳ ဒီ Offer သက်တမ်းကုန်သွားပါပြီ။", alert=True)
    if event.sender_id != gift["user_id"]:
        return await event.answer("⚠️ ဒါ မင်းအတွက် မဟုတ်ဘူး!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Processing...", alert=False)
    await users_catcher_col.update_one({"user_id": gift["user_id"]}, {"$inc": {"star_balance": gift["star_amount"]}}, upsert=True)
    pending_premium_gifts.pop(gift_id, None)
    await event.answer("🎉 Star ရပါပြီ!", alert=True)
    await event.edit(f"✅ <b>+{gift['star_amount']}⭐ ရရှိပါပြီ! 👑</b>", parse_mode='html', buttons=None)

async def premium_gift_skip_callback(event):
    gift_id = event.pattern_match.group(1)
    if isinstance(gift_id, bytes): gift_id = gift_id.decode('utf-8')
    gift = pending_premium_gifts.get(gift_id)
    if gift and event.sender_id != gift["user_id"]:
        return await event.answer("⚠️ ဒါ မင်းအတွက် မဟုတ်ဘူး!", alert=True)
    pending_premium_gifts.pop(gift_id, None)
    await event.answer("👍 OK")
    await event.edit("🙅 <b>ငြင်းလိုက်ပါပြီ။</b>", parse_mode='html', buttons=None)

# Guard Bot (bot3) has been merged into bot1 — this now always registers on bot1.
_premium_gift_bot = bot1
_premium_gift_bot.on(events.NewMessage)(premium_daily_gift_trigger_handler)
_premium_gift_bot.on(events.CallbackQuery(pattern=r'^premgift_take_(\S+)$'))(premium_gift_take_callback)
_premium_gift_bot.on(events.CallbackQuery(pattern=r'^premgift_skip_(\S+)$'))(premium_gift_skip_callback)

# ==========================================
# 🧾 /buylist — OWNER ONLY: history of every ⭐ Owner Shop purchase (/buy [char id])
# ==========================================
BUYLIST_PAGE_SIZE = 10

async def render_buylist_page(page):
    skip = page * BUYLIST_PAGE_SIZE
    total = await star_purchase_log_col.count_documents({})
    rows = await star_purchase_log_col.find({}).sort("timestamp", -1).skip(skip).limit(BUYLIST_PAGE_SIZE).to_list(length=BUYLIST_PAGE_SIZE)
    total_pages = max(1, (total + BUYLIST_PAGE_SIZE - 1) // BUYLIST_PAGE_SIZE)
    if not rows:
        body = "<i>မှတ်တမ်းမရှိသေးပါ။</i>"
    else:
        lines = []
        for r in rows:
            dt = datetime.fromtimestamp(r["timestamp"], TZ).strftime("%Y-%m-%d %H:%M")
            lines.append(
                f"👤 <code>{r['buyer_id']}</code> — <code>{escape_html(r.get('char_name','?'))}</code> "
                f"[<code>{display_char_id(r['char_id'])}</code>] — <code>{r['stars_paid']}⭐</code> — <i>{dt}</i>"
            )
        body = "\n".join(lines)
    text = f"🧾 <b>SHOP BUY HISTORY</b> <i>({min(page + 1, total_pages)}/{total_pages})</i>\n{body}\n💰 <b>Total sales:</b> <code>{total}</code>"
    buttons = []
    nav = []
    if page > 0:
        nav.append(Button.inline("⬅️ Prev", data=f"buylistpg_{page - 1}"))
    if skip + BUYLIST_PAGE_SIZE < total:
        nav.append(Button.inline("➡️ Next", data=f"buylistpg_{page + 1}"))
    if nav:
        buttons.append(nav)
    return text, (buttons or None)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buylist(?:@\w+)?$', 'bot1')))
async def buylist_handler(event):
    if event.sender_id != OWNER_ID: return
    text, buttons = await render_buylist_page(0)
    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^buylistpg_(\d+)$'))
async def buylist_page_callback(event):
    if event.sender_id != OWNER_ID:
        return await event.answer("⚠️ Owner only.", alert=True)
    page = int(event.pattern_match.group(1))
    text, buttons = await render_buylist_page(page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

# ---- /clearbuylist — OWNER ONLY: purge the /buylist history log (star_purchase_log_col)
# whenever it's grown too big. This is just a rolling audit log, viewed briefly and forgotten —
# it doesn't affect wallet/star balances, owned cards, or anything a player can see. Preview
# shows the record count first; add "confirm" to actually delete. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]clearbuylist(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def clear_buylist_handler(event):
    if event.sender_id != OWNER_ID: return
    confirm = bool(event.pattern_match.group(1))
    total = await star_purchase_log_col.count_documents({})
    if not total:
        return await event.reply("📭 <b>/buylist History က အလွတ်ပါ — ဖျက်စရာ မရှိပါ။</b>", parse_mode='html')
    if not confirm:
        return await event.reply(
            f"⚠️ <b>/buylist History (<code>{total:,}</code> records) ကို ဖျက်တော့မလား?</b>\n"
            f"<i>ဒါက Database ထဲက audit log ကိုပဲ ဖျက်တာပါ — player wallet balance/owned cards ဘာမှ မထိပါဘူး။</i>\n\n"
            f"အတည်ပြုရန် <code>/clearbuylist confirm</code> ကို ရိုက်ပါ။",
            parse_mode='html'
        )
    result = await star_purchase_log_col.delete_many({})
    await event.reply(
        f"🧹 <b>/buylist History ဖျက်ပြီးပါပြီ!</b>\n🗑️ <code>{result.deleted_count:,}</code> records ဖယ်ရှားလိုက်ပါပြီ။",
        parse_mode='html'
    )

# ==========================================
# 🧾 /starlist — OWNER ONLY: unified history of every ⭐ Star movement —
# Owner buybacks (/sell accepted offers) AND /buystar & /sellstar USD<->Star exchanges —
# newest first, with running totals for each.
# ==========================================
STARLIST_PAGE_SIZE = 10

async def render_starlist_page(page):
    skip = page * STARLIST_PAGE_SIZE
    total_cardsell = await star_sell_log_col.count_documents({})
    total_exchange = await star_exchange_log_col.count_documents({})
    total = total_cardsell + total_exchange
    total_pages = max(1, (total + STARLIST_PAGE_SIZE - 1) // STARLIST_PAGE_SIZE)

    pipeline = [
        {"$addFields": {"log_type": "card_sell"}},
        {"$unionWith": {"coll": "star_exchange_log", "pipeline": [{"$addFields": {"log_type": "$type"}}]}},
        {"$sort": {"timestamp": -1}},
        {"$skip": skip},
        {"$limit": STARLIST_PAGE_SIZE},
    ]
    rows = await star_sell_log_col.aggregate(pipeline).to_list(length=STARLIST_PAGE_SIZE)

    buyback_agg = await star_sell_log_col.aggregate([{"$group": {"_id": None, "s": {"$sum": "$stars_paid"}}}]).to_list(length=1)
    total_buyback_stars = buyback_agg[0]["s"] if buyback_agg else 0
    buy_agg = await star_exchange_log_col.aggregate([{"$match": {"type": "buy"}}, {"$group": {"_id": None, "s": {"$sum": "$star_amount"}, "m": {"$sum": "$mmk_amount"}}}]).to_list(length=1)
    total_bought_star, total_bought_mmk = (buy_agg[0]["s"], buy_agg[0]["m"]) if buy_agg else (0, 0)
    sell_agg = await star_exchange_log_col.aggregate([{"$match": {"type": "sell"}}, {"$group": {"_id": None, "s": {"$sum": "$star_amount"}, "m": {"$sum": "$mmk_amount"}}}]).to_list(length=1)
    total_sold_star, total_sold_mmk = (sell_agg[0]["s"], sell_agg[0]["m"]) if sell_agg else (0, 0)

    if not rows:
        body = "<i>မှတ်တမ်းမရှိသေးပါ။</i>"
    else:
        lines = []
        for r in rows:
            dt = datetime.fromtimestamp(r["timestamp"], TZ).strftime("%Y-%m-%d %H:%M")
            if r["log_type"] == "card_sell":
                lines.append(
                    f"🏷️ <code>{r['seller_id']}</code> — <code>{escape_html(r.get('char_name','?'))}</code> "
                    f"[<code>{display_char_id(r['char_id'])}</code>] — <code>{format_star_plain(r['stars_paid'])}</code> — <i>{dt}</i>"
                )
            elif r["log_type"] == "buy":
                lines.append(
                    f"⬆️ <code>{r['user_id']}</code> — bought <code>{format_star_plain(r['star_amount'])}</code> "
                    f"for <code>{r['mmk_amount']:,} USD</code> — <i>{dt}</i>"
                )
            else:
                lines.append(
                    f"⬇️ <code>{r['user_id']}</code> — sold <code>{format_star_plain(r['star_amount'])}</code> "
                    f"for <code>{r['mmk_amount']:,} USD</code> — <i>{dt}</i>"
                )
        body = "\n".join(lines)
    text = (
        f"🧾 <b>STAR ACTIVITY HISTORY</b> <i>({min(page + 1, total_pages)}/{total_pages})</i>\n"
        f"{body}\n"
        f"🔢 <b>Total entries:</b> <code>{total}</code>\n"
        f"🏷️ <b>Card buybacks paid:</b> <code>{format_star_plain(total_buyback_stars)}</code>\n"
        f"⬆️ <b>/buystar:</b> <code>{format_star_plain(total_bought_star)}</code> bought · <code>{total_bought_mmk:,.0f} USD</code> spent\n"
        f"⬇️ <b>/sellstar:</b> <code>{format_star_plain(total_sold_star)}</code> sold · <code>{total_sold_mmk:,.0f} USD</code> received"
    )
    buttons = []
    nav = []
    if page > 0:
        nav.append(Button.inline("⬅️ Prev", data=f"starlistpg_{page - 1}"))
    if skip + STARLIST_PAGE_SIZE < total:
        nav.append(Button.inline("➡️ Next", data=f"starlistpg_{page + 1}"))
    if nav:
        buttons.append(nav)
    return text, (buttons or None)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]starlist(?:@\w+)?$', 'bot1')))
async def starlist_handler(event):
    if event.sender_id != OWNER_ID: return
    text, buttons = await render_starlist_page(0)
    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^starlistpg_(\d+)$'))
async def starlist_page_callback(event):
    if event.sender_id != OWNER_ID:
        return await event.answer("⚠️ Owner only.", alert=True)
    page = int(event.pattern_match.group(1))
    text, buttons = await render_starlist_page(page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

# ---- /clearstarlist — OWNER ONLY: purge the /starlist history logs (both star_sell_log_col —
# card buybacks — AND star_exchange_log_col — /buystar & /sellstar — since /starlist displays
# them merged together). Same rolling-audit-log reasoning as /clearbuylist: viewed briefly,
# doesn't affect any player's actual star/wallet balance. Preview first; add "confirm" to
# actually delete. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]clearstarlist(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def clear_starlist_handler(event):
    if event.sender_id != OWNER_ID: return
    confirm = bool(event.pattern_match.group(1))
    total_sell = await star_sell_log_col.count_documents({})
    total_exchange = await star_exchange_log_col.count_documents({})
    total = total_sell + total_exchange
    if not total:
        return await event.reply("📭 <b>/starlist History က အလွတ်ပါ — ဖျက်စရာ မရှိပါ။</b>", parse_mode='html')
    if not confirm:
        return await event.reply(
            f"⚠️ <b>/starlist History ကို ဖျက်တော့မလား?</b>\n"
            f"🏷️ <b>Card buyback records:</b> <code>{total_sell:,}</code>\n"
            f"💱 <b>Star exchange records:</b> <code>{total_exchange:,}</code>\n"
            f"🧾 <b>Total:</b> <code>{total:,}</code>\n\n"
            f"<i>ဒါက Database ထဲက audit log ကိုပဲ ဖျက်တာပါ — player star/wallet balance ဘာမှ မထိပါဘူး။</i>\n\n"
            f"အတည်ပြုရန် <code>/clearstarlist confirm</code> ကို ရိုက်ပါ။",
            parse_mode='html'
        )
    r1 = await star_sell_log_col.delete_many({})
    r2 = await star_exchange_log_col.delete_many({})
    await event.reply(
        f"🧹 <b>/starlist History ဖျက်ပြီးပါပြီ!</b>\n🗑️ <code>{(r1.deleted_count + r2.deleted_count):,}</code> records ဖယ်ရှားလိုက်ပါပြီ။",
        parse_mode='html'
    )

# ==========================================
# ⭐ /buystar & /sellstar — USD <-> Star exchange, at a FIXED rate. Trading no longer moves
# the rate at all; it only ever changes when the Owner runs /setstarrate.
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]buystar(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def buy_star_handler(event):
    user_id = event.sender_id
    raw = event.pattern_match.group(1)
    market = await get_or_create_star_market()
    if not raw:
        return await event.reply(
            f"⭐ <b>Star ဝယ်ရန်</b>\n"
            f"💱 <b>နှုန်းထား:</b> <code>1⭐ = {market['price']:,.0f} USD</code>\n"
            f"📌 <b>Usage:</b> <code>/buystar [Star amount]</code>\n"
            f"<i>Example:</i> <code>/buystar 1</code>",
            parse_mode='html'
        )
    try:
        star_amount = float(raw)
    except ValueError:
        return await event.reply("❌ <b>Star ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    if star_amount <= 0:
        return await event.reply("❌ <b>Star ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    mmk_cost = round(star_amount * market["price"])
    if not await try_deduct_balance(user_id, mmk_cost):
        return await event.reply("❌ <b>USD Balance မလုံလောက်ပါ။</b>", parse_mode='html')
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"star_balance": star_amount}}, upsert=True)
    await star_exchange_log_col.insert_one({
        "user_id": user_id, "type": "buy", "star_amount": star_amount, "mmk_amount": mmk_cost,
        "rate": market["price"], "timestamp": time.time()
    })
    premium_note = ""
    newly_premium_until = await _track_star_activity_and_maybe_grant_premium(user_id, "bought", star_amount)
    if newly_premium_until:
        premium_note = f"\n\n👑 <b>⭐ ဝယ်ယူမှု များပြားလို့ Bot Premium User {PREMIUM_AUTO_GRANT_DAYS}ရက် အပိုရရှိပါပြီ!</b>"
    await event.reply(
        f"✅ <b>Star ဝယ်ယူမှု အောင်မြင်ပါတယ်!</b>\n"
        f""
        f"⭐ <b>ဝယ်ယူ:</b> <code>{format_star_plain(star_amount)}</code>\n"
        f"💸 <b>ပေးချေ:</b> <code>{mmk_cost:,} USD</code>\n"
        f"💱 <b>နှုန်းထား:</b> <code>1⭐ = {market['price']:,.0f} USD</code>"
        f""
        f"{premium_note}",
        parse_mode='html'
    )

# ==========================================
# ⭐ /sellstar — Owner: သတ်မှတ်ပုံသေ နှုန်းထားနဲ့ Star ရောင်းချခြင်း (၁ Star = ၂၅၀ USD)
# ==========================================
SELL_STAR_RATE = 250  # ဒီနေရာမှာ သင်သတ်မှတ်ချင်တဲ့ နှုန်းထားကို ပြောင်းပါ

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]sellstar(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def sell_star_handler(event):
    user_id = event.sender_id
    raw = event.pattern_match.group(1)
    
    if not raw:
        return await event.reply(
            f"⭐ <b>Star ရောင်းရန်</b>\n"
            f"💱 <b>နှုန်းထား:</b> <code>1⭐ = {SELL_STAR_RATE:,} USD</code> (ပုံသေ)\n"
            f"📌 <b>Usage:</b> <code>/sellstar [Star amount]</code>\n"
            f"<i>Example:</i> <code>/sellstar 1</code>",
            parse_mode='html'
        )
    
    try:
        star_amount = float(raw)
    except ValueError:
        return await event.reply("❌ <b>Star ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    
    if star_amount <= 0:
        return await event.reply("❌ <b>Star ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    
    if not await try_deduct_star(user_id, star_amount):
        return await event.reply("❌ <b>Star Balance မလုံလောက်ပါ။</b>", parse_mode='html')
    
    usd_gained = round(star_amount * SELL_STAR_RATE, 2)
    
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$inc": {"wallet_balance": usd_gained}},
        upsert=True
    )
    
    await star_exchange_log_col.insert_one({
        "user_id": user_id,
        "type": "sell",
        "star_amount": star_amount,
        "mmk_amount": usd_gained,
        "rate": SELL_STAR_RATE,
        "timestamp": time.time()
    })
    
    await event.reply(
        f"✅ <b>Star ရောင်းချမှု အောင်မြင်ပါတယ်!</b>\n"
        f""
        f"⭐ <b>ရောင်း:</b> <code>{format_star_plain(star_amount)}</code>\n"
        f"💸 <b>ရရှိ:</b> <code>{format_usd(usd_gained)}</code>\n"
        f"💱 <b>နှုန်းထား:</b> <code>1⭐ = {SELL_STAR_RATE:,} USD</code> (ပုံသေ)"
        f"",
        parse_mode='html'
    )
# ==========================================
# 🛠️ /setstarrate [USD] — OWNER ONLY: manually re-peg the ⭐ Star <-> USD exchange rate.
# This is the only way the rate ever changes now (defaults to 1⭐ = STAR_STARTING_PRICE at genesis).
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]setstarrate(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def set_star_rate_handler(event):
    if event.sender_id != OWNER_ID: return
    raw = event.pattern_match.group(1)
    market = await get_or_create_star_market()
    if not raw:
        return await event.reply(
            f"⭐ <b>Star Exchange Rate</b>\n"
            f"💱 <b>လက်ရှိနှုန်းထား:</b> <code>1⭐ = {market['price']:,.0f} USD</code>\n"
            f"📌 <b>Usage:</b> <code>/setstarrate [USD amount]</code>\n"
            f"<i>Example:</i> <code>/setstarrate 1000000</code>",
            parse_mode='html'
        )
    try:
        new_rate = float(raw)
    except ValueError:
        return await event.reply("❌ <b>USD ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    if new_rate <= 0:
        return await event.reply("❌ <b>USD ပမာဏ မှန်ကန်အောင် ရိုက်ပါ။</b>", parse_mode='html')
    old_price = market["price"]
    new_price = await _write_star_price(market, new_rate)
    await event.reply(
        f"✅ <b>Star Exchange Rate ကို ပြောင်းလိုက်ပါပြီ!</b>\n"
        f""
        f"↩️ <b>Old:</b> <code>1⭐ = {old_price:,.0f} USD</code>\n"
        f"➡️ <b>New:</b> <code>1⭐ = {new_price:,.0f} USD</code>"
        f"",
        parse_mode='html'
    )

# ==========================================
# 🏆 LEADERBOARDS
# ==========================================
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
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]balance(?:@\w+)?$', 'bot1')))
async def check_points_balance(event):
    user_id = event.sender_id
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    mention = await get_html_mention(event, user_id)

    text = (
        f"💰 <b>➤ {mention}'s Balance</b>\n"
        f""
        f"💵 <b>◈ US Dollars:</b> <code>{format_usd_compact(balance)}</code>\n"
        f"⭐ <b>☆ Stars:</b> <code>{format_star_plain(star_balance)}</code>"
        f""
    )

    # 🔹 ဒီမှာ ခလုတ်တွေကို ၂ တန်း ၂ လုံးစီ ခွဲထားတယ်
    buttons = [
        [
            Button.inline("🏪 စျေးဝယ်မယ်", data=f"buyhub_cards_{user_id}"),
            Button.inline("⭐ Star ဝယ်မယ်", data=f"buyhub_star_{user_id}")
        ],
        [
            Button.inline("👑 Premium ဝယ်မယ်", data=f"buyhub_premium_{user_id}"),
            Button.inline("🎰 Casino ဂိမ်းများ", data="nav_casino_main")  # ဒီခလုတ်က bot1 မှာရှိတဲ့ Menu ကိုပဲ ခေါ်သွားမယ်
        ]
    ]

    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]topgift(?:@\w+)?$', 'bot1')))
async def top_gifters_handler(event):
    cursor = users_catcher_col.find({"total_gifted": {"$gt": 0}}).sort("total_gifted", -1).limit(10)
    top_users = await cursor.to_list(length=10)
    if not top_users:
        return await event.reply(f"🎁 <b>No gifts sent yet.</b>\n<i>/gift a card to get on the board!</i>", parse_mode='html')
    mentions = await _resolve_top_mentions(event.client, top_users)
    lines = []
    for i, (u, mention) in enumerate(zip(top_users, mentions)):
        count = u.get("total_gifted", 0)
        rank_tag = TOP_MEDALS.get(i, f"<code>#{i + 1}</code>")
        title = get_giver_title(count)
        title_str = f" {title[0]}" if title else ""
        lines.append(f"{rank_tag}  {mention}{title_str} — <code>{count:,} gifts</code>")
    msg = (
        f"🎁 <b>TOP 10 GIFTERS</b>\n"
        f"{chr(10).join(lines)}"
    )
    await event.reply(msg, parse_mode='html')

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

    if sender_id != OWNER_ID:
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

    # 🩹 FIX: the 1000 USD gift fee is now charged HERE — only once validation above has
    # already succeeded (char exists, sender genuinely owns it) and the gift is definitely
    # going through. Previously this fired the instant /gift was typed, before any of that was
    # checked, so a bad char_id or a card the sender didn't own still cost 1000 USD with no
    # refund, and even hitting Cancel on the confirmation kept the fee too.
    gift_fee = 1000.0
    gift_fee_paid = await try_deduct_balance(sender_id, gift_fee)
    if gift_fee_paid:
        fee_note = f"💰 <b>Gift Fee Paid:</b> <code>{format_usd(gift_fee)}</code>\n"
    else:
        await debts_col.update_one({"user_id": sender_id}, {"$inc": {"amount": gift_fee}}, upsert=True)
        await bot3_treasury_adjust(usd=gift_fee)
        fee_note = f"⚠️ <b>Gift Fee ({format_usd(gift_fee)}) added as debt</b> — insufficient balance.\n"

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
        f"{fee_note}"
        f"\n"
        f"🍔 <i>…all done</i>"
        f"{giver_promo_line}",
        parse_mode='html',
        buttons=None
    )
    await event.answer("Gift sent successfully!", alert=True)
    # 🩹 CHANGED (per owner request): a DM to the receiver used to be sent here too — removed,
    # the in-chat confirmation above is enough now.

# ==========================================
# 🎁 /giftusd, /giftstar, /giftpremium — direct user-to-user gifting of USD, ⭐ Star, and Bot
# Premium. All three: reply to the receiver's message, same confirm/cancel pattern as the card
# /gift above. /giftpremium is paid for by the SENDER in ⭐ Star at the exact /buypremium rate
# (see PREMIUM_TIERS) — the days land on the RECEIVER instead of the buyer; the Star still
# flows to the Owner, same Star sink as every other Premium purchase.
# ==========================================
GIFT_USD_MIN = 0.01
GIFT_STAR_MIN = 0.01

async def _resolve_gift_receiver(event):
    """Shared receiver resolution + validation for all three /gift* commands below.
    Returns (receiver_id, error_message_or_None)."""
    if not event.is_reply:
        return None, "❌ <b>Reply to the user you want to gift.</b>"
    reply_msg = await event.get_reply_message()
    receiver_id = reply_msg.sender_id if reply_msg else None
    if not receiver_id:
        return None, "❌ <b>Couldn't identify that user.</b>"
    if receiver_id == event.sender_id:
        return None, "❌ <b>Can't gift to yourself!</b>"
    if receiver_id in bot_ids:
        return None, "❌ <b>Can't gift to a bot.</b>"
    return receiver_id, None

# ---- /giftusd ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftusd(?:@\w+)?\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def gift_usd_handler(event):
    amount = round(float(event.pattern_match.group(1)), 2)
    receiver_id, err = await _resolve_gift_receiver(event)
    if err:
        return await event.reply(err, parse_mode='html')
    
    # 💰 0.2% Fee (0.002)
    fee_rate = 0.002
    fee = round(amount * fee_rate, 2)
    net_amount = round(amount - fee, 2)
    
    if fee <= 0:
        return await event.reply("❌ <b>Gift amount too small (fee would be zero).</b>", parse_mode='html')
    
    sender_id = event.sender_id
    r_mention = await get_html_mention(event, receiver_id)
    
    # Check sender balance (including fee)
    sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
    balance = sender_doc.get("wallet_balance", 0) if sender_doc else 0
    if balance < amount:
        return await event.reply(
            f"❌ <b>Insufficient balance!</b> You need {format_usd(amount)} (including {format_usd(fee)} fee).",
            parse_mode='html'
        )
    
    confirm_text = (
        f"💵 <b>Gift Confirmation</b>\n\n"
        f"💰 <b>Amount:</b> <code>{format_usd(amount)}</code>\n"
        f"🏦 <b>Fee (0.2%):</b> <code>{format_usd(fee)}</code>\n"
        f"📥 <b>Receiver gets:</b> <code>{format_usd(net_amount)}</code>\n"
        f"🎯 <b>Receiver:</b> {r_mention}\n\n"
        f"Are you sure you want to send this?"
    )
    buttons = [[
        Button.inline("✅ Confirm", data=f"giftusd_confirm_{sender_id}_{receiver_id}_{amount}_{fee}"),
        Button.inline("❌ Cancel", data=f"giftusd_cancel_{sender_id}_{receiver_id}_{amount}")
    ]]
    await event.reply(confirm_text, buttons=buttons, parse_mode='html')
@bot1.on(events.CallbackQuery(pattern=r'^giftusd_(confirm|cancel)_(\d+)_(\d+)_([\d.]+)(?:_([\d.]+))?$'))
async def gift_usd_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    amount = round(float(event.pattern_match.group(4)), 2)
    fee = round(float(event.pattern_match.group(5) or 0), 2) if event.pattern_match.group(5) else 0
    
    if event.sender_id != sender_id:
        return await event.answer("❌ This action is not for you!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    
    if action == "cancel":
        await event.edit(f"❌ <b>Gift Cancelled.</b> {format_usd(amount)} was not sent.", parse_mode='html', buttons=None)
        return await event.answer("Gift cancelled.", alert=True)
    
    # Deduct full amount first
    if not await try_deduct_balance(sender_id, amount):
        await event.edit("❌ <b>Not enough USD balance anymore.</b>", parse_mode='html', buttons=None)
        return await event.answer("Insufficient balance.", alert=True)
    
    # Send net amount to receiver
    net_amount = round(amount - fee, 2)
    if net_amount > 0:
        r_plain_name = await get_plain_name(event, receiver_id)
        await users_catcher_col.update_one(
            {"user_id": receiver_id},
            {"$inc": {"wallet_balance": net_amount}, "$set": {"fullname": r_plain_name}},
            upsert=True
        )
    
    # Send fee to bot3 treasury
    if fee > 0:
        await bot3_treasury_adjust(usd=fee)
    
    r_mention = await get_html_mention(event, receiver_id)
    s_mention = await get_html_mention(event, sender_id)
    await event.edit(
        f"✅ <b>{format_usd(net_amount)} sent to {r_mention}!</b>\n"
        f"🏦 <b>Fee (0.2%):</b> {format_usd(fee)} (added to bot3 treasury)",
        parse_mode='html',
        buttons=None
    )
    # 🩹 CHANGED (per owner request): the receiver DM notification was removed here — the
    # in-chat confirmation above is enough now.

# ---- /giftstar ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftstar(?:@\w+)?\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def gift_star_handler(event):
    amount = round(float(event.pattern_match.group(1)), 2)
    receiver_id, err = await _resolve_gift_receiver(event)
    if err:
        return await event.reply(err, parse_mode='html')
    
    # 💰 0.2% Fee (0.002)
    fee_rate = 0.002
    fee = round(amount * fee_rate, 2)
    net_amount = round(amount - fee, 2)
    
    if fee <= 0:
        return await event.reply("❌ <b>Gift amount too small (fee would be zero).</b>", parse_mode='html')
    
    sender_id = event.sender_id
    r_mention = await get_html_mention(event, receiver_id)
    
    # Check sender Star balance (including fee)
    sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
    star_balance = sender_doc.get("star_balance", 0) if sender_doc else 0
    if star_balance < amount:
        return await event.reply(
            f"❌ <b>Insufficient Star balance!</b> You need {format_star_plain(amount)} (including {format_star_plain(fee)} fee).",
            parse_mode='html'
        )
    
    confirm_text = (
        f"⭐ <b>Gift Confirmation</b>\n\n"
        f"💰 <b>Amount:</b> <code>{format_star_plain(amount)}</code>\n"
        f"🏦 <b>Fee (0.2%):</b> <code>{format_star_plain(fee)}</code>\n"
        f"📥 <b>Receiver gets:</b> <code>{format_star_plain(net_amount)}</code>\n"
        f"🎯 <b>Receiver:</b> {r_mention}\n\n"
        f"Are you sure you want to send this?"
    )
    buttons = [[
        Button.inline("✅ Confirm", data=f"giftstar_confirm_{sender_id}_{receiver_id}_{amount}_{fee}"),
        Button.inline("❌ Cancel", data=f"giftstar_cancel_{sender_id}_{receiver_id}_{amount}")
    ]]
    await event.reply(confirm_text, buttons=buttons, parse_mode='html')

@bot1.on(events.CallbackQuery(pattern=r'^giftstar_(confirm|cancel)_(\d+)_(\d+)_([\d.]+)(?:_([\d.]+))?$'))
async def gift_star_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    amount = round(float(event.pattern_match.group(4)), 2)
    fee = round(float(event.pattern_match.group(5) or 0), 2) if event.pattern_match.group(5) else 0
    
    if event.sender_id != sender_id:
        return await event.answer("❌ This action is not for you!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    
    if action == "cancel":
        await event.edit(f"❌ <b>Gift Cancelled.</b> {format_star_plain(amount)} was not sent.", parse_mode='html', buttons=None)
        return await event.answer("Gift cancelled.", alert=True)
    
    # Deduct full amount first (gross Star)
    if not await try_deduct_star(sender_id, amount):
        await event.edit("❌ <b>Not enough ⭐ Star balance anymore.</b>", parse_mode='html', buttons=None)
        return await event.answer("Insufficient Star.", alert=True)
    
    # Send net amount to receiver
    net_amount = round(amount - fee, 2)
    if net_amount > 0:
        r_plain_name = await get_plain_name(event, receiver_id)
        await users_catcher_col.update_one(
            {"user_id": receiver_id},
            {"$inc": {"star_balance": net_amount}, "$set": {"fullname": r_plain_name}},
            upsert=True
        )
    
    # Send fee to bot3 treasury (Star side)
    if fee > 0:
        await bot3_treasury_adjust(star=fee)
    
    r_mention = await get_html_mention(event, receiver_id)
    s_mention = await get_html_mention(event, sender_id)
    await event.edit(
        f"✅ <b>{format_star_plain(net_amount)} sent to {r_mention}!</b>\n"
        f"🏦 <b>Fee (0.2%):</b> {format_star_plain(fee)} (added to bot3 treasury)",
        parse_mode='html',
        buttons=None
    )
    # 🩹 CHANGED (per owner request): the receiver DM notification was removed here — the
    # in-chat confirmation above is enough now.
    
# ---- /giftpremium ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftpremium(?:@\w+)?\s+(\d+)$', 'bot1')))
async def gift_premium_handler(event):
    months = int(event.pattern_match.group(1))
    tier = next((t for t in PREMIUM_TIERS if t[0] == months), None)
    if not tier:
        valid = ", ".join(str(t[0]) for t in PREMIUM_TIERS)
        return await event.reply(f"❌ <b>Invalid duration.</b> Valid tiers (months): <code>{valid}</code>", parse_mode='html')
    receiver_id, err = await _resolve_gift_receiver(event)
    if err:
        return await event.reply(err, parse_mode='html')
    sender_id = event.sender_id
    _, price, days = tier
    r_mention = await get_html_mention(event, receiver_id)
    confirm_text = (
        f"👑 <b>Gift Premium Confirmation</b>\n\n"
        f"⏳ <b>Duration:</b> <code>{_premium_tier_label(months)}</code>\n"
        f"💰 <b>Cost (from your ⭐ Star):</b> <code>{price}⭐</code>\n"
        f"🎯 <b>Receiver:</b> {r_mention}\n\n"
        f"Are you sure you want to gift Premium to {r_mention}?"
    )
    buttons = [[
        Button.inline("✅ Confirm", data=f"giftprem_confirm_{sender_id}_{receiver_id}_{months}"),
        Button.inline("❌ Cancel", data=f"giftprem_cancel_{sender_id}_{receiver_id}_{months}")
    ]]
    await event.reply(confirm_text, buttons=buttons, parse_mode='html')

@bot1.on(events.CallbackQuery(pattern=r'^giftprem_(confirm|cancel)_(\d+)_(\d+)_(\d+)$'))
async def gift_premium_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes): action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    months = int(event.pattern_match.group(4))
    if event.sender_id != sender_id:
        return await event.answer("❌ This action is not for you!", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ Already processing...", alert=False)
    tier = next((t for t in PREMIUM_TIERS if t[0] == months), None)
    if not tier:
        await event.edit("❌ <b>Invalid tier.</b>", parse_mode='html', buttons=None)
        return await event.answer("Invalid tier.", alert=True)
    _, price, days = tier
    if action == "cancel":
        await event.edit("❌ <b>Gift Cancelled.</b> Premium was not sent.", parse_mode='html', buttons=None)
        return await event.answer("Gift cancelled.", alert=True)
    if not await try_deduct_star(sender_id, price):
        buyer_doc = await users_catcher_col.find_one({"user_id": sender_id})
        have = buyer_doc.get("star_balance", 0) if buyer_doc else 0
        await event.edit(f"❌ <b>Not enough ⭐ Star.</b> Need: <code>{price}⭐</code> | Have: <code>{format_star_plain(have)}</code>", parse_mode='html', buttons=None)
        return await event.answer("Insufficient Star.", alert=True)
    new_until = await grant_premium_days(receiver_id, days)
    # Same Star sink as every other Premium purchase — the Owner receives the Star paid.
    await users_catcher_col.update_one({"user_id": OWNER_ID}, {"$inc": {"star_balance": price}}, upsert=True)
    r_mention = await get_html_mention(event, receiver_id)
    s_mention = await get_html_mention(event, sender_id)
    expiry_str = datetime.fromtimestamp(new_until, TZ).strftime("%Y-%m-%d %H:%M")
    await event.edit(
        f"✅ <b>Premium gifted to {r_mention}!</b>\n⏳ <b>Runs until:</b> <code>{expiry_str}</code>",
        parse_mode='html', buttons=None
    )
    # 🩹 CHANGED (per owner request): the receiver DM notification was removed here — the
    # in-chat confirmation above is enough now.

# 🤝 TRADE
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]trade(?:@\w+)?\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)$', 'bot1')))
async def trade_proposal_handler(event):
    if not event.is_reply: return await event.reply(f"❌ <b>Reply to the user you want to trade with.</b>", parse_mode='html')
    my_char_id = normalize_char_id_input(event.pattern_match.group(1))
    their_char_id = normalize_char_id_input(event.pattern_match.group(2))
    sender_id = event.sender_id
    reply_msg = await event.get_reply_message()
    target_user_id = reply_msg.sender_id
    if sender_id == target_user_id: return
    s_doc = await users_catcher_col.find_one({"user_id": sender_id})
    t_doc = await users_catcher_col.find_one({"user_id": target_user_id})
    s_harem = s_doc.get("harem", []) if s_doc else []
    t_harem = t_doc.get("harem", []) if t_doc else []
    s_has = any(isinstance(x, dict) and x.get("char_id") == my_char_id and x.get("status") != "market" for x in s_harem)
    t_has = any(isinstance(x, dict) and x.get("char_id") == their_char_id and x.get("status") != "market" for x in t_harem)
    if not s_has: return await event.reply(f"❌ You don’t have <code>{my_char_id}</code> available.", parse_mode='html')
    if not t_has: return await event.reply(f"❌ They don’t have <code>{their_char_id}</code> available.", parse_mode='html')
    s_char = await characters_base_col.find_one({"char_id": my_char_id})
    t_char = await characters_base_col.find_one({"char_id": their_char_id})
    trade_text = f"🤝 <b>TRADE CONTRACT</b>\n📤 <b>Your Offer:</b> <code>{s_char['name']}</code> ({my_char_id})\n📥 <b>Their Request:</b> <code>{t_char['name']}</code> ({their_char_id})\n⚡ ━━━━ ⚡\nConfirm or cancel – decision is theirs."
    buttons = [[Button.inline("🤝 Confirm", data=f"tr_conf_{sender_id}_{target_user_id}_{my_char_id}_{their_char_id}"), Button.inline("❌ Cancel", data=f"tr_canc_{sender_id}_{target_user_id}")]]
    await event.reply(trade_text, parse_mode='html', buttons=buttons)

# ==========================================
# 🎰 CASINO GAMES
# ==========================================
# Guard Bot (bot3) has been merged into bot1, so these 8 games' commands and their outgoing
# result/board messages all go through the single bot1 client now — no more cross-client
# routing or load-shedding needed.
async def _out(event, text, **kwargs):
    """Drop-in replacement for event.reply(text, **kwargs)."""
    return await event.reply(text, **kwargs)

# =========================================================
# 🏦 BOT3 TREASURY BALANCE — /bot3balance (anyone can run this, no owner restriction)
# =========================================================
# Read-only: shows the seed bankroll bot3 was given vs its current balance, so how much bot3
# has actually won or lost across every casino game (see bot3_treasury_adjust calls throughout
# this file) is always a single command away instead of being uncountable.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:bot3balance|housebalance)(?:@\w+)?$', 'bot1')))
async def bot3_balance_command(event):
    treasury = await get_or_create_bot3_treasury()
    seed_usd = treasury.get("seed_wallet_balance", BOT3_SEED_WALLET_BALANCE)
    seed_star = treasury.get("seed_star_balance", BOT3_SEED_STAR_BALANCE)
    now_usd = treasury.get("wallet_balance", seed_usd)
    now_star = treasury.get("star_balance", seed_star)
    profit_usd = round(now_usd - seed_usd, 2)
    profit_star = round(now_star - seed_star, 2)
    usd_sign = "📈" if profit_usd > 0 else ("📉" if profit_usd < 0 else "➖")
    star_sign = "📈" if profit_star > 0 else ("📉" if profit_star < 0 else "➖")
    usd_profit_str = f"+{format_usd_compact(profit_usd)}" if profit_usd >= 0 else f"-{format_usd_compact(abs(profit_usd))}"
    star_profit_str = f"+{format_star_plain(profit_star)}" if profit_star >= 0 else f"-{format_star_plain(abs(profit_star))}"
    text = (
        f"🏦 <b>Bot3 Treasury (Casino House Balance)</b>\n"
        f""
        f"💵 <b>USD</b>\n"
        f" ┣ Seed (မူလ): <code>{format_usd_compact(seed_usd)}</code>\n"
        f" ┣ လက်ရှိ: <code>{format_usd_compact(now_usd)}</code>\n"
        f" ┗ {usd_sign} <b>အမြတ်/အရှုံး:</b> <code>{usd_profit_str}</code>\n\n"
        f"⭐ <b>Star</b>\n"
        f" ┣ Seed (မူလ): <code>{format_star_plain(seed_star)}</code>\n"
        f" ┣ လက်ရှိ: <code>{format_star_plain(now_star)}</code>\n"
        f" ┗ {star_sign} <b>အမြတ်/အရှုံး:</b> <code>{star_profit_str}</code>"
        f""
    )
    await _out(event, text, parse_mode='html')
# =========================================================
# 🎰 SLOT - ANIMATION EMOJI + လှုပ်ရှားမှု
# =========================================================

# ---- SLOT SESSIONS ----
active_slot_sessions = {}  # user_id -> {bet, net, msg_id, chat_id, spins}
SLOT_BET_PRESETS = [1, 10, 100, 1000, 10000, 100000]

# ---- Anti-Whale ----
# 🩹 FIX: these 4 constants were referenced everywhere below (_slot_spin_logic_bot3,
# _slot_end_bot3, _roulette_spin_bot3, _roulette_end_bot3) but were NEVER actually defined
# anywhere in the file — the comment here used to (incorrectly) claim they lived "at the
# top". Every single spin/color/number tap hit a NameError on the very first line of the
# handler (before any event.answer() call), so Telegram just showed the tap doing nothing.
# Cashout looked "fine" only because it skips the CASHOUT_PROFIT_TAX line entirely when
# net <= 0 — i.e. before you've ever completed a winning spin.
# 💡 These are game-balance numbers, not technical constants — tune them to taste:
SPIN_BURN_RATE = 0.02            # 2% of the bet is taken as a flat "casino play fee" every spin, win or lose
# 🩹 CHANGED (per owner request): the player-facing label for this was "မီးရှို့ခ" (burn fee) —
# owner found it scared players off, so it's now shown as "ကာစီနို ဆော့ခ" (casino play fee)
# everywhere across all 12 games. SPIN_BURN_RATE itself is unchanged, just the wording.
CASHOUT_PROFIT_TAX = 0.05        # 5% tax, taken only from PROFIT (net > 0) when you cash out
WEALTH_THRESHOLD = 1000          # USD wallet balance above which whale tax starts applying at all
# 🩹 CHANGED (per owner request): the old system applied a single flat 50% cut to EVERY whale,
# whether they were $1,001 or $10,000,000 — a hard cliff that felt punishing right at the
# threshold and prompted player complaints. Replaced with a progressive table: the cut now
# scales up smoothly with wealth, like a tax bracket. Sorted ascending; a balance's multiplier
# is whichever tier it satisfies, using the highest (richest) tier that applies.
WHALE_TAX_TIERS = [
    (1_000,   0.98),   # $1,000   – $5,000    → 2% cut
    (5_000,   0.955),  # $5,000   – $20,000   → 4.5% cut
    (20_000,  0.925),  # $20,000  – $100,000  → 7.5% cut
    (100_000, 0.885),  # $100,000+            → 11.5% cut
]

def get_whale_multiplier(balance):
    """Returns the raw-winnings multiplier for a given wallet_balance, per WHALE_TAX_TIERS.
    1.0 (no cut at all) for anyone at or below the lowest tier's threshold."""
    multiplier = 1.0
    for threshold, mult in WHALE_TAX_TIERS:
        if balance > threshold:
            multiplier = mult
    return multiplier

def apply_whale_tax(balance, raw_win):
    """Applies the progressive whale tax to a raw winnings amount. Returns
    (taxed_win, note_html) — note_html is "" when no tax applies (not a whale, or no win)."""
    if raw_win <= 0:
        return raw_win, ""
    multiplier = get_whale_multiplier(balance)
    if multiplier >= 1.0:
        return raw_win, ""
    taxed = round(raw_win * multiplier, 2)
    cut_pct = round((1 - multiplier) * 100)
    note = f"\n🐋 <b>ငွေကြေးရှိသူအခွန် ({cut_pct}% လျှော့):</b> <code>-{format_usd(round(raw_win - taxed, 2))}</code>"
    return taxed, note
SLOT_MIN_SPINS = 3  # အနည်းဆုံး ၃ ခါလှည့်မှ ငွေထုတ်ခွင့်ရမယ်
# Slot သင်္ကေတများ (ဂန္တဝင် အကောင်များ)
SLOT_SYMBOLS = ["🐢", "🐕", "🐊", "🐇", "🐉", "🦬", "🦉"]
JACKPOT_SYMBOL = "🦬"

def _render_slot_bot3(session, result=None, final=False, animating=False):
    user_id = session["user_id"]
    bet = session["bet"]
    net = session["net"]
    spins = session.get("spins", 0)
    mention = session.get("mention", f"<a href='tg://user?id={user_id}'><b>သင့်အကောင်</b></a>")
    
    # 🎨 UPGRADED UI: symbols now sit inside a framed "reel" box instead of a bare code line,
    # and the result banner scales with how big the win is (jackpot gets its own treatment)
    # instead of one generic "you won" message for every win size.
    if animating:
        anim_syms = random.choices(SLOT_SYMBOLS, k=7)
        reel_line = " │ ".join(anim_syms)
    elif result:
        reel_line = " │ ".join(result["symbols"])
    else:
        reel_line = " │ ".join(["❔"] * 7)

    reel_box = (
        f"<code>┏━━━━━━━━━━━━━━━━━━━━━━━━━┓\n"
        f"┃  {reel_line}  ┃\n"
        f"┗━━━━━━━━━━━━━━━━━━━━━━━━━┛</code>"
    )

    status_line = ""
    if animating:
        status_line = "👾 <b>လှည့်နေပါပြီ...</b> 🔄🔄🔄"
    elif result:
        if result["win"] >= bet * 20:
            status_line = f"🔥🎊 <b>J A C K P O T ! !</b> 🎊🔥\n💰 <b>+{result['win']:.2f} USD</b>"
        elif result["win"] >= bet * 2:
            status_line = f"✨🎉 <b>BIG WIN! +{result['win']:.2f} USD</b> 🎉✨"
        elif result["win"] > 0:
            status_line = f"🎉 <b>+{result['win']:.2f} USD</b> ရလိုက်ပါပြီ!"
        else:
            status_line = "💔 <b>ဒီတစ်ခါ မအောင်မြင်ဘူး</b>"
    else:
        status_line = "👆 <b>'လှည့်မယ်' ကိုနှိပ်ပြီး စလိုက်ပါ</b>"

    # 🩹 FIX: ငွေထုတ်ဖို့ အနည်းဆုံးလှည့်ရမယ့်အကြောင်း အသိပေးစာ
    min_spins_note = ""
    if not final and spins < SLOT_MIN_SPINS:
        min_spins_note = f"\n⚠️ <i>ငွေထုတ်ဖို့ အနည်းဆုံး {SLOT_MIN_SPINS} ခါလှည့်ရမယ်။ (လက်ရှိ {spins}/{SLOT_MIN_SPINS})</i>"

    net_emoji = "📈" if net > 0 else ("📉" if net < 0 else "➖")
    net_display = f"{'+' if net >= 0 else ''}{net:.2f} USD"

    text = (
        f"🎰 <b>S L O T   M A C H I N E</b> 🎰\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{bet:.2f} USD</code>  │  🔄 <b>ပွဲ:</b> <code>{spins}</code>\n"
        f"{net_emoji} <b>စုစုပေါင်း:</b> <code>{net_display}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"{reel_box}\n\n"
        f"{status_line}"
        f"{min_spins_note}\n\n"
        f"<i>ဆက်ကစားရန် ခလုတ်နှိပ်ပါ။</i>"
    )

    buttons = []
    if not final:
        buttons.append([Button.inline("🔄 လှည့်မယ်", data=f"sl3_spin_{user_id}"),
                        Button.inline("💰 ငွေထုတ်မယ်", data=f"sl3_cashout_{user_id}")])
        row1, row2, row3 = [], [], []
        for i, amt in enumerate(SLOT_BET_PRESETS):
            label = f"+{amt}"
            data = f"sl3_addbet_{user_id}_{amt}"
            if i < 2: row1.append(Button.inline(label, data=data))
            elif i < 4: row2.append(Button.inline(label, data=data))
            else: row3.append(Button.inline(label, data=data))
        if row1: buttons.append(row1)
        if row2: buttons.append(row2)
        if row3: buttons.append(row3)
    else:
        buttons.append([Button.inline("🔄 အသစ်စပါ", data=f"sl3_new_{user_id}")])
    return text, buttons

async def _slot_end_bot3(user_id, chat_id, msg_id, cashout=True):
    session = active_slot_sessions.pop(user_id, None)
    if not session: return
    net = session.get("net", 0)
    tax_text = ""
    if cashout and net > 0:
        tax = round(net * CASHOUT_PROFIT_TAX, 2)
        if tax > 0:
            await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": -tax}})
            await bot3_treasury_adjust(usd=tax)
            session["net"] = round(net - tax, 2)
            tax_text = f"\n🏦 <b>အမြတ်အခွန် ({int(CASHOUT_PROFIT_TAX*100)}%):</b> <code>-{tax:.2f} USD</code>"
        else:
            tax_text = "\n✅ <b>အခွန်ကင်းလွတ်</b>"
    elif cashout and net <= 0:
        tax_text = "\n💔 <b>အရှုံးပေါ် — အခွန်မကောက်ပါ</b>"
    final_text, _ = _render_slot_bot3(session, final=True)
    final_text += tax_text
    try:
        await bot1.edit_message(chat_id, msg_id, final_text, parse_mode='html', buttons=None)
    except Exception: pass

@bot1.on(events.NewMessage(pattern=r'^[/.]slot(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?'))
async def slot_cmd_bot3(event):
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1) if event.pattern_match.group(1) else None

    if user_id in active_slot_sessions:
        session = active_slot_sessions[user_id]
        if bet_str:
            await _slot_end_bot3(user_id, event.chat_id, session["msg_id"], cashout=False)
        else:
            return await bot1.send_message(event.chat_id, "⚠️ Slot ကစားပွဲရှိနေပြီ။ အောက်ကခလုတ်သုံးပါ။", parse_mode='html', reply_to=session["msg_id"])

    if not bet_str:
        return await bot1.send_message(event.chat_id, "🎰 ငွေပမာဏထည့်ပါ။ ဥပမာ: <code>/slot 5</code>", parse_mode='html')

    bet = round(float(bet_str), 2)
    if bet <= 0:
        return await bot1.send_message(event.chat_id, "❌ အနည်းဆုံး 0.01 USD လောင်းပါ။", parse_mode='html')

    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    if balance < bet:
        return await bot1.send_message(event.chat_id, f"❌ မင်းမှာ {balance:.2f} USD ပဲရှိတယ်။", parse_mode='html')

    # ✅ ဒီနေရာမှာ Mention ကိုထုတ်ယူပြီး Session ထဲထည့်ပါ
    mention = await get_html_mention(event, user_id)

    session = {
        "user_id": user_id,
        "mention": mention,   # ✅ ဒီစာကြောင်း ထည့်ပါ
        "bet": bet,
        "net": 0.0,
        "chat_id": event.chat_id,
        "msg_id": None,
        "spins": 0
    }
    text, buttons = _render_slot_bot3(session)
    msg = await bot1.send_message(event.chat_id, text, parse_mode='html', buttons=buttons)
    session["msg_id"] = msg.id
    active_slot_sessions[user_id] = session

async def _slot_spin_logic_bot3(event, user_id):
    session = active_slot_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိတော့ဘူး။", alert=True)
    chat_id, bet = session["chat_id"], session["bet"]

    # 🔥 Spin Burn
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        await event.answer("❌ ကာစီနိုဆော့ခ မပေးနိုင် — ပိတ်မယ်။", alert=True)
        return await _slot_end_bot3(user_id, chat_id, session["msg_id"], cashout=False)
    await bot3_treasury_adjust(usd=burn)
    if not await try_deduct_bet_bot3(event, user_id, bet):
        await event.answer("❌ ငွေနှုတ်လို့မရ — ပိတ်မယ်။", alert=True)
        return await _slot_end_bot3(user_id, chat_id, session["msg_id"], cashout=False)
    await bot3_treasury_adjust(usd=bet)

    # Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD

    # 🎬 Animation (၄ ခါ လှည့်ပြီး ရလဒ်ပြမယ်)
    for _ in range(1):
        anim_text, _ = _render_slot_bot3(session, animating=True)
        try:
            await event.edit(anim_text, parse_mode='html', buttons=None)
        except:
            pass
        await asyncio.sleep(0.2)

    # 🎰 တကယ့်ရလဒ်
    res = random.choices(SLOT_SYMBOLS, k=7)
    counts = Counter(res)
    most, max_count = counts.most_common(1)[0]
    raw_win = 0
    if max_count >= 7: raw_win = bet * 20 if most == JACKPOT_SYMBOL else bet * 50
    elif max_count == 6: raw_win = bet * 2
    elif max_count == 5: raw_win = bet * 3
    elif max_count == 3: raw_win = bet * 2
    elif max_count == 3: raw_win = round(bet * 2.5, 2)
    elif max_count == 2: raw_win = round(bet * 0.5, 1)
    else: raw_win = 0

    if is_whale and raw_win > 0:
        raw_win, whale_note = apply_whale_tax(whale_balance, raw_win)
        penalty_text = "\n🐋 မီလျံနာများ,ဘီလျံနာများ စတီဗင်ချောင်နဲ့ ပြိုင်ချင်တာလား" + whale_note
    else: penalty_text = ""

    win = raw_win
    if win > 0:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": win}})
        await bot3_treasury_adjust(usd=-(win))
        net_change = win - bet
    else: net_change = -bet

    session["net"] += net_change
    session["spins"] = session.get("spins", 0) + 1
    result = {"symbols": res, "win": win}
    text_final, buttons_final = _render_slot_bot3(session, result=result)
    if burn > 0:
        text_final += f"\n🔥 <b>စလော့စက်လှည့်ခ:</b> <code>-{burn:.2f} USD</code>"
    text_final += penalty_text
    try:
        await event.edit(text_final, parse_mode='html', buttons=buttons_final)
    except:
        pass
    await event.answer("🎰 လှည့်ပြီး!")
    if win >= bet * 50:
        mention = await get_html_mention(event, user_id)
        await bot1.send_message(chat_id, f"🔥 {mention} Slot Jackpot <b>{win:.2f} USD</b> ပေါက်သွားပြီ!", parse_mode='html')

# ---- Slot Callbacks ----
@bot1.on(events.CallbackQuery(pattern=r'^sl3_spin_(\d+)$'))
async def sl3_spin_cb(event):
    if event.sender_id != int(event.pattern_match.group(1)):
        return await event.answer("⚠️ မင်းslotဟုတ်လို့လား?", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    await _slot_spin_logic_bot3(event, int(event.pattern_match.group(1)))

@bot1.on(events.CallbackQuery(pattern=r'^sl3_addbet_(\d+)_(\d+)$'))
async def sl3_addbet_cb(event):
    user_id, add = int(event.pattern_match.group(1)), float(event.pattern_match.group(2))
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းslotစက်ဟုတ်လို့လား?", alert=True)
    session = active_slot_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိ", alert=True)
    
    # ✅ ဒီမှာ Balance စစ်ဆေးတယ်
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    new_bet = session["bet"] + add
    
    if new_bet > balance:
        return await event.answer(f"❌ မင်းမှာ {balance:.2f} USD ပဲရှိတယ်။ {new_bet:.2f} USD မလုံလောက်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("ခဏစောင့်", alert=False)
    
    session["bet"] = new_bet
    text, buttons = _render_slot_bot3(session)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer(f"✅ လောင်းငွေ {session['bet']:.2f} USD ဖြစ်သွားပြီ", alert=False)
    except:
        pass

@bot1.on(events.CallbackQuery(pattern=r'^sl3_cashout_(\d+)$'))
async def sl3_cashout_cb(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းslotဟုတ်လို့လား?", alert=True)
    session = active_slot_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိ", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    
    # 🩹 FIX: အနည်းဆုံး ၃ ခါ လှည့်ပြီးလား စစ်ဆေးမယ်
    spins = session.get("spins", 0)
    if spins < SLOT_MIN_SPINS:
        return await event.answer(
            f"⚠️ အနည်းဆုံး {SLOT_MIN_SPINS} ခါလှည့်မှ ငွေထုတ်လို့ရမယ်။ လက်ရှိ {spins} ခါပဲလှည့်ရသေးတယ်။",
            alert=True
        )
    
    await _slot_end_bot3(user_id, session["chat_id"], session["msg_id"], cashout=True)
    await event.answer("💰 ငွေထုတ်ပြီး!", alert=True)

@bot1.on(events.CallbackQuery(pattern=r'^sl3_new_(\d+)$'))
async def sl3_new_cb(event):
    await event.answer("🔄 /slot [ငွေ] ရိုက်ပြီး အသစ်စပါ။", alert=True)

# =========================================================
# 🎡 ROULETTE - ANIMATION EMOJI + လှုပ်ရှားမှု
# =========================================================

active_roulette_sessions = {}
ROULETTE_BET_PRESETS = [1, 10, 100, 1000, 10000, 100000]
ROULETTE_COLORS = {0: "🟢", 1: "🔴", 2: "⚫", 3: "🔴", 4: "⚫", 5: "🔴",
                   6: "⚫", 7: "🔴", 8: "⚫", 9: "🔴", 10: "⚫"}
ROULETTE_COLOR_NAMES = {"🔴": "အနီ", "⚫": "အမည်း", "🟢": "အစိမ်း"}
ROULETTE_MULTIPLIERS = {"🔴": 2, "⚫": 2, "🟢": 14}

def _render_roulette_bot3(session, result=None, final=False, animating=False):
    user_id = session["user_id"]
    bet = session["bet"]
    net = session["net"]
    spins = session.get("spins", 0)

    status_line = ""
    if animating:
        # Animation ဖြစ်နေရင် ဘီးလှည့်နေသလို ပြမယ်
        anim_number = random.randint(0, 10)
        anim_color = ROULETTE_COLORS[anim_number]
        status_line = f"🎡 <b>ဘီးလှည့်နေပါပြီ...</b> {anim_color} {anim_number} 🌀"
    elif result:
        win, number, color = result.get("win", 0), result.get("number", "?"), result.get("color", "❔")
        if win > 0:
            status_line = f"🎉 <b>+{win:.2f} USD</b> ({ROULETTE_COLOR_NAMES.get(color, '')} ပေါက်)"
        else:
            status_line = f"💔 <b>ရှုံးသွားပြီ</b> ({ROULETTE_COLOR_NAMES.get(color, '')} ပေါက်)"
        status_line += f"\n🎯 <b>ပေါက်ဂဏန်း:</b> <code>{number}</code> {color}"
    else:
        status_line = "👆 အောက်ကခလုတ်နှိပ်ပြီး စပါ။"

    net_display = f"{'+' if net >= 0 else ''}{net:.2f} USD"
    text = (f"🎡 <b>ROULETTE (ရူလက်)</b>\n"
            f"👤 <a href='tg://user?id={user_id}'><b>လောင်းကစားသမား</b></a>\n"
            f"💵 <b>လက်ရှိလောင်းငွေ:</b> <code>{bet:.2f} USD</code>\n"
            f"🔄 <b>အရေအတွက်:</b> <code>{spins}</code> ပွဲ\n"
            f"📊 <b>စုစုပေါင်းအမြတ်/အရှုံး:</b> <code>{net_display}</code>\n\n"
            f"{status_line}\n\n"
            f"<i>အောက်ကခလုတ်နှိပ်ပြီး ရွေးပါ။</i>")

    buttons = []
    if not final:
        buttons.append([Button.inline("🔴(x2)", data=f"r3_color_{user_id}_🔴"),
                        Button.inline("⚫(x2)", data=f"r3_color_{user_id}_⚫"),
                        Button.inline("🟢(x14)", data=f"r3_color_{user_id}_🟢")])
        row1, row2 = [], []
        for i in range(1, 11):
            (row1 if i <= 5 else row2).append(Button.inline(str(i), data=f"r3_num_{user_id}_{i}"))
        buttons.append(row1)
        buttons.append(row2)
        r1, r2, r3 = [], [], []
        for i, amt in enumerate(ROULETTE_BET_PRESETS):
            data = f"r3_addbet_{user_id}_{amt}"
            if i < 2: r1.append(Button.inline(f"+{amt}", data=data))
            elif i < 4: r2.append(Button.inline(f"+{amt}", data=data))
            else: r3.append(Button.inline(f"+{amt}", data=data))
        if r1: buttons.append(r1)
        if r2: buttons.append(r2)
        if r3: buttons.append(r3)
        buttons.append([Button.inline("💰 ငွေထုတ်မယ်", data=f"r3_cashout_{user_id}")])
    else:
        buttons.append([Button.inline("🔄 အသစ်စပါ", data=f"r3_new_{user_id}")])
    return text, buttons

async def _roulette_end_bot3(user_id, chat_id, msg_id, cashout=True):
    session = active_roulette_sessions.pop(user_id, None)
    if not session: return
    net = session.get("net", 0)
    tax_text = ""
    if cashout and net > 0:
        tax = round(net * CASHOUT_PROFIT_TAX, 2)
        if tax > 0:
            await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": -tax}})
            await bot3_treasury_adjust(usd=tax)
            session["net"] = round(net - tax, 2)
            tax_text = f"\n🏦 <b>အမြတ်အခွန် ({int(CASHOUT_PROFIT_TAX*100)}%):</b> <code>-{tax:.2f} USD</code>"
        else:
            tax_text = "\n✅ အခွန်ကင်း"
    elif cashout and net <= 0:
        tax_text = "\n💔 အရှုံးပေါ် — အခွန်မကောက်ပါ"
    final_text, _ = _render_roulette_bot3(session, final=True)
    final_text += tax_text
    try:
        await bot1.edit_message(chat_id, msg_id, final_text, parse_mode='html', buttons=None)
    except:
        pass

@bot1.on(events.NewMessage(pattern=r'^[/.](roulette|r)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?'))
async def roulette_cmd_bot3(event):
    user_id = event.sender_id
    bet_str = event.pattern_match.group(2) if event.pattern_match.group(2) else None

    if user_id in active_roulette_sessions:
        session = active_roulette_sessions[user_id]
        if bet_str:
            await _roulette_end_bot3(user_id, event.chat_id, session["msg_id"], cashout=False)
        else:
            return await bot1.send_message(event.chat_id, "⚠️ Roulette ရှိနေပြီ။ အောက်ကခလုတ်သုံးပါ။", parse_mode='html', reply_to=session["msg_id"])

    if not bet_str:
        return await bot1.send_message(event.chat_id, "🎡 ငွေပမာဏထည့်ပါ။ ဥပမာ: <code>/r 5</code>", parse_mode='html')

    bet = round(float(bet_str), 2)
    if bet <= 0:
        return await bot1.send_message(event.chat_id, "❌ အနည်းဆုံး 0.01 USD", parse_mode='html')

    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await bot1.send_message(event.chat_id, f"❌ ငွေမလုံလောက်", parse_mode='html')

    session = {"user_id": user_id, "bet": bet, "net": 0.0, "chat_id": event.chat_id, "msg_id": None, "spins": 0}
    text, buttons = _render_roulette_bot3(session)
    msg = await bot1.send_message(event.chat_id, text, parse_mode='html', buttons=buttons)
    session["msg_id"] = msg.id
    active_roulette_sessions[user_id] = session

async def _roulette_spin_bot3(event, user_id, bet_type, bet_value=None):
    session = active_roulette_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိ", alert=True)
    chat_id, bet = session["chat_id"], session["bet"]

    # Burn
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        await event.answer("❌ ကာစီနိုဆော့ခ မပေးနိုင်", alert=True)
        return await _roulette_end_bot3(user_id, chat_id, session["msg_id"], cashout=False)
    await bot3_treasury_adjust(usd=burn)
    if not await try_deduct_bet_bot3(event, user_id, bet):
        await event.answer("❌ ငွေနှုတ်လို့မရ", alert=True)
        return await _roulette_end_bot3(user_id, chat_id, session["msg_id"], cashout=False)
    await bot3_treasury_adjust(usd=bet)

    # Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD

    # 🎬 Animation (၃ ခါ လှည့်ပြီး ရလဒ်ပြမယ်)
    for _ in range(3):
        anim_text, _ = _render_roulette_bot3(session, animating=True)
        try:
            await event.edit(anim_text, parse_mode='html', buttons=None)
        except:
            pass
        await asyncio.sleep(0.4)

    # တကယ့်ရလဒ်
    number = random.randint(0, 10)
    color = ROULETTE_COLORS[number]
    multiplier = 0
    if bet_type == "number" and bet_value == number:
        multiplier = 10
    elif bet_type == "color" and color == bet_value:
        multiplier = ROULETTE_MULTIPLIERS.get(color, 0)
    raw_win = round(bet * multiplier, 2) if multiplier > 0 else 0

    if is_whale and raw_win > 0:
        raw_win, whale_note = apply_whale_tax(whale_balance, raw_win)
        penalty_text = whale_note
    else:
        penalty_text = ""

    win = raw_win
    if win > 0:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": win}})
        await bot3_treasury_adjust(usd=-(win))
        net_change = win - bet
    else:
        net_change = -bet

    session["net"] += net_change
    session["spins"] = session.get("spins", 0) + 1
    result = {"number": number, "color": color, "win": win}
    text_final, buttons_final = _render_roulette_bot3(session, result=result)
    if burn > 0:
        text_final += f"\n🔥 <b>ကာစီနိုဆော့ခ:</b> <code>-{burn:.2f} USD</code>"
    text_final += penalty_text
    try:
        await event.edit(text_final, parse_mode='html', buttons=buttons_final)
    except:
        pass
    await event.answer("🎡 လှည့်ပြီး!")
    if win >= bet * 10:
        mention = await get_html_mention(event, user_id)
        await bot1.send_message(chat_id, f"🔥 {mention} Roulette မှာ <b>{win:.2f} USD</b> ပေါက်သွားပြီ!", parse_mode='html')

# ---- Roulette Callbacks ----
@bot1.on(events.CallbackQuery(pattern=r'^r3_color_(\d+)_(🔴|⚫|🟢)$'))
async def r3_color_cb(event):
    user_id, color = int(event.pattern_match.group(1)), event.pattern_match.group(2)
    if isinstance(color, bytes):
        color = color.decode('utf-8')
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းဟုတ်လား?", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    await _roulette_spin_bot3(event, user_id, "color", color)

@bot1.on(events.CallbackQuery(pattern=r'^r3_num_(\d+)_(\d+)$'))
async def r3_num_cb(event):
    user_id, number = int(event.pattern_match.group(1)), int(event.pattern_match.group(2))
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းဟုတ်လား?", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    await _roulette_spin_bot3(event, user_id, "number", number)

@bot1.on(events.CallbackQuery(pattern=r'^r3_addbet_(\d+)_(\d+)$'))
async def r3_addbet_cb(event):
    user_id, add = int(event.pattern_match.group(1)), float(event.pattern_match.group(2))
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းဟုတ်လား?", alert=True)
    session = active_roulette_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိ", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    session["bet"] = max(0.01, session["bet"] + add)
    text, buttons = _render_roulette_bot3(session)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer(f"✅ လောင်းငွေ {session['bet']:.2f} USD", alert=False)
    except:
        pass

@bot1.on(events.CallbackQuery(pattern=r'^r3_cashout_(\d+)$'))
async def r3_cashout_cb(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("⚠️ မင်းဟုတ်လား?", alert=True)
    session = active_roulette_sessions.get(user_id)
    if not session:
        return await event.answer("❌ Session မရှိ", alert=True)
    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်", alert=False)
    await _roulette_end_bot3(user_id, session["chat_id"], session["msg_id"], cashout=True)
    await event.answer("💰 ငွေထုတ်ပြီး!", alert=True)

@bot1.on(events.CallbackQuery(pattern=r'^r3_new_(\d+)$'))
async def r3_new_cb(event):
    await event.answer("🔄 /r [ငွေ] ရိုက်ပြီး အသစ်စပါ။", alert=True)
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cardgame(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def create_cardgame_lobby(event):
    if event.is_private: return
    chat_id = event.chat_id
    bet_str = event.pattern_match.group(1)
    if not bet_str:
        return await _out(event, f"🃏 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/cardgame 1</code>", parse_mode='html')
    bet = round(float(bet_str), 2)
    if bet < (100 / MMK_PER_USD): return await _out(event, f"❌ <b>Minimum bet is {format_usd(100 / MMK_PER_USD)}.</b>", parse_mode='html')
    if chat_id in active_card_games: return await _out(event, "⚠️ <b>A game is already running.</b>", parse_mode='html')
    host_id = event.sender_id
    if not await try_deduct_bet_bot3(event, host_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": host_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"❌ <b>Insufficient balance! You have {balance} USD</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    if chat_id in active_card_games:
        # Someone else's /cardgame won the race while we were deducting — refund and bail.
        await users_catcher_col.update_one({"user_id": host_id}, {"$inc": {"wallet_balance": bet}})
        await bot3_treasury_adjust(usd=-(bet))
        return await _out(event, "⚠️ <b>A game is already running.</b>", parse_mode='html')
    try:
        sender = await event.get_sender()
        fullname = f"{getattr(sender, 'first_name', '')} {getattr(sender, 'last_name', '')}".strip() or getattr(sender, 'username', '') or "Host"
    except: fullname = "Host"
    host_mention = f"<a href='tg://user?id={host_id}'><b>{escape_html(fullname)}</b></a>"
    active_card_games[chat_id] = {"host_id": host_id, "bet": bet, "players": {host_id: fullname}, "status": "lobby", "msg_id": None}
    lobby_text = f"🃏 <b>MULTIPLAYER CARD GAME</b>\n👑 <b>Host:</b> {host_mention}\n💵 <b>Bet:</b> <code>{bet} USD</code>\n\n👥 <b>Players (1):</b>\n 1. {host_mention} (Host)\n\n📌 <i>At least 2 players. Host: <code>/startgame</code></i>"
    buttons = [[Button.inline("🃏 Join Game", data=f"cardjoin_{chat_id}")]]
    msg = await _out(event, lobby_text, parse_mode='html', buttons=buttons)
    active_card_games[chat_id]["msg_id"] = msg.id

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]startgame(?:@\w+)?$', 'bot1')))
async def start_cardgame_handler(event):
    if event.is_private: return
    chat_id = event.chat_id
    if chat_id not in active_card_games: return await _out(event, "❌ <b>No game lobby to start.</b>", parse_mode='html')
    game = active_card_games[chat_id]
    if game["status"] != "lobby": return
    if event.sender_id != game["host_id"]: return await _out(event, "❌ <b>Only the host can start.</b>", parse_mode='html')
    if len(game["players"]) < 2: return await _out(event, "👥 <b>Need at least 2 players.</b>", parse_mode='html')
    game["status"] = "playing"
    pool = game["bet"] * len(game["players"])
    results = {}
    max_score = -1
    for pid, name in game["players"].items():
        card_score = random.randint(1, 10)
        results[pid] = {"name": name, "score": card_score}
        if card_score > max_score: max_score = card_score
    winners = [pid for pid, data in results.items() if data["score"] == max_score]
    split_prize = round(pool / len(winners), 2)
    for w_id in winners: await users_catcher_col.update_one({"user_id": w_id}, {"$inc": {"wallet_balance": split_prize}})
    await bot3_treasury_adjust(usd=-(split_prize * len(winners)))
    reveal_msg = await _out(event, f"🃏 <b>Dealing cards...</b>\n💰 <b>Prize Pool:</b> <code>{pool} USD</code>", parse_mode='html')
    dealt_text = f"🃏 <b>GAME RESULTS</b>\n💰 <b>Prize Pool:</b> <code>{pool} USD</code>\n\n"
    for pid, data in results.items():
        p_mention = f"<a href='tg://user?id={pid}'><b>{escape_html(data['name'])}</b></a>"
        dealt_text += f"🎴 {p_mention} drew: <b>[??]</b>\n"
        await asyncio.sleep(0.5)
        try:
            await reveal_msg.edit(dealt_text, parse_mode='html')
        except Exception:
            pass
    result_text = f"🃏 <b>GAME RESULTS</b>\n💰 <b>Prize Pool:</b> <code>{pool} USD</code>\n\n"
    for pid, data in results.items():
        p_mention = f"<a href='tg://user?id={pid}'><b>{escape_html(data['name'])}</b></a>"
        win_tag = " 🏆 (WINNER)" if pid in winners else ""
        result_text += f"🃏 {p_mention} drew card: <b>[{data['score']}/10]</b>{win_tag}\n"
    if len(winners) > 1: result_text += f"🤝 <b>Tie! Each winner gets <code>{split_prize} USD</code></b>"
    else:
        winner_mention = f"<a href='tg://user?id={winners[0]}'><b>{escape_html(results[winners[0]]['name'])}</b></a>"
        result_text += f"🎉 <b>{winner_mention} wins <code>{pool} USD</code>!</b>"
    result_text += GAME_FOOTER
    del active_card_games[chat_id]
    await reveal_msg.edit(result_text, parse_mode='html')
    if not event.is_private:
        schedule_game_cleanup(reveal_msg.client, event.chat_id, reveal_msg)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cancelgame(?:@\w+)?$', 'bot1')))
async def cancel_cardgame_handler(event):
    if event.is_private: return
    chat_id = event.chat_id
    if chat_id not in active_card_games: return await _out(event, "❌ <b>No game to cancel.</b>", parse_mode='html')
    game = active_card_games[chat_id]
    if event.sender_id != game["host_id"] and event.sender_id != OWNER_ID: return await _out(event, "❌ <b>Only the host can cancel.</b>", parse_mode='html')
    for pid in game["players"].keys(): await users_catcher_col.update_one({"user_id": pid}, {"$inc": {"wallet_balance": game["bet"]}})
    await bot3_treasury_adjust(usd=-(game["bet"] * len(game["players"])))
    bet_amount = game["bet"]
    del active_card_games[chat_id]
    await _out(event, f"🎯 <b>GAME CANCELLED</b>\nRefunded <code>{bet_amount} USD</code> to all players.", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]flip(?:@\w+)?(?:\s+(ခေါင်း|ပန်း)\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def coin_flip_handler(event):
    user_id = event.sender_id
    choice = event.pattern_match.group(1)
    bet_str = event.pattern_match.group(2)
    
    if not choice or not bet_str:
        return await _out(event, f"🪙 ခေါင်း/ပန်း ရွေးပြီး ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/flip ခေါင်း 1</code> (သို့) <code>/flip ပန်း 1</code>", parse_mode='html')
    
    bet_amount = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet_amount > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet_amount * SPIN_BURN_RATE, 2)
    
    # Burn အတွက် သီးခြားနှုတ်မယ်
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    # ကျန်တဲ့ လောင်းငွေကို နှုတ်မယ်
    if not await try_deduct_bet_bot3(event, user_id, bet_amount):
        return await _out(event, "❌ <b>Insufficient balance!</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet_amount)
    
    result = random.choice(["ခေါင်း", "ပန်း"])
    mention = await get_html_mention(event, user_id)
    
    try:
        spin_msg = await _out(event, "🪙 <b>Flipping...</b>", parse_mode='html')
        await asyncio.sleep(0.5)
        try:
            await spin_msg.edit("<b>🪙 ↻</b>", parse_mode='html')
        except Exception:
            pass
        await asyncio.sleep(0.5)
    except FloodWaitError:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Too many people playing right now — your bet was refunded. Try again in a few seconds.</b>", parse_mode='html')
    except Exception:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Something went wrong — your bet was refunded.</b>", parse_mode='html')
    
    if choice == result:
        # 🐋 Whale Check
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
        is_whale = whale_balance > WEALTH_THRESHOLD
        
        raw_win = bet_amount * 2
        if is_whale:
            raw_win, whale_note = apply_whale_tax(whale_balance, raw_win)
            penalty_text = whale_note
        else:
            penalty_text = ""
        
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": raw_win}})
        await bot3_treasury_adjust(usd=-(raw_win))
        caption_text = f"🪙 {mention} <b>YOU WON!</b>\n✨ Result: [ <b>{result}</b> ]\n🎉 You guessed right! <code>+{raw_win:.2f} USD</code>"
        if burn > 0:
            caption_text += f"\n🔥 <b>ကာစီနို ဆော့ခ:</b> <code>-{burn:.2f} USD</code>"
        caption_text += penalty_text
    else:
        caption_text = f"🪙 {mention} <b>YOU LOST.</b>\n💨 Result: [ <b>{result}</b> ]\n💸 You guessed wrong. <code>-{bet_amount:.2f} USD</code>"
        if burn > 0:
            caption_text += f"\n🔥 <b>ကာစီနို ဆော့ခ:</b> <code>-{burn:.2f} USD</code>"
    
    caption_text += GAME_FOOTER
    try:
        await spin_msg.edit(caption_text, parse_mode='html')
    except Exception:
        try:
            await _out(event, caption_text, parse_mode='html')
        except Exception:
            pass
    if not event.is_private:
        schedule_game_cleanup(spin_msg.client, event.chat_id, spin_msg)
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]dice(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def dice_game_handler(event):
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, f"🎲 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/dice 1</code>", parse_mode='html')
    
    bet_amount = round(float(bet_str), 2)
    if bet_amount <= 0:
        return await _out(event, "<b>အနည်းဆုံး 0.01 USD လောင်းပါ။</b>", parse_mode='html')
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet_amount > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet_amount * SPIN_BURN_RATE, 2)
    
    # Burn အတွက် သီးခြားနှုတ်မယ်
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    # ကျန်တဲ့ လောင်းငွေကို နှုတ်မယ်
    if not await try_deduct_bet_bot3(event, user_id, bet_amount):
        return await _out(event, "❌ <b>Insufficient balance!</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet_amount)
    
    chat_id = event.chat_id
    try:
        dice_msg = await _out(event, "🎲 <b>Rolling...</b>", parse_mode='html')
        await asyncio.sleep(0.5)
        try:
            await dice_msg.edit("<b>🎲 ↻</b>", parse_mode='html')
        except Exception:
            pass
        await asyncio.sleep(1.0)
    except FloodWaitError:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Too many people playing right now — your bet was refunded. Try again in a few seconds.</b>", parse_mode='html')
    except Exception:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Something went wrong — your bet was refunded.</b>", parse_mode='html')
    
    dice_value = random.randint(1, 6)
    mention = await get_html_mention(event, user_id)
    
    if dice_value >= 4:
        # 🐋 Whale Check
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
        is_whale = whale_balance > WEALTH_THRESHOLD
        
        raw_win = bet_amount * 2
        if is_whale:
            raw_win, whale_note = apply_whale_tax(whale_balance, raw_win)
            penalty_text = whale_note
        else:
            penalty_text = ""
        
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": raw_win}})
        await bot3_treasury_adjust(usd=-(raw_win))
        result_msg = await _out(event, f"🎉 {mention} <b>YOU WIN!</b> Dice: {dice_value}\n🪙 Added: <code>+{raw_win:.2f} USD</code>", parse_mode='html')
        if burn > 0:
            await result_msg.edit(f"{result_msg.text}\n🔥 <b>ကာစီနို ဆော့ခ:</b> <code>-{burn:.2f} USD</code>{penalty_text}{GAME_FOOTER}", parse_mode='html')
    else:
        result_msg = await _out(event, f"💸 {mention} <b>YOU LOSE!</b> Dice: {dice_value}\n🪙 Deducted: <code>-{bet_amount:.2f} USD</code>", parse_mode='html')
        if burn > 0:
            await result_msg.edit(f"{result_msg.text}\n🔥 <b>ကာစီနို ဆော့ခ:</b> <code>-{burn:.2f} USD</code>{GAME_FOOTER}", parse_mode='html')
    
    if not event.is_private:
        schedule_game_cleanup(result_msg.client, event.chat_id, result_msg)
        
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]hilo(?:@\w+)?(?:\s+(\d+(?:\.\d+))?)?$', 'bot1')))
async def hilo_game_handler(event):
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, f"🃏 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/hilo 1</code>", parse_mode='html')
    
    bet_amount = round(float(bet_str), 2)
    if bet_amount <= 0:
        return await _out(event, "❌ <b>အနည်းဆုံး 0.01 USD လောင်းပါ။</b>", parse_mode='html')
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet_amount > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet_amount * SPIN_BURN_RATE, 2)
    
    # Burn အတွက် သီးခြားနှုတ်မယ်
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    # လောင်းငွေကို နှုတ်မယ်
    if not await try_deduct_bet_bot3(event, user_id, bet_amount):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"❌ <b>Insufficient balance! You have {balance} USD</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet_amount)
    
    base_card = random.randint(2, 12)
    card_map = {1: "A", 11: "J", 12: "Q", 13: "K"}
    base_display = base_card if base_card <= 10 else card_map.get(base_card, str(base_card))
    
    mention = await get_html_mention(event, user_id)
    
    buttons = [
        [Button.inline("📈 Higher", data=f"hilo_HIGH_{base_card}_{bet_amount}_{user_id}"),
         Button.inline("📉 Lower", data=f"hilo_LOW_{base_card}_{bet_amount}_{user_id}")]
    ]
    
    await _out(
        event,
        f"🃏 <b>HI-LO GAME</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet_amount)}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ (2%):</b> <code>{format_usd(burn)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎴 <b>လက်ရှိကတ်:</b> <code>[ {base_display} ]</code>\n\n"
        f"<b>ဘယ်ကိုရွေးမလဲ?</b>",
        buttons=buttons,
        parse_mode='html'
    )
    
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]daily(?:@\w+)?$', 'bot1')))
async def daily_bounty_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    now = time.time()
    last_daily = user_doc.get("last_daily", 0)
    streak = user_doc.get("daily_streak", 0)
    if now - last_daily < 86400:
        rem_time = int(86400 - (now - last_daily))
        return await event.reply(f"⏳ {mention} <b>You already claimed today!</b> Next claim in {str(timedelta(seconds=rem_time))}.", parse_mode='html')
    if now - last_daily > 172800: streak = 0
    new_streak = streak + 1
    # 🔺 BUMPED x1000 (per owner request, Aug 2026) — see the matching note on
    # _RARITY_VALUE_MAP above for why (Star now pegged at 1⭐ = 1,000,000 USD).
    base_bonus = round(random.randint(20000000, 500000000) / MMK_PER_USD, 2)
    streak_bonus = round(min(new_streak * 20000000, 300000000) / MMK_PER_USD, 2)
    bonus = base_bonus + streak_bonus
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bonus}, "$set": {"last_daily": now, "daily_streak": new_streak, "fullname": plain_name}})
    newly_earned = await check_and_award_achievements(user_id)
    reply_text = f"🎁 {mention} <b>Daily bonus claimed! <code>+{bonus} USD</code></b>\n🔥 <b>{new_streak} day streak</b> — Streak Bonus: <code>+{streak_bonus} USD</code>"
    reply_text += format_achievement_unlocks(newly_earned)
    await event.reply(reply_text, parse_mode='html')

# ==========================================
# ==========================================
# 💰 RICHEST LEADERBOARD (TOP 10 ONLY — NO PAGINATION)
# ==========================================
# 🩹 CHANGED (per owner request): this used to paginate through EVERY single player with a
# positive wallet_balance (5 per page) — with ~1,586 active players that's well over 300
# pages for what's supposed to be a leaderboard. Now it just shows the top 10, full stop,
# same as /top and /gtop.
RICHEST_TOP_N = 10

async def render_richest_page():
    """Render the top RICHEST_TOP_N richest players. No pagination."""
    pipeline = [
        {"$match": {"wallet_balance": {"$gt": 0}}},
        {"$project": {
            "user_id": 1,
            "fullname": 1,
            "wallet_balance": 1,
            "star_balance": 1,
            # 🩹 FIX: plain {"$size": "$harem"} throws and aborts the WHOLE aggregation the
            # moment it hits any user doc that's missing "harem" entirely (legacy accounts
            # created before that field existed, or via a path that skipped ensure_user_
            # registered's $setOnInsert default) — which silently broke /richest for
            # everyone, not just that one user. $ifNull falls back to an empty array first.
            "cards": {"$size": {"$ifNull": ["$harem", []]}}
        }},
        {"$sort": {"wallet_balance": -1}},
        {"$limit": RICHEST_TOP_N}
    ]
    users = await users_catcher_col.aggregate(pipeline).to_list(length=RICHEST_TOP_N)

    if not users:
        return "🏆 <b>No wealthy players yet!</b>"

    # Header
    text = f"💰 <b>TOP {len(users)} RICHEST PLAYERS</b>\n\n"

    # Build each user row
    for idx, u in enumerate(users, start=1):
        # Safe conversion for balances (fix string issues)
        try:
            bal = float(u.get("wallet_balance", 0))
        except (ValueError, TypeError):
            bal = 0.0

        try:
            star = float(u.get("star_balance", 0))
        except (ValueError, TypeError):
            star = 0.0

        cards = u.get("cards", 0)

        # User mention
        name = clean_display_name(u.get('fullname'), fallback=f"User {u['user_id']}")
        mention = f"<a href='tg://user?id={u['user_id']}'>{escape_html(name)}</a>"

        # Format: '1' Name
        # 💵 $10,000.00 | ⭐ 500 | 🎴 50
        # ----------
        text += f"<b>'{idx}'</b> {mention}\n"
        text += f"💵 {format_usd(bal)} | ⭐ {format_star_plain(star)} | 🎴 {cards:,}\n"
        text += f"----------\n"

    return text


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]richest(?:@\w+)?$', 'bot1')))
async def richest_paginated_handler(event):
    """Handle /richest command — shows the top 10 richest players, no pagination."""
    try:
        text = await render_richest_page()
    except Exception as e:
        print(f"❌ /richest error: {e}")
        return await event.reply("⚠️ <b>Richest leaderboard ကို ခေတ္တ ဖော်ပြလို့မရသေးပါ — ထပ်ကြိုးစားကြည့်ပါ။</b>", parse_mode='html')
    await event.reply(text, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]gamble(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def high_risk_gamble_handler(event):
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, f"🎲 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/gamble 1</code>", parse_mode='html')
    
    bet_amount = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet_amount > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet_amount < 0.01:
        return await _out(event, f"❌ <b>အနည်းဆုံး 0.01 USD လောင်းပါ။</b>", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet_amount * SPIN_BURN_RATE, 2)
    
    # Burn အတွက် သီးခြားနှုတ်မယ်
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    # လောင်းငွေကို နှုတ်မယ်
    if not await try_deduct_bet_bot3(event, user_id, bet_amount):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"❌ <b>Insufficient balance! You have {format_usd(balance)}</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet_amount)
    
    mention = await get_html_mention(event, user_id)
    
    # 🎬 Animation
    try:
        suspense_msg = await _out(event, "🎲 <b>Rolling the dice of fate...</b>", parse_mode='html')
        await asyncio.sleep(0.5)
        try:
            await suspense_msg.edit("<b>🎲 ⚀</b>", parse_mode='html')
        except Exception:
            pass
        await asyncio.sleep(0.5)
        try:
            await suspense_msg.edit("<b>🎲 ⚂</b>", parse_mode='html')
        except Exception:
            pass
        await asyncio.sleep(0.5)
    except FloodWaitError:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Too many people playing right now — your bet was refunded. Try again in a few seconds.</b>", parse_mode='html')
    except Exception:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": bet_amount + burn}})
        await bot3_treasury_adjust(usd=-(bet_amount + burn))
        return await _out(event, "⚠️ <b>Something went wrong — your bet was refunded.</b>", parse_mode='html')
    
    # 🎲 ရလဒ်
    win = random.choice([True, False])
    
    # 🐋 Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD
    
    result_text = ""
    whale_text = ""
    payout = 0
    net = 0
    
    if win:
        raw_win = bet_amount * 2
        if is_whale:
            raw_win, whale_text = apply_whale_tax(whale_balance, raw_win)
        payout = raw_win
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": payout}})
        await bot3_treasury_adjust(usd=-(payout))
        result_text = f"🎉 <b>RISK WON!</b> <code>+{format_usd(payout)}</code>"
        net = round(payout - bet_amount - burn, 2)
    else:
        result_text = f"💸 <b>RISK LOST.</b> <code>-{format_usd(bet_amount)}</code>"
        net = round(-bet_amount - burn, 2)
    
    # 📊 Final Message
    net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
    
    final_message = (
        f"🎲 <b>GAMBLE RESULT</b>\n"
        f"━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet_amount)}</code>\n"
        f"🔥 <b>ကာစီနိုကစားခ (2%):</b> <code>{format_usd(burn)}</code>\n"
        f"━━━━━━━━━━\n"
        f"{result_text}\n"
        f"📊 <b>အသားတင် (Net):</b> <code>{net_display}</code>"
        f"{whale_text}"
        f"\n━━━━━━━━━\n"
        f"{GAME_FOOTER}"
    )
    
    try:
        await suspense_msg.edit(final_message, parse_mode='html')
    except Exception:
        try:
            await _out(event, final_message, parse_mode='html')
        except Exception:
            pass
    
    if not event.is_private:
        schedule_game_cleanup(suspense_msg.client, event.chat_id, suspense_msg)
# ---- MINES ----
# 5x5 grid, 5 hidden bombs among 20 safe tiles. Tap a hidden tile to reveal it — each safe
# reveal raises the payout multiplier; tap a bomb and the whole bet is gone. The player picks
# when to Cash Out, same idea as the popular "Mines" games on other casino-style bots.
MINES_GRID_SIZE = 25  # 5x5
MINES_BOMB_COUNT = 7  # 20 safe tiles
MINES_HOUSE_EDGE = 0.97  # ~3% house edge, in line with a typical odds-based casino game
active_mines_games = bot_state.active_mines_games
_mines_game_counter = 0

def _mines_fair_multiplier(safe_revealed, total=MINES_GRID_SIZE, bombs=MINES_BOMB_COUNT):
    if safe_revealed <= 0:
        return 1.0
    safe = total - bombs
    survive_prob = 1.0
    for i in range(safe_revealed):
        survive_prob *= (safe - i) / (total - i)
    fair = 1 / survive_prob

    # စိန်ဖွင့်ပြီးသား အချိုးအစား (0 → 1)
    progress = safe_revealed / safe

    # house edge factor ကို ပိုတင်းကျပ်အောင် ချိန်ညှိထားတယ်
    # စောစောပိုင်းမှာ 0.65၊ နောက်ကျရင် 0.88 အထိ ချဉ်းကပ်
    edge_factor = 0.65 + 0.23 * progress

    # ပိုပြီး ဖောင်းပွမှုကို ထိန်းချုပ်ဖို့ multiplier ကို အများဆုံး ၈x လောက်ထိ ကန့်သတ်ထားတယ်
    raw_multiplier = fair * edge_factor
    return round(min(raw_multiplier, 8.0), 2)

def _render_mines_board(game, game_id, final=False, hit_idx=None):
    safe_total = MINES_GRID_SIZE - MINES_BOMB_COUNT
    safe_revealed = len(game["revealed"])
    multiplier = _mines_fair_multiplier(safe_revealed)
    potential_payout = round(game["bet"] * multiplier, 2)
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx in game["revealed"]:
                label = "💎"
            elif final and idx in game["bombs"]:
                label = "💥" if idx == hit_idx else "💣"
            elif final:
                label = "🟤"
            else:
                label = "🟡"
            cb = f"minesnoop_{game_id}" if (final or idx in game["revealed"]) else f"minestap_{game_id}_{idx}"
            row.append(Button.inline(label, data=cb))
        rows.append(row)
    if not final:
        cashout_label = f"💰 ငွေထုတ်တော့မယ် ({potential_payout:,} USD)" if safe_revealed > 0 else "💰 Cash Out"
        rows.append([Button.inline(cashout_label, data=f"minescash_{game_id}")])
    text = (
        f"💣 <b>ဗုံးရှောင်ဂိမ်း</b>\n"
        f"👤 <b>ကစားသမား −</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ −</b> <code>{game['bet']:,} USD</code>\n"
        f"💎 <b>ဖွင့်ပြီးသား −</b> <code>{safe_revealed} / {safe_total}</code>\n"
        f"📈 <b>လက်ရှိ အမြတ်ဆတိုးနှုန်း −</b> <code>x{multiplier}</code>\n"
        f"<i>Box ကိုနှိပ်ပြီး ဆက်ကစားမလား၊ ငွေထုတ်မလား ရွေးပါ။</i>"
    )
    return text, rows
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mines(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def mines_game_handler(event):
    global _mines_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, f"💣 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/mines 1</code>", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet <= 0:
        return await _out(event, "<b>အနည်းဆုံး 0.01 USD လောင်းပါ။</b>", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"<b>မင်းမှာ {format_usd(balance)} ပဲရှိတယ်နော်!</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _mines_game_counter += 1
    game_id = _mines_game_counter
    bombs = set(random.sample(range(MINES_GRID_SIZE), MINES_BOMB_COUNT))
    game = {
        "user_id": user_id,
        "bet": bet,
        "burn": burn,
        "bombs": bombs,
        "revealed": set(),
        "chat_id": event.chat_id,
        "mention": mention,
        "start_time": time.time()
    }
    active_mines_games[game_id] = game
    text, rows = _render_mines_board(game, game_id)
    await _out(event, text, parse_mode='html', buttons=rows)


@bot1.on(events.CallbackQuery(pattern=r'^minestap_(\d+)_(\d+)$'))
async def mines_tap_handler(event):
    game_id = int(event.pattern_match.group(1))
    idx = int(event.pattern_match.group(2))
    game = active_mines_games.get(game_id)
    
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    if idx in game["revealed"]:
        return await event.answer()
    if idx in game["bombs"]:
        active_mines_games.pop(game_id, None)
        safe_total = MINES_GRID_SIZE - MINES_BOMB_COUNT
        _, rows = _render_mines_board(game, game_id, final=True, hit_idx=idx)
        text = (
            f"💣 <b>MINES — 💥 ဗုံးနင်းမိပြီ!</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
            f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(game['bet'])}</code>\n"
            f"🔥 <b>ကာစီနို ဆော့ခ:</b> <code>{format_usd(game['burn'])}</code>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"💎 <b>ဖွင့်နိုင်ခဲ့တာ:</b> <code>{len(game['revealed'])} / {safe_total}</code>\n"
            f"🐸 <b>လောင်းထားတဲ့ {format_usd(game['bet'])} လုံးဝ ရှုံးသွားပါပြီ။</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"<i>နောက်တစ်ခါ ကံကောင်းပါစေ!</i>"
        )
        await event.edit(text, parse_mode='html', buttons=rows)
        await event.answer("💥 ဗုံးနင်းမိပြီ!")
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id)
        return
    
    game["revealed"].add(idx)
    safe_total = MINES_GRID_SIZE - MINES_BOMB_COUNT
    
    # 🔥 3 diamonds minimum before cashout
    MIN_REVEALS_FOR_CASHOUT = 3
    if len(game["revealed"]) >= safe_total:
        await _mines_cash_out(event, game_id, auto=True)
        return
    
    text, rows = _render_mines_board(game, game_id)
    
    # ⚠️ ငွေထုတ်ဖို့ အနည်းဆုံး ၃ လုံးဖွင့်ရမယ်ဆိုတဲ့ သတိပေးချက်
    if len(game["revealed"]) < MIN_REVEALS_FOR_CASHOUT:
        text += f"\n⚠️ <i>ငွေထုတ်ဖို့ အနည်းဆုံး {MIN_REVEALS_FOR_CASHOUT} လုံးဖွင့်ရမယ်။ (လက်ရှိ {len(game['revealed'])}/{MIN_REVEALS_FOR_CASHOUT})</i>"
    
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer("💎 လုံခြုံပါတယ်!")


async def _mines_cash_out(event, game_id, auto=False):
    game = active_mines_games.pop(game_id, None)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    
    safe_total = MINES_GRID_SIZE - MINES_BOMB_COUNT
    safe_revealed = len(game["revealed"])
    
    # 🛡️ အနည်းဆုံး ၃ လုံးဖွင့်ပြီးမှ ငွေထုတ်ခွင့်ရမယ်
    MIN_REVEALS_FOR_CASHOUT = 3
    if safe_revealed < MIN_REVEALS_FOR_CASHOUT and not auto:
        return await event.answer(f"⚠️ အနည်းဆုံး {MIN_REVEALS_FOR_CASHOUT} လုံးဖွင့်မှ ငွေထုတ်လို့ရမယ်။ လက်ရှိ {safe_revealed} လုံးပဲဖွင့်ရသေးတယ်။", alert=True)
    
    # 🐋 Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": game["user_id"]})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD
    
    # 📈 Multiplier တွက်ချက်ပုံ (အနည်းဆုံး ၃ လုံးမှ ၁.၅x ခွဲတိုးမယ်)
    if safe_revealed >= MIN_REVEALS_FOR_CASHOUT:
        base_multiplier = 1.0
        extra_reveals = safe_revealed - MIN_REVEALS_FOR_CASHOUT
        multiplier = 1.0 + (extra_reveals * 0.5)  # တစ်လုံးတိုးတိုင်း ၀.၅x တိုး
        multiplier = round(multiplier, 2)
    else:
        multiplier = 1.0
    
    # 🐋 Whale penalty
    if is_whale and multiplier > 1.0:
        raw_payout = round(game["bet"] * multiplier, 2)
        payout, whale_text = apply_whale_tax(whale_balance, raw_payout)
    else:
        payout = round(game["bet"] * multiplier, 2)
        whale_text = ""
    
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net_gain = round(payout - game["bet"] - game.get("burn", 0), 2)
    sign = "+" if net_gain >= 0 else ""
    
    header = "🏆 <b>Box အားလုံး ဖွင့်ပြီးပြီ — အများဆုံး ရလိုက်ပြီ!</b>" if auto else "💰 <b>ငွေရှင်းသိမ်းလိုက်ပြီ!</b>"
    
    text = (
        f"💣 <b>MINES — CASH OUT</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(game['bet'])}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ:</b> <code>{format_usd(game.get('burn', 0))}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"💎 <b>ဖွင့်ပြီးသား:</b> <code>{safe_revealed} / {safe_total}</code>\n"
        f"📈 <b>Multiplier:</b> <code>x{multiplier}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{header}\n"
        f"🔄 <b>ရငွေ:</b> <code>{format_usd(payout)}</code>\n"
        f"📊 <b>အမြတ်/အရှုံး:</b> <code>{sign}{format_usd(abs(net_gain))}</code>"
        f"{whale_text}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{GAME_FOOTER}"
    )
    
    _, rows = _render_mines_board(game, game_id, final=True)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer("💰 Cashed out!")
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id)


@bot1.on(events.CallbackQuery(pattern=r'^minescash_(\d+)$'))
async def mines_cashout_handler(event):
    game_id = int(event.pattern_match.group(1))
    game = active_mines_games.get(game_id)
    
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    
    MIN_REVEALS_FOR_CASHOUT = 3
    if len(game["revealed"]) < MIN_REVEALS_FOR_CASHOUT:
        return await event.answer(f"⚠️ အနည်းဆုံး {MIN_REVEALS_FOR_CASHOUT} လုံးဖွင့်မှ ငွေထုတ်လို့ရမယ်။ လက်ရှိ {len(game['revealed'])} လုံးပဲဖွင့်ရသေးတယ်။", alert=True)
    
    if len(game["revealed"]) == 0:
        return await event.answer("⚠️ Box တစ်ခုမှ မဖွင့်ရသေးဘူး — အနည်းဆုံး တစ်ခု ဖွင့်ပါ။", alert=True)
    
    await _mines_cash_out(event, game_id, auto=False)


@bot1.on(events.CallbackQuery(pattern=r'^minesnoop_(\d+)$'))
async def mines_noop_handler(event):
    await event.answer()

# ---- PLINKO (ပလင်ကို) ----
PLINKO_ROWS = 8
PLINKO_MULTIPLIERS = [0.5, 0.7, 1.0, 1.5, 2.0, 1.5, 1.0, 0.7, 0.5]
active_plinko_games = {}
_plinko_game_counter = 0
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:plinko|p)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def plinko_cmd_handler(event):
    global _plinko_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /plinko 10 သို့မဟုတ် /p 10", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet <= 0:
        return await _out(event, "အနည်းဆုံး ၀.၀၁ USD လောင်းပါ။", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {format_usd(balance)} သာရှိသည်။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _plinko_game_counter += 1
    game_id = _plinko_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "burn": burn,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "start_time": time.time()
    }
    active_plinko_games[game_id] = game
    
    text = (
        f"🔴 <b>PLINKO</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet)}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ (2%):</b> <code>{format_usd(burn)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>ဘောလုံးကို အောက်က ခလုတ်နှိပ်ပြီး ချလိုက်ပါ။</i>"
    )
    buttons = [[Button.inline("🔴 ဘောလုံးချမယ်", data=f"plinko_drop_{game_id}")]]
    await _out(event, text, parse_mode='html', buttons=buttons)


@bot1.on(events.CallbackQuery(pattern=r'^plinko_drop_(\d+)$'))
async def plinko_drop_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_plinko_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /plinko နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။ ခဏစောင့်ပါ။", alert=False)
    
    # 🛡️ အနည်းဆုံး ၃ ခါကျအောင် ဆက်ကစားရမယ်
    MIN_DROPS_FOR_CASHOUT = 3
    game["drops"] = game.get("drops", 0) + 1
    current_drop = game["drops"]
    
    # 🐋 Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": game["user_id"]})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD
    
    position = 4
    path = []
    pos_history = [4]
    
    for _ in range(PLINKO_ROWS):
        direction = random.choice(["ဘယ်", "ညာ"])
        path.append(direction)
        if direction == "ညာ":
            position += 1
        else:
            position -= 1
        position = max(0, min(len(PLINKO_MULTIPLIERS) - 1, position))
        pos_history.append(position)
    
    bet = game['bet']
    
    for step in range(1, PLINKO_ROWS + 1):
        current_pos = pos_history[step]
        lines = []
        for row in range(step + 1):
            width = row + 1
            ball_at = pos_history[row] if row <= step else None
            slots = []
            for col in range(width):
                if ball_at == col:
                    slots.append("⬤")
                else:
                    slots.append("·")
            indent = "  " * (PLINKO_ROWS - row)
            lines.append(indent + " ".join(slots))
        
        anim_text = (
            f"🔴 <b>PLINKO</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
            f"💵 <b>လောင်းငွေ:</b> {format_usd(bet)}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            + "\n".join(lines) +
            f"\n━━━━━━━━━━━━━━━━━━━━\n"
            f"အဆင့် {step}/{PLINKO_ROWS}"
        )
        try:
            await event.edit(anim_text, parse_mode='html', buttons=None)
            await asyncio.sleep(0.3)
        except Exception:
            pass
    
    multiplier = PLINKO_MULTIPLIERS[position]
    raw_payout = round(bet * multiplier, 2)
    
    if is_whale and multiplier > 1.0:
        payout, whale_text = apply_whale_tax(whale_balance, raw_payout)
    else:
        payout = raw_payout
        whale_text = ""
    
    # ပထမ ၃ ခါကျတဲ့အထိ multiplier ကို ၁.၀ ပဲထားမယ်
    if current_drop < MIN_DROPS_FOR_CASHOUT:
        payout = bet
        multiplier = 1.0
        whale_text = ""
    
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    # အနည်းဆုံး ၃ ခါ ပြည့်သွားရင် ဆက်ကစားခွင့်ရှိမရှိစစ်
    if current_drop < MIN_DROPS_FOR_CASHOUT:
        game["drops"] = current_drop
        active_plinko_games[game_id] = game
        text = (
            f"🔴 <b>PLINKO</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
            f"💵 <b>လောင်းငွေ:</b> {format_usd(bet)}\n"
            f"🔥 <b>ကာစီနို ဆော့ခ:</b> {format_usd(game['burn'])}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🎯 <b>ကျသွားသည့်နေရာ:</b> အမှတ် {position} (မြှောက်ကိန်း x{multiplier})\n"
            f"🔄 <b>ရငွေ:</b> {format_usd(payout)}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ <i>ငွေထုတ်ဖို့ အနည်းဆုံး {MIN_DROPS_FOR_CASHOUT} ခါကျရမယ်။ (လက်ရှိ {current_drop}/{MIN_DROPS_FOR_CASHOUT})</i>\n\n"
            f"ဆက်ကျမလား ဒါမှမဟုတ် ငွေထုတ်မလား?"
        )
        buttons = [
            [Button.inline("🔴 ထပ်ကျမယ်", data=f"plinko_drop_{game_id}")],
            [Button.inline("💰 ငွေထုတ်မယ်", data=f"plinko_cashout_{game_id}")]
        ]
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer(f"အကြိမ် {current_drop}/{MIN_DROPS_FOR_CASHOUT}")
        return
    
    # ၃ ခါပြည့်သွားရင် ငွေထုတ်ခွင့်ရပြီ
    game["drops"] = current_drop
    active_plinko_games[game_id] = game
    
    net = round(payout - bet - game.get("burn", 0), 2)
    net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
    path_str = " → ".join(path)
    
    text = (
        f"🔴 <b>PLINKO</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> {format_usd(bet)}\n"
        f"🔥 <b>ကာစီနို ဆော့ခ:</b> {format_usd(game['burn'])}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🔴 <b>ဘောလုံးလမ်းကြောင်း:</b> {path_str}\n"
        f"🎯 <b>ကျသွားသည့်နေရာ:</b> အမှတ် {position} (မြှောက်ကိန်း x{multiplier})\n"
        f"🔄 <b>ရငွေ:</b> {format_usd(payout)}\n"
        f"📊 <b>အသားတင်:</b> <code>{net_display}</code>"
        f"{whale_text}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{GAME_FOOTER}"
    )
    buttons = [[Button.inline("🔄 အသစ်စပါ", data=f"plinko_new_{game_id}")]]
    await event.edit(text, parse_mode='html', buttons=buttons)
    await event.answer("ဘောလုံးကျသွားပြီ။")
    
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)


@bot1.on(events.CallbackQuery(pattern=r'^plinko_cashout_(\d+)$'))
async def plinko_cashout_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_plinko_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    MIN_DROPS_FOR_CASHOUT = 3
    drops = game.get("drops", 0)
    
    if drops < MIN_DROPS_FOR_CASHOUT:
        return await event.answer(f"⚠️ အနည်းဆုံး {MIN_DROPS_FOR_CASHOUT} ခါကျမှ ငွေထုတ်လို့ရမယ်။ လက်ရှိ {drops} ခါပဲကျသေးတယ်။", alert=True)
    
    # နောက်ဆုံးကျခဲ့တဲ့ payout ကိုရယူမယ်
    payout = game.get("last_payout", game["bet"])
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"] - game.get("burn", 0), 2)
    net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
    
    active_plinko_games.pop(game_id, None)
    
    text = (
        f"🔴 <b>PLINKO — CASH OUT</b>\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> {format_usd(game['bet'])}\n"
        f"🔥 <b>​ဆော့ခ:</b> {format_usd(game.get('burn', 0))}\n"
        f"💰 <b>ရငွေ:</b> {format_usd(payout)}\n"
        f"📊 <b>အသားတင်:</b> <code>{net_display}</code>\n"
        f"{GAME_FOOTER}"
    )
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer("ငွေထုတ်ပြီးပါပြီ။")


@bot1.on(events.CallbackQuery(pattern=r'^plinko_new_(\d+)$'))
async def plinko_new_callback(event):
    await event.answer("🔄 /plinko နဲ့ အသစ်စပါ။", alert=True)
# ---- BLACKJACK (၂၁ ကောင်း) ----
# ကတ်အုပ်စု (အမှတ်၊ သင်္ကေတ)
CARD_SUITS = ["♠", "♥", "♦", "♣"]
CARD_RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
CARD_VALUES = {
    "A": [1, 11], "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7,
    "8": 8, "9": 9, "10": 10, "J": 10, "Q": 10, "K": 10
}
BJ_MIN_BET = 0.5
active_blackjack_games = {}
_bj_game_counter = 0

def _create_deck():
    deck = []
    for suit in CARD_SUITS:
        for rank in CARD_RANKS:
            deck.append({"rank": rank, "suit": suit})
    random.shuffle(deck)
    return deck

def _card_value(rank, soft=False):
    if rank == "A":
        return 11 if soft else 1
    return CARD_VALUES[rank]

def _hand_value(hand):
    total = 0
    aces = 0
    for card in hand:
        rank = card["rank"]
        if rank == "A":
            aces += 1
            total += 11
        else:
            total += CARD_VALUES[rank]
    while total > 21 and aces > 0:
        total -= 10
        aces -= 1
    return total

def _hand_display(hand, hidden=False):
    if hidden:
        return f"[{hand[0]['rank']}{hand[0]['suit']}] [?]"
    return " ".join([f"[{c['rank']}{c['suit']}]" for c in hand])

def _render_bj_board(game, dealer_hidden=True, game_over=False, message=""):
    player_hand = game["player_hand"]
    dealer_hand = game["dealer_hand"]
    bet = game["bet"]
    burn = game.get("burn", 0)
    
    player_val = _hand_value(player_hand)
    dealer_val = _hand_value(dealer_hand) if not dealer_hidden else _hand_value([dealer_hand[0]])
    
    text = (
        f"🃏 <b>BLACKJACK</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> {format_usd(bet)}\n"
        f"🔥 <b>ကာစီနို ဆော့ခ:</b> {format_usd(burn)}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎴 <b>စတီဗင်ချောင်:</b> {_hand_display(dealer_hand, dealer_hidden)}\n"
    )
    
    if not dealer_hidden:
        text += f"📊 <b>စတီ​ဗင်​​​ ပေါင်း:</b> {dealer_val}\n"
    
    text += (
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎴 <b>သင့်ကတ်:</b> {_hand_display(player_hand)}\n"
        f"📊 <b>သင့်ပေါင်း:</b> {player_val}\n"
    )
    
    if message:
        text += f"\n{message}"
    
    if game_over:
        text += f"\n━━━━━━━━━━━━━━━━━━━━\n{GAME_FOOTER}"
        return text, None
    
    buttons = []
    if not game.get("stand"):
        row = []
        if player_val < 21:
            row.append(Button.inline("📥 Hit", data=f"bj_hit_{game['game_id']}"))
        row.append(Button.inline("🛑 Stand", data=f"bj_stand_{game['game_id']}"))
        buttons.append(row)
        if len(player_hand) == 2 and not game.get("doubled"):
            buttons.append([Button.inline("💎 Double Down", data=f"bj_double_{game['game_id']}")])
    
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:blackjack|bj)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def blackjack_cmd_handler(event):
    global _bj_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /bj 10", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet < BJ_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {BJ_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {format_usd(balance)} သာရှိသည်။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _bj_game_counter += 1
    game_id = _bj_game_counter
    
    deck = _create_deck()
    player_hand = [deck.pop(), deck.pop()]
    dealer_hand = [deck.pop(), deck.pop()]
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "burn": burn,
        "max_bet": 0,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "deck": deck,
        "player_hand": player_hand,
        "dealer_hand": dealer_hand,
        "stand": False,
        "doubled": False,
        "start_time": time.time()
    }
    active_blackjack_games[game_id] = game
    
    text, buttons = _render_bj_board(game, dealer_hidden=True, game_over=False)
    await _out(event, text, parse_mode='html', buttons=buttons)


@bot1.on(events.CallbackQuery(pattern=r'^bj_(hit|stand|double)_(\d+)$'))
async def blackjack_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    game_id = int(event.pattern_match.group(2))
    
    game = active_blackjack_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /bj နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။ ခဏစောင့်ပါ။", alert=False)
    
    if action == "stand":
        game["stand"] = True
    
    elif action == "hit":
        if game.get("stand"):
            return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
        new_card = game["deck"].pop()
        game["player_hand"].append(new_card)
        if _hand_value(game["player_hand"]) > 21:
            game["stand"] = True
    
    elif action == "double":
        if len(game["player_hand"]) != 2 or game.get("doubled"):
            return await event.answer("ဒီအချိန်မှာ Double Down မလုပ်နိုင်ပါ။", alert=True)
        if game["bet"] * 2 > game["max_bet"]:
            return await event.answer(f"ငွေမလုံလောက်ပါ။ နှစ်ဆဖို့ {format_usd(game['bet']*2)} လိုပါတယ်။", alert=True)
        if not await try_deduct_bet_bot3(event, game["user_id"], game["bet"]):
            return await event.answer("ငွေထပ်နှုတ်လို့မရပါ။", alert=True)
        await bot3_treasury_adjust(usd=game["bet"])
        game["bet"] *= 2
        game["doubled"] = True
        new_card = game["deck"].pop()
        game["player_hand"].append(new_card)
        game["stand"] = True
    
    # ---- ဂိမ်းပြီးဆုံးမှု စစ်ဆေးမယ် ----
    if game.get("stand") or _hand_value(game["player_hand"]) > 21:
        dealer_val = _hand_value(game["dealer_hand"])
        while dealer_val < 17:
            game["dealer_hand"].append(game["deck"].pop())
            dealer_val = _hand_value(game["dealer_hand"])
        
        player_val = _hand_value(game["player_hand"])
        result_msg = ""
        payout = 0
        
        # 🐋 Whale Check
        user_doc = await users_catcher_col.find_one({"user_id": game["user_id"]})
        whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
        is_whale = whale_balance > WEALTH_THRESHOLD
        
        if player_val > 21:
            result_msg = "သင့်ကတ်ပျက်သွားသည်။ ရှုံးသည်။"
            payout = 0
        elif dealer_val > 21:
            result_msg = "ဒိုင်လာပျက်သွားသည်။ သင်နိုင်သည်။"
            payout = game["bet"] * 2
        elif player_val > dealer_val:
            result_msg = f"သင်နိုင်သည် ({player_val} vs {dealer_val})"
            payout = game["bet"] * 2
        elif player_val < dealer_val:
            result_msg = f"သင်ရှုံးသည် ({player_val} vs {dealer_val})"
            payout = 0
        else:
            result_msg = f"အပြိုင် ({player_val} vs {dealer_val})"
            payout = game["bet"]
        
        # Whale penalty for win only
        whale_text = ""
        if is_whale and payout > game["bet"]:
            payout, whale_text = apply_whale_tax(whale_balance, payout)
        
        if payout > 0:
            await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
        await bot3_treasury_adjust(usd=-(payout))
        
        net = round(payout - game["bet"] - game.get("burn", 0), 2)
        net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
        
        game_over = True
        text = (
            f"🃏 <b>BLACKJACK</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
            f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(game['bet'])}</code>\n"
            f"🔥 <b>ကာစီနို ဆော့ခ (2%):</b> <code>{format_usd(game.get('burn', 0))}</code>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🎴 <b>ဒိုင်လာ:</b> {_hand_display(game['dealer_hand'], hidden=False)}\n"
            f"📊 <b>ဒိုင်လာပေါင်း:</b> {dealer_val}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🎴 <b>သင့်ကတ်:</b> {_hand_display(game['player_hand'])}\n"
            f"📊 <b>သင့်ပေါင်း:</b> {player_val}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{result_msg}\n"
            f"🔄 <b>ရငွေ:</b> {format_usd(payout)}\n"
            f"📊 <b>အသားတင်:</b> <code>{net_display}</code>"
            f"{whale_text}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{GAME_FOOTER}"
        )
        active_blackjack_games.pop(game_id, None)
        await event.edit(text, parse_mode='html', buttons=None)
        await event.answer("ဂိမ်းပြီးဆုံးပါပြီ။")
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
        return
    
    # ---- ဂိမ်းဆက်ကစားမယ် ----
    text, buttons = _render_bj_board(game, dealer_hidden=True, game_over=False)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()
        
# ---- CRASH GAME (ပြိုကျဂိမ်း) ----
CRASH_MIN_BET = 0.5
CRASH_MAX_MULTIPLIER = 100.0
CRASH_MULTIPLIER_STEP = 0.05  # တစ်ခါတိုးတိုင်း တိုးနှုန်း
CRASH_UPDATE_INTERVAL = 0.3   # စက္ကန့်
active_crash_games = {}
_crash_game_counter = 0

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:crash|c)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def crash_cmd_handler(event):
    global _crash_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /c 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    if bet < CRASH_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {CRASH_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    if balance < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {balance} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _crash_game_counter += 1
    game_id = _crash_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "multiplier": 1.00,
        "crashed": False,
        "cashed_out": False,
        "msg_id": None,
    }
    active_crash_games[game_id] = game
    
    text = f"ပြိုကျဂိမ်း\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\n\nမြှောက်ကိန်း - x1.00\n\nဘယ်အချိန်မဆို ငွေထုတ်နိုင်ပါတယ်။ မြှောက်ကိန်း တက်လေလေ အမြတ်များလေလေပါ။"
    buttons = [[Button.inline("ငွေထုတ်မယ်", data=f"crash_cashout_{game_id}")]]
    msg = await _out(event, text, parse_mode='html', buttons=buttons)
    game["msg_id"] = msg.id
    
    # နောက်ခံမှာ multiplier တက်နေအောင် လုပ်မယ်
    asyncio.create_task(_crash_loop(game_id))

async def _crash_loop(game_id):
    game = active_crash_games.get(game_id)
    if not game:
        return
    
    multiplier = 1.00
    while True:
        await asyncio.sleep(CRASH_UPDATE_INTERVAL)
        
        # ဂိမ်းပျက်သွားပြီလား စစ်ဆေးမယ်
        game = active_crash_games.get(game_id)
        if not game or game.get("cashed_out"):
            return
        
        # မြှောက်ကိန်း တိုးမယ် (ကျပန်း တိုးနှုန်း)
        step = CRASH_MULTIPLIER_STEP * random.uniform(0.8, 1.2)
        multiplier += step
        game["multiplier"] = round(multiplier, 2)
        
        # Crash ဖြစ်မလား ဆုံးဖြတ်မယ် (မြှောက်ကိန်းများလေ ပျက်ခြေများလေ)
        crash_prob = min(0.90, 0.05 + (multiplier - 1.0) * 0.008)
        if random.random() < crash_prob or multiplier >= CRASH_MAX_MULTIPLIER:
            game["crashed"] = True
            # ရလဒ်ပြမယ်
            text = f"ပြိုကျဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nမြှောက်ကိန်း - x{game['multiplier']}\n\nပြိုကျသွားပါပြီ။ လောင်းထားငွေ ဆုံးရှုံးသည်။"
            try:
                await bot1.edit_message(game["chat_id"], game["msg_id"], text, parse_mode='html', buttons=None)
            except Exception:
                pass
            active_crash_games.pop(game_id, None)
            return
        
        # ဂိမ်းရှိနေသေးရင် update လုပ်မယ်
        text = f"ပြိုကျဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nမြှောက်ကိန်း - x{game['multiplier']}\n\nဘယ်အချိန်မဆို ငွေထုတ်နိုင်ပါတယ်။"
        buttons = [[Button.inline("ငွေထုတ်မယ်", data=f"crash_cashout_{game_id}")]]
        try:
            await bot1.edit_message(game["chat_id"], game["msg_id"], text, parse_mode='html', buttons=buttons)
        except Exception:
            pass

@bot1.on(events.CallbackQuery(pattern=r'^crash_cashout_(\d+)$'))
async def crash_cashout_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_crash_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /c နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("cashed_out") or game.get("crashed"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    multiplier = game["multiplier"]
    payout = round(game["bet"] * multiplier, 2)
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    game["cashed_out"] = True
    net = round(payout - game["bet"], 2)
    result_text = f"ပြိုကျဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nမြှောက်ကိန်း - x{multiplier}\nရငွေ - {payout} USD\n"
    if net > 0:
        result_text += f"အမြတ် - +{net} USD"
    elif net < 0:
        result_text += f"အရှုံး - {net} USD"
    else:
        result_text += f"အပြိုင်"
    
    active_crash_games.pop(game_id, None)
    await event.edit(result_text, parse_mode='html', buttons=None)
    await event.answer("ငွေထုတ်ပြီးပါပြီ။")
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
# ---- ကျောက်/ကတ်ကြေး/စာရွက် (RPS) ----
RPS_MIN_BET = 0.5
active_rps_games = {}
_rps_game_counter = 0
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:rps)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def rps_cmd_handler(event):
    global _rps_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /rps 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet < RPS_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {RPS_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {format_usd(balance)} သာရှိသည်။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _rps_game_counter += 1
    game_id = _rps_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "burn": burn,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "done": False
    }
    active_rps_games[game_id] = game
    
    text = (
        f"🪨 <b>RPS (ကျောက်/ကတ်ကြေး/စာရွက်)</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet)}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ (2%):</b> <code>{format_usd(burn)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>အောက်က ရွေးချယ်စရာတစ်ခုကို နှိပ်ပါ။</i>"
    )
    buttons = [
        [
            Button.inline("🪨 ကျောက်", data=f"rps_play_{game_id}_ကျောက်"),
            Button.inline("✂️ ကတ်ကြေး", data=f"rps_play_{game_id}_ကတ်ကြေး"),
            Button.inline("📄 စာရွက်", data=f"rps_play_{game_id}_စာရွက်")
        ]
    ]
    await _out(event, text, parse_mode='html', buttons=buttons)


@bot1.on(events.CallbackQuery(pattern=r'^rps_play_(\d+)_(.+)$'))
async def rps_play_callback(event):
    game_id = int(event.pattern_match.group(1))
    player_choice = event.pattern_match.group(2)
    if isinstance(player_choice, bytes):
        player_choice = player_choice.decode('utf-8')
    
    game = active_rps_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /rps နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။ ခဏစောင့်ပါ။", alert=False)
    
    if game.get("done"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    # 🐋 Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": game["user_id"]})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD
    
    bot_choice = random.choice(["ကျောက်", "ကတ်ကြေး", "စာရွက်"])
    game["done"] = True
    
    win = False
    tie = False
    if player_choice == bot_choice:
        tie = True
    elif (player_choice == "ကျောက်" and bot_choice == "ကတ်ကြေး") or \
         (player_choice == "ကတ်ကြေး" and bot_choice == "စာရွက်") or \
         (player_choice == "စာရွက်" and bot_choice == "ကျောက်"):
        win = True
    
    payout = 0
    result_msg = ""
    whale_text = ""
    
    if tie:
        payout = game["bet"]
        result_msg = "🤝 အပြိုင်"
    elif win:
        raw_payout = game["bet"] * 2
        if is_whale:
            payout, whale_text = apply_whale_tax(whale_balance, raw_payout)
        else:
            payout = raw_payout
        result_msg = "🎉 သင်နိုင်သည်"
    else:
        payout = 0
        result_msg = "💸 သင်ရှုံးသည်"
    
    if payout > 0:
        await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"] - game.get("burn", 0), 2)
    net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
    
    active_rps_games.pop(game_id, None)
    
    # Emoji map for choices
    choice_emoji = {"ကျောက်": "🪨", "ကတ်ကြေး": "✂️", "စာရွက်": "📄"}
    
    text = (
        f"🪨 <b>RPS ရလဒ်</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(game['bet'])}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ:</b> <code>{format_usd(game.get('burn', 0))}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{choice_emoji.get(player_choice, '')} <b>သင်ရွေး:</b> {player_choice}\n"
        f"{choice_emoji.get(bot_choice, '')} <b>Bot ရွေး:</b> {bot_choice}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{result_msg}\n"
        f"🔄 <b>ရငွေ:</b> <code>{format_usd(payout)}</code>\n"
        f"📊 <b>အသားတင်:</b> <code>{net_display}</code>"
        f"{whale_text}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{GAME_FOOTER}"
    )
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer(result_msg)
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
        
# ---- ကံဘီး (Wheel of Fortune) ----
WHEEL_MIN_BET = 0.5
# ကဏ္ဍများ (မြှောက်ကိန်း၊ အလေးချိန်)
WHEEL_SEGMENTS = [
    {"multiplier": 0.0, "weight": 20, "label": "၀x"},
    {"multiplier": 0.5, "weight": 20, "label": "၀.၅x"},
    {"multiplier": 1.0, "weight": 20, "label": "၁x"},
    {"multiplier": 0.0, "weight": 15, "label": "၀x"},
    {"multiplier": 3.0, "weight": 10, "label": "၃x"},
    {"multiplier": 5.0, "weight": 0, "label": "၅x"},
    {"multiplier": 10.0, "weight": 0, "label": "၁၀x"},
    {"multiplier": 20.0, "weight": 0, "label": "၂၀x"},
]

def _wheel_segment_strip(landed_idx=None):
    """🎨 UPGRADED UI: renders every possible WHEEL_SEGMENTS outcome as one strip, with the
    segment that was actually landed on visually pointed at — gives the wheel a real 'this is
    where it stopped' feel instead of a single plain multiplier line."""
    parts = []
    for i, seg in enumerate(WHEEL_SEGMENTS):
        if i == landed_idx:
            parts.append(f"👉<b>[{seg['label']}]</b>👈")
        else:
            parts.append(f"<code>{seg['label']}</code>")
    return "  ".join(parts)
active_wheel_games = {}
_wheel_game_counter = 0
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:wheel)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def wheel_cmd_handler(event):
    global _wheel_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /wheel 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    
    # 🛡️ လောင်းငွေ အများဆုံး ကန့်သတ်ချက် (၁ သန်း)
    MAX_BET = 1_000_000
    if bet > MAX_BET:
        return await _out(event, f"❌ <b>တစ်ခါလောင်းလို့ အများဆုံး {format_usd(MAX_BET)} ပဲ လောင်းလို့ရပါတယ်။</b>", parse_mode='html')
    
    if bet < WHEEL_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {WHEEL_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    # 💰 Burn Rate (၂%)
    burn = round(bet * SPIN_BURN_RATE, 2)
    if burn > 0 and not await try_deduct_balance(user_id, burn):
        return await _out(event, "❌ <b>ကာစီနို ဆော့ခ မပေးနိုင်လို့ ကစားလို့မရပါ။</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=burn)
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {format_usd(balance)} သာရှိသည်။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _wheel_game_counter += 1
    game_id = _wheel_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "burn": burn,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "done": False
    }
    active_wheel_games[game_id] = game
    
    text = (
        f"🎡 <b>WHEEL OF FORTUNE (ကံဘီး)</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {mention}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(bet)}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ (2%):</b> <code>{format_usd(burn)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎡 {_wheel_segment_strip()}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>အောက်က ခလုတ်နှိပ်ပြီး ဘီးလှည့်ပါ။</i>"
    )
    buttons = [[Button.inline("🎡 ဘီးလှည့်မယ်", data=f"wheel_spin_{game_id}")]]
    await _out(event, text, parse_mode='html', buttons=buttons)


@bot1.on(events.CallbackQuery(pattern=r'^wheel_spin_(\d+)$'))
async def wheel_spin_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_wheel_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /wheel နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။ ခဏစောင့်ပါ။", alert=False)
    
    if game.get("done"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    # 🐋 Whale Check
    user_doc = await users_catcher_col.find_one({"user_id": game["user_id"]})
    whale_balance = (user_doc.get("wallet_balance", 0) if user_doc else 0)
    is_whale = whale_balance > WEALTH_THRESHOLD
    
    # အလေးချိန်ပေါ်မူတည်ပြီး ကျပန်းရွေးမယ်
    choices = []
    weights = []
    for seg in WHEEL_SEGMENTS:
        choices.append(seg)
        weights.append(seg["weight"])
    
    chosen = random.choices(choices, weights=weights, k=1)[0]
    chosen_idx = WHEEL_SEGMENTS.index(chosen)
    game["done"] = True
    
    multiplier = chosen["multiplier"]
    raw_payout = round(game["bet"] * multiplier, 2)
    
    whale_text = ""
    if is_whale and multiplier > 1.0:
        payout, whale_text = apply_whale_tax(whale_balance, raw_payout)
    else:
        payout = raw_payout
    
    if payout > 0:
        await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"] - game.get("burn", 0), 2)
    net_display = f"{'+' if net >= 0 else ''}{format_usd(net)}"
    
    active_wheel_games.pop(game_id, None)
    
    text = (
        f"🎡 <b>WHEEL OF FORTUNE ရလဒ်</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား:</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ:</b> <code>{format_usd(game['bet'])}</code>\n"
        f"🔥 <b>ကာစီနို ဆော့ခ:</b> <code>{format_usd(game.get('burn', 0))}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎡 {_wheel_segment_strip(chosen_idx)}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 <b>ဘီးရပ်သွားသည့်နေရာ:</b> {chosen['label']} (မြှောက်ကိန်း x{multiplier})\n"
        f"🔄 <b>ရငွေ:</b> <code>{format_usd(payout)}</code>\n"
        f"📊 <b>အသားတင်:</b> <code>{net_display}</code>"
        f"{whale_text}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{GAME_FOOTER}"
    )
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer(f"{chosen['label']} ကျသွားပါပြီ။")
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
BAC_MIN_BET = 0.5
BAC_SUITS = ["♠", "♥", "♦", "♣"]
BAC_RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
active_bac_games = {}
_bac_game_counter = 0

def _bac_deck():
    deck = []
    for s in BAC_SUITS:
        for r in BAC_RANKS:
            deck.append({"rank": r, "suit": s})
    random.shuffle(deck)
    return deck

def _bac_value(rank):
    if rank in ["J", "Q", "K", "10"]:
        return 0
    if rank == "A":
        return 1
    return int(rank)

def _bac_hand_total(hand):
    return sum(_bac_value(c["rank"]) for c in hand) % 10

def _bac_card_str(card):
    return f"[{card['rank']}{card['suit']}]"

def _bac_hand_str(hand):
    return " ".join(_bac_card_str(c) for c in hand)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:bac|baccarat)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def baccarat_cmd_handler(event):
    global _bac_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /bac 10", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    if bet < BAC_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {BAC_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _bac_game_counter += 1
    game_id = _bac_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "done": False
    }
    active_bac_games[game_id] = game
    
    text = f"ဘက်ကရက် ဂိမ်း\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\n\nဘယ်အပေါ်မှာ လောင်းမလဲ ရွေးပါ။\nပလေယာ (၂ဆ)၊ ဘဏ်သမား (၁.၉ဆ)၊ အပြိုင် (၈ဆ)"
    buttons = [
        [
            Button.inline("ပလေယာ", data=f"bac_bet_{game_id}_player"),
            Button.inline("ဘဏ်သမား", data=f"bac_bet_{game_id}_banker"),
            Button.inline("အပြိုင်", data=f"bac_bet_{game_id}_tie")
        ]
    ]
    await _out(event, text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^bac_bet_(\d+)_(player|banker|tie)$'))
async def baccarat_play_callback(event):
    game_id = int(event.pattern_match.group(1))
    bet_side = event.pattern_match.group(2)
    if isinstance(bet_side, bytes):
        bet_side = bet_side.decode('utf-8')
    
    game = active_bac_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /bac နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    deck = _bac_deck()
    player_hand = [deck.pop(), deck.pop()]
    banker_hand = [deck.pop(), deck.pop()]
    
    # ပထမဆုံး စုစုပေါင်း
    p_total = _bac_hand_total(player_hand)
    b_total = _bac_hand_total(banker_hand)
    
    # နတ်ခရိုင် (Natural 8/9) စစ်ဆေးမယ်
    p_natural = p_total in [8, 9]
    b_natural = b_total in [8, 9]
    
    # ပလေယာအတွက် တတိယကတ် ဆွဲမလား
    p_third = None
    b_third = None
    if not p_natural and not b_natural:
        # ပလေယာ ဆွဲမလား
        if p_total <= 5:
            p_third = deck.pop()
            player_hand.append(p_third)
            p_total = _bac_hand_total(player_hand)
        
        # ဘဏ်သမား ဆွဲမလား (ပလေယာရဲ့ တတိယကတ်ပေါ်မူတည်)
        if b_total <= 5:
            # ဘဏ်သမားရဲ့ ဆွဲစည်းမျဉ်း
            draw_banker = False
            if p_third is None:
                # ပလေယာ မဆွဲဘူးဆိုရင် ဘဏ်သမားက ၅ အောက်ဆို ဆွဲမယ်
                draw_banker = b_total <= 5
            else:
                third_val = _bac_value(p_third["rank"])
                if b_total <= 2:
                    draw_banker = True
                elif b_total == 3 and third_val != 8:
                    draw_banker = True
                elif b_total == 4 and third_val in [2, 3, 4, 5, 6, 7]:
                    draw_banker = True
                elif b_total == 5 and third_val in [4, 5, 6, 7]:
                    draw_banker = True
                elif b_total == 6 and third_val in [6, 7]:
                    draw_banker = True
                else:
                    draw_banker = False
            
            if draw_banker:
                b_third = deck.pop()
                banker_hand.append(b_third)
                b_total = _bac_hand_total(banker_hand)
    
    # အနိုင်ရှာ ဆုံးဖြတ်မယ်
    result = ""
    payout_multiplier = 0
    if p_total > b_total:
        result = "ပလေယာ နိုင်"
        payout_multiplier = 2.0 if bet_side == "player" else 0
    elif b_total > p_total:
        result = "ဘဏ်သမား နိုင်"
        if bet_side == "banker":
            payout_multiplier = 1.9
        else:
            payout_multiplier = 0
    else:
        result = "အပြိုင်"
        payout_multiplier = 8.0 if bet_side == "tie" else 0
    
    # အပြိုင်ဆိုရင် လောင်းငွေ ပြန်ပေးတယ် (သေချာအောင်)
    if result == "အပြိုင်":
        if bet_side == "tie":
            payout = game["bet"] * 8.0
        else:
            payout = game["bet"]  # ပလေယာ/ဘဏ်သမား အပြိုင်ဆိုရင် လောင်းငွေပြန်ရမယ် (push)
    else:
        payout = game["bet"] * payout_multiplier if payout_multiplier > 0 else 0
    
    if payout > 0:
        await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"], 2)
    game["done"] = True
    active_bac_games.pop(game_id, None)
    
    text = f"ဘက်ကရက် ရလဒ်\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nပလေယာကတ် - {_bac_hand_str(player_hand)} (ပေါင်း {p_total})\nဘဏ်သမားကတ် - {_bac_hand_str(banker_hand)} (ပေါင်း {b_total})\nရလဒ် - {result}\nသင်လောင်း - {bet_side}\nရငွေ - {payout} USD\n"
    if net > 0:
        text += f"အမြတ် - +{net} USD"
    elif net < 0:
        text += f"အရှုံး - {net} USD"
    else:
        text += f"အပြိုင်"
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer(result)
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
# ---- အရောင်တက်ဂိမ်း (Color Tower) ----
CT_MIN_BET = 0.5
# တစ်ဆင့်ချင်း မြှောက်ကိန်းတွေ (မှန်တိုင်း တက်သွားမယ်)
CT_MULTIPLIERS = [1.0, 1.5, 2.5, 4.0, 6.5, 10.0, 15.0, 25.0]
active_ct_games = {}
_ct_game_counter = 0

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:ct|colortower)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def ct_cmd_handler(event):
    global _ct_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /ct 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    if bet < CT_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {CT_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _ct_game_counter += 1
    game_id = _ct_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "level": 0,
        "cashed_out": False,
        "done": False,
        "msg_id": None
    }
    active_ct_games[game_id] = game
    
    text = f"အရောင်တက်ဂိမ်း\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\n\nလက်ရှိမြှောက်ကိန်း - x{CT_MULTIPLIERS[0]}\nအောက်က အနီ သို့မဟုတ် အမည်း ရွေးပြီး ဆက်တက်ပါ။ ငွေထုတ်လို့လည်းရပါတယ်။"
    buttons = [
        [
            Button.inline("အနီ", data=f"ct_guess_{game_id}_အနီ"),
            Button.inline("အမည်း", data=f"ct_guess_{game_id}_အမည်း")
        ],
        [Button.inline("ငွေထုတ်မယ်", data=f"ct_cashout_{game_id}")]
    ]
    msg = await _out(event, text, parse_mode='html', buttons=buttons)
    game["msg_id"] = msg.id

@bot1.on(events.CallbackQuery(pattern=r'^ct_guess_(\d+)_(.+)$'))
async def ct_guess_callback(event):
    game_id = int(event.pattern_match.group(1))
    guess = event.pattern_match.group(2)
    if isinstance(guess, bytes):
        guess = guess.decode('utf-8')
    
    game = active_ct_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /ct နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done") or game.get("cashed_out"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    # ကျပန်း အနီ/အမည်း ရွေးမယ်
    result = random.choice(["အနီ", "အမည်း"])
    
    if guess == result:
        game["level"] += 1
        level = game["level"]
        if level >= len(CT_MULTIPLIERS):
            # နောက်ဆုံးအဆင့်ရောက်ရင် အနိုင်ရပြီး ငွေထုတ်ခိုင်းမယ်
            game["done"] = True
            multiplier = CT_MULTIPLIERS[-1]
            payout = round(game["bet"] * multiplier, 2)
            await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
            await bot3_treasury_adjust(usd=-(payout))
            net = round(payout - game["bet"], 2)
            active_ct_games.pop(game_id, None)
            text = f"အရောင်တက်ဂိမ်း ပြီးဆုံးသည်\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nအဆင့်အားလုံး အောင်မြင်သွားပါပြီ။ နောက်ဆုံးမြှောက်ကိန်း x{multiplier}\nရငွေ - {payout} USD\n"
            if net > 0: text += f"အမြတ် - +{net} USD"
            elif net < 0: text += f"အရှုံး - {net} USD"
            else: text += f"အပြိုင်"
            await event.edit(text, parse_mode='html', buttons=None)
            await event.answer("ချန်ပီယံ!")
            if not event.is_private:
                schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
            return
        
        # ဆက်ကစားမယ်
        multiplier = CT_MULTIPLIERS[level]
        text = f"အရောင်တက်ဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nမှန်ပါသည်။ လက်ရှိမြှောက်ကိန်း - x{multiplier}\nဆက်ရွေးပါ သို့မဟုတ် ငွေထုတ်ပါ။"
        buttons = [
            [
                Button.inline("အနီ", data=f"ct_guess_{game_id}_အနီ"),
                Button.inline("အမည်း", data=f"ct_guess_{game_id}_အမည်း")
            ],
            [Button.inline("ငွေထုတ်မယ်", data=f"ct_cashout_{game_id}")]
        ]
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer(f"မှန်ပါသည်။ (x{multiplier})")
    else:
        # အရှုံး
        game["done"] = True
        active_ct_games.pop(game_id, None)
        text = f"အရောင်တက်ဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nသင်ရွေး - {guess}\nကျသွားသည် - {result}\n\nမှားသွားပါပြီ။ လောင်းထားငွေ ဆုံးရှုံးသည်။"
        await event.edit(text, parse_mode='html', buttons=None)
        await event.answer("မှားသွားပါပြီ။")
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)

@bot1.on(events.CallbackQuery(pattern=r'^ct_cashout_(\d+)$'))
async def ct_cashout_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_ct_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done") or game.get("cashed_out"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    game["cashed_out"] = True
    level = game["level"]
    multiplier = CT_MULTIPLIERS[level]
    payout = round(game["bet"] * multiplier, 2)
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"], 2)
    active_ct_games.pop(game_id, None)
    
    text = f"အရောင်တက်ဂိမ်း ငွေထုတ်ပြီး\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nငွေထုတ်လိုက်သည်။ မြှောက်ကိန်း x{multiplier}\nရငွေ - {payout} USD\n"
    if net > 0: text += f"အမြတ် - +{net} USD"
    elif net < 0: text += f"အရှုံး - {net} USD"
    else: text += f"အပြိုင်"
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer("ငွေထုတ်ပြီးပါပြီ။")
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
# ---- ကံဂဏန်း (Lucky Number) ----
LUCKY_MIN_BET = 0.5
# ဂဏန်းတစ်ခုကို ရွေးပြီး အန်စာတုံးပေါက်ရင် ၅ဆ ပြန်ရမယ် (သင်္ချာအရ အိမ်ရှင်ဘက်က အားသာချက် ~၁၆.၇%)
LUCKY_PAYOUT = 5.0
active_lucky_games = {}
_lucky_game_counter = 0

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:lucky)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def lucky_cmd_handler(event):
    global _lucky_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /lucky 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    if bet < LUCKY_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {LUCKY_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _lucky_game_counter += 1
    game_id = _lucky_game_counter
    
    game = {
        "user_id": user_id,
        "bet": bet,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "done": False
    }
    active_lucky_games[game_id] = game
    
    text = f"ကံဂဏန်း ဂိမ်း\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\n\n၁ ကနေ ၆ အတွင်း ဂဏန်းတစ်ခုကို ရွေးပါ။ အန်စာတုံးပေါက်တဲ့ဂဏန်းနဲ့ ကိုက်ရင် {LUCKY_PAYOUT}x ရမယ်။"
    buttons = [
        [
            Button.inline("၁", data=f"lucky_pick_{game_id}_1"),
            Button.inline("၂", data=f"lucky_pick_{game_id}_2"),
            Button.inline("၃", data=f"lucky_pick_{game_id}_3")
        ],
        [
            Button.inline("၄", data=f"lucky_pick_{game_id}_4"),
            Button.inline("၅", data=f"lucky_pick_{game_id}_5"),
            Button.inline("၆", data=f"lucky_pick_{game_id}_6")
        ]
    ]
    await _out(event, text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^lucky_pick_(\d+)_([1-6])$'))
async def lucky_play_callback(event):
    game_id = int(event.pattern_match.group(1))
    player_num = int(event.pattern_match.group(2))
    
    game = active_lucky_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /lucky နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    bot_roll = random.randint(1, 6)
    
    if player_num == bot_roll:
        payout = game["bet"] * LUCKY_PAYOUT
        result = "သင်နိုင်သည်"
    else:
        payout = 0
        result = "သင်ရှုံးသည်"
    
    if payout > 0:
        await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"], 2)
    game["done"] = True
    active_lucky_games.pop(game_id, None)
    
    text = f"ကံဂဏန်း ရလဒ်\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nသင်ရွေး - {player_num}\nအန်စာတုံးပေါက် - {bot_roll}\nရလဒ် - {result}\nရငွေ - {payout} USD\n"
    if net > 0:
        text += f"အမြတ် - +{net} USD"
    elif net < 0:
        text += f"အရှုံး - {net} USD"
    else:
        text += f"အပြိုင်"
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer(result)
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
# ---- STAR စာရင်းအင်း (.stars) ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]stars(?:@\w+)?$', 'bot1')))
async def stars_info_handler(event):
    user_id = event.sender_id
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    
    # ယနေ့ သုံးစွဲမှုနဲ့ ဝယ်ယူမှုအချက်အလက်
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    star_spent_today = 0
    star_bought_today = 0
    if user_doc and user_doc.get("star_activity_date") == today_str:
        star_spent_today = user_doc.get("star_spent_today", 0)
        star_bought_today = user_doc.get("star_bought_today", 0)
    
    # လက်ရှိ ငွေလဲနှုန်း
    market = await get_or_create_star_market()
    rate = market.get("price", STAR_STARTING_PRICE)
    
    mention = await get_html_mention(event, user_id)
    text = f"⭐ Star အခြေအနေ\nကစားသမား - {mention}\n\nStar လက်ကျန် - {format_star_plain(star_balance)}\n"
    text += f"ယနေ့ သုံးစွဲပြီးသား - {format_star_plain(star_spent_today)}\n"
    text += f"ယနေ့ ဝယ်ယူပြီးသား - {format_star_plain(star_bought_today)}\n"
    text += f"လက်ရှိ ငွေလဲနှုန်း - ၁⭐ = {rate:,.0f} USD\n\n"
    text += f"ကဒ်ဝယ်ရန်၊ Premium ဝယ်ရန်၊ ငွေလဲရန် အောက်က ခလုတ်များကို နှိပ်ပါ။"
    
    buttons = [
        [
            Button.inline("⭐ Star ဝယ်မယ်", data=f"buyhub_star_{user_id}"),
            Button.inline("🛍️ ကဒ်များဝယ်မယ်", data=f"buyhub_cards_{user_id}")
        ],
        [
            Button.inline("👑 Premium ဝယ်မယ်", data=f"buyhub_premium_{user_id}"),
            Button.inline("💰 လက်ကျန်ငွေကြည့်မယ်", data=f"buyhub_balance_{user_id}")
        ]
    ]
    
    await event.reply(text, parse_mode='html', buttons=buttons)

# ---- လက်ကျန်ငွေပြခလုတ် (balance from .stars) ----
@bot1.on(events.CallbackQuery(pattern=r'^buyhub_balance_(\d+)$'))
async def buyhub_balance_callback(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("ဒါက သင့်ရဲ့ menu မဟုတ်ပါ။", alert=True)
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    mention = await get_html_mention(event, user_id)
    
    text = f"လက်ကျန်ငွေစာရင်း\nကစားသမား - {mention}\n\n💵 USD - {format_usd(balance)}\n⭐ Star - {format_star_plain(star_balance)}"
    buttons = [[Button.inline("🔙 နောက်သို့", data=f"stars_back_{user_id}")]]
    await event.edit(text, parse_mode='html', buttons=buttons)
    await event.answer()

# ---- .stars မှ နောက်သို့ပြန်ခလုတ် ----
@bot1.on(events.CallbackQuery(pattern=r'^stars_back_(\d+)$'))
async def stars_back_callback(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("ဒါက သင့်ရဲ့ menu မဟုတ်ပါ။", alert=True)
    
    # အဓိက .stars စာမျက်နှာကို ပြန်ခေါ်မယ်
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    today_str = datetime.now(TZ).strftime("%Y-%m-%d")
    star_spent_today = 0
    star_bought_today = 0
    if user_doc and user_doc.get("star_activity_date") == today_str:
        star_spent_today = user_doc.get("star_spent_today", 0)
        star_bought_today = user_doc.get("star_bought_today", 0)
    market = await get_or_create_star_market()
    rate = market.get("price", STAR_STARTING_PRICE)
    mention = await get_html_mention(event, user_id)
    
    text = f"⭐ Star အခြေအနေ\nကစားသမား - {mention}\n\nStar လက်ကျန် - {format_star_plain(star_balance)}\nယနေ့ သုံးစွဲပြီးသား - {format_star_plain(star_spent_today)}\nယနေ့ ဝယ်ယူပြီးသား - {format_star_plain(star_bought_today)}\nလက်ရှိ ငွေလဲနှုန်း - ၁⭐ = {rate:,.0f} USD\n\nကဒ်ဝယ်ရန်၊ Premium ဝယ်ရန်၊ ငွေလဲရန် အောက်က ခလုတ်များကို နှိပ်ပါ။"
    buttons = [
        [
            Button.inline("⭐ Star ဝယ်မယ်", data=f"buyhub_star_{user_id}"),
            Button.inline("🛍️ ကဒ်များဝယ်မယ်", data=f"buyhub_cards_{user_id}")
        ],
        [
            Button.inline("👑 Premium ဝယ်မယ်", data=f"buyhub_premium_{user_id}"),
            Button.inline("💰 လက်ကျန်ငွေကြည့်မယ်", data=f"buyhub_balance_{user_id}")
        ]
    ]
    await event.edit(text, parse_mode='html', buttons=buttons)
    await event.answer()
# ---- ကန့်လန့်ဖြတ် (Limbo) ----
LIMBO_MIN_BET = 0.5
LIMBO_MAX_TARGET = 100.0
LIMBO_MIN_TARGET = 1.1
active_limbo_games = {}

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:limbo|lm)(?:@\w+)?\s+(\d+(?:\.\d+)?)\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def limbo_cmd_handler(event):
    user_id = event.sender_id
    target_str = event.pattern_match.group(1)
    bet_str = event.pattern_match.group(2)
    
    try:
        target = float(target_str)
        bet = round(float(bet_str), 2)
    except ValueError:
        return await _out(event, "ပုံစံမှန်ကန်အောင်ရိုက်ပါ။ ဥပမာ - /limbo 2.0 5", parse_mode='html')
    
    if target < LIMBO_MIN_TARGET:
        return await _out(event, f"အနည်းဆုံး မြှောက်ကိန်း {LIMBO_MIN_TARGET}x ထည့်ပါ။", parse_mode='html')
    if target > LIMBO_MAX_TARGET:
        return await _out(event, f"အများဆုံး မြှောက်ကိန်း {LIMBO_MAX_TARGET}x ထည့်ပါ။", parse_mode='html')
    if bet < LIMBO_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {LIMBO_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    
    # ကျပန်း ပြိုကျဂဏန်း ထုတ်မယ် (သင်္ချာအရ အိမ်ရှင်ဘက်က အားသာချက် ~၅%)
    crash_point = random.uniform(1.0, LIMBO_MAX_TARGET * 1.5)
    # ပြိုကျဂဏန်းက target အောက်ကျရင် ရှုံး၊ အထက်ကျရင် နိုင်
    win = target <= crash_point
    
    if win:
        payout = round(bet * target, 2)
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": payout}})
        await bot3_treasury_adjust(usd=-(payout))
        net = round(payout - bet, 2)
        result_text = f"ကန့်လန့်ဖြတ် ရလဒ်\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\nသင်ရွေးထားသော မြှောက်ကိန်း - x{target}\nပြိုကျဂဏန်း - {crash_point:.2f}x\n\nသင်နိုင်သည်။ ရငွေ - {payout} USD\nအမြတ် - +{net} USD"
    else:
        result_text = f"ကန့်လန့်ဖြတ် ရလဒ်\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\nသင်ရွေးထားသော မြှောက်ကိန်း - x{target}\nပြိုကျဂဏန်း - {crash_point:.2f}x\n\nသင်ရှုံးသည်။ လောင်းငွေ ဆုံးရှုံးသည်။"
    
    await _out(event, result_text, parse_mode='html')
# ---- အပေါ်အောက် (Over/Under 7) ----
OU_MIN_BET = 0.5
active_ou_games = {}
_ou_game_counter = 0

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:ou|overunder)(?:@\w+)?\s+(over|under|exact)\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def ou_cmd_handler(event):
    global _ou_game_counter
    user_id = event.sender_id
    choice = event.pattern_match.group(1)
    if isinstance(choice, bytes):
        choice = choice.decode('utf-8')
    bet_str = event.pattern_match.group(2)
    
    bet = round(float(bet_str), 2)
    if bet < OU_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {OU_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    
    # အန်စာတုံး ၂ လုံး လှိမ့်မယ်
    dice1 = random.randint(1, 6)
    dice2 = random.randint(1, 6)
    total = dice1 + dice2
    
    result = ""
    payout = 0
    if choice == "over":
        if total > 7:
            result = "သင်နိုင်သည်"
            payout = bet * 2  # ၁:၁ အနိုင်
        elif total == 7:
            result = "အပြိုင် (တိကျ)"
            payout = bet  # လောင်းငွေပြန်ရမယ် (push)
        else:
            result = "သင်ရှုံးသည်"
            payout = 0
    elif choice == "under":
        if total < 7:
            result = "သင်နိုင်သည်"
            payout = bet * 2
        elif total == 7:
            result = "အပြိုင် (တိကျ)"
            payout = bet
        else:
            result = "သင်ရှုံးသည်"
            payout = 0
    elif choice == "exact":
        if total == 7:
            result = "သင်နိုင်သည် (တိကျ)"
            payout = bet * 5  # ၅ဆ ပြန်ရမယ် (မြင့်မားတဲ့အန္တရာယ်)
        else:
            result = "သင်ရှုံးသည်"
            payout = 0
    
    if payout > 0:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - bet, 2)
    
    choice_map = {"over": "၇ အထက်", "under": "၇ အောက်", "exact": "တိကျ ၇"}
    text = f"အပေါ်အောက် ရလဒ်\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\nအန်စာတုံး ၁ - {dice1}\nအန်စာတုံး ၂ - {dice2}\nစုစုပေါင်း - {total}\nသင်ရွေး - {choice_map[choice]}\nရလဒ် - {result}\nရငွေ - {payout} USD\n"
    if net > 0:
        text += f"အမြတ် - +{net} USD"
    elif net < 0:
        text += f"အရှုံး - {net} USD"
    else:
        text += f"အပြိုင်"
    
    await _out(event, text, parse_mode='html')
# ---- တာဝါ (Tower) ----
TW_MIN_BET = 0.5
TW_MULTIPLIERS = [1.0, 2.0, 4.0, 6.0, 10.0, 16.0, 25.0, 50.0]
active_tw_games = {}
_tw_game_counter = 0

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:tw|tower)(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def tw_cmd_handler(event):
    global _tw_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    
    if not bet_str:
        return await _out(event, "ငွေပမာဏထည့်ပါ။ ဥပမာ - /tw 5", parse_mode='html')
    
    bet = round(float(bet_str), 2)
    if bet < TW_MIN_BET:
        return await _out(event, f"အနည်းဆုံး {TW_MIN_BET} USD လောင်းပါ။", parse_mode='html')
    
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if (user_doc.get("wallet_balance", 0) if user_doc else 0) < bet:
        return await _out(event, f"ငွေမလုံလောက်ပါ။ သင့်တွင် {user_doc.get('wallet_balance', 0)} USD သာရှိသည်။", parse_mode='html')
    
    if not await try_deduct_bet_bot3(event, user_id, bet):
        return await _out(event, "ငွေနှုတ်လို့မရပါ။", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    
    mention = await get_html_mention(event, user_id)
    _tw_game_counter += 1
    game_id = _tw_game_counter
    
    # ပထမအဆင့် သေတ္တာ ၃ လုံး ပြင်ဆင်မယ်
    bomb_pos = random.randint(0, 2)
    game = {
        "user_id": user_id,
        "bet": bet,
        "mention": mention,
        "game_id": game_id,
        "chat_id": event.chat_id,
        "level": 0,
        "bomb_pos": bomb_pos,
        "done": False,
        "cashed_out": False,
        "msg_id": None
    }
    active_tw_games[game_id] = game
    
    text = f"တာဝါ ဂိမ်း\nကစားသမား - {mention}\nလောင်းငွေ - {bet} USD\n\nအဆင့် {game['level']+1} - လက်ရှိမြှောက်ကိန်း x{TW_MULTIPLIERS[0]}\nသေတ္တာ ၃ လုံးထဲက တစ်လုံးကိုရွေးပါ။ ဘေးကင်းရင် ဆက်တက်မယ်။ ဗုံးမိရင် ရှုံးမယ်။"
    buttons = [
        [
            Button.inline("📦 ၁", data=f"tw_pick_{game_id}_0"),
            Button.inline("📦 ၂", data=f"tw_pick_{game_id}_1"),
            Button.inline("📦 ၃", data=f"tw_pick_{game_id}_2")
        ]
    ]
    msg = await _out(event, text, parse_mode='html', buttons=buttons)
    game["msg_id"] = msg.id

@bot1.on(events.CallbackQuery(pattern=r'^tw_pick_(\d+)_([0-2])$'))
async def tw_pick_callback(event):
    game_id = int(event.pattern_match.group(1))
    pick = int(event.pattern_match.group(2))
    
    game = active_tw_games.get(game_id)
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။ /tw နဲ့ အသစ်စပါ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done") or game.get("cashed_out"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    # ဗုံးမိလား စစ်ဆေးမယ်
    if pick == game["bomb_pos"]:
        # ရှုံး
        game["done"] = True
        active_tw_games.pop(game_id, None)
        text = f"တာဝါ ဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nအဆင့် {game['level']+1} မှာ ဗုံးမိသွားပါပြီ။ လောင်းငွေ ဆုံးရှုံးသည်။"
        await event.edit(text, parse_mode='html', buttons=None)
        await event.answer("ဗုံးမိသွားပြီ။")
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
        return
    
    # ဘေးကင်း
    game["level"] += 1
    level = game["level"]
    
    if level >= len(TW_MULTIPLIERS):
        # နောက်ဆုံးအဆင့်ရောက်ရင် အနိုင်ရပြီး ငွေထုတ်ခိုင်းမယ်
        game["done"] = True
        multiplier = TW_MULTIPLIERS[-1]
        payout = round(game["bet"] * multiplier, 2)
        await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
        await bot3_treasury_adjust(usd=-(payout))
        net = round(payout - game["bet"], 2)
        active_tw_games.pop(game_id, None)
        text = f"တာဝါ ဂိမ်း ပြီးဆုံးသည်\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nအဆင့်အားလုံး အောင်မြင်သွားပါပြီ။ နောက်ဆုံးမြှောက်ကိန်း x{multiplier}\nရငွေ - {payout} USD\n"
        if net > 0:
            text += f"အမြတ် - +{net} USD"
        elif net < 0:
            text += f"အရှုံး - {net} USD"
        else:
            text += f"အပြိုင်"
        await event.edit(text, parse_mode='html', buttons=None)
        await event.answer("ချန်ပီယံ!")
        if not event.is_private:
            schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
        return
    
    # ဆက်ကစားမယ် (သေတ္တာအသစ် ၃ လုံး ပြင်ဆင်မယ်)
    bomb_pos = random.randint(0, 2)
    game["bomb_pos"] = bomb_pos
    multiplier = TW_MULTIPLIERS[level]
    
    text = f"တာဝါ ဂိမ်း\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nအဆင့် {level+1} - လက်ရှိမြှောက်ကိန်း x{multiplier}\nသေတ္တာ ၃ လုံးထဲက တစ်လုံးကိုရွေးပါ။ ဆက်တက်မယ် သို့မဟုတ် ငွေထုတ်ပါ။"
    buttons = [
        [
            Button.inline("📦 ၁", data=f"tw_pick_{game_id}_0"),
            Button.inline("📦 ၂", data=f"tw_pick_{game_id}_1"),
            Button.inline("📦 ၃", data=f"tw_pick_{game_id}_2")
        ],
        [Button.inline("ငွေထုတ်မယ်", data=f"tw_cashout_{game_id}")]
    ]
    await event.edit(text, parse_mode='html', buttons=buttons)
    await event.answer(f"မှန်ပါသည်။ (x{multiplier})")

@bot1.on(events.CallbackQuery(pattern=r'^tw_cashout_(\d+)$'))
async def tw_cashout_callback(event):
    game_id = int(event.pattern_match.group(1))
    game = active_tw_games.get(game_id)
    
    if not game:
        return await event.answer("ဒီဂိမ်းသက်တမ်းကုန်သွားပါပြီ။", alert=True)
    
    if event.sender_id != game["user_id"]:
        return await event.answer("ဒါက မင်းရဲ့ဂိမ်းမဟုတ်ဘူး။", alert=True)
    
    if not claim_single_tap(event):
        return await event.answer("လုပ်ဆောင်ချက် လုပ်နေဆဲပါ။", alert=False)
    
    if game.get("done") or game.get("cashed_out"):
        return await event.answer("ဂိမ်းပြီးသွားပါပြီ။", alert=True)
    
    level = game["level"]
    multiplier = TW_MULTIPLIERS[level]
    payout = round(game["bet"] * multiplier, 2)
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    
    net = round(payout - game["bet"], 2)
    game["cashed_out"] = True
    active_tw_games.pop(game_id, None)
    
    text = f"တာဝါ ဂိမ်း ငွေထုတ်ပြီး\nကစားသမား - {game['mention']}\nလောင်းငွေ - {game['bet']} USD\n\nငွေထုတ်လိုက်သည်။ မြှောက်ကိန်း x{multiplier}\nရငွေ - {payout} USD\n"
    if net > 0:
        text += f"အမြတ် - +{net} USD"
    elif net < 0:
        text += f"အရှုံး - {net} USD"
    else:
        text += f"အပြိုင်"
    
    await event.edit(text, parse_mode='html', buttons=None)
    await event.answer("ငွေထုတ်ပြီးပါပြီ။")
    if not event.is_private:
        schedule_game_cleanup(event.client, event.chat_id, event.message_id, delay=15)
# ---- BOX (Deal or No Deal) ----
# 30 boxes, one prize value each — spread from well below the bet to well above it, so
# there's real downside AND real upside, not just a coin flip. The player locks in one box
# as their own (kept sealed to the very end), then opens the other 29 one at a time. After
# every box opened, Morgan — the casino owner — offers a cash buyout based on the actual
# expected value of everything still unopened (including the player's own box, since that's
# still "in play"); the offer isn't a fixed cut, it moves with what's left, same as the real
# show — losing a big box crashes the offer, and it climbs as fewer, higher-variance boxes
# remain. Accept ("Deal!") and the game ends there; decline ("No Deal") and keep opening.
# Empty out every other box with no deal taken, and the payout is simply whatever was inside
# the player's own sealed box.
# 🩹 FIX: the old multiplier list (0.01x up to 100x) averaged ~7.8x the bet across all 30
# boxes — since the player's payout (own box, or any deal, which is itself just a % of the
# average of what's left) always comes from that same pool, the game was structurally
# profitable no matter how anyone played: deal early, deal late, or never deal at all.
# Rescaled so the 30 boxes now average 0.97x (a ~3% house edge, matching MINES_HOUSE_EDGE
# elsewhere) — same shape (one big jackpot box, a long tail of small ones), just no longer a
# guaranteed-profit machine.
BOX_TOTAL = 30
BOX_MIN_BET = 1000 / MMK_PER_USD
BOX_MULTIPLIERS = [0.04, 0.06, 0.07, 0.11, 0.15, 0.18, 0.22, 0.26, 0.3, 0.33,
                   0.37, 0.41, 0.44, 0.48, 0.52, 0.55, 0.59, 0.66, 0.74, 0.81,
                   0.92, 1.03, 1.18, 1.33, 1.48, 1.85, 2.21, 2.95, 3.69, 5.17]
active_box_games = bot_state.active_box_games
_box_game_counter = 0

def _box_calc_offer(game):
    """Morgan's offer: the house-edge-trimmed expected value of everything still unopened
    (the 29-minus-opened remaining boxes PLUS the player's own sealed box, since it's still
    part of what could end up being paid out), scaled by a percentage that climbs from ~55%
    early in the game toward ~98% near the very end — cautious early, generous late, but
    🩹 FIX: capped below 100% (was climbing to 105%, letting a late deal briefly beat fair
    value) so every offer, at every stage, stays on the house's side of break-even."""
    remaining_idxs = [i for i in range(BOX_TOTAL) if i != game["own_idx"] and i not in game["opened"]]
    remaining_values = [game["values"][i] for i in remaining_idxs] + [game["values"][game["own_idx"]]]
    expected_value = sum(remaining_values) / len(remaining_values)
    progress = len(game["opened"]) / (BOX_TOTAL - 1)
    offer_pct = 0.55 + 0.43 * progress
    return max(0.01, round(expected_value * offer_pct, 2))

def _render_box_pick_own(game, game_id):
    rows = []
    for r in range(6):
        row = [Button.inline(f"📦{r*5+c+1}", data=f"boxown_{game_id}_{r*5+c}") for c in range(5)]
        rows.append(row)
    text = (
        f"📦 {f('DEAL OR NO DEAL')}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား −</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ −</b> <code>{game['bet']:,} USD</code>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<i>ပထမဆုံး — မင်းရဲ့ ကိုယ်ပိုင် Box တစ်ခုကို ရွေးပါ။ ဒီ Box ကို နောက်ဆုံးအထိ မဖွင့်ဘဲ ချန်ထားပါမယ်။</i>"
    )
    return text, rows

def _render_box_board(game, game_id):
    rows = []
    for r in range(6):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx == game["own_idx"]:
                row.append(Button.inline(f"🔒{idx+1}", data=f"boxnoop_{game_id}"))
            elif idx in game["opened"]:
                row.append(Button.inline(f"{game['values'][idx]:,}", data=f"boxnoop_{game_id}"))
            else:
                row.append(Button.inline(f"📦{idx+1}", data=f"boxopen_{game_id}_{idx}"))
        rows.append(row)
    remaining_idxs = [i for i in range(BOX_TOTAL) if i != game["own_idx"] and i not in game["opened"]]
    text = (
        f"📦 {f('DEAL OR NO DEAL')}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား −</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ −</b> <code>{game['bet']:,} USD</code>\n"
        f"🔒 <b>ကိုယ်ပိုင် Box −</b> #{game['own_idx']+1}\n"
        f"📦 <b>ကျန်ရှိ Box −</b> {len(remaining_idxs)}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<i>ဖျက်ချင်တဲ့ Box တစ်ခုကို ရွေးပါ။</i>"
    )
    return text, rows

def _render_box_offer(game, game_id, revealed_value, offer):
    remaining_idxs = [i for i in range(BOX_TOTAL) if i != game["own_idx"] and i not in game["opened"]]
    text = (
        f"📦 {f('DEAL OR NO DEAL')}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား −</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ −</b> <code>{game['bet']:,} USD</code>\n"
        f"📦 <b>ဖွင့်လိုက်တဲ့ Box ထဲမှာ −</b> <code>{revealed_value:,} USD</code> ပါတယ်\n"
        f"🔲 <b>ကျန်ရှိနေတာ −</b> {len(remaining_idxs)} Box (+ မင်းရဲ့ ကိုယ်ပိုင် Box)\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"☎️ <b>Morgan ရဲ့ ကမ်းလှမ်းချက် −</b> <code>{offer:,} USD</code>\n"
        f"<i>ဒီ Offer ကို လက်ခံမလား၊ ဆက်ကစားမလား?</i>"
    )
    rows = [[
        Button.inline(f"✅ Deal! ({offer:,} USD)", data=f"boxdeal_{game_id}"),
        Button.inline("❌ No Deal", data=f"boxnodeal_{game_id}")
    ]]
    return text, rows

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]box(?:@\w+)?(?:\s+(\d+(?:\.\d+)?))?$', 'bot1')))
async def box_game_handler(event):
    global _box_game_counter
    user_id = event.sender_id
    bet_str = event.pattern_match.group(1)
    if not bet_str:
        return await _out(event, f"📦 ငွေပမာဏထည့်ပါ။\nဥပမာ: <code>/box 5</code>", parse_mode='html')
    bet = round(float(bet_str), 2)
    if bet < BOX_MIN_BET:
        return await _out(event, f"<b>အနည်းဆုံး {format_usd(BOX_MIN_BET)} လောင်းပါ။</b>", parse_mode='html')
    if not await try_deduct_bet_bot3(event, user_id, bet):
        user_doc = await users_catcher_col.find_one({"user_id": user_id})
        balance = user_doc.get("wallet_balance", 0) if user_doc else 0
        return await _out(event, f"<b>မင်းမှာ {balance} USD ပဲရှိတယ်နော်!</b>", parse_mode='html')
    await bot3_treasury_adjust(usd=bet)
    mention = await get_html_mention(event, user_id)
    values = [max(0.01, round(bet * m, 2)) for m in BOX_MULTIPLIERS]
    random.shuffle(values)
    _box_game_counter += 1
    game_id = _box_game_counter
    game = {"user_id": user_id, "bet": bet, "mention": mention, "chat_id": event.chat_id,
            "values": values, "own_idx": None, "opened": set()}
    active_box_games[game_id] = game
    text, rows = _render_box_pick_own(game, game_id)
    await _out(event, text, parse_mode='html', buttons=rows)

@bot1.on(events.CallbackQuery(pattern=r'^boxown_(\d+)_(\d+)$'))
async def box_pick_own_handler(event):
    game_id = int(event.pattern_match.group(1))
    idx = int(event.pattern_match.group(2))
    game = active_box_games.get(game_id)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    if game["own_idx"] is not None:
        return await event.answer()
    game["own_idx"] = idx
    text, rows = _render_box_board(game, game_id)
    await event.edit(text, parse_mode='html', buttons=rows)
    await event.answer("🔒 မင်းရဲ့ Box ကို သိမ်းထားလိုက်ပြီ!")

@bot1.on(events.CallbackQuery(pattern=r'^boxopen_(\d+)_(\d+)$'))
async def box_open_handler(event):
    game_id = int(event.pattern_match.group(1))
    idx = int(event.pattern_match.group(2))
    game = active_box_games.get(game_id)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    if idx == game["own_idx"] or idx in game["opened"]:
        return await event.answer()
    game["opened"].add(idx)
    revealed_value = game["values"][idx]
    remaining_idxs = [i for i in range(BOX_TOTAL) if i != game["own_idx"] and i not in game["opened"]]
    if not remaining_idxs:
        # Nothing left to trade with Morgan — settle for whatever's in the player's own box.
        await _box_settle(event, game_id, payout=game["values"][game["own_idx"]], reason="own")
        return
    offer = _box_calc_offer(game)
    text, rows = _render_box_offer(game, game_id, revealed_value, offer)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer(f"📦 {revealed_value:,} USD ပါတယ်")

@bot1.on(events.CallbackQuery(pattern=r'^boxnodeal_(\d+)$'))
async def box_nodeal_handler(event):
    game_id = int(event.pattern_match.group(1))
    game = active_box_games.get(game_id)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    text, rows = _render_box_board(game, game_id)
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer("🔥 ဆက်ကစားမယ်!")

@bot1.on(events.CallbackQuery(pattern=r'^boxdeal_(\d+)$'))
async def box_deal_handler(event):
    game_id = int(event.pattern_match.group(1))
    game = active_box_games.get(game_id)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    if event.sender_id != game["user_id"]:
        return await event.answer("⚠️ ဒါက မင်းရဲ့ game မဟုတ်ဘူး။", alert=True)
    if not claim_single_tap(event):
        return await event.answer()
    offer = _box_calc_offer(game)
    await _box_settle(event, game_id, payout=offer, reason="deal")

async def _box_settle(event, game_id, payout, reason):
    game = active_box_games.pop(game_id, None)
    if not game:
        return await event.answer("⚠️ ဒီ game ပြီးသွားပါပြီ။", alert=True)
    await users_catcher_col.update_one({"user_id": game["user_id"]}, {"$inc": {"wallet_balance": payout}})
    await bot3_treasury_adjust(usd=-(payout))
    net_gain = payout - game["bet"]
    sign = "+" if net_gain >= 0 else "-"
    rows = []
    for r in range(6):
        row = []
        for c in range(5):
            idx = r * 5 + c
            val = game["values"][idx]
            label = f"👑{val:,}" if idx == game["own_idx"] else f"{val:,}"
            row.append(Button.inline(label, data=f"boxnoop_{game_id}"))
        rows.append(row)
    header = ("🤝 <b>DEAL! Morgan ရဲ့ ကမ်းလှမ်းချက်ကို လက်ခံလိုက်ပြီ။</b>" if reason == "deal"
              else "🏆 <b>Box အားလုံး ကုန်သွားပြီ — ကိုယ်ပိုင် Box ထဲက ငွေကို ရလိုက်ပြီ!</b>")
    text = (
        f"📦 {f('DEAL OR NO DEAL')} — အဆုံးသတ်\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>ကစားသမား −</b> {game['mention']}\n"
        f"💵 <b>လောင်းငွေ −</b> <code>{game['bet']:,} USD</code>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"{header}\n"
        f"🔄 <b>ရငွေ −</b> <code>{payout:,} USD</code>\n"
        f"📊 <b>အမြတ်/အရှုံး −</b> <code>{sign}{abs(net_gain):,} USD</code>"
        f"{GAME_FOOTER}"
    )
    try:
        await event.edit(text, parse_mode='html', buttons=rows)
    except errors.MessageNotModifiedError:
        pass
    await event.answer("🎉 ပြီးပါပြီ!" if reason == "deal" else "🏆 Box ကုန်ပြီ!")
    if not event.is_private:
        schedule_game_cleanup(event.client, game["chat_id"], event.message_id, delay=15)

@bot1.on(events.CallbackQuery(pattern=r'^boxnoop_(\d+)$'))
async def box_noop_handler(event):
    await event.answer()

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]hunt(?:@\w+)?$', 'bot1')))
async def text_adventure_hunt_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    current_time = time.time()
    last_hunt = user_doc.get("hunt_cooldown", 0) if user_doc else 0
    if current_time - last_hunt < 180:
        return await event.reply(f"⏳ {mention} <b>You must wait {int(180 - (current_time - last_hunt))}s.</b>", parse_mode='html')
    # 🔺 BUMPED x1000 (per owner request, Aug 2026) — was random.randint(200, 8000); see the
    # matching note on _RARITY_VALUE_MAP above for why (Star now pegged at 1⭐ = 1,000,000 USD).
    earned = round(random.randint(200000, 8000000) / MMK_PER_USD, 2)
    events_pool = [f"🌲 {mention} <b>found treasure! (+<code>{earned} USD</code>)</b>", f"⚔️ {mention} <b>defeated a rival! (+<code>{earned} USD</code>)</b>", f"🌌 {mention} <b>collected quantum points! (+<code>{earned} USD</code>)</b>"]
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": earned}, "$set": {"hunt_cooldown": current_time, "fullname": plain_name}}, upsert=True)
    await event.reply(random.choice(events_pool), parse_mode='html')

MARKET_LISTINGS_PER_PAGE = 5

async def send_market_page(client, chat_id, page=1, edit_msg_id=None):
    all_listings = await marketplace_col.find().sort("timestamp", -1).to_list(length=None)
    if not all_listings:
        msg = "🏪 <b>No items on the market.</b>"
        if edit_msg_id:
            try:
                await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html')
            except errors.MessageNotModifiedError:
                pass
        else:
            await client.send_message(chat_id, msg, parse_mode='html')
        return
    total_pages = max(1, (len(all_listings) + MARKET_LISTINGS_PER_PAGE - 1) // MARKET_LISTINGS_PER_PAGE)
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    start_idx = (page - 1) * MARKET_LISTINGS_PER_PAGE
    page_listings = all_listings[start_idx:start_idx + MARKET_LISTINGS_PER_PAGE]
    msg = (
        f"🏪 <b>MARKETPLACE CATALOG</b>\nAUCTION\n"
        f"📑 <b>Page:</b> <code>{page}/{total_pages}</code> | <b>Total Listings:</b> <code>{len(all_listings)}</code>\n\n"
    )
    for item in page_listings:
        msg += f"📦 <b>Card:</b> <code>{item['char_name']}</code> [<code>{display_char_id(item['char_id'])}</code>]\n ├─ 💰 <b>Price:</b> <code>{item['price']} USD</code>\n └─ 👤 <b>Seller:</b> {item['seller_name']}\n\n"
    buttons = []
    nav_buttons = []
    if page > 1:
        nav_buttons.append(Button.inline("⬅️ Prev", data=f"mktpg_{page-1}"))
    if page < total_pages:
        nav_buttons.append(Button.inline("Next ➡️", data=f"mktpg_{page+1}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    if not buttons:
        buttons = None
    if edit_msg_id:
        try:
            await client.edit_message(chat_id, edit_msg_id, msg, parse_mode='html', buttons=buttons)
        except errors.MessageNotModifiedError:
            pass
    else:
        await client.send_message(chat_id, msg, parse_mode='html', buttons=buttons)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]market(?:@\w+)?$', 'bot1')))
async def global_market_catalog_viewer(event):
    user_id = event.sender_id
    await ensure_user_registered(user_id, await get_plain_name(event, user_id))
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    balance = user_doc.get("wallet_balance", 0) if user_doc else 0
    star_balance = user_doc.get("star_balance", 0) if user_doc else 0
    premium_line = ""
    if is_premium_active(user_doc):
        expiry_str = datetime.fromtimestamp(user_doc["premium_until"], TZ).strftime("%Y-%m-%d")
        premium_line = f"\n👑 <b>Premium:</b> <code>{expiry_str}</code> အထိ"
    buttons = [
        [Button.inline("🌠 ကဒ်များ", data=f"buyhub_cards_{user_id}")],
        [Button.inline("⭐ ကဒ်ဝယ်ဖို့ Star ဝယ်မယ်", data=f"buyhub_star_{user_id}")],
        [Button.inline("👑 Premium ဝယ်မယ်", data=f"buyhub_premium_{user_id}")],
    ]
    await event.reply(
        f"🏪 <b>MARKET</b>\n"
        f""
        f"💵 <b>USD:</b> <code>{format_usd(balance)}</code>\n"
        f"⭐ <b>Star:</b> <code>{format_star_plain(star_balance)}</code>"
        f"{premium_line}"
        f"\n"
        f"👇 <i>ဘာကိုဝယ်ချင်ပါသလဲ?</i>",
        parse_mode='html',
        buttons=buttons
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]stats(?:@\w+)?$', 'bot1')))
async def system_inflation_stats(event):
    status_msg = await event.reply("⏳ <b>Compiling statistics...</b>", parse_mode='html')
    try:
        pipeline_cash = [
            {"$group": {
                "_id": None,
                "total_cash": {"$sum": "$wallet_balance"},
                "players_count": {"$sum": 1}
            }}
        ]
        econ_data = await users_catcher_col.aggregate(pipeline_cash).to_list(length=1)
        metrics = econ_data[0] if econ_data else {"total_cash": 0, "players_count": 0}
        all_base_chars = await characters_base_col.find({}, {"rarity": 1}).to_list(length=None)
        base_total = len(all_base_chars)
        base_tier_counts = {t: 0 for t in RARITY_TIERS}
        for c in all_base_chars:
            tier = classify_rarity(c.get("rarity", ""))
            if tier in base_tier_counts:
                base_tier_counts[tier] += 1
        all_users = await users_catcher_col.find({}, {"harem": 1}).to_list(length=None)
        catch_tier_counts = {t: 0 for t in RARITY_TIERS}
        other_catch_count = 0  # 🩹 FIX: harem items whose rarity string doesn't match any
        # known tier (e.g. legacy "Unknown" rarity from old trades/gifts) used to be silently
        # dropped from the per-tier breakdown while still counted in total_catches, so the 9
        # tier counts never summed to the total shown. Tracked separately here so the numbers
        # always reconcile, and logged so the offending raw rarity strings can be found.
        other_rarity_samples = set()
        total_catches = 0
        caught_unique_ids = set()
        for u in all_users:
            harem = u.get("harem", [])
            total_catches += len(harem)
            for item in harem:
                if isinstance(item, dict) and "char_id" in item:
                    caught_unique_ids.add(item["char_id"])
                    raw_rarity = item.get("rarity", "")
                    tier = classify_rarity(raw_rarity)
                    if tier in catch_tier_counts:
                        catch_tier_counts[tier] += 1
                    else:
                        other_catch_count += 1
                        if len(other_rarity_samples) < 20:
                            other_rarity_samples.add(repr(raw_rarity))
        if other_catch_count:
            print(f"⚠️ /stats: {other_catch_count} harem items had unclassifiable rarity strings: {sorted(other_rarity_samples)}")
        discovery_count = len(caught_unique_ids)
        msg = (
            f"📊 <b>GLOBAL ECONOMY & COLLECTION STATS</b>\n"
            f"⚡ ━━━━━━━━━━━━━━━━━━━━ ⚡\n\n"
            f"👥 <b>Active Agents:</b> <code>{metrics['players_count']} Players</code>\n"
            f"🪙 <b>Total Money in Circulation:</b> <code>{metrics['total_cash']:,} USD</code>\n\n"
            f"🗄️ <b>CHARACTER DATABASE</b> (<code>/addchar</code> total: <code>{base_total}</code>)\n"
        )
        for tier in RARITY_TIERS:
            cnt = base_tier_counts[tier]
            msg += f"{RARITY_EMOJI[tier]} <b>{tier}</b> — <code>{cnt}</code>\n"
            msg += f"<code>{build_progress_bar(cnt, base_total)}</code>\n"
        msg += f"\n🃏 <b>TOTAL CATCHES</b> (all players combined: <code>{total_catches}</code>)\n"
        for tier in RARITY_TIERS:
            cnt = catch_tier_counts[tier]
            msg += f"{RARITY_EMOJI[tier]} <b>{tier}</b> — <code>{cnt}</code>\n"
            msg += f"<code>{build_progress_bar(cnt, total_catches)}</code>\n"
        if other_catch_count:
            msg += f"❓ <b>OTHER/UNKNOWN</b> — <code>{other_catch_count}</code>\n"
            msg += f"<code>{build_progress_bar(other_catch_count, total_catches)}</code>\n"
        msg += f"\n🔎 <b>DISCOVERY RATE</b> (unique characters caught at least once)\n"
        msg += f"<code>{build_progress_bar(discovery_count, base_total)}</code>\n"
        msg += f"<code>{discovery_count}/{base_total}</code> characters discovered by players"
        await status_msg.edit(msg, parse_mode='html')
    except Exception as e:
        error_text = f"❌ <b>Stats Error:</b>\n<code>{escape_html(str(e))}</code>"
        await status_msg.edit(error_text, parse_mode='html')
        await report_system_error("system_inflation_stats", e)

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
        "    I combine fun, economy, and powerful group management — all in one place.\n"
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
        "    • /fuck [name]     –  capture the character and earn USD\n"
        "    • /harem          –  view your vault (paginated inventory)\n"
        "    • /fav [ID]       –  set a favourite card\n"
        "    • /profile, /myinfo –  check your stats and balance\n"
        "    • /shop           –  buy Titles, Emblems & Frames for your profile\n"
        "    • /top /gtop      –  local and global leaderboards\n"
        "    • /check [ID]     –  detailed character info & top collectors\n"
        "\n"
        "🎰  CASINO & GAMBLING\n"
        "    • /slot [amount]       –  spin the 7‑symbol slot machine\n"
        "    • /cardgame [amount]   –  create a multiplayer card game lobby\n"
        "    • /startgame /cancelgame  –  start or cancel the lobby\n"
        "    • /flip [heads/tails] [amount]  –  coin flip (50/50)\n"
        "    • /dice [amount]       –  roll a dice, win on 4‑6\n"
        "    • /hilo [amount]       –  higher/lower card game\n"
        "    • /gamble [amount]     –  double or nothing (50% chance)\n"
        "    • /mines [amount]      –  reveal safe tiles, cash out before you hit a bomb\n"
        "    • /box [amount]        –  Deal or No Deal: 30 boxes, keep one, take Morgan's offer\n"
        "    • /roulette [amount] (/r)  –  bet on a color or number, spin the wheel\n"
        "    • /plinko [amount] (/p)    –  drop a ball through pegs for a random multiplier\n"
        "    • /wheel [amount]      –  spin the fortune wheel for a random multiplier\n"
        "    • /rps [amount]        –  rock-paper-scissors against the bot, win doubles your bet\n"
        "\n"
        "💰  ECONOMY & TRADING\n"
        "    • /balance        –  view your wallet balance\n"
        "    • /daily           –  claim daily bonus (streak rewards)\n"
        "    • /hunt            –  go hunting for extra cash (3min cooldown)\n"
        "    • /gift [cardID]   –  gift a card to someone (reply)\n"
        "    • /trade [myID] [theirID]  –  propose a card swap (reply)\n"
        "    • /sell [ID]       –  Owner offers to buy your card back with ⭐ Star (0.5x-1.5x its price)\n"
        "    • /buy [ID]        –  buy a fresh copy from the Owner Shop with ⭐ Star\n"
        "    • /buypremium      –  buy Bot Premium User status with ⭐ Star\n"
        "    • /market          –  browse all active listings\n"
        "    • /richest         –  top 10 wealthiest players\n"
        "    • /stats           –  global economy overview\n"
        "\n"
        "🔗  SOCIAL & REFERRAL\n"
        "    • /referral        –  get your unique invite link\n"
        "                         (you get 0.50 USD, friend gets 0.25 USD)\n"
        "\n"
        "🌦️  WEATHER\n"
        "    • /weather         –  live weather for Myanmar & Thailand\n"
        "                         (choose country, then city)\n"
        "\n"
        "📚  HELP & NAVIGATION\n"
        "    • /help            –  detailed command reference\n"
        "    • /game            –  casino games overview\n"
        "    • /introduce       –  you are reading this!\n"
        "\n"
        "⚙️  OWNER‑ONLY (hidden from normal users)\n"
        "    • /addchar, /delchar, /editchar, /setchar, /addartist,\n"
        "      /change CharID (reply to new photo/video)  –  swap a character's media\n"
        "                         (e.g. upgrade a blurry upload) without affecting anyone's catches,\n"
        "      /revokereward UserID [confirm]  –  claw back ONE account's force-sub join\n"
        "                         reward (e.g. it was granted by mistake to a bot account),\n"
        "      /reclaimforcesub [confirm]  –  BULK claw back the join reward from every\n"
        "                         account that never caught anything beyond it (i.e. only\n"
        "                         joined to farm the free USD/card, never actually played),\n"
        "      /exportchars      –  send the full character database as a CSV file,\n"
        "      /changeallrarity confirm  –  rebrand all rarity names/emoji DB-wide,\n"
        "      /linkartist, /unlinkartist  –  link an /addartist name to a real Telegram\n"
        "                         account so the Guard Bot can pay them for collected cards,\n"
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
# ⭐ STAR ကြဲပွဲ (STAR GIVEAWAY) — owner broadcasts an easy Burmese trivia question with 4
# inline-button choices to EVERY group at once. Answers are recorded SILENTLY for the full
# STAR_GIVEAWAY_DURATION window (no right/wrong reveal on click) — this is intentional: button
# taps count toward Telegram's Monthly Active Users metric, so the goal is to keep people
# tapping for the whole window rather than settling the instant someone answers. Only once the
# timer runs out does each group's message get edited to reveal the correct answer and (if
# anyone in that group got it right) the winner, who receives STAR_GIVEAWAY_REWARD Stars.
# ==========================================
STAR_GIVEAWAY_DURATION = 120  # seconds (2 minutes)
STAR_GIVEAWAY_REWARD = 1000   # ⭐ Stars for the first correct answer in each group
active_star_giveaways = {}    # giveaway_id -> {question, options, correct_idx, expiry, reward,
                              #  messages: {chat_id: msg_id}, attempts: {chat_id: [(user_id, option_idx, ts)]},
                              #  answered: {(chat_id, user_id)}, owner_chat}

# 50 easy Burmese trivia questions: (question, [4 options], correct_option_index)
STAR_GIVEAWAY_QUESTIONS = [
    ("မြန်မာနိုင်ငံရဲ့ မြို့တော်က ဘယ်မြို့လဲ?", ["ရန်ကုန်", "မန္တလေး", "နေပြည်တော်", "ပုဂံ"], 2),
    ("၂ + ၂ = ဘယ်နှစ်လဲ?", ["၃", "၄", "၅", "၆"], 1),
    ("မြန်မာနိုင်ငံရဲ့ အရှည်ဆုံးမြစ်က ဘာလဲ?", ["သံလွင်မြစ်", "ဧရာဝတီမြစ်", "ချင်းတွင်းမြစ်", "စစ်တောင်းမြစ်"], 1),
    ("တစ်နှစ်မှာ ဘယ်နှစ်လ ရှိလဲ?", ["၁၀လ", "၁၁လ", "၁၂လ", "၁၃လ"], 2),
    ("ရွှေတိဂုံစေတီတော် ဘယ်မြို့မှာ ရှိလဲ?", ["မန္တလေး", "ရန်ကုန်", "ပုဂံ", "တောင်ကြီး"], 1),
    ("အင်းလေးကန် ဘယ်ပြည်နယ်မှာ ရှိလဲ?", ["ကချင်ပြည်နယ်", "ရှမ်းပြည်နယ်", "ချင်းပြည်နယ်", "ကရင်ပြည်နယ်"], 1),
    ("မြန်မာနိုင်ငံ လွတ်လပ်ရေးရသည့်ခုနှစ်က ဘယ်နှစ်လဲ?", ["၁၉၄၅", "၁၉၄၇", "၁၉၄၈", "၁၉၅၀"], 2),
    ("သင်္ကြန်ပွဲတော်ကို များသောအားဖြင့် ဘယ်လမှာ ကျင်းပလဲ?", ["မတ်လ", "ဧပြီလ", "မေလ", "ဇွန်လ"], 1),
    ("ကမ္ဘာပေါ်မှာ အကြီးဆုံးတိုက်က ဘာလဲ?", ["အာဖရိကတိုက်", "အာရှတိုက်", "ဥရောပတိုက်", "အမေရိကတိုက်"], 1),
    ("ဂျပန်နိုင်ငံရဲ့ မြို့တော်က ဘာလဲ?", ["အိုဆာကာ", "တိုကျို", "ကျိုတို", "နာဂိုယာ"], 1),
    ("ထိုင်းနိုင်ငံရဲ့ မြို့တော်က ဘာလဲ?", ["ချင်းမိုင်", "ဘန်ကောက်", "ဖူးခက်", "ပတ္တရား"], 1),
    ("ကမ္ဘာပေါ်မှာ အမြင့်ဆုံးတောင်က ဘာလဲ?", ["K2", "ဧဗရက်စ်တောင်", "ကီလီမန်ဂျာရိုတောင်", "ဖူဂျီတောင်"], 1),
    ("ဧဖယ်လ်မျှော်စင် (Eiffel Tower) ဘယ်မြို့မှာ ရှိလဲ?", ["လန်ဒန်", "ပါရီ", "ရောမ", "ဗာလင်စီယာ"], 1),
    ("ကမ္ဘာပေါ်မှာ အကြီးဆုံး သမုဒ္ဒရာက ဘာလဲ?", ["အတ္တလန်တစ် သမုဒ္ဒရာ", "အိန္ဒိယ သမုဒ္ဒရာ", "ပစိဖိတ် သမုဒ္ဒရာ", "အာတိတ် သမုဒ္ဒရာ"], 2),
    ("၁၀ - ၄ = ဘယ်နှစ်လဲ?", ["၄", "၅", "၆", "၇"], 2),
    ("၅ x ၅ = ဘယ်နှစ်လဲ?", ["၂၀", "၂၅", "၃၀", "၃၅"], 1),
    ("၁၀၀ ÷ ၂၀ = ဘယ်နှစ်လဲ?", ["၄", "၅", "၆", "၇"], 1),
    ("၃ x ၃ = ဘယ်နှစ်လဲ?", ["၆", "၇", "၈", "၉"], 3),
    ("၉ + ၆ = ဘယ်နှစ်လဲ?", ["၁၃", "၁၄", "၁၅", "၁၆"], 2),
    ("၂၀ - ၇ = ဘယ်နှစ်လဲ?", ["၁၁", "၁၂", "၁၃", "၁၄"], 2),
    ("တောရဲ့ဘုရင် လို့ခေါ်ကြတဲ့ တိရစ္ဆာန်က ဘာလဲ?", ["ကျား", "ဆင်", "ခြင်္သေ့", "ဝံ"], 2),
    ("ကုန်းနေတိရစ္ဆာန်တွေထဲမှာ အကြီးဆုံးက ဘာလဲ?", ["ကျား", "ဆင်", "ဒရယ်", "မြင်း"], 1),
    ("ကုန်းနေတိရစ္ဆာန်တွေထဲမှာ အမြန်ဆုံးပြေးနိုင်တာ ဘာလဲ?", ["ခြင်္သေ့", "ကျား", "ချီတား", "မြင်း"], 2),
    ("ကုလားအုတ်ရဲ့ ကျောကုန်းအနုံထဲမှာ ဘာသိုလှောင်ထားလဲ?", ["ရေ", "အဆီ", "အသား", "အရိုး"], 1),
    ("ငှက်တွေက ဘယ်လိုမျိုးပွားလဲ?", ["ကလေးမွေးတယ်", "ဥကနေထွက်တယ်", "ခွဲထွက်တယ်", "အခွံဖောက်ထွက်တယ်"], 1),
    ("ရေရဲ့ ဓာတုနာမည်က ဘာလဲ?", ["CO2", "H2O", "O2", "NaCl"], 1),
    ("သက်တံရဲ့ အရောင်က ဘယ်နှစ်ရောင်ပါလဲ?", ["၅ရောင်", "၆ရောင်", "၇ရောင်", "၈ရောင်"], 2),
    ("လူ့ခန္ဓာကိုယ်ထဲမှာ သွေးကို ပန့်ပို့ပေးတဲ့ အင်္ဂါက ဘာလဲ?", ["အဆုတ်", "နှလုံး", "အသည်း", "ကျောက်ကပ်"], 1),
    ("ကမ္ဘာမြေက နေကို တစ်ပတ်လှည့်ဖို့ ဘယ်လောက်ကြာလဲ?", ["၁ ရက်", "၁ လ", "၁ နှစ်", "၁၀ နှစ်"], 2),
    ("တစ်ရက်မှာ ဘယ်နှစ်နာရီရှိလဲ?", ["၁၂", "၂၀", "၂၄", "၃၀"], 2),
    ("တနင်္ဂနွေနေ့ရဲ့ နောက်တစ်ရက်က ဘာနေ့လဲ?", ["စနေနေ့", "တနင်္လာနေ့", "အင်္ဂါနေ့", "ဗုဒ္ဓဟူးနေ့"], 1),
    ("သစ်ရွက်တွေရဲ့ ပုံမှန်အရောင်က ဘာလဲ?", ["အနီ", "အဝါ", "အစိမ်း", "အပြာ"], 2),
    ("နှင်းရဲ့ အရောင်က ဘာလဲ?", ["ဖြူ", "အနက်", "အဝါ", "အနီ"], 0),
    ("နေက ဘယ်ဘက်ကနေ ထွက်လဲ?", ["အနောက်", "တောင်", "အရှေ့", "မြောက်"], 2),
    ("တစ်ပတ်မှာ ဘယ်နှစ်ရက် ရှိလဲ?", ["၅ရက်", "၆ရက်", "၇ရက်", "၈ရက်"], 2),
    ("နွားနို့ရဲ့ ပုံမှန်အရောင်က ဘာလဲ?", ["ဖြူ", "အဝါ", "အညို", "ပြာ"], 0),
    ("ငါးတွေ ရေထဲမှာ အသက်ရှုဖို့ ဘယ်အင်္ဂါကို သုံးလဲ?", ["အဆုတ်", "ယင်ကို", "အသည်း", "နှလုံး"], 1),
    ("ကမ္ဘာပေါ်မှာ အကြီးဆုံး သဲကန္တာရက ဘာလဲ?", ["ဂိုဘီ", "ဆာဟာရ", "အာရေဗျ", "သာရ်"], 1),
    ("ပါရီမြို့က ဘယ်နိုင်ငံမှာ ရှိလဲ?", ["အီတလီ", "ပြင်သစ်", "ဂျာမနီ", "စပိန်"], 1),
    ("မြန်မာ့အမျိုးသားအားကစား (ရိုးရာ) က ဘာလဲ?", ["ဘောလုံး", "ချင်လုံ", "တင်းနစ်", "ရေကူး"], 1),
    ("ပုဂံမြို့က ဘယ်တိုင်းဒေသကြီးထဲ ရှိလဲ?", ["စစ်ကိုင်းတိုင်း", "မန္တလေးတိုင်း", "မကွေးတိုင်း", "ပဲခူးတိုင်း"], 1),
    ("မြန်မာနိုင်ငံရဲ့ တရားဝင်ဘာသာစကားက ဘာလဲ?", ["အင်္ဂလိပ်", "မြန်မာ", "ထိုင်း", "တရုတ်"], 1),
    ("ပျားရည်ကို ဘယ်ပိုးက ထုတ်လုပ်လဲ?", ["ပုရွက်ဆိတ်", "ပျား", "ပိုးကောင်", "ယင်"], 1),
    ("ကမ္ဘာပေါ်မှာ အနှေးဆုံး ရွေ့လျားတဲ့ တိရစ္ဆာန်တစ်မျိုးက ဘာလဲ?", ["လိပ်", "ချစ်ချက်", "ခွာသုံးလိပ်", "ပျား"], 0),
    ("တစ်လအတွင်း ရက်အနည်းဆုံးရှိတဲ့လက ဘယ်လလဲ?", ["ဇန်နဝါရီ", "ဖေဖော်ဝါရီ", "မတ်", "ဧပြီ"], 1),
    ("၈ + ၇ = ဘယ်နှစ်လဲ?", ["၁၃", "၁၄", "၁၅", "၁၆"], 2),
    ("၆ x ၄ = ဘယ်နှစ်လဲ?", ["၂၀", "၂၂", "၂၄", "၂၆"], 2),
    ("ရေခဲရဲ့ အခြေအနေက ဘာလဲ (အစိုင်အခဲ/အရည်/အငွေ့)?", ["အရည်", "အစိုင်အခဲ", "အငွေ့", "ဓာတ်ငွေ့"], 1),
    ("မီးရထားလမ်းပေါ်မှာ အသုံးများဆုံး သတ္တုက ဘာလဲ?", ["ရွှေ", "သံမဏိ", "ကြေး", "ခဲ"], 1),
    ("လကို ဘယ်အချိန်မှာ အကောင်းဆုံး မြင်ရလဲ?", ["နေ့ခင်း", "ညဘက်", "နံနက်", "ညနေ"], 1),
]

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]stardrop(?:@\w+)?$', 'bot1')))
async def star_giveaway_start(event):
    if event.sender_id != OWNER_ID: return
    q_text, options, correct_idx = random.choice(STAR_GIVEAWAY_QUESTIONS)
    giveaway_id = f"SG{random.randint(100000, 999999)}"
    buttons = [
        [Button.inline(f"1️⃣ {options[0]}", data=f"sgans_{giveaway_id}_0"),
         Button.inline(f"2️⃣ {options[1]}", data=f"sgans_{giveaway_id}_1")],
        [Button.inline(f"3️⃣ {options[2]}", data=f"sgans_{giveaway_id}_2"),
         Button.inline(f"4️⃣ {options[3]}", data=f"sgans_{giveaway_id}_3")],
    ]
    text = (
        f"⭐🎉 <b>STAR ကြဲပွဲ!</b> 🎉⭐\n\n"
        f"❓ <b>{escape_html(q_text)}</b>\n\n"
        f"⏱ <i>2 မိနစ်အတွင်း အဖြေမှန်ကို ရွေးပါ — ဒီ Group ထဲက အမြန်ဆုံး အဖြေမှန်ရွေးသူ "
        f"⭐ {STAR_GIVEAWAY_REWARD} ရမည်!</i>\n"
        f"🤫 <i>ရလဒ်ကို 2 မိနစ်ပြည့်မှ တစ်ပြိုင်နက် ကြေညာပါမည်။</i>"
    )
    giveaway = {
        "question": q_text, "options": options, "correct_idx": correct_idx,
        "expiry": time.time() + STAR_GIVEAWAY_DURATION, "reward": STAR_GIVEAWAY_REWARD,
        "messages": {}, "attempts": {}, "answered": set(), "owner_chat": event.chat_id,
    }
    active_star_giveaways[giveaway_id] = giveaway

    status_msg = await event.reply("⏳ <b>Star ကြဲပွဲကို Group အားလုံးဆီ ပို့နေပါသည်...</b>", parse_mode='html')
    groups = await groups_col.find().to_list(length=None)
    sent, failed = 0, 0
    for g in groups:
        chat_id = g["chat_id"]
        try:
            msg = await bot1.send_message(chat_id, text, parse_mode='html', buttons=buttons)
            giveaway["messages"][chat_id] = msg.id
            giveaway["attempts"][chat_id] = []
            sent += 1
            await asyncio.sleep(4)  # gentle pacing — same rate as /send, avoids FloodWaitError across many groups
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 2)
            try:
                msg = await bot1.send_message(chat_id, text, parse_mode='html', buttons=buttons)
                giveaway["messages"][chat_id] = msg.id
                giveaway["attempts"][chat_id] = []
                sent += 1
            except Exception:
                failed += 1
        except Exception:
            failed += 1

    await status_msg.edit(
        f"✅ <b>Star ကြဲပွဲ ပို့ပြီးပါပြီ!</b>\n"
        f"📨 <b>Group အောင်မြင်:</b> <code>{sent}</code>  │  ❌ <b>မအောင်မြင်:</b> <code>{failed}</code>\n"
        f"⏱ <i>2 မိနစ်အကြာမှာ ရလဒ် အနှစ်ချုပ်ကို ဒီမှာ ပြန်ကြေညာပါမယ်။</i>",
        parse_mode='html'
    )
    asyncio.create_task(_finalize_star_giveaway(giveaway_id))


@bot1.on(events.CallbackQuery(pattern=r'^sgans_(\S+)_(\d)$'))
async def star_giveaway_answer_callback(event):
    giveaway_id = event.pattern_match.group(1)
    if isinstance(giveaway_id, bytes): giveaway_id = giveaway_id.decode('utf-8')
    option_idx = int(event.pattern_match.group(2))
    giveaway = active_star_giveaways.get(giveaway_id)
    if not giveaway or time.time() > giveaway["expiry"]:
        return await event.answer("⏳ ဒီ Star ကြဲပွဲ ပြီးဆုံးသွားပါပြီ။", alert=True)
    chat_id = event.chat_id
    user_id = event.sender_id
    key = (chat_id, user_id)
    if key in giveaway["answered"]:
        return await event.answer("✅ သင် ဖြေပြီးသားပါ — ရလဒ်ကို စောင့်ပါ။", alert=False)
    giveaway["answered"].add(key)
    giveaway["attempts"].setdefault(chat_id, []).append((user_id, option_idx, time.time()))
    # 🩹 INTENTIONAL: never reveal correct/incorrect here — see module note above. Keeping
    # everyone guessing (and tapping) for the full window is the whole point.
    await event.answer("🗳️ သင့်အဖြေကို မှတ်တမ်းတင်ပြီးပါပြီ! ရလဒ်ကို 2 မိနစ်ပြည့်မှ ကြေညာပါမယ်။", alert=True)


async def _finalize_star_giveaway(giveaway_id):
    giveaway = active_star_giveaways.get(giveaway_id)
    if not giveaway:
        return
    await asyncio.sleep(max(0, giveaway["expiry"] - time.time()))
    reward = giveaway["reward"]
    correct_idx = giveaway["correct_idx"]
    correct_text = giveaway["options"][correct_idx]
    groups_with_winner = 0
    winners_total = 0
    for chat_id, msg_id in giveaway["messages"].items():
        attempts = giveaway["attempts"].get(chat_id, [])
        correct_attempts = sorted((a for a in attempts if a[1] == correct_idx), key=lambda a: a[2])
        if correct_attempts:
            winner_id = correct_attempts[0][0]
            await users_catcher_col.update_one({"user_id": winner_id}, {"$inc": {"star_balance": reward}}, upsert=True)
            groups_with_winner += 1
            winners_total += 1
            mention = f"<a href='tg://user?id={winner_id}'>🏆 Winner</a>"
            result_text = (
                f"⭐ <b>STAR ကြဲပွဲ ပြီးဆုံးပါပြီ!</b>\n\n"
                f"❓ {escape_html(giveaway['question'])}\n"
                f"✅ <b>အဖြေမှန်:</b> {escape_html(correct_text)}\n\n"
                f"🏆 {mention} က ဒီ Group ထဲမှာ အမြန်ဆုံး အဖြေမှန်ရွေးနိုင်ခဲ့လို့ ⭐ {reward} ရရှိသွားပါတယ်!"
            )
        else:
            result_text = (
                f"⭐ <b>STAR ကြဲပွဲ ပြီးဆုံးပါပြီ!</b>\n\n"
                f"❓ {escape_html(giveaway['question'])}\n"
                f"✅ <b>အဖြေမှန်:</b> {escape_html(correct_text)}\n\n"
                f"😢 ဒီ Group ထဲမှာ ဘယ်သူမှ အဖြေမှန် မရွေးနိုင်ခဲ့ပါဘူး။"
            )
        try:
            await bot1.edit_message(chat_id, msg_id, result_text, parse_mode='html', buttons=None)
        except Exception:
            pass
        await asyncio.sleep(0.3)  # gentle pacing on the reveal edits too

    total_groups = len(giveaway["messages"])
    try:
        await bot1.send_message(
            giveaway["owner_chat"],
            f"📊 <b>Star ကြဲပွဲ ရလဒ် အနှစ်ချုပ်</b>\n"
            f"🪐 <b>Group စုစုပေါင်း:</b> <code>{total_groups}</code>\n"
            f"🏆 <b>အနိုင်ရ Group အရေအတွက်:</b> <code>{groups_with_winner}</code>\n"
            f"⭐ <b>Star ရရှိသူ စုစုပေါင်း:</b> <code>{winners_total}</code> ယောက် (တစ်ယောက်လျှင် ⭐{reward} စီ)",
            parse_mode='html'
        )
    except Exception:
        pass
    active_star_giveaways.pop(giveaway_id, None)

# ==========================================
# 🗑️ HAITIME / RESETSTATS / GIFTALL / STEALTH
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftall(?:@\w+)?\s+(\d+(?:\.\d+)?)$', 'bot1')))
async def owner_giftall_broadcast(event):
    if event.sender_id != OWNER_ID: return
    amount = round(float(event.pattern_match.group(1)), 2)
    try:
        result = await users_catcher_col.update_many({}, {"$inc": {"wallet_balance": amount}})
        await event.reply(f"🎉 <b>GIVEAWAY</b>\n<code>{amount:,} USD</code> was given to <b>{result.modified_count}</b> players.", parse_mode='html')
    except Exception as e:
        await event.reply(f"❌ Error: <code>{e}</code>", parse_mode='html')

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
# ==========================================
# 🏰 SQUAD SYSTEM (အသင်း) - မြန်မာလို
# ==========================================
# Founding a Squad costs SQUAD_CREATION_COST Star and reserves up to SQUAD_MAX_MEMBERS seats
# (leader included). Squad "Points" = the sum of every member's total_caught + total_gifted +
# total_buys, which is what both the cross-squad Global Rank (/squads) and each member's own
# in-squad rank (shown on /squad) are sorted by — so every member contributing (catching,
# gifting, or buying) moves the whole squad up, not just the leader.
SQUAD_CREATION_COST = 100000      # ⭐ Star cost to found a Squad
SQUAD_MAX_MEMBERS = 8             # seats, leader included
SQUAD_SETUP_TIMEOUT = 1200        # 20 min to submit Name + Photo before the flow auto-cancels
SQUAD_INVITE_FEE = 10000          # ⭐ Star an invited member pays to actually join a Squad
SQUAD_INVITE_LEADER_CUT = 1000    # ⭐ of that fee the Squad leader keeps; the rest → bot3 treasury


async def get_user_squad(user_id):
    """The Squad doc the user currently belongs to (as leader or member), or None."""
    return await squads_col.find_one({"members": user_id})


async def _compute_squad_points(members):
    """One batched query for every member's contribution — returns
    (total_points, total_wealth, member_list). member_list carries each member's raw
    catch/gift/buy counts plus their combined 'points', already keyed by user_id so callers
    can look a specific member up without a second query."""
    if not members:
        return 0, 0, []
    user_docs = await users_catcher_col.find(
        {"user_id": {"$in": members}},
        {"user_id": 1, "fullname": 1, "wallet_balance": 1, "total_caught": 1, "total_gifted": 1, "total_buys": 1}
    ).to_list(length=None)
    total_points = 0
    total_wealth = 0
    member_list = []
    seen = set()
    for doc in user_docs:
        uid = doc["user_id"]
        seen.add(uid)
        pts = doc.get("total_caught", 0) + doc.get("total_gifted", 0) + doc.get("total_buys", 0)
        total_points += pts
        total_wealth += doc.get("wallet_balance", 0)
        member_list.append({
            "user_id": uid,
            "fullname": doc.get("fullname") or f"User {uid}",
            "total_caught": doc.get("total_caught", 0),
            "total_gifted": doc.get("total_gifted", 0),
            "total_buys": doc.get("total_buys", 0),
            "points": pts,
        })
    # A member listed on the Squad doc but with no users_catcher_col record yet (shouldn't
    # normally happen) still gets a zeroed row so member counts/UI stay consistent.
    for uid in members:
        if uid not in seen:
            member_list.append({"user_id": uid, "fullname": f"User {uid}", "total_caught": 0, "total_gifted": 0, "total_buys": 0, "points": 0})
    return total_points, total_wealth, member_list


async def calculate_squad_rank(squad_id):
    """Global rank (1 = highest Squad Points) among every Squad that currently exists."""
    all_squads = await squads_col.find({}, {"squad_id": 1, "members": 1}).to_list(length=None)
    if not all_squads:
        return 1
    squad_points = {}
    for sq in all_squads:
        sid = sq.get("squad_id")
        if not sid:
            continue
        pts, _, _ = await _compute_squad_points(sq.get("members", []))
        squad_points[sid] = pts
    sorted_squads = sorted(squad_points.items(), key=lambda x: x[1], reverse=True)
    for idx, (sid, _) in enumerate(sorted_squads, start=1):
        if sid == squad_id:
            return idx
    return len(sorted_squads) + 1


async def render_squad_profile(squad_doc, viewer_id, page=1):
    """Squad Profile — Page 1 is the squad's own stats PLUS the viewing member's personal
    standing inside it (their in-squad rank, points, and % contribution); Page 2 is the
    full member list ranked by contribution, with the viewer's own row marked."""
    squad_id = squad_doc["squad_id"]
    name = squad_doc.get("name", "Unnamed")
    leader_id = squad_doc.get("leader_id")
    members = squad_doc.get("members", [])

    total_points, total_wealth, member_list = await _compute_squad_points(members)
    rank = await calculate_squad_rank(squad_id)

    # Names come straight from each member's own cached `fullname` (populated on every catch)
    # rather than a live get_entity() lookup — up to 8 API round-trips per single profile view
    # would otherwise risk flood-waits on a busy bot.
    leader_entry = next((m for m in member_list if m["user_id"] == leader_id), None)
    if leader_entry:
        leader_mention = f"<a href='tg://user?id={leader_id}'><b>{escape_html(clean_display_name(leader_entry['fullname']))}</b></a>"
    else:
        leader_mention = f"<code>{leader_id}</code>"

    sorted_members = sorted(member_list, key=lambda x: x["points"], reverse=True)
    viewer_rank, viewer_entry = None, None
    for idx, m in enumerate(sorted_members, start=1):
        if m["user_id"] == viewer_id:
            viewer_rank, viewer_entry = idx, m
            break
    viewer_points = viewer_entry["points"] if viewer_entry else 0
    contribution_pct = (viewer_points / total_points * 100) if total_points > 0 else 0.0
    role_label = "👑 Squad Leader" if viewer_id == leader_id else "🧑‍🤝‍🧑 Member"

    if page == 1:
        text = (
            f"🏰 <b>SQUAD PROFILE</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"📛 <b>Name:</b> <code>{escape_html(name)}</code>\n"
            f"👑 <b>Leader:</b> {leader_mention}\n"
            f"🏅 <b>Global Rank:</b> <code>#{rank}</code>\n"
            f"👥 <b>Members:</b> <code>{len(members)} / {SQUAD_MAX_MEMBERS}</code>\n"
            f"⭐ <b>Squad Points:</b> <code>{total_points:,}</code>\n"
            f"💰 <b>Total Wealth:</b> <code>{format_usd(total_wealth)}</code>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>YOUR STANDING</b>\n"
            f"🪪 <b>Role:</b> {role_label}\n"
            f"🎖 <b>Your Rank in Squad:</b> <code>#{viewer_rank if viewer_rank else '-'} / {len(members)}</code>\n"
            f"⭐ <b>Your Points:</b> <code>{viewer_points:,}</code> <i>({contribution_pct:.1f}% of squad)</i>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"<i>👇 Member စာရင်းကြည့်ရန် အောက်ခလုတ်နှိပ်ပါ။</i>"
        )
        buttons = [[Button.inline("👥 Member List (Page 2)", data=f"squad_page_{squad_id}_2")]]
        return text, buttons

    # Page 2: full member list, ranked by contribution, viewer's own row marked
    member_lines = []
    for idx, m in enumerate(sorted_members, start=1):
        mention = f"<a href='tg://user?id={m['user_id']}'><b>{escape_html(clean_display_name(m['fullname']))}</b></a>"
        crown = " 👑" if m["user_id"] == leader_id else ""
        you_tag = " <i>(You)</i>" if m["user_id"] == viewer_id else ""
        member_lines.append(
            f"{idx}. {mention}{crown}{you_tag}\n"
            f"   └─ 🎯 <code>{m['total_caught']}</code> | 🎁 <code>{m['total_gifted']}</code> | 🛒 <code>{m['total_buys']}</code> | ⭐ <code>{m['points']:,}</code>"
        )

    text = (
        f"🏰 <b>SQUAD MEMBERS</b> <i>(Active Ranking)</i>\n"
        f"📛 <b>Squad:</b> <code>{escape_html(name)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        + "\n".join(member_lines[:SQUAD_MAX_MEMBERS]) +
        f"\n━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>👑 Leader | ⭐ = 🎯Catch + 🎁Gift + 🛒Buy</i>"
    )
    buttons = [[Button.inline("⬅️ Back to Profile", data=f"squad_page_{squad_id}_1")]]
    return text, buttons


async def send_squad_profile_message(event, squad_doc, page=1):
    text, buttons = await render_squad_profile(squad_doc, event.sender_id, page=page)
    storage_msg_id = squad_doc.get("storage_msg_id")
    if storage_msg_id:
        try:
            storage_msg = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_msg_id)
            if storage_msg and storage_msg.media:
                await _out(event, text, parse_mode='html', file=storage_msg.media, buttons=buttons)
                return
        except Exception:
            pass
    await _out(event, text, parse_mode='html', buttons=buttons)


# ==========================================
# 📝 1. Squad တည်ထောင်ခြင်း (/create)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]create(?:@\w+)?$', 'bot1')))
async def squad_create_command(event):
    user_id = event.sender_id

    if await get_user_squad(user_id):
        return await _out(event, "❌ သင်သည် Squad တစ်ခုထဲမှာ ရှိပြီးသားပါ။", parse_mode='html')

    if user_id in pending_squad_setup:
        return await _out(
            event,
            "⏳ သင့်ရဲ့ Squad တည်ထောင်ခြင်း လုပ်ငန်းစဉ် တစ်ခု ဆက်လက်လုပ်ဆောင်နေဆဲပါ။\n"
            "ပယ်ဖျက်ချင်ရင် <code>/cancelsquad</code> ရိုက်ပါ (Star ပြန်အမ်းပေးပါမယ်)။",
            parse_mode='html'
        )

    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    star_bal = user_doc.get("star_balance", 0) if user_doc else 0
    if star_bal < SQUAD_CREATION_COST:
        return await _out(
            event,
            f"❌ Squad တည်ထောင်ဖို့ <code>{SQUAD_CREATION_COST:,}⭐</code> လိုပါတယ်။ "
            f"မင်းမှာ <code>{format_star_plain(star_bal)}</code> ပဲရှိတယ်။",
            parse_mode='html'
        )

    text = (
        f"🏰 <b>Squad တည်ထောင်ရန်</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"💰 <b>တည်ထောင်စရိတ်:</b> <code>{SQUAD_CREATION_COST:,}⭐</code>\n"
        f"👥 <b>အများဆုံးအသင်းသား:</b> <code>{SQUAD_MAX_MEMBERS} ယောက်</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>Squad တည်ထောင်ပြီးပါက အောက်ပါအဆင့်များ ဆက်လုပ်ရမယ်။</i>\n"
        f"1️⃣ Squad Name ပေးရမယ်\n"
        f"2️⃣ Squad Profile Photo/Video ပေးရမယ်\n\n"
        f"တည်ထောင်မလား?"
    )
    buttons = [
        [Button.inline("✅ တည်ထောင်မယ်", data=f"squad_create_confirm_{user_id}"),
         Button.inline("❌ မတည်ထောင်ဘူး", data=f"squad_create_cancel_{user_id}")]
    ]
    await _out(event, text, parse_mode='html', buttons=buttons)


async def _squad_setup_timeout_watchdog(user_id, origin_chat_id, deadline):
    """If Name+Photo aren't both submitted within SQUAD_SETUP_TIMEOUT, refunds the Star cost
    and clears the pending state — otherwise a user who abandons the flow partway through
    would have paid SQUAD_CREATION_COST for a Squad that never gets created, with no way back
    short of an admin manually fixing their balance."""
    wait_for = deadline - time.time()
    if wait_for > 0:
        await asyncio.sleep(wait_for)
    state = pending_squad_setup.get(user_id)
    if not state or state.get("deadline") != deadline:
        return  # already completed, cancelled, or superseded by a newer attempt
    pending_squad_setup.pop(user_id, None)
    try:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"star_balance": SQUAD_CREATION_COST}})
    except Exception as e:
        logging.error(f"❌ Squad setup refund failed for {user_id}: {e}")
        return
    notice = (
        f"⏳ <b>Squad Setup Timeout</b>\n"
        f"Squad Name/Photo ကို {SQUAD_SETUP_TIMEOUT // 60} မိနစ်အတွင်း လက်ခံရရှိခြင်း မရှိလို့ "
        f"Squad တည်ထောင်ခြင်းကို အလိုအလျောက် ပယ်ဖျက်လိုက်ပါပြီ။\n"
        f"⭐ <code>{SQUAD_CREATION_COST:,}</code> ကို ပြန်အမ်းပေးလိုက်ပါပြီ။ <code>/create</code> နဲ့ ပြန်စနိုင်ပါတယ်။"
    )
    try:
        await bot1.send_message(user_id, notice, parse_mode='html')
        return
    except Exception:
        pass
    try:
        await send_safe_message(bot1, origin_chat_id, notice, parse_mode='html')
    except Exception:
        pass


# ==========================================
# 🔘 Squad Creation Callbacks
# ==========================================
@bot1.on(events.CallbackQuery(pattern=r'^squad_create_confirm_(\d+)$'))
async def squad_create_confirm_callback(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("⚠️ ဒါ မင်းရဲ့ လုပ်ဆောင်ချက် မဟုတ်ဘူး။", alert=True)

    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်ပါ...", alert=False)

    if await get_user_squad(user_id):
        await event.edit("❌ သင်သည် Squad တစ်ခုထဲမှာ ရှိပြီးသားပါ။", parse_mode='html', buttons=None)
        return await event.answer("Already in squad.", alert=True)

    if user_id in pending_squad_setup:
        await event.edit("⏳ Squad တည်ထောင်ခြင်း လုပ်ငန်းစဉ် တစ်ခု ရှိနှင့်ပြီးသားပါ။", parse_mode='html', buttons=None)
        return await event.answer("Already pending.", alert=True)

    if not await try_deduct_star(user_id, SQUAD_CREATION_COST):
        await event.edit(f"❌ Star မလုံလောက်ပါ။ <code>{SQUAD_CREATION_COST:,}⭐</code> လိုပါတယ်။", parse_mode='html', buttons=None)
        return await event.answer("Insufficient Star.", alert=True)

    prompt_msg = await event.edit(
        "✅ <b>Star နှုတ်ယူပြီးပါပြီ!</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "ပထမဆုံးအနေနဲ့ <b>Squad Name</b> ကို ဒီမက်ဆေ့ခ်ျကို <u>Reply</u> ကာ ရိုက်ထည့်ပါ။\n"
        "<i>(ဘယ် Font နဲ့ရေးရေး လက်ခံပါတယ်)</i>\n\n"
        f"⏳ <i>{SQUAD_SETUP_TIMEOUT // 60} မိနစ်အတွင်း မပြီးစီးရင် Star ကို အလိုအလျောက် ပြန်အမ်းပေးပါမယ်။</i>",
        parse_mode='html', buttons=None
    )
    deadline = time.time() + SQUAD_SETUP_TIMEOUT
    pending_squad_setup[user_id] = {
        "stage": "name",
        "name": None,
        "chat_id": event.chat_id,
        "prompt_msg_id": prompt_msg.id,
        "deadline": deadline,
    }
    asyncio.create_task(_squad_setup_timeout_watchdog(user_id, event.chat_id, deadline))
    await event.answer("✅ Star နှုတ်ပြီးပါပြီ။ Name ထည့်ပါ။", alert=True)


@bot1.on(events.CallbackQuery(pattern=r'^squad_create_cancel_(\d+)$'))
async def squad_create_cancel_callback(event):
    user_id = int(event.pattern_match.group(1))
    if event.sender_id != user_id:
        return await event.answer("⚠️ ဒါ မင်းရဲ့ လုပ်ဆောင်ချက် မဟုတ်ဘူး။", alert=True)
    await event.edit("❌ Squad တည်ထောင်ခြင်းကို ပယ်ဖျက်လိုက်ပါပြီ။", parse_mode='html', buttons=None)
    await event.answer("Cancelled.", alert=True)


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]cancelsquad(?:@\w+)?$', 'bot1')))
async def squad_cancel_setup_command(event):
    """Lets a user back out of an in-progress /create flow early (Star refunded immediately)
    instead of having to wait out the full SQUAD_SETUP_TIMEOUT for the watchdog to do it."""
    user_id = event.sender_id
    state = pending_squad_setup.pop(user_id, None)
    if not state:
        return await _out(event, "❌ ပယ်ဖျက်ရန် Squad တည်ထောင်ခြင်း လုပ်ငန်းစဉ် မရှိပါ။", parse_mode='html')
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"star_balance": SQUAD_CREATION_COST}})
    await _out(
        event,
        f"✅ Squad တည်ထောင်ခြင်းကို ပယ်ဖျက်ပြီး Star <code>{SQUAD_CREATION_COST:,}⭐</code> ကို ပြန်အမ်းပေးလိုက်ပါပြီ။",
        parse_mode='html'
    )


# ==========================================
# 📝 2. Squad Name နဲ့ Photo လက်ခံခြင်း (Reply Handler)
# ==========================================
# Only ever consumes an explicit reply to the EXACT prompt message this flow itself just sent
# (matched on both chat_id and message_id) — any other message from that user, anywhere else,
# passes straight through untouched. Without this check a broad incoming=True handler like
# this one would risk swallowing a completely unrelated message the user happens to send in
# some other group while a /create flow is still pending.
@bot1.on(events.NewMessage(incoming=True))
async def squad_setup_reply_handler(event):
    user_id = event.sender_id
    state = pending_squad_setup.get(user_id)
    if not state:
        return
    if not event.is_reply or event.chat_id != state["chat_id"] or event.reply_to_msg_id != state["prompt_msg_id"]:
        return

    if state["stage"] == "name":
        if not event.raw_text or not event.raw_text.strip():
            await event.reply("❌ Squad Name ကို စာသားအနေနဲ့ ရိုက်ထည့်ပြီး ဒီစာကို Reply ပြန်ပါ။")
            return
        squad_name = clean_display_name(event.raw_text.strip(), max_len=40, fallback="Unnamed Squad")
        state["name"] = squad_name
        state["stage"] = "photo"
        prompt_msg = await event.reply(
            f"✅ Squad Name <code>{escape_html(squad_name)}</code> ကို သိမ်းဆည်းလိုက်ပါပြီ။\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "အခု <b>Squad Profile Photo</b> (Photo/Video) ကို ဒီစာကို <u>Reply</u> ကာ ပို့ပေးပါ။",
            parse_mode='html'
        )
        state["prompt_msg_id"] = prompt_msg.id
        return

    if state["stage"] == "photo":
        if not (event.photo or event.video or event.document):
            await event.reply("❌ Photo သို့မဟုတ် Video တစ်ခု ပို့ပြီး ဒီစာကို Reply ပြန်ပါ။")
            return
        try:
            fwd_msg = await send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=event.media)
            storage_msg_id = fwd_msg.id
        except Exception as e:
            await event.reply(f"❌ Media သိမ်းဆည်းရာမှာ အမှားရှိသွားတယ်: {escape_html(str(e))}")
            return

        squad_name = state.get("name") or "Unnamed Squad"
        squad_id = f"SQD_{random.randint(10000, 99999)}"
        while await squads_col.find_one({"squad_id": squad_id}):
            squad_id = f"SQD_{random.randint(10000, 99999)}"

        await squads_col.insert_one({
            "squad_id": squad_id,
            "name": squad_name,
            "leader_id": user_id,
            "members": [user_id],
            "storage_msg_id": storage_msg_id,
            "created_at": time.time(),
        })
        pending_squad_setup.pop(user_id, None)

        await event.reply(
            f"✅ <b>Squad တည်ထောင်ခြင်း အောင်မြင်ပါပြီ!</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"📛 <b>Squad Name:</b> <code>{escape_html(squad_name)}</code>\n"
            f"🆔 <b>Squad ID:</b> <code>{squad_id}</code>",
            parse_mode='html'
        )

        squad_doc = await squads_col.find_one({"squad_id": squad_id})
        if squad_doc:
            await send_squad_profile_message(event, squad_doc)
        return


# ==========================================
# 📊 3. Squad Profile ပြသခြင်း (/squad သို့မဟုတ် /squadprofile)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]squad(?:profile)?(?:@\w+)?$', 'bot1')))
async def squad_profile_command(event):
    user_id = event.sender_id
    squad_doc = await get_user_squad(user_id)
    if not squad_doc:
        return await _out(event, "❌ သင်သည် Squad တစ်ခုခုထဲမှာ မပါဝင်သေးပါ။ <code>/create</code> နဲ့ တည်ထောင်ပါ။", parse_mode='html')
    await send_squad_profile_message(event, squad_doc, page=1)


# ==========================================
# 🔘 Squad Page Navigation Callback
# ==========================================
@bot1.on(events.CallbackQuery(pattern=r'^squad_page_([a-zA-Z0-9_]+)_(\d+)$'))
async def squad_page_callback(event):
    squad_id = event.pattern_match.group(1)
    if isinstance(squad_id, bytes):
        squad_id = squad_id.decode('utf-8')
    page = int(event.pattern_match.group(2))

    user_id = event.sender_id
    squad_doc = await squads_col.find_one({"squad_id": squad_id})
    if not squad_doc:
        return await event.answer("❌ Squad မရှိတော့ဘူး။", alert=True)
    if user_id not in squad_doc.get("members", []):
        return await event.answer("⚠️ ဒီ Squad ထဲမှာ မင်းမပါဘူး။", alert=True)

    text, buttons = await render_squad_profile(squad_doc, user_id, page=page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
    except errors.MessageNotModifiedError:
        pass
    await event.answer()


# ==========================================
# 👥 4. Squad ထဲသို့ ဖိတ်ကြားခြင်း (/invite) — ဝင်ကြေး SQUAD_INVITE_FEE ⭐ ပါ
# ==========================================
# Flow: leader /invite (reply) sends a request only — nothing is charged or added yet.
# The INVITED user then taps Accept, which is the only point money actually moves:
#   target pays SQUAD_INVITE_FEE ⭐ total → SQUAD_INVITE_LEADER_CUT ⭐ of it goes straight to
#   the leader's star_balance, the remainder goes to the bot3 treasury (star side) exactly
#   like every other bot3 economy flow, via bot3_treasury_adjust. Only after the fee clears
#   does the target actually get added to squads_col.members.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]invite(?:@\w+)?$', 'bot1')))
async def squad_invite_command(event):
    user_id = event.sender_id
    squad_doc = await get_user_squad(user_id)
    if not squad_doc:
        return await _out(event, "❌ သင်သည် Squad တစ်ခုခုထဲမှာ မပါဝင်သေးပါ။", parse_mode='html')

    if squad_doc.get("leader_id") != user_id:
        return await _out(event, "❌ Squad Leader မှသာ ဖိတ်ကြားနိုင်ပါတယ်။", parse_mode='html')

    members = squad_doc.get("members", [])
    if len(members) >= SQUAD_MAX_MEMBERS:
        return await _out(event, f"❌ Squad ပြည့်နေပါပြီ။ ({SQUAD_MAX_MEMBERS} ယောက်)", parse_mode='html')

    if not event.is_reply:
        return await _out(event, "📌 ဖိတ်ချင်တဲ့ User ကို Reply လုပ်ပြီး <code>/invite</code> ရိုက်ပါ။", parse_mode='html')

    reply_msg = await event.get_reply_message()
    target_id = reply_msg.sender_id if reply_msg else None
    if not target_id:
        return await _out(event, "❌ ဒီ Message ကို ပို့ခဲ့သူကို မတွေ့ပါ။", parse_mode='html')
    if target_id == user_id:
        return await _out(event, "❌ ကိုယ့်ကိုယ်ကို ဖိတ်လို့မရဘူး။", parse_mode='html')
    if target_id in bot_ids:
        return await _out(event, "❌ Bot ကို ဖိတ်လို့မရဘူး။", parse_mode='html')

    target_squad = await get_user_squad(target_id)
    if target_squad:
        return await _out(event, "❌ ဒီ User က Squad တစ်ခုထဲမှာ ရှိပြီးသားပါ။", parse_mode='html')

    target_mention = await get_html_mention(event, target_id)
    leader_mention = await get_html_mention(event, user_id)
    squad_name = escape_html(squad_doc.get('name', ''))
    await _out(
        event,
        f"🏰 {leader_mention} က {target_mention} ကို Squad <code>{squad_name}</code> ထဲ ဖိတ်ကြားလိုက်ပါပြီ။\n"
        f"⏳ <b>{target_mention} ရဲ့ အတည်ပြုချက်ကို စောင့်နေပါတယ်။</b>",
        parse_mode='html'
    )

    buttons = [[
        Button.inline(f"✅ ဝင်မယ် ({SQUAD_INVITE_FEE:,}⭐ ပေးမယ်)", data=f"sqinv_ok_{squad_doc['squad_id']}_{user_id}_{target_id}"),
        Button.inline("❌ ငြင်းမယ်", data=f"sqinv_no_{squad_doc['squad_id']}_{user_id}_{target_id}")
    ]]
    try:
        await bot1.send_message(
            target_id,
            f"🏰 {leader_mention} က မင်းကို Squad <code>{squad_name}</code> ထဲ ဖိတ်ကြားလိုက်ပါပြီ။\n"
            f"💵 <b>ဝင်ကြေး −</b> <code>{SQUAD_INVITE_FEE:,}⭐</code>\n"
            f"<i>(Leader ကို {SQUAD_INVITE_LEADER_CUT:,}⭐ ရောက်ပါမယ်)</i>\n\n"
            f"လက်ခံပြီး Squad ထဲဝင်မလား?",
            parse_mode='html', buttons=buttons
        )
    except Exception:
        await _out(event, "⚠️ ဖိတ်စာ ပို့လို့မရပါ — User က Bot ကို Block ထားနိုင်ပါတယ်။", parse_mode='html')

@bot1.on(events.CallbackQuery(pattern=r'^sqinv_(ok|no)_([a-zA-Z0-9_]+)_(\d+)_(\d+)$'))
async def squad_invite_response_callback(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    squad_id = event.pattern_match.group(2)
    if isinstance(squad_id, bytes):
        squad_id = squad_id.decode('utf-8')
    leader_id = int(event.pattern_match.group(3))
    target_id = int(event.pattern_match.group(4))

    if event.sender_id != target_id:
        return await event.answer("⚠️ ဒီဖိတ်စာက မင်းအတွက်မဟုတ်ဘူး။", alert=True)

    if not claim_single_tap(event):
        return await event.answer("⏳ ခဏစောင့်ပါ...", alert=False)

    if action == "no":
        try:
            await event.edit("❌ <b>ဖိတ်စာကို ငြင်းလိုက်ပါပြီ။</b>", parse_mode='html', buttons=None)
        except errors.MessageNotModifiedError:
            pass
        return await event.answer()

    squad_doc = await squads_col.find_one({"squad_id": squad_id})
    if not squad_doc or squad_doc.get("leader_id") != leader_id:
        return await event.edit("❌ <b>Squad ဒါမှမဟုတ် Leader ပြောင်းလဲသွားပါပြီ — ဖိတ်စာ သက်တမ်းကုန်သွားပါပြီ။</b>", parse_mode='html', buttons=None)

    existing_squad = await get_user_squad(target_id)
    if existing_squad:
        return await event.edit("❌ <b>မင်း Squad တစ်ခုခုထဲမှာ ရှိနေပြီးသားပါ။</b>", parse_mode='html', buttons=None)

    if len(squad_doc.get("members", [])) >= SQUAD_MAX_MEMBERS:
        return await event.edit(f"❌ <b>Squad ပြည့်နေပါပြီ။</b> ({SQUAD_MAX_MEMBERS} ယောက်)", parse_mode='html', buttons=None)

    if not await try_deduct_star(target_id, SQUAD_INVITE_FEE):
        return await event.answer(f"❌ Star Balance မလုံလောက်ပါ။ {SQUAD_INVITE_FEE:,}⭐ လိုအပ်ပါတယ်။", alert=True)

    # Same atomic slot-guard as before — now happens at accept-time instead of invite-time.
    result = await squads_col.update_one(
        {"squad_id": squad_id, f"members.{SQUAD_MAX_MEMBERS - 1}": {"$exists": False}},
        {"$addToSet": {"members": target_id}}
    )
    if result.modified_count == 0:
        # Squad filled up in the gap between the checks above and this write — refund in full.
        await users_catcher_col.update_one({"user_id": target_id}, {"$inc": {"star_balance": SQUAD_INVITE_FEE}})
        return await event.edit(f"❌ <b>Squad ပြည့်သွားပါပြီ — ဝင်ကြေး ပြန်အမ်းပေးလိုက်ပါပြီ။</b>", parse_mode='html', buttons=None)

    remainder = SQUAD_INVITE_FEE - SQUAD_INVITE_LEADER_CUT
    await users_catcher_col.update_one({"user_id": leader_id}, {"$inc": {"star_balance": SQUAD_INVITE_LEADER_CUT}}, upsert=True)
    await bot3_treasury_adjust(star=remainder)

    target_mention = await get_html_mention(event, target_id)
    squad_name = escape_html(squad_doc.get('name', ''))
    await event.edit(
        f"✅ <b>{target_mention} Squad <code>{squad_name}</code> ထဲ ဝင်ရောက်လိုက်ပါပြီ!</b>\n"
        f"💸 ပေးဆောင် − <code>{SQUAD_INVITE_FEE:,}⭐</code>",
        parse_mode='html', buttons=None
    )
    await event.answer("🎉 Squad ထဲဝင်ရောက်ပါပြီ!")
    try:
        leader_mention = await get_html_mention(event, leader_id)
        await bot1.send_message(
            leader_id,
            f"🎉 {target_mention} က Squad <code>{squad_name}</code> ထဲ ဝင်ရောက်လိုက်ပါပြီ!\n"
            f"⭐ <b>ရရှိ −</b> <code>+{SQUAD_INVITE_LEADER_CUT:,}⭐</code>",
            parse_mode='html'
        )
    except Exception:
        pass


# ==========================================
# 📋 5. Squad အားလုံးစာရင်း (/squads သို့မဟုတ် /topsquads)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](squads|topsquads)(?:@\w+)?$', 'bot1')))
async def squad_list_command(event):
    # Squad creation is expensive (SQUAD_CREATION_COST Star each), so this list is never going
    # to be huge in practice — but this cap keeps a busy server from ever having to fully
    # recompute points for an unbounded number of squads on a single /squads call.
    all_squads = await squads_col.find({}).sort("created_at", -1).limit(200).to_list(length=None)
    if not all_squads:
        return await _out(event, "📭 Squad မရှိသေးပါ။ <code>/create</code> နဲ့ ပထမဆုံး Squad တည်ထောင်လိုက်ပါ။", parse_mode='html')

    viewer_squad = await get_user_squad(event.sender_id)
    viewer_squad_id = viewer_squad.get("squad_id") if viewer_squad else None

    squad_summaries = []
    for sq in all_squads:
        members = sq.get("members", [])
        pts, _, member_list = await _compute_squad_points(members)
        leader_entry = next((m for m in member_list if m["user_id"] == sq.get("leader_id")), None)
        leader_name = clean_display_name(leader_entry["fullname"]) if leader_entry else f"User {sq.get('leader_id')}"
        squad_summaries.append({
            "name": sq.get("name", "Unnamed"),
            "squad_id": sq.get("squad_id"),
            "members": len(members),
            "points": pts,
            "leader_name": leader_name,
        })

    squad_summaries.sort(key=lambda x: x["points"], reverse=True)
    top10 = squad_summaries[:10]

    lines = []
    viewer_in_top10 = False
    for idx, sq in enumerate(top10, start=1):
        medal = "🥇" if idx == 1 else "🥈" if idx == 2 else "🥉" if idx == 3 else f"#{idx}"
        you_tag = ""
        if sq["squad_id"] == viewer_squad_id:
            you_tag = " 👈 <i>(Your Squad)</i>"
            viewer_in_top10 = True
        lines.append(
            f"{medal} <b>{escape_html(sq['name'])}</b>{you_tag}\n"
            f"   └─ 👑 {escape_html(sq['leader_name'])} | 👥 <code>{sq['members']}/{SQUAD_MAX_MEMBERS}</code> | ⭐ <code>{sq['points']:,}</code>"
        )

    footer_note = ""
    if viewer_squad_id and not viewer_in_top10:
        for idx, sq in enumerate(squad_summaries, start=1):
            if sq["squad_id"] == viewer_squad_id:
                footer_note = f"\n\n📍 <i>Your Squad (</i><b>{escape_html(sq['name'])}</b><i>) is ranked</i> <code>#{idx}</code>"
                break

    text = (
        f"🏆 <b>TOP 10 SQUADS</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        + "\n".join(lines) +
        f"\n━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>Points = Catches + Gifts + Buys (စုစုပေါင်း)</i>"
        + footer_note
    )
    await _out(event, text, parse_mode='html')


# ==========================================
# 💰 /fixbalance — Owner: လူတိုင်းရဲ့ လက်ကျန်ငွေကို USD 10,000 နဲ့ Star 500 ပြန်သတ်မှတ်မယ် (Owner မပါ)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]fixbalance(?:@\w+)?$', 'bot1')))
async def owner_fix_all_balances(event):
    if event.sender_id != OWNER_ID:
        return

    status_msg = await event.reply("⏳ <b>လူတိုင်းရဲ့ လက်ကျန်ငွေကို USD 10,000 နဲ့ Star 500 ပြန်သတ်မှတ်နေပါပြီ (Owner မပါ)...</b>", parse_mode='html')
    
    try:
        # Owner ကိုချန်လှပ်ပြီး ကျန်သူအားလုံးကို update လုပ်မယ်
        result = await users_catcher_col.update_many(
            {"user_id": {"$ne": OWNER_ID}},  # Owner မဟုတ်သူများ
            {"$set": {"wallet_balance": 10000.00, "star_balance": 500.00}}
        )
        
        await status_msg.edit(
            f"✅ <b>Balance Reset Complete!</b>\n"
            f"👥 <b>Users updated:</b> <code>{result.modified_count}</code>\n"
            f"💰 <b>New USD:</b> <code>$10,000.00</code>\n"
            f"⭐ <b>New Star:</b> <code>500 ⭐</code>\n\n"
            f"<i>(Owner အကောင့်ကို ထိခိုက်မှုမရှိစေရ ချန်လှပ်ထားပါသည်။)</i>",
            parse_mode='html'
        )
    except Exception as e:
        await status_msg.edit(f"❌ Error: <code>{escape_html(str(e))}</code>", parse_mode='html')
# ==========================================
# 🚀 SYSTEM INITIALIZATION
# ==========================================
# Two bots run in the same process, side by side:
#   bot1 — the public-facing game bot (everything, including what used to be the separate
#          Guard Bot: artist rewards, premium daily Star, force-join-room game moderation)
#   bot2 — owner-only control bot: /addchar, /ktr, /ktrr, /shadow, /unshadow
# Each has its own independent reconnect loop so a disconnect/crash on one never takes
# the other down with it; asyncio.gather runs both loops concurrently forever.
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
            await load_disabled_buy_tiers_cache()
            await load_group_spawn_counters_cache()
            asyncio.create_task(ghost_spawn_cleaner())
            # ⭐ Star's rate is now a fixed peg (see /setstarrate) — no background drift task.
            asyncio.create_task(group_counter_flush_loop())
            print("📅 Background tasks started.")
            await bot1.run_until_disconnected()
        except Exception as system_fault:
            print(f"⚠️ Main Bot disconnected: {system_fault}")
            print("⏳ Restarting Main Bot in 30 seconds...")
            await asyncio.sleep(30)

async def run_bot2_forever():
    global BOT2_USERNAME
    while True:
        try:
            print("🚀 Connecting Owner Bot (bot2)...")
            await bot2.start(bot_token=OWNER_BOT_TOKEN)
            me_owner = await bot2.get_me()
            print(f"✅ Owner Bot connected as @{me_owner.username}")
            if me_owner.username: BOT2_USERNAME = me_owner.username.lower()
            if me_owner.id not in bot_ids: bot_ids.append(me_owner.id)
            await bot2.run_until_disconnected()
        except Exception as system_fault:
            print(f"⚠️ Owner Bot disconnected: {system_fault}")
            print("⏳ Restarting Owner Bot in 30 seconds...")
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
    await asyncio.gather(run_bot1_forever(), run_bot2_forever())

if __name__ == "__main__":
    try:
        asyncio.run(start_system())
    except (KeyboardInterrupt, SystemExit):
        print("Bot System Shutting Down.")
        
