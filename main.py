#############.
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
from bson import ObjectId  # used by the 🛒 market feature to look up listings by _id
from html import escape as escape_html
from telethon.errors import FloodWaitError
from telethon import TelegramClient, events, functions, types, Button, errors
from telethon import utils as tl_utils  # pack_bot_file_id — used by /addtriviamedia
from telethon.tl.types import ChannelParticipantsAdmins
from telethon.extensions import html
from telethon.tl.types import MessageEntityCustomEmoji
from telethon.sessions import StringSession
from typing import Optional, List, Dict, Set, Tuple
# 🩹 REMOVED (per owner report): "import redis.asyncio as redis" used to live here. See the
# block right below (where REDIS_URL/redis_client used to be defined) for why it's gone.

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
        self._gban_notice_last_sent = {}      # user_id -> ts — throttles the /gban "you're banned" reply only

        # ---- Caches with an explicit (payload, expiry_ts) or {"expiry": ts} shape ----
        self.force_sub_membership_cache = {}  # user_id -> (is_member, expiry_ts)
        self.market_force_sub_membership_cache = {}  # user_id -> (is_member, expiry_ts) — separate cache, separate group (see MARKET_FORCE_SUB_INVITE_LINK)
        self._welcome_toggle_cache = {}       # chat_id -> (enabled, ts)
        self._spawn_target_cache = {}         # chat_id -> (spawn_target, ts)
        self.admin_cache = {}                 # chat_id -> {"ids": [...], "expiry": ts}
        self.gbanned_until = {}               # user_id -> {"expiry","reason","duration_label"} — see is_gbanned() near bot1's creation

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
        self.pending_gban_prompt_ids = {}  # /gban wizard: reply_to_msg_id -> {"step","target_id","target_name","reason"}
        self.pending_ccm_event_prompt_ids = {}  # /setvalue's SUPREME event-value picker: reply_to_msg_id -> event_name

        # ---- LIVE game/feature state — deliberately EXCLUDED from cleanup_expired(). Each of
        # these already has its own dedicated timeout task elsewhere that removes an entry at
        # exactly the right moment (spawn timeout, quiz timeout, game round ending, etc.). A
        # generic time-based sweep here could race with that and tear down something mid-play. ----
        self.active_group_spawns = {}
        self.active_haido_events = {}
        self.pending_rarity_quiz = {}
        self.pending_trivia_quiz = {}  # 🧠 TRIVIA — chat_id -> {"options","correct_index","question","msg_id","quiz_time","solved","attempted_users","revealed"}

        # ---- Trivia's own message-count spawn trigger — fully independent of
        # group_spawn_counters (character spawns), same "separate counter, separate pacing"
        # design as the character-spawn one above. Safe to exclude from cleanup_expired() too:
        # worst case on a restart is losing a few messages' progress toward the next question,
        # never a stuck state (there's no timeout tied to these, unlike pending_trivia_quiz). ----
        self.trivia_spawn_counters = {}
        self.trivia_spawn_targets = {}

        # ---- asyncio.Lock factories — never swept; a lock can be actively held ----
        self.spawn_locks = defaultdict(asyncio.Lock)
        self.bot_added_locks = defaultdict(asyncio.Lock)
        # 🩹 FIX (market_sellpick_choose_callback "Cannot open exclusive conversation" /
        # PeerIdInvalidError spam): user_id -> asyncio.Lock. bot1.conversation(<user_id>, ...)
        # is keyed by peer in Telethon's own client-side registry, and by default is
        # "exclusive" — only ONE such conversation may be open per peer at a time, across
        # EVERY feature that opens one. Both the sell flow (market_sellpick_choose_callback)
        # and the bid flow (market_bid_start_callback) open a private conversation keyed by
        # user_id, so a user tapping two different sell/bid rows in a row (two different
        # callback datas, so claim_single_tap alone can't catch it), or tapping "Sell" while a
        # bid conversation with them is still open, opens two conversations for the same peer
        # and the second one raises "Cannot open exclusive conversation in a chat that already
        # has one open conversation". Shared across both flows so they can't collide either.
        self.market_dm_conversation_locks = defaultdict(asyncio.Lock)

        # {chat_id: [(event, user_id), ...]} — the catch-race judging buffer. See
        # CATCH_RACE_JUDGE_WINDOW's docstring near catch_handler for what this is for.
        # Self-clearing: catch_handler always pops its own chat_id back out once judged, so
        # there's nothing here to sweep.
        self.catch_race_buffer = {}

        # ---- Misc ----
        self.bot_ids = []
        self.admin_warned_sticker = set()  # (chat_id, admin_id)
        self.admin_warned_char = set()     # (chat_id, admin_id)

        # ⚡ PERFORMANCE: the unlimited vault (OWNER_ID / added_owner_ids in send_paginated_harem)
        # is IDENTICAL for every such viewer at a given rarity filter — always the whole roster,
        # nothing personal. rarity_filter (or "__all__") -> (pages, page_char_ids_per_page, expiry_ts).
        # See invalidate_character_caches() for the roster-change invalidation path.
        self._unlimited_vault_pages_cache = {}

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
                  self.force_sub_prompt_last_sent, self.user_mute_until, self._gban_notice_last_sent):
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
        for d in (self.admin_cache, self.gbanned_until):
            stale_keys = [k for k, v in list(d.items()) if isinstance(v, dict) and now > v.get("expiry", 0)]
            for k in stale_keys:
                del d[k]
                removed += 1
        # {key: (..., ..., expiry_ts)} — the unlimited-vault pages cache stores its expiry as
        # the LAST tuple element (see send_paginated_harem) rather than the second.
        stale_keys = [k for k, v in list(self._unlimited_vault_pages_cache.items())
                      if isinstance(v, tuple) and len(v) >= 1 and now > v[-1]]
        for k in stale_keys:
            del self._unlimited_vault_pages_cache[k]
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

# Small-caps table tuned to match catch_bot's OWN ".check" reply font choices exactly, built
# from codepoint analysis of the two real replies the owner supplied. Differs from the
# general-purpose small_caps() above in exactly two verified ways: lowercase 's' is left
# completely alone — catch_bot's "ᴛɪᴍᴇs" / "ᴄᴀᴛᴄʜᴇʳs" / "ᴛʜɪs" all keep a plain 's', never 'ꜱ' —
# and lowercase 'f' becomes the Cyrillic look-alike 'ғ' (U+0493) rather than the Latin small
# capital 'ꜰ' used elsewhere in this file. Only for the catch_bot-styled /check card below;
# every other small-caps use in this file should keep using small_caps() as before.
_CATCHSTYLE_CAPS_SRC = "abcdefghijklmnopqrtuvwxyzABCDEFGHIJKLMNOPQRTUVWXYZ"  # no 's' — passthrough
_CATCHSTYLE_CAPS_DST = ("ᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀᴛᴜᴠᴡxʏᴢ" "ᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀᴛᴜᴠᴡxʏᴢ")
_CATCHSTYLE_CAPS_TRANS = str.maketrans(_CATCHSTYLE_CAPS_SRC, _CATCHSTYLE_CAPS_DST)

def catchstyle_caps(text):
    return text.translate(_CATCHSTYLE_CAPS_TRANS)

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

def name_with_event_tag(name: str, event_str) -> str:
    """Appends the compact '[emoji]' event tag to a name for display — use this instead of
    hand-rolling f'{name} [{tag}]' at a display site.
    🩹 FIX (real bug — reported: character names in /harem showing the event emoji TWICE, e.g.
    'Ram [🍷] [🍷]'). catch_bot's own '.check' replies bake the tag straight into the name text
    itself ('Ram [🍷]', 'Retsu Unohana [🥷]'), and /syncfromcatch stores that name verbatim (see
    parse_catchbot_check) so /check's catch_bot-style card can reproduce it exactly — but every
    OTHER import path (see extract_new_character_info's plain 'Character Name:' line) stores
    name WITHOUT a bracket and relies on this being appended at display time instead. A synced
    character has both: the bracket already in name AND a matching event field, so blindly
    appending here doubled it. Checking whether name already ends in that exact tag first
    handles both shapes correctly with the one helper, regardless of which import path the
    character came from."""
    tag = event_emoji_tag(event_str)
    if not tag:
        return name
    if name.rstrip().endswith(f"[{tag}]"):
        return name
    return f"{name} [{tag}]"

async def ensure_user_registered(user_id, fullname):
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {
            "$setOnInsert": {
                "total_caught": 0,
                "harem": [],
                "fullname": fullname,
                "ccm_balance": 0,  # 💰 CCM — earned from trivia only (see CURRENCY SYSTEM block)
                "gram_balance": 0,  # 🪙 GRAM — bought with ccm via /exchange (see CURRENCY SYSTEM block)
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

def telethon_env_info():
    """One-line description of the Telethon that is ACTUALLY running in this process: package
    version, TL layer, and whether it knows the "tap to copy" button type. Printed at startup
    and attached to every copy-button error report."""
    try:
        import telethon as _tl
        version = getattr(_tl, "__version__", "?")
    except Exception:
        version = "?"
    try:
        from telethon.tl.alltlobjects import LAYER as _layer
    except Exception:
        _layer = "?"
    has_copy = hasattr(types, "KeyboardButtonCopy")
    info = f"Telethon {version} · layer {_layer} · KeyboardButtonCopy: {'yes' if has_copy else 'NO'}"
    if not has_copy:
        info += f" · copy-like names in types: {sorted(n for n in dir(types) if 'copy' in n.lower()) or 'none'}"
    return info

# ---- 📋 COPY BUTTONS (2026-09) ----------------------------------------------------------
# Telegram's "tap to copy" inline button (KeyboardButtonCopy) is missing from newer Telethon
# builds (1.45.0 / layer 229 has no types.KeyboardButtonCopy at all), so every place that built
# it through Telethon silently ended up with no button. The Bot API itself still supports it
# (InlineKeyboardButton.copy_text), so when Telethon can't build the button the message is
# sent through the Bot API's HTTP endpoint instead — same bot token, same chat, same reply
# target; from the player's side it's just a normal bot reply with working copy buttons.
async def bot_api_send_with_copy_buttons(chat_id, reply_to_msg_id, text_html, rows):
    """rows = [[(button_text, copy_text), ...], ...]. Raises on ANY failure so the caller can
    fall back — never returns a half-success. The bot token is scrubbed from error text so it
    can't leak into logs or the owner alert. (httpx is already installed: openai/groq need it.)"""
    try:
        import httpx
    except ImportError:
        raise RuntimeError("httpx is not installed")
    payload = {
        "chat_id": chat_id,
        "text": text_html,
        "parse_mode": "HTML",
        "reply_parameters": {"message_id": reply_to_msg_id, "allow_sending_without_reply": True},
        "reply_markup": {"inline_keyboard": [
            [{"text": btn_text, "copy_text": {"text": copy_text}} for btn_text, copy_text in row]
            for row in rows
        ]},
    }
    try:
        async with httpx.AsyncClient(timeout=10) as http_client:
            resp = await http_client.post(f"https://api.telegram.org/bot{MAIN_BOT_TOKEN}/sendMessage", json=payload)
        data = resp.json()
    except Exception as e:
        raise RuntimeError(str(e).replace(MAIN_BOT_TOKEN, "***")) from None
    if not data.get("ok"):
        raise RuntimeError(f"Bot API {data.get('error_code')}: {data.get('description')}")
    return data["result"]

_COPY_BTN_LAST_REPORT = {}

async def _report_copy_button_problem(location, detail):
    """Prints every failure, but alerts the owner at most once per 15 minutes per location so a
    persistent problem can't turn into an alert on every single /who."""
    print(f"⚠️ {location}: {detail}")
    now = time.time()
    if now - _COPY_BTN_LAST_REPORT.get(location, 0) < 900:
        return
    _COPY_BTN_LAST_REPORT[location] = now
    await report_system_error(location, f"{detail} | {telethon_env_info()}")

async def reply_with_copy_buttons(event, text_html, rows, location="copy_button"):
    """Replies to `event` with copy button(s). Returns True if the reply went out WITH working
    copy buttons, False if every route failed (in which case NOTHING was sent — the caller sends
    its own plain fallback). Order: Telethon's own KeyboardButtonCopy if this build has it, then
    the Bot API. The Telethon markup is built as an explicit ReplyInlineMarkup because Telethon's
    automatic buttons= classifier doesn't treat KeyboardButtonCopy as inline-only
    (LonamiWebs/Telethon#4588) and builds a ReplyKeyboardMarkup that Telegram rejects."""
    if hasattr(types, "KeyboardButtonCopy"):
        try:
            markup = types.ReplyInlineMarkup(rows=[
                types.KeyboardButtonRow(buttons=[
                    types.KeyboardButtonCopy(text=btn_text, copy_text=copy_text) for btn_text, copy_text in row
                ])
                for row in rows
            ])
            await event.reply(text_html, parse_mode='html', buttons=markup)
            return True
        except Exception as e:
            await _report_copy_button_problem(location, f"Telethon copy button failed: {type(e).__name__}: {e}")
    try:
        await bot_api_send_with_copy_buttons(event.chat_id, event.id, text_html, rows)
        return True
    except Exception as e:
        await _report_copy_button_problem(location, f"Bot API copy button failed: {type(e).__name__}: {e}")
    return False

# 🚪 AUTO-LEAVE ON "CAN'T WRITE HERE" (muted / restricted / demoted, etc.)
# ==========================================
# Telegram raises errors.ChatWriteForbiddenError from SendMessageRequest/SendMediaRequest the
# moment the bot has no permission to post in a chat — most commonly because an admin muted the
# bot's send-messages permission. Before this fix, release_spawn()/start_rarity_gate_quiz() just
# fell into their generic `except Exception` handler, which called report_system_error() on
# EVERY attempt trigger_dynamic_spawn() made (up to 5, one per candidate character) — that's
# exactly the burst of 4-5 near-identical "CRITICAL SYSTEM ERROR" alerts per silenced chat.
# There's also nothing productive the bot CAN do once it can't post — trying a different
# character doesn't help, since the chat itself is the problem, not the pick.
# This is called the first time that specific error is seen for a chat: leave immediately (no
# point staying somewhere it can't speak), and send exactly ONE alert instead of a flood.
async def _handle_write_forbidden(chat_id, location):
    left = False
    try:
        await bot1.delete_dialog(chat_id)
        left = True
    except Exception as leave_err:
        print(f"⚠️ Could not leave chat {chat_id} after write-forbidden: {leave_err}")
    note = f"Bot is muted/restricted in chat {chat_id} — " + ("left the chat." if left else "tried to leave but that failed too, check logs.")
    await report_system_error(location, note)

# 📸 GRACEFUL MEDIA-PERMISSION FALLBACK (one level short of the full write-ban above)
# ==========================================
# Telegram's per-chat permissions aren't one single "can post" switch — admins can allow plain
# text while blocking specific media types individually (photos, videos, stickers, GIFs, voice
# notes, round videos, docs, audio — CHAT_SEND_PHOTOS_FORBIDDEN and ~8 siblings). Before this
# fix, a spawn hitting one of these raised straight into release_spawn's/
# start_rarity_gate_quiz's generic `except Exception`: one CRITICAL SYSTEM ERROR alert PER
# candidate character (up to 5, from trigger_dynamic_spawn's retry loop) even though the bot
# could have posted the exact same message as plain text just fine — that's the
# "cannot send photos ... (caused by SendMediaRequest)" flood.
# Matched on the error's message rather than a fixed list of exception classes: Telegram has
# ~9 of these fine-grained "can't send THIS media type here" errors, and not every installed
# Telethon version exposes each one as its own named class yet — matching text keeps this
# working regardless of exactly which one fires or how that build phrases it.
_MEDIA_FORBIDDEN_HINTS = (
    "send photos", "send_photos", "send media", "send_media",
    "send videos", "send_videos", "send stickers", "send_stickers",
    "send gifs", "send_gifs", "send voice", "send_voice",
    "send round", "send_round", "send docs", "send_docs", "send documents",
    "send audio", "send_audio",
)

def _is_media_forbidden_error(exc: Exception) -> bool:
    """True for an RPCError that means 'this chat blocks THIS media type, but plain text still
    goes through' — the signal to fall back to a text-only spawn instead of failing/alerting.
    False for errors.ChatWriteForbiddenError (bot can't post ANYTHING here — see
    _handle_write_forbidden above, which is what should run instead) and for anything else."""
    if not isinstance(exc, errors.RPCError) or isinstance(exc, errors.ChatWriteForbiddenError):
        return False
    text = str(exc).lower()
    return any(hint in text for hint in _MEDIA_FORBIDDEN_HINTS)

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

    # Send to the community group (DAILY_REPORT_CHAT_ID — the old force-sub group)
    try:
        await send_safe_message(bot1, DAILY_REPORT_CHAT_ID, text, parse_mode='html')
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
# 🎴 RARITY TIERS & CORE DISPLAY CONSTANTS
# ==========================================
# Rank 1 (rarest) -> Rank 9 (most common). All tiers accept photo or video media — no
# tier is restricted to a specific media type.
# 🩹 CHANGED (per owner request): expanded from 4 tiers to 9, matching catch_bot's own scheme
# 1:1 (Supreme..Common) instead of compressing it down. Every EXISTING character on the old
# 4-tier scheme (Sweetie/Blossom/Fluffy/Kawaii) is migrated to MYSTICAL — see
# _migrate_old_4tier_to_9tier() below — a deliberate one-time choice, not a "best guess"
# equivalence, since the old 4 tiers don't map onto the new 9 in any principled way.
RARITY_TIERS = ["SUPREME", "CATAPHRACT", "CROSSVERSE", "DIVINE", "MYSTICAL", "LEGENDARY", "RARE", "UNCOMMON", "COMMON",
                "CNFT SS", "CNFT S", "CNFT A"]
# ⚠️ The 3 CNFT tiers above are APPENDED at the end, deliberately never inserted earlier in the
# list: RARITY_GATE_TIERS below is defined as RARITY_TIERS[0..3] BY POSITION — appending instead
# of inserting guarantees those 4 stay exactly SUPREME/CATAPHRACT/CROSSVERSE/DIVINE, unchanged,
# so CNFT never accidentally becomes quiz-gated and nothing already quiz-gated silently stops
# being so. CNFT characters are also excluded from random spawning entirely regardless of any of
# this — see the "spawnable" field (set False by /addspecial) and its check in
# trigger_dynamic_spawn — these 3 tiers exist here ONLY so classify_rarity/RARITY_EMOJI/
# rarity_rank_value recognize them correctly for display purposes (/harem, /check, gifts, etc.)
# on whatever a player receives manually.
# ⚠️ SINGLE SOURCE OF TRUTH for rarity emoji (Rarity No.1 = SUPREME ... No.9 = COMMON).
# Change emoji here ONLY — RARITY_NUM_MAP below is generated from this, so spawns, /who,
# the /addchar legend, stats and /changeallrarity all stay in sync automatically.
# Emoji match catch_bot's own exactly, so a character's rarity looks identical either bot.
RARITY_EMOJI = {
    "SUPREME": "🪞", "CATAPHRACT": "✨", "CROSSVERSE": "⚡", "DIVINE": "⚜️",
    "MYSTICAL": "💮", "LEGENDARY": "🟡", "RARE": "🟠", "UNCOMMON": "🟣", "COMMON": "🔵",
    "CNFT SS": "💠", "CNFT S": "💠", "CNFT A": "💠"
}
RARITY_DEFAULT_EMOJI = "❓"  # fallback shown only when a tier truly can't be classified
RARITY_LABEL_STYLED = "𝙍𝘼𝙍𝙄𝙏𝙔"  # matches catch_bot's own inline-query card caption styling
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

# 💠 Multi-favourite (per owner request): /fav used to store a single char_id in the scalar
# 'fav_card' field. It now accepts up to MAX_FAV_CARDS at once, stored ordered in a 'fav_cards'
# array. get_fav_card_list is the single place every reader goes through, so old accounts that
# haven't re-run /fav since this upgrade keep working via the legacy 'fav_card' fallback.
MAX_FAV_CARDS = 10

def get_fav_card_list(user_doc):
    """Returns a user's favourite char_ids, newest schema first: 'fav_cards' (already ordered,
    capped defensively at MAX_FAV_CARDS) if present, else a 1-item list from the legacy
    'fav_card' field, else an empty list."""
    if not user_doc:
        return []
    cards = user_doc.get("fav_cards")
    if cards:
        return [c for c in cards if c][:MAX_FAV_CARDS]
    legacy = user_doc.get("fav_card")
    return [legacy] if legacy else []

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

_bit_count = int.bit_count if hasattr(int, "bit_count") else (lambda x: bin(x).count("1"))
# ⚡ PERF: int.bit_count() (Python 3.10+) does the popcount in C — measurably faster than
# building a binary string and counting "1" characters in it, especially across a roster scan
# of thousands of comparisons (find_character_by_media, get_cached_xbot_lookup below). Resolved
# ONCE here rather than inside hamming_distance() itself, so the hasattr check isn't repeated
# on every single comparison.

def hamming_distance(hash_a, hash_b):
    if not hash_a or not hash_b:
        return 999
    try:
        return _bit_count(int(hash_a, 16) ^ int(hash_b, 16))
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
    # ⏱️ TEMP DIAGNOSTICS (owner keeps reporting /who is still slow even after the thumb=0 +
    # run_blocking fixes above): every optimization so far was reasoned from reading the code,
    # not measured against what's actually slow on the live bot. This times the download step
    # separately from the hash step and prints both, so the NEXT slow /who tells us which one
    # it actually is instead of more guessing. Safe to remove once the real bottleneck is found.
    t0 = time.time()
    try:
        if msg.photo or msg.video or msg.document:
            # 🩹 PERF FIX (owner report — /who takes several seconds on anything that isn't
            # bot1's own live spawn): the photo branch used to call download_media(file=bytes)
            # with NO thumb=, which fetches the FULL-resolution original — up to several MB —
            # just to shrink it down to a 16x16 dHash a few lines below. The video/document
            # branch asked for thumb=-1, which Telethon docs confirm is the LARGEST available
            # thumbnail (sizes are sorted ascending, so -1 is the tail), not the smallest.
            # thumb=0 asks Telegram for its SMALLEST generated size instead — typically a few
            # KB — for both cases: plenty of resolution for a 16x16 hash, a fraction of the
            # download weight. This is the dominant cost of the whole /who pipeline for any
            # media that isn't a live in-memory spawn match (Path A, which never downloads
            # anything at all — see who_reveal_handler), so it applies no matter who sent the
            # photo/video.
            media_bytes = await msg.download_media(thumb=0, file=bytes)
        else:
            return None
        t1 = time.time()
        if not media_bytes:
            print(f"compute_phash_for_message: empty download (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}) — "
                  f"likely no embedded thumbnail to fetch. [download took {t1 - t0:.2f}s]")
            return None
        # 🩹 PERF FIX (owner report — /who went from ~0.1s to 10s+ for anything that isn't
        # bot1's own live spawn, especially since the anti-snipe warning above now actively
        # sends confused players to /who far more often than before): compute_dhash does a real
        # image decode + resize in PIL — genuine CPU work, not I/O — and was being called
        # directly here with no await, meaning it ran ON the single asyncio event loop thread.
        # While ANY one person's image was decoding, the ENTIRE bot was frozen: every other
        # user's spawn, catch, DM, and DB call queued up behind it. That's invisible at low
        # traffic (one decode every so often, a few tens of ms each) and becomes exactly this
        # symptom under real concurrent load — requests pile up waiting for the CPU-bound work
        # ahead of them, compounding into seconds. run_blocking (see NON-BLOCKING EXECUTOR
        # BRIDGE near send_safe_file) already exists for precisely this — it just wasn't being
        # used at the one call site that actually needed it.
        result = await run_blocking(compute_dhash, media_bytes)
        t2 = time.time()
        print(f"⏱️ compute_phash_for_message (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}, "
              f"{len(media_bytes)} bytes): download={t1 - t0:.2f}s, hash={t2 - t1:.2f}s, total={t2 - t0:.2f}s")
        if not result:
            print(f"compute_phash_for_message: dHash failed to decode (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}) — "
                  f"see compute_dhash error above for the PIL exception.")
        return result
    except Exception as e:
        print(f"compute_phash_for_message error (msg_id={getattr(msg, 'id', '?')}, kind={media_kind}) "
              f"after {time.time() - t0:.2f}s: {type(e).__name__}: {e}")
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
# 🎲 RARITY SPAWN PATTERN (per owner request — replaces the fixed halving weights)
# ==========================================
# The old system rolled weighted dice for every single spawn, so a chat could go 300 spawns without a
# Mystical or get three Divine in a row. Now each CHAT works through a shuffled DECK built from a PATTERN —
# "out of every N spawns, exactly K are tier X" — so the long-run percentages are exact and streaks of
# luck (good or bad) are bounded. When a chat's deck runs out it is re-shuffled.
#
# Default pattern (per 100 spawns):
#     COMMON · UNCOMMON · RARE · LEGENDARY  20 each (equal — 80% together)
#     MYSTICAL 12   — less than the four above
#     DIVINE    6   — the big drop
#     CROSSVERSE 2  — rarer still
#     SUPREME / CATAPHRACT  NEVER spawn on their own — only the owner's /fspawn <char id | sup | cata> makes them
#                           appear (see NEVER_SPAWN_TIERS and force_spawn_by_owner).
# Change it live with /spawnpattern (saved in the database, survives restarts) — no code edit needed.
# /spawnweight (Divine ×) and /topspawn (event boost) still work on top of the pattern.
SPAWN_PATTERN_DEFAULT = {"COMMON": 20, "UNCOMMON": 20, "RARE": 20, "LEGENDARY": 20, "MYSTICAL": 12, "DIVINE": 6, "CROSSVERSE": 2}
NEVER_SPAWN_TIERS = ("SUPREME", "CATAPHRACT")
_cached_spawn_pattern = None   # owner override saved by /spawnpattern; None = SPAWN_PATTERN_DEFAULT
DEFAULT_RARITY_WEIGHTS = {tier: SPAWN_PATTERN_DEFAULT.get(tier, 0) for tier in RARITY_TIERS}   # kept for older references
# /topspawn on = a temporary "top tiers drop" event: these FOUR tiers are lifted to (at least) this equal weight
# while it is on. SUPREME / CATAPHRACT are NOT part of it — they never spawn on their own, event or not.
TOP_TIER_EVENT_WEIGHT_ON = {"CROSSVERSE": 25, "DIVINE": 25, "MYSTICAL": 25, "LEGENDARY": 25}
TOP_TIER_WEIGHT_ON = TOP_TIER_EVENT_WEIGHT_ON["CROSSVERSE"]  # name kept for older references
_cached_top_tier_enabled = False  # default off — /topspawn's handler + load_rarity_weight_cache() keep this in sync with bot_settings_col
# ✏️ To add more /spawnweight levels yourself later, just add another "level: multiplier" pair
# here — e.g. {1: 1, 2: 3, 3: 5} adds a level 3 that's 5x default. Nothing else needs to change.
SPAWNWEIGHT_LEVEL_MULTIPLIERS = {1: 1, 2: 3}
_cached_spawnweight_level = 1  # level 1 = 1x = untouched defaults

async def load_rarity_weight_cache():
    global _cached_spawnweight_level, _cached_top_tier_enabled, _cached_spawn_pattern
    try:
        doc = await bot_settings_col.find_one({"_id": "rarity_spawn_weight_level"})
        if doc and doc.get("level") in SPAWNWEIGHT_LEVEL_MULTIPLIERS:
            _cached_spawnweight_level = doc["level"]
    except Exception as e:
        print(f"load_rarity_weight_cache error: {e}")
    try:
        top_doc = await bot_settings_col.find_one({"_id": "top_tier_spawn_enabled"})
        if top_doc:
            _cached_top_tier_enabled = bool(top_doc.get("enabled", False))
    except Exception as e:
        print(f"load_rarity_weight_cache (top_tier) error: {e}")
    try:
        pat_doc = await bot_settings_col.find_one({"_id": "spawn_pattern"})
        if pat_doc and isinstance(pat_doc.get("counts"), dict):
            _cached_spawn_pattern = clean_spawn_pattern(pat_doc["counts"])
    except Exception as e:
        print(f"load_rarity_weight_cache (spawn_pattern) error: {e}")


def clean_spawn_pattern(counts):
    """Pure. {tier: n} → only spawnable tiers (never SUPREME/CATAPHRACT), n a positive int ≤ 1000.
    Returns None when nothing usable is left (→ the default pattern is used)."""
    out = {}
    for tier, n in (counts or {}).items():
        tier = str(tier).upper()
        if tier in NEVER_SPAWN_TIERS or tier not in SPAWN_PATTERN_DEFAULT:
            continue
        try:
            n = int(n)
        except (TypeError, ValueError):
            continue
        if n > 0:
            out[tier] = min(n, 1000)
    return out or None


def get_spawn_pattern():
    return dict(_cached_spawn_pattern or SPAWN_PATTERN_DEFAULT)


def get_effective_rarity_weights():
    """Per-tier relative frequency used by the spawn deck (and by /spawnrates): the PATTERN
    (get_spawn_pattern) with DIVINE multiplied by the /spawnweight level, and — while /topspawn is ON —
    CROSSVERSE / DIVINE / MYSTICAL / LEGENDARY lifted to at least TOP_TIER_EVENT_WEIGHT_ON.
    SUPREME and CATAPHRACT are ALWAYS 0: they only ever appear through the owner's /fspawn."""
    multiplier = SPAWNWEIGHT_LEVEL_MULTIPLIERS.get(_cached_spawnweight_level, 1)
    pattern = get_spawn_pattern()
    weights = {tier: pattern.get(tier, 0) for tier in RARITY_TIERS}
    weights["DIVINE"] = weights.get("DIVINE", 0) * multiplier
    if _cached_top_tier_enabled:
        for tier, boost in TOP_TIER_EVENT_WEIGHT_ON.items():
            weights[tier] = max(weights.get(tier, 0), boost)
    for tier in NEVER_SPAWN_TIERS:
        weights[tier] = 0
    return weights

UNKNOWN_TIER_WEIGHT = 1  # weight of a tier classify_rarity() can't recognise ("OTHER"). The old per-character
# code used 20 here, which only made sense per card — as a whole TIER it would grab ~24% of all spawns.

def spawn_deck_counts(tier_weights, deck_size=None):
    """Pure. Turns relative tier weights into whole-number slots for one shuffled deck (largest-remainder
    rounding; every tier with weight > 0 gets at least 1 slot). With the default pattern (sums to 100) the
    result is exactly the pattern. The deck is made bigger when a tier is rarer than 1 in 100."""
    items = {t: w for t, w in tier_weights.items() if w and w > 0}
    if not items:
        return {}
    total = sum(items.values())
    if deck_size is None:
        deck_size = min(1000, max(100, int(1 / (min(items.values()) / total)) + 1))
    raw = {t: w / total * deck_size for t, w in items.items()}
    counts = {t: max(1, int(v)) for t, v in raw.items()}
    diff = deck_size - sum(counts.values())
    if diff > 0:
        for t in sorted(raw, key=lambda t: raw[t] - int(raw[t]), reverse=True)[:diff]:
            counts[t] += 1
        while sum(counts.values()) < deck_size:       # more to give than tiers (can't happen with sane sizes) — spread evenly
            for t in sorted(raw, key=raw.get, reverse=True):
                counts[t] += 1
                if sum(counts.values()) >= deck_size:
                    break
    while diff < 0 and sum(counts.values()) > deck_size and max(counts.values()) > 1:
        t = max(counts, key=counts.get)
        counts[t] -= 1
    return counts

_spawn_decks = {}   # chat_id -> {"sig": tuple(sorted(counts.items())), "deck": [tier, ...]}

def draw_tier_from_deck(chat_id, counts, rng=random):
    """Next tier for this chat from its shuffled deck (re-shuffled when empty or when the pattern changes)."""
    if not counts:
        return None
    sig = tuple(sorted(counts.items()))
    st = _spawn_decks.get(chat_id)
    if st is None or st["sig"] != sig or not st["deck"]:
        deck = [t for t, n in counts.items() for _ in range(n)]
        rng.shuffle(deck)
        st = {"sig": sig, "deck": deck}
        _spawn_decks[chat_id] = st
        if len(_spawn_decks) > 5000:
            for k in list(_spawn_decks)[:1000]:
                _spawn_decks.pop(k, None)
    return st["deck"].pop()

def pick_character_by_tier(candidates, tier_weights, chat_id=None):
    """Picks the TIER first, then a random card inside it, so a tier's chance doesn't depend on how many cards
    it contains. With a chat_id the tier comes from that chat's shuffled pattern DECK (exact percentages, no
    luck streaks); without one it falls back to a plain weighted roll. Only tiers that actually have a
    candidate take part. If every present tier has weight 0 (shouldn't happen) → uniform pick, never raises."""
    by_tier = {}
    for c in candidates:
        tier = c.get("rarity_tier") or classify_rarity(c.get("rarity", ""))
        by_tier.setdefault(tier, []).append(c)
    tiers = list(by_tier.keys())
    if not tiers:
        return None
    present = {t: tier_weights.get(t, UNKNOWN_TIER_WEIGHT) for t in tiers}
    if sum(present.values()) <= 0:
        return random.choice(candidates)
    chosen_tier = None
    if chat_id is not None:
        chosen_tier = draw_tier_from_deck(chat_id, spawn_deck_counts(present))
    if chosen_tier is None or chosen_tier not in by_tier:
        weights = [present[t] for t in tiers]
        chosen_tier = random.choices(tiers, weights=weights, k=1)[0]
    return random.choice(by_tier[chosen_tier])

def get_spawn_eligible_characters(characters_list):
    """The organic-spawn pool: skips /addspecial CNFT cards (spawnable=False), anything that already hit
    its CatchLimit, and every SUPREME / CATAPHRACT card (NEVER_SPAWN_TIERS — those are owner /fspawn only).
    Shared by trigger_dynamic_spawn and /spawnrates so the two can't disagree about who's eligible."""
    eligible = []
    for char in characters_list:
        if not char.get("spawnable", True):
            continue
        if (char.get("rarity_tier") or classify_rarity(char.get("rarity", ""))) in NEVER_SPAWN_TIERS:
            continue
        limit = char.get("spawn_limit", 0)
        if limit and limit > 0 and char.get("spawn_count", 0) >= limit:
            continue
        eligible.append(char)
    return eligible

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
# 🕵️ ANTI-SNIPE, PART 3 — a THIRD-PARTY bot (not ours, has admin in the group) auto-replies to
# .w/.who/.waifu with the full name the instant it's asked, same as our own /who used to. We
# can't touch that bot's code or stop it from answering — but we CAN make its answer useless:
# require every catch to end with CATCH_REQUIRED_SUFFIX, and only put that suffix into the
# copy-paste commands generated by OUR OWN reveal of an ACTIVE LIVE SPAWN (who_reveal_handler's
# Path A) — that's the only place the rival bot's snipe race actually happens. The rival bot has
# no way to know about a requirement it was never told exists, so its hint/full-name replies will
# keep coming back WITHOUT the suffix and will always fail the catch — while anyone using OUR
# bot's own reveal (tap the copy button, or type it out exactly as shown) still succeeds normally.
# ⚠️ _identify_media_and_reply (Path B — identifying a reposted/forwarded photo that ISN'T the
# current live spawn) deliberately does NOT add the suffix: that path is pure lookup, not part of
# the snipe race, so a dot there would just be confusing noise on top of a command that may not
# even be tied to anything currently catchable.
# 🔑 IMPORTANT: catch_handler rejects a missing/wrong suffix with the EXACT SAME "❌ …that's not
# my name" message as a wrong guess — never a distinct "you're missing a dot" error. The moment
# that distinction leaks (in the group, in logs someone can see, anywhere), anyone who noticed
# can just start appending "." to whatever the rival bot gives them and this stops working.
# normalize_name() above already strips all punctuation before comparing — so the suffix check
# has to happen on the RAW text first, separately, before normalize_name ever sees it.
# ==========================================
CATCH_REQUIRED_SUFFIX = "."

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
# 🗂️ PERSISTENT /who file-identity index (2026-09): raw Telegram photo/document id -> char_id.
# Before this, that map (_MEDIA_ID_CACHE) lived in memory only, so every deploy started it
# empty and /who had to re-download + re-hash media until it was warmed again. See
# load_media_identity_cache_from_db / warm_media_identity_cache_from_db below.
media_identity_col = db["media_identity_index"]
users_catcher_col = db["users_catcher_data"]
groups_counters_col = db["groups_msg_counters"]
groups_config_col = db["groups_catcher_config"]
guilds_col = db["guilds_data"]
gift_history_col = db["gift_history"]
haido_history_col = db["haido_history"] # records each person-to-person /gift for profile stats
artists_col = db["artists"]  # 🎨 artist_name (lowercased) -> linked Telegram user_id, for Guard Bot collect rewards — see /linkartist
rarity_quiz_bank_col = db["rarity_quiz_bank"] # 🔐 owner-authored Rarity 1-4 gate quiz questions
trivia_bank_col = db["trivia_question_bank"]  # 🧠 owner-authored /addtrivia questions — see trigger_trivia_spawn near perform_catch
trivia_media_col = db["trivia_media"]  # 🌸 owner-added host pictures/GIFs/videos shown with trivia questions — see /addtriviamedia
bot_settings_col = db["bot_settings"] # ⚙️ single-document global settings
added_owners_col = db["added_owners"]  # /addowner — see load_added_owners_cache below
uploaders_col = db["uploaders"]  # /adduploader — users who may use /addchar (but nothing else owner-only); see load_uploaders_cache
gban_col = db["gban_data"]  # 🚫 /gban — durable record of every global ban; see is_gbanned()
owner_mode_clicks_col = db["owner_mode_clicks"]  # 🖤 one doc per tap of the spawn's OWNER MODE promo button — see /count
# near bot1's creation for the fast in-memory gate, and the GBAN COMMANDS section near
# /addowner further down for /gban, /ungban, /gunban and load_active_gbans_cache().
# 🔭 CROSS-BOT MONITOR — merged in from the standalone "identify other bots' spawns" script.
# Separate collections from characters_col/characters_base_col on purpose: these hold OTHER
# people's bots' characters (catch_bot, obtain_bot, ...), never our own — see the big comment
# block above the cross-bot monitor commands further down for the full picture.
xbot_hashes_col = db["xbot_character_hashes"]      # hash -> {name, source_bot, chat_id, ...}
monitored_channels_col = db["xbot_monitored_channels"]  # chat_id -> source_bot type being watched
bot_mapping_col = db["xbot_bot_mapping"]           # other bot's user_id -> source_bot type
# 🩹 REMOVED Redis entirely (per owner report — .w/.who was taking OVER A MINUTE on media
# it had never seen before, sometimes even on cached media). Root cause: redis.Redis.from_url()
# below was constructed with NO socket_connect_timeout/socket_timeout, and whenever
# Redis was unreachable (wrong REDIS_URL, no Redis actually running, a Render add-on that
# silently stopped, etc.) every single `await redis_client.get/setex(...)` call would hang for
# a long time — sometimes upwards of 30-60s each — before finally raising, getting caught by
# the try/except, and falling through. A single .who call could chain THREE OR MORE of these
# in sequence (find_character_by_media's own cache check, get_all_characters_cached inside it,
# then _xbot_identify_fallback_and_reply's separate cache check on top if step 1 came back
# empty) — which is exactly "over a minute" for one command. Setting a short timeout would
# have made a down Redis fail fast instead of hanging, but the owner asked to just remove it
# outright: this is a single Render instance (see the comment that already existed above
# get_char_display_media below), so a plain in-process dict is the simplest cache that
# actually fits the architecture — no network hop, no timeout to misconfigure, nothing to go
# down independently of the bot process itself. Every function below that used to check Redis
# first now checks one of the plain dicts declared alongside it instead; TTL values are
# unchanged from before, just enforced by comparing time.time() instead of Redis's own EXPIRE.
_USER_CACHE = {}  # user_id -> (user_doc, cached_at)
USER_CACHE_TTL = 300  # unchanged from the old Redis SETEX
async def get_cached_user(user_id):
    cached = _USER_CACHE.get(user_id)
    if cached and (time.time() - cached[1]) < USER_CACHE_TTL:
        return cached[0]
    user = await users_catcher_col.find_one({"user_id": user_id}, {"_id": 0})  # exclude ObjectId (not JSON serializable)
    _USER_CACHE[user_id] = (user, time.time())
    return user

# ---- Character-data cache: characters_base_data barely changes (only via /addchar, /editchar,
# /delchar) but is read on almost every group message (spawn trigger) and every /dex lookup.
# TTL is short on purpose: a newly-hit spawn_limit may stay "eligible" for a few seconds longer
# than it should, which is a harmless, rare edge case compared to hitting Mongo on every message.
CHAR_CACHE_TTL = 300  # 5 minutes — roster only changes on /addchar,/editchar,/delchar (which invalidate this explicitly anyway)
_ALL_CHARS_CACHE = {"data": None, "cached_at": 0}
_ALL_CATEGORIES_CACHE = {"data": None, "cached_at": 0}
_CATEGORY_TOTALS_CACHE = {"data": None, "cached_at": 0}

_ALL_CHARS_CACHE["gen"] = 0          # bumped by invalidate_character_caches() — see _refresh_all_characters
_ALL_CHARS_REFRESH_TASK = None       # the one in-flight background refresh, if any

async def _refresh_all_characters():
    gen_at_start = _ALL_CHARS_CACHE["gen"]
    data = await characters_base_col.find({}, {"_id": 0}).to_list(length=None)
    # If /addchar, /editchar or /delchar invalidated the cache while this query was in flight,
    # what we just read may already be out of date — hand it back to the caller, but don't
    # store it (the next call re-reads fresh instead of serving the stale copy for 5 more minutes).
    if _ALL_CHARS_CACHE["gen"] == gen_at_start:
        _ALL_CHARS_CACHE["data"] = data
        _ALL_CHARS_CACHE["cached_at"] = time.time()
    return data

async def _refresh_all_characters_safe():
    try:
        await _refresh_all_characters()
    except Exception as e:
        print(f"⚠️ background roster refresh failed (keeping the previous copy): {e}")

async def get_all_characters_cached():
    """🩹 PERF FIX (2026-09, owner report — /who and everything media-related feels slow, worst
    right after a deploy): the roster is ~7000 full documents. Every 5 minutes the cache used to
    expire and WHOEVER happened to ask next (a /who, or just the next group message that
    triggers a spawn check) sat and waited for the whole collection to be re-read from Mongo —
    seconds, on the request's critical path. Now stale-while-revalidate: once we have ANY copy,
    an expired one is still returned instantly and a single background task refreshes it for
    the next caller. Only the very first load (cold start — see _startup_media_identity_warm,
    which triggers it in the background at boot) or right after an explicit invalidation
    (/addchar, /editchar, /delchar) ever waits on Mongo."""
    global _ALL_CHARS_REFRESH_TASK
    data = _ALL_CHARS_CACHE["data"]
    if data is not None:
        if (time.time() - _ALL_CHARS_CACHE["cached_at"]) >= CHAR_CACHE_TTL:
            if _ALL_CHARS_REFRESH_TASK is None or _ALL_CHARS_REFRESH_TASK.done():
                _ALL_CHARS_REFRESH_TASK = asyncio.create_task(_refresh_all_characters_safe())
        return data
    return await _refresh_all_characters()

_ROSTER_INDEX = {"src": None, "by_id": {}}

def _get_roster_index(chars):
    """{by_id} derived from the current roster snapshot — rebuilt only when the snapshot list
    object itself changes (a refresh or an invalidation), never per request. Call sites that
    used to scan or re-map all ~7000 characters to find one id do a dict lookup instead.
    The docs inside are SHARED with the snapshot — treat them as read-only."""
    if _ROSTER_INDEX["src"] is chars:
        return _ROSTER_INDEX
    by_id = {}
    for c in chars:
        cid = c.get("char_id")
        if cid is not None:
            by_id.setdefault(cid, c)
    _ROSTER_INDEX["src"] = chars
    _ROSTER_INDEX["by_id"] = by_id
    return _ROSTER_INDEX

async def get_character_by_id_cached(char_id):
    """One character doc by char_id (or None) — O(1) instead of scanning the whole roster."""
    return _get_roster_index(await get_all_characters_cached())["by_id"].get(char_id)

async def get_all_categories_cached():
    if _ALL_CATEGORIES_CACHE["data"] is not None and (time.time() - _ALL_CATEGORIES_CACHE["cached_at"]) < CHAR_CACHE_TTL:
        return _ALL_CATEGORIES_CACHE["data"]
    data = await characters_base_col.distinct("category")
    _ALL_CATEGORIES_CACHE["data"] = data
    _ALL_CATEGORIES_CACHE["cached_at"] = time.time()
    return data

async def get_category_totals_cached():
    """{category: total_card_count} across the whole roster — used by /harem to show
    'owned/total' per series. Only changes on /addchar, /editchar, /delchar, so it's
    cached the same way as the other character-roster lookups above."""
    if _CATEGORY_TOTALS_CACHE["data"] is not None and (time.time() - _CATEGORY_TOTALS_CACHE["cached_at"]) < CHAR_CACHE_TTL:
        return _CATEGORY_TOTALS_CACHE["data"]
    pipeline = [{"$group": {"_id": "$category", "count": {"$sum": 1}}}]
    data = {(doc["_id"] or "Unknown Series"): doc["count"] for doc in await characters_base_col.aggregate(pipeline).to_list(length=None)}
    _CATEGORY_TOTALS_CACHE["data"] = data
    _CATEGORY_TOTALS_CACHE["cached_at"] = time.time()
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
CHAR_PHOTO_CACHE_FAILURE_TTL = 20  # seconds — how long a FAILED/empty fetch is remembered (see get_char_display_media)
_CHAR_PHOTO_LAST_ERROR = {}  # char_id -> repr of the last fetch exception, surfaced in release_spawn's owner alert

async def get_char_display_media(client, char_id, storage_msg_id):
    """Cached wrapper around client.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_msg_id)
    for a character's stored photo. Returns the media object, or None if it can't be fetched.

    🩹 FIX (2026-09, owner report — "media is there, /harem and /check show it, yet a solved
    rarity gate says 'I got lost on my way to you', and it keeps happening after every deploy
    until the cache has 'filled'"): a failed or empty fetch used to be cached under the SAME
    1-hour TTL as a successful one. One transient hiccup — a FloodWait while the startup warm-up
    was hammering get_messages, a momentary network error right after the reconnect — and that
    character then reported "media missing" for EVERYONE for a full hour, even though the
    message in the control group was perfectly fine. Now:
      • a real hit is cached for CHAR_PHOTO_CACHE_TTL as before;
      • a miss/failure is only remembered for CHAR_PHOTO_CACHE_FAILURE_TTL (20s), so the very
        next attempt genuinely retries;
      • the fetch itself retries transient errors up to 3 times (waiting out a short
        FloodWait instead of giving up on it), and the last error is kept in
        _CHAR_PHOTO_LAST_ERROR so release_spawn's alert can say WHY instead of guessing."""
    cached = _CHAR_PHOTO_CACHE.get(char_id)
    if cached:
        cached_media, cached_at = cached
        ttl = CHAR_PHOTO_CACHE_TTL if cached_media is not None else CHAR_PHOTO_CACHE_FAILURE_TTL
        if (time.time() - cached_at) < ttl:
            return cached_media
    media = None
    _CHAR_PHOTO_LAST_ERROR.pop(char_id, None)
    for attempt in range(3):
        try:
            storage_msg = await client.get_messages(SPECIFIC_CONTROL_GROUP, ids=storage_msg_id)
            if storage_msg and storage_msg.media:
                media = storage_msg.media
            break  # a definite answer (found it, or it's genuinely gone) — no point retrying
        except FloodWaitError as e:
            _CHAR_PHOTO_LAST_ERROR[char_id] = f"FloodWaitError: wait {e.seconds}s"
            if e.seconds > 15:
                break
            await asyncio.sleep(e.seconds + 1)
        except Exception as e:
            _CHAR_PHOTO_LAST_ERROR[char_id] = f"{type(e).__name__}: {e}"
            print(f"⚠️ get_char_display_media fetch error for {char_id} (attempt {attempt + 1}/3): {type(e).__name__}: {e}")
            await asyncio.sleep(0.5 * (attempt + 1))
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
        ttl = CHAR_PHOTO_CACHE_TTL if (cached and cached[0] is not None) else CHAR_PHOTO_CACHE_FAILURE_TTL
        if cached and (now - cached[1]) < ttl:
            result[cid] = cached[0]
        elif not card.get("storage_msg_id"):
            result[cid] = None  # no media ever uploaded for this card — nothing to fetch (and one bad card must not sink the whole page)
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

async def invalidate_character_caches(hard: bool = True):
    """Call this right after /addchar, /editchar, or /delchar successfully changes the roster.

    🩹 PERF FIX (owner report — /who and spawns go very slow while /syncfromcatch is running):
    hard=True (the default, used by every ordinary one-off caller — /addchar, /editchar,
    /delchar, ...) clears _ALL_CHARS_CACHE outright, so the very NEXT call to
    get_all_characters_cached() blocks on a full, live characters_base_col scan (~7000+ docs)
    to rebuild it. Correct and cheap for a rare, deliberate change.

    hard=False is for high-frequency bulk callers (currently: /syncfromcatch's
    store_character_from_check and /syncfromcatch_parallel's per-id worker, each of which can
    call this every 1-2 seconds for HOURS, for nearly every id checked). Nulling the cache on
    every single one of those meant every /who and every spawn trigger that happened to land in
    that window paid the full blocking re-scan too — for the entire sync run, on top of the
    sync's own heavy Telegram/Mongo traffic. That's the actual "slow" here, not just contention.
    Soft mode instead reuses the SAME stale-while-revalidate path get_all_characters_cached
    already uses once CHAR_CACHE_TTL naturally expires: it bumps the generation counter (so a
    write that was already in flight still can't clobber a newer refresh) and kicks ONE
    background refresh task, while every concurrent caller keeps getting the current (briefly
    stale) roster snapshot immediately — never blocked on Mongo because of this call. The photo
    cache, vault-pages cache, and categories/totals caches are left untouched in soft mode too:
    the one changed character's photo entry is already popped by the caller (see
    store_character_from_check), and a few extra minutes of staleness on the others is a
    complete non-issue during a bulk resync.
    """
    global _ALL_CHARS_REFRESH_TASK
    _ALL_CHARS_CACHE["gen"] = _ALL_CHARS_CACHE.get("gen", 0) + 1  # see _refresh_all_characters
    if hard:
        _CHAR_PHOTO_CACHE.clear()  # cheap in-process clear — cheaper to wipe it all than to track exactly which char_id(s) changed
        _unlimited_vault_pages_cache.clear()  # the owner/added-owner /harem view is stale the instant the roster changes
        _ALL_CHARS_CACHE["data"] = None
        _ROSTER_INDEX["src"] = None
        _ALL_CATEGORIES_CACHE["data"] = None
        _CATEGORY_TOTALS_CACHE["data"] = None
    else:
        if _ALL_CHARS_CACHE["data"] is not None and (_ALL_CHARS_REFRESH_TASK is None or _ALL_CHARS_REFRESH_TASK.done()):
            _ALL_CHARS_REFRESH_TASK = asyncio.create_task(_refresh_all_characters_safe())
        # _ROSTER_INDEX is left alone on purpose — it's keyed by object identity against
        # _ALL_CHARS_CACHE["data"], which soft mode hasn't replaced yet, so it's still valid
        # and will rebuild itself for free the moment the background refresh above swaps in a
        # new list (see _get_roster_index).

async def _generate_new_char_id():
    """BOD-prefixed SEQUENTIAL ID — ATOMIC counter (bot_settings_col._id="bod_char_id_counter").
    🩹 FIX (real race condition — per owner report of channel-listener imports not landing
    reliably, characters going missing/overwriting each other): the previous version re-scanned
    the WHOLE collection for the current highest BOD number on every call, then used max+1 —
    with no locking between reading that max and using it. The channel auto-import path fires
    auto_import_character_from_catchbot via asyncio.create_task WITHOUT awaiting it, so when
    catch_bot posts several "added new Character" announcements close together, multiple
    imports run CONCURRENTLY — more than one could read the exact same "current highest" before
    either had finished inserting, handing out the identical char_id to two different
    characters (one silently clobbers the other in the DB).
    Mongo's findOneAndUpdate with $inc is atomic — no two concurrent callers can ever receive
    the same number, and ids come out in strict, gap-free, call-arrival order — every future
    caller of this function (/addchar, the channel auto-import, and the orphan-character
    self-heal fallback) draws from one shared, race-free counter instead of separately
    guessing at the same number.
    First call ever seeds the counter from the OLD scan-based max (continuing exactly where the
    previous system left off rather than colliding with or restarting behind existing IDs);
    every call after that is a single atomic increment, no scan."""
    counter_doc = await bot_settings_col.find_one({"_id": "bod_char_id_counter"})
    if not counter_doc:
        highest = 0
        async for char in characters_base_col.find({"char_id": {"$regex": r"^BOD\d+$"}}, {"char_id": 1, "_id": 0}):
            try:
                num = int(char["char_id"][3:])
            except ValueError:
                continue
            if num > highest:
                highest = num
        # $setOnInsert + upsert is itself race-safe: if two callers hit this seeding path at
        # once, only one insert wins — the other just updates nothing, since by then the doc
        # already exists. Both would have computed the same `highest` anyway (neither has
        # inserted a new character yet at this point), so it's harmless either way.
        await bot_settings_col.update_one(
            {"_id": "bod_char_id_counter"},
            {"$setOnInsert": {"value": highest}},
            upsert=True
        )
    while True:
        counter_doc = await bot_settings_col.find_one_and_update(
            {"_id": "bod_char_id_counter"},
            {"$inc": {"value": 1}},
            upsert=True,
            return_document=ReturnDocument.AFTER
        )
        candidate = f"BOD{counter_doc['value']}"
        # /addchar can now be given a manual ID (e.g. BOD500) — if the counter ever reaches a
        # number that was already taken that way, skip it instead of colliding on the unique index.
        if not await characters_base_col.find_one({"char_id": candidate}, {"_id": 1}):
            return candidate

# ==========================================
# 💠 /addspecial — CNFT-tier characters, added by forwarding ANOTHER bot's own "added new ...
# CNFT character/rank" announcement straight into this bot's DM, one at a time. These live in
# the same roster (characters_base_col) as everything else, but with spawnable: False (see the
# check added in trigger_dynamic_spawn) — they never enter the organic spawn pool, only however
# you choose to hand them out manually later. char_id is derived directly from the source's own
# numbering (e.g. "#2A" -> "CNFT2A") rather than the BOD-sequential scheme _generate_new_char_id
# uses — a different, unrelated source bot, so keeping the id namespace separate avoids any
# chance of collision or of skewing the BOD/catch_bot-mirroring count.
# ==========================================
_addspecial_armed = False  # toggled by /addspecial — while True, every forward in owner's DM
# that LOOKS like a CNFT announcement gets auto-parsed and added; anything else is ignored.

CNFT_ANIME_LINE_RE = re.compile(r'Anime:\s*(.+)')
CNFT_NAME_LINE_RE = re.compile(r'Name:\s*(.+?)\s*#(\w+)\s*$', re.MULTILINE)
CNFT_ID_TIER_RE = re.compile(r'^(\d+)([A-Za-z]+)$')
CNFT_TIER_LETTER_MAP = {"A": "CNFT A", "S": "CNFT S", "SS": "CNFT SS"}

def parse_cnft_forward(caption):
    """Parses one of the source bot's "added new ... CNFT character/rank" announcements out of
    a forwarded caption. Returns {"anime", "name", "group_id", "tier_letters", "rarity_tier"} on
    a match, or None if `caption` doesn't look like one of these at all — lets the ingest
    handler below silently ignore anything else forwarded while armed, rather than erroring on
    every unrelated DM.
    Expected shape (blank lines and exact emoji don't matter, only these two labeled lines do):
        🫧 Anime: <anime name>
        🏖️ Name: <character name> [<tag>] #<group id><tier letters>
    e.g. "🏖️ Name: Rias Gremory [🤖] #2SS" -> name="Rias Gremory [🤖]", group_id="2", tier="SS".
    """
    if not caption or "CNFT" not in caption:
        return None
    anime_m = CNFT_ANIME_LINE_RE.search(caption)
    name_m = CNFT_NAME_LINE_RE.search(caption)
    if not anime_m or not name_m:
        return None
    anime = anime_m.group(1).strip()
    name = name_m.group(1).strip()
    code = name_m.group(2).strip().upper()
    id_tier_m = CNFT_ID_TIER_RE.match(code)
    if not id_tier_m:
        return None
    group_id, tier_letters = id_tier_m.group(1), id_tier_m.group(2)
    rarity_tier = CNFT_TIER_LETTER_MAP.get(tier_letters)
    if not anime or not name or not rarity_tier:
        return None
    return {"anime": anime, "name": name, "group_id": group_id, "tier_letters": tier_letters, "rarity_tier": rarity_tier}


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
    # 🚫 gban_data: user_id looked up on every /gban, /ungban, and lazy-expiry cleanup in
    # is_gbanned(); active is looked up once at boot by load_active_gbans_cache().
    await gban_col.create_index("user_id")
    await gban_col.create_index("active")
    # 🖤 OWNER MODE promo taps — /count does a distinct("user_id") plus a plain
    # count_documents({}) over this collection, so user_id is the only index it needs.
    await owner_mode_clicks_col.create_index("user_id")
    await _migrate_rarity_tiers()
    await _migrate_old_4tier_to_9tier()
    await _migrate_name_normalized()
    print("Database Indexes synchronized! ✔️")

try:
    asyncio.get_event_loop()
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

bot1 = TelegramClient('bot_main_session', APP_ID, APP_HASH, flood_sleep_threshold=10)

# ==========================================================================================
# 🤖 SECONDARY BOT (bot2) — spawn-reveal fallback ONLY. In chats where bot1 is NOT a member,
# bot2 posts the same auto-name reveal (+ copy button) that bot1 would. Where bot1 IS present,
# bot1 always answers (see _autoname_send) — bot2 never doubles up.
# bot2 handles no commands at all; its only handler is registered next to the auto name reveal
# block (search "bot2.add_event_handler"). BOT2_USERNAME is declared near own_pattern().
# Optional: SECONDARY_BOT_TOKEN unset -> bot2 = None -> the file behaves exactly as before.
# ⚠️ @BotFather: bot2 needs "Bot-to-Bot Communication Mode" ON, and in each group bot2 must be
# added (admin + Group Privacy off), same as bot1.
# ==========================================================================================
SECONDARY_BOT_TOKEN = (os.environ.get("SECONDARY_BOT_TOKEN") or "").strip() or None
bot2 = TelegramClient('bot_second_session', APP_ID, APP_HASH, flood_sleep_threshold=10) if SECONDARY_BOT_TOKEN else None

# ==========================================================================================
# 🚧 BOT-SENDER GATE (per owner request) — registered IMMEDIATELY after bot1 is created, so it
# is the FIRST NewMessage handler bot1 has. Same mechanism as gban_block_gate below: Telethon
# runs handlers of one event type in registration order, and events.StopPropagation stops every
# handler after the one that raised it.
#
# WHY: with @BotFather's "Bot-to-Bot Communication Mode" on (needed so bot1 can see catch_bot's
# spawns), bot1 starts receiving EVERY other bot's group messages too. Before that, it never saw
# a single one — so no handler in this file was ever written to expect a bot as the sender. The
# catch-alls (global_message_counter_handler's spawn counter, trivia's counter, spam tracking,
# ensure_user_registered, ...) would silently start counting/registering bots.
#
# RULES:
#   * catch_bot (CATCH_BOT_ID): NEVER reaches any other handler — so it can't move the
#     /haitime spawn counter, however many messages it posts. The ONLY thing its messages do
#     is (a) hand its spawn media to the auto name reveal (see AUTO NAME REVEAL block), (b) stop.
#   * every other bot: dropped here, before anything else sees it. Exactly the behavior from
#     before Bot-to-Bot mode existed. A bot can't trigger bot1's commands either.
#   * humans and channels: untouched. One dict lookup, no task, no I/O on the hot path.
#   * Fail-open: if a sender genuinely can't be resolved, the message passes through as before —
#     this gate can only ever remove bot traffic, never a real player's message.
# Independent of /autoname: switching the reveal off does NOT let catch_bot's messages back in.
# ==========================================================================================
_BOT_SENDER_CACHE = {}     # user_id -> bool (is a bot). A user's bot-ness never changes.
_BOTGATE_STATS = Counter()
_BOTGATE_BG_TASKS = set()

def _botgate_cache_put(user_id, is_bot):
    if len(_BOT_SENDER_CACHE) >= 50000:
        _BOT_SENDER_CACHE.clear()   # tiny ints — a full reset is cheaper than tracking LRU order
    _BOT_SENDER_CACHE[user_id] = bool(is_bot)

def _botgate_prefilter(e):
    """SYNC, runs before the handler is even scheduled. True = the gate handler must look at
    this message (catch_bot, a known bot, or a sender we haven't classified yet). False = a
    human/channel — costs one dict lookup and never becomes a task. Must NEVER raise (a raising
    filter aborts dispatch of that whole update), so any error means "not gated"."""
    try:
        sid = e.sender_id
        if not sid:
            return False
        if sid == CATCH_BOT_ID:
            return True
        cached = _BOT_SENDER_CACHE.get(sid)
        if cached is not None:
            return cached
        sender = e.message.sender   # sync — populated from the update's own user list
        if sender is not None:
            is_bot = bool(getattr(sender, "bot", False))
            _botgate_cache_put(sid, is_bot)
            return is_bot
        return True                 # unknown sender: let the handler resolve it once
    except Exception:
        return False

@bot1.on(events.NewMessage(incoming=True, func=_botgate_prefilter))
async def nonhuman_sender_gate(event):
    sid = event.sender_id
    if sid == CATCH_BOT_ID:
        _BOTGATE_STATS["catchbot_isolated"] += 1
        try:
            # Only spawn media matters to us; autoname re-checks the caption itself. Run it as
            # its own task so a slow lookup never holds this update's dispatch.
            if _autoname_event_filter(event):
                task = asyncio.ensure_future(autoname_catchbot_spawn_handler(event))
                _BOTGATE_BG_TASKS.add(task)
                task.add_done_callback(lambda t: (_BOTGATE_BG_TASKS.discard(t), t.cancelled() or t.exception()))
        except Exception as e:
            print(f"⚠️ botgate: could not hand spawn to autoname: {type(e).__name__}: {e}")
        raise events.StopPropagation

    is_bot = _BOT_SENDER_CACHE.get(sid)
    if is_bot is None:
        try:
            sender = event.message.sender or await asyncio.wait_for(event.get_sender(), timeout=3)
            is_bot = bool(getattr(sender, "bot", False)) if sender is not None else None
        except Exception:
            is_bot = None
        if is_bot is None:
            _BOTGATE_STATS["unresolved_passed_through"] += 1
            return                  # can't tell -> fail-open, behaves exactly as before
        _botgate_cache_put(sid, is_bot)
    if is_bot:
        _BOTGATE_STATS["other_bots_skipped"] += 1
        raise events.StopPropagation

def verify_botgate_is_first():
    """Startup self-check: the whole guarantee rests on this being bot1's FIRST NewMessage
    handler. If some future edit registers another NewMessage handler above it, say so loudly
    instead of silently letting bot traffic through."""
    try:
        for callback, ev in bot1.list_event_handlers():
            if isinstance(ev, events.NewMessage):
                if callback is nonhuman_sender_gate:
                    print("🚧 [botgate] OK — bot-sender gate is bot1's first NewMessage handler.")
                    return True
                msg = (f"nonhuman_sender_gate is NOT bot1's first NewMessage handler "
                       f"(first is {getattr(callback, '__name__', callback)}). Bots' messages can reach it.")
                print(f"🚨 [botgate] {msg}")
                asyncio.ensure_future(report_system_error("verify_botgate_is_first", msg))
                return False
    except Exception as e:
        print(f"⚠️ verify_botgate_is_first could not run: {type(e).__name__}: {e}")
    return None

# 🛡️ bot2/bot3 have been fully retired — everything now runs on bot1. bot3 is kept as a
# permanent `None` (rather than deleting the name outright) so any leftover `bot3 is None` /
# `bot3 is not None` check elsewhere still resolves safely instead of raising a NameError.
bot3 = None
bot_ids = bot_state.bot_ids
active_group_spawns = bot_state.active_group_spawns
STEALTH_MAU_MODE = False
spawn_locks = bot_state.spawn_locks
market_dm_conversation_locks = bot_state.market_dm_conversation_locks
catch_race_buffer = bot_state.catch_race_buffer
pending_editchar_prompt_ids = bot_state.pending_editchar_prompt_ids
pending_gban_prompt_ids = bot_state.pending_gban_prompt_ids  # /gban wizard — see GBAN COMMANDS section near /addowner
pending_ccm_event_prompt_ids = bot_state.pending_ccm_event_prompt_ids  # /setvalue's SUPREME event-value picker
sticker_spam_data = bot_state.sticker_spam_data
char_spam_data = bot_state.char_spam_data
admin_cache = bot_state.admin_cache
dark_passenger_targets = bot_state.dark_passenger_targets
_unlimited_vault_pages_cache = bot_state._unlimited_vault_pages_cache
UNLIMITED_VAULT_PAGES_CACHE_TTL = 600  # 10 min safety-net TTL — invalidate_character_caches() clears this immediately on any real roster change
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

# 📤 /adduploader — user_ids the owner has authorised to use /addchar (and ONLY /addchar).
# Unlike /addowner this grants no vault/gift privilege and no other owner command. Loaded once at
# startup (load_uploaders_cache), kept in sync in-memory on every /adduploader or /removeuploader.
uploader_ids = set()

async def load_uploaders_cache():
    global uploader_ids
    try:
        docs = await uploaders_col.find({}, {"user_id": 1}).to_list(length=None)
        uploader_ids = {d["user_id"] for d in docs}
    except Exception as e:
        print(f"load_uploaders_cache error: {e}")

def can_addchar(user_id):
    return user_id == OWNER_ID or user_id in uploader_ids

# ==========================================
# 🚫 GBAN — GLOBAL BAN SYSTEM, ENFORCEMENT GATES (Owner-only)
# ==========================================
# /gban blocks a user bot-wide — every group AND every DM, every command AND every inline
# button tap — and confiscates their cards. This section is ONLY the fast enforcement check
# (is_gbanned) and the two gates that use it; the actual /gban, /ungban, /gunban commands and
# the 2-step reason->duration wizard that WRITE to gbanned_until live in their own "GBAN
# COMMANDS" section near /addowner further down — same split as user_mute_until (aliased
# early, right below this block) vs. the spam-mute logic that populates it further down.
#
# 🔑 Registration order matters here: Telethon dispatches handlers of a given event type in
# the order they were registered, and events.StopPropagation stops every handler after the
# one that raised it from ever seeing that update. Both gates below are registered
# IMMEDIATELY after bot1 is created — before callback_spam_click_guard (the current first
# CallbackQuery handler) and before global_slash_cmd_acc_opener (the current first NewMessage
# handler) — specifically so a banned user's tap or command never reaches anything else,
# including the "am I muted" checks, force-sub gate, or any real command logic below.
#
# 🔑 Storage is two layers, same pattern as user_mute_until:
#   gbanned_until (in-memory, aliased below) — fast: checked synchronously on every single
#   message and callback, no DB round trip.
#   gban_col (Mongo, see gban_col = db["gban_data"] near added_owners_col above) — durable:
#   survives a restart via load_active_gbans_cache() (GBAN COMMANDS section), so a "perm" ban
#   doesn't quietly lift itself just because the process restarted.
#
# ⚠️ The message gate below matches own_pattern(r'^[/.]', 'bot1') — same as
# global_slash_cmd_acc_opener — so an explicit "@SomeOtherBot" mention still passes through
# untouched, and a banned user's normal chat (no leading / or .) is deliberately left alone;
# only their commands are blocked.
GBAN_NOTICE_COOLDOWN = 20  # seconds — don't re-send the "you're banned" reply more than once per window
gbanned_until = bot_state.gbanned_until                     # user_id -> {"expiry","reason","duration_label"}
_gban_notice_last_sent = bot_state._gban_notice_last_sent   # user_id -> ts, throttles the reply only — the callback alert below is an ephemeral per-tap popup, not a chat message, so it isn't throttled

def is_gbanned(user_id):
    """Fast, sync, in-memory-only — safe as literally the first check in every handler.
    Returns (banned: bool, record: dict|None). Lazily expires + self-heals gbanned_until the
    moment anything checks a ban whose time has already passed, rather than waiting on a
    periodic sweep, and nudges gban_col's 'active' flag false in the background so the DB
    doesn't keep showing an already-expired ban as active."""
    rec = gbanned_until.get(user_id)
    if not rec:
        return False, None
    if rec["expiry"] != float('inf') and time.time() >= rec["expiry"]:
        gbanned_until.pop(user_id, None)
        try:
            asyncio.create_task(gban_col.update_many(
                {"user_id": user_id, "active": True},
                {"$set": {"active": False, "lifted_at": time.time()}}
            ))
        except Exception:
            pass
        return False, None
    return True, rec

def build_gban_blocked_text(rec):
    reason = escape_html(rec.get("reason") or "No reason given")
    duration_label = escape_html(str(rec.get("duration_label", "Permanent")))
    return (
        f"🚫 <b>You are globally banned from this bot.</b>\n\n"
        f"📝 <b>Reason:</b> {reason}\n"
        f"⏳ <b>Duration:</b> {duration_label}\n\n"
        f"📩 Contact {owner_tag()} if you think this is a mistake."
    )

@bot1.on(events.CallbackQuery())
async def gban_block_gate_callback(event):
    banned, rec = is_gbanned(event.sender_id)
    if not banned:
        return
    try:
        await event.answer("🚫 You're globally banned from this bot.", alert=True)
    except Exception:
        pass
    raise events.StopPropagation

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]', 'bot1')))
async def gban_block_gate(event):
    banned, rec = is_gbanned(event.sender_id)
    if not banned:
        return
    now = time.time()
    if now - _gban_notice_last_sent.get(event.sender_id, 0) >= GBAN_NOTICE_COOLDOWN:
        _gban_notice_last_sent[event.sender_id] = now
        try:
            await event.reply(build_gban_blocked_text(rec), parse_mode='html')
        except Exception:
            pass
    raise events.StopPropagation

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
pending_trivia_quiz = bot_state.pending_trivia_quiz  # 🧠 TRIVIA — see trigger_trivia_spawn near perform_catch
trivia_spawn_counters = bot_state.trivia_spawn_counters
trivia_spawn_targets = bot_state.trivia_spawn_targets
RARITY_GATE_TIERS = {RARITY_TIERS[0], RARITY_TIERS[1], RARITY_TIERS[2], RARITY_TIERS[3]}
RARITY_GATE_TIMEOUT_SECONDS = 60
# 🩹 NEW (2026-09, owner request — "wrong tap = no spawn, so the top rarities are actually worth
# something"): True = the FIRST tap decides the gate for everybody. Correct -> spawn; wrong ->
# the gate closes, the character is NOT released, and the chat is told who tapped wrong.
# Set False to go back to the older rule (each person gets one try, the gate stays open for the
# others until someone taps the right answer or the timer runs out).
RARITY_GATE_WRONG_ANSWER_CLOSES_GATE = True
RARITY_GATE_FAIL_NOTICE_SECONDS = 10  # how long the "X tapped the wrong answer" notice stays before it's deleted
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
# 🎴 PER-TIER "VALUE" — a flat internal worth number stored on every character record,
# mirroring catch_bot's own per-tier values for parity. Purely a data field now — the
# currency system that used to let players earn/spend it has been removed, and nothing
# displays it to players anymore. Rarity 1 (highest) → 9 (lowest).
# ==========================================
# Emoji come from RARITY_EMOJI so there is only
# ever ONE place to change them. "name" is what gets stored on characters/harem items and
# shown everywhere — it's just the emoji + fancy font tier name, no rank number, so the
# name itself stays clean (no "No.X", no Burmese) wherever it's displayed.
_RARITY_VALUE_MAP = {
    "SUPREME": 100000, "CATAPHRACT": 70000, "CROSSVERSE": 50000, "DIVINE": 35000, "MYSTICAL": 25000,
    "LEGENDARY": 15000, "RARE": 10000, "UNCOMMON": 6000, "COMMON": 3000,
    "CNFT SS": 150000, "CNFT S": 120000, "CNFT A": 100000  # vestigial like the rest (see comment above) — never displayed or spent
}
# ⚠️ Display name for each tier, English only (no Burmese in the rarity name).
# classify_rarity() still matches on the bare RARITY_TIERS token (e.g. "SUPREME"), which is
# always the English display name here too, so this is safe to change freely without touching
# classification/sorting/weights.
RARITY_DISPLAY_NAME = {
    "SUPREME": "Supreme", "CATAPHRACT": "Cataphract", "CROSSVERSE": "CrossVerse", "DIVINE": "Divine",
    "MYSTICAL": "Mystical", "LEGENDARY": "Legendary", "RARE": "Rare", "UNCOMMON": "Uncommon", "COMMON": "Common",
    "CNFT SS": "CNFT SS", "CNFT S": "CNFT S", "CNFT A": "CNFT A"
}
# ⚠️ CNFT_TIERS: the 3 tiers appended to the end of RARITY_TIERS above. Excluded from
# RARITY_NUM_MAP/RARITY_TIER_TO_NUM below on purpose — /addchar's numeric 1-9 picker must never
# grow extra options that map to CNFT (those characters would spawn normally, since only
# /addspecial sets spawnable=False). CNFT is reachable ONLY by forwarding a card while
# /addspecial is armed, or via checksync importing one that already exists on catch_bot's side.
# 💠 CHANGED (per owner request): CNFT used to be one-of-one (a single current holder, forcibly
# transferred away on every re-gift). That's gone now — CNFT behaves exactly like a regular
# card for ownership/gifting purposes (see gift_asset_handler/gift_callback_handler), so the
# owner can gift the same CNFT card to as many different buyers as they like, each keeping
# their own independent copy. spawnable=False remains the ONLY thing that's still special about
# CNFT — it just never turns up as a random spawn.
CNFT_TIERS = {"CNFT SS", "CNFT S", "CNFT A"}
CNFT_PROMO_GROUP_URL = "https://t.me/Comeback_BoD"  # used by the cnft. inline query below (release_spawn's own button now opens the OWNER MODE promo instead — see OWNER_MODE_* below)

# ==========================================
# 🖤 OWNER MODE — paid lifetime "unlock every card" promo. release_spawn's spawn button
# (previously a direct link to CNFT_PROMO_GROUP_URL above) now opens this instead: tapping it
# DMs the tapper OWNER_MODE_TEXT_MY plus a Purchase button (-> OWNER_MODE_CONTACT_USERNAME) and
# a Translate button (-> OWNER_MODE_TEXT_EN). Every tap is logged to owner_mode_clicks_col; see
# /count. This is advertising only — same as CNFT, the actual sale/grant still happens by hand,
# by DM, with OWNER_ID (or whoever owns that Telegram handle) on the other end.
# ==========================================
OWNER_MODE_CONTACT_USERNAME = "LiberatorofHumanPotential"  # 🩹 update here if the purchase contact ever changes — nowhere else references the raw handle

OWNER_MODE_TEXT_MY = (
    "𖤐 𝗙𝗨𝗖𝗞 𝗕𝗢𝗧 — 𝗢𝗪𝗡𝗘𝗥 𝗠𝗢𝗗𝗘 𖤐\n"
    "♛ 𝗨𝗡𝗟𝗢𝗖𝗞 𝗧𝗛𝗘 𝗙𝗨𝗟𝗟 𝗘𝗫𝗣𝗘𝗥𝗜𝗘𝗡𝗖𝗘 ♛\n\n"
    "OWNER MODE နဲ့ Card အားလုံးကို Lifetime Unlock လုပ်ထားနိုင်ပါပြီ။\n\n"
    "╭───────────────╮\n"
    "⌬ OWNER MODE PERKS\n"
    "╰───────────────╯\n\n"
    "✦ SUP • CATA • CV • DV • MYST\n"
    " → Card အားလုံးကို Harem တိုင်းမှာ ရရှိနိုင်မယ်\n\n"
    "✦ NEW CARDS — AUTO UNLOCK\n"
    " → Card အသစ်တွေ ထပ်ထည့်တိုင်း အလိုအလျောက် ပါဝင်လာမယ်\n\n"
    "✦ 3× GIFT SYSTEM\n"
    " → Card တွေကို 3× Time အထိ Gift လုပ်နိုင်ပြီး ကိုယ့် Card မလျော့ပါ\n\n"
    "✦ ♾️ LIFETIME ACCESS\n"
    " → တစ်ကြိမ်ဝယ်ထားရုံနဲ့ Lifetime Owner\n\n"
    "━━━━━━━━━━━━━━━━━━\n\n"
    "💰 OWNER MODE — 20,000 Ks\n"
    "♾️ LIFETIME ACCESS\n\n"
    "𖤐 OWN MORE. UNLOCK MORE. PLAY MORE. 𖤐"
)

OWNER_MODE_TEXT_EN = (
    "𖤐 𝗙𝗨𝗖𝗞 𝗕𝗢𝗧 — 𝗢𝗪𝗡𝗘𝗥 𝗠𝗢𝗗𝗘 𖤐\n"
    "♛ 𝗨𝗡𝗟𝗢𝗖𝗞 𝗧𝗛𝗘 𝗙𝗨𝗟𝗟 𝗘𝗫𝗣𝗘𝗥𝗜𝗘𝗡𝗖𝗘 ♛\n\n"
    "Unlock every Card, for life, with OWNER MODE.\n\n"
    "╭───────────────╮\n"
    "⌬ OWNER MODE PERKS\n"
    "╰───────────────╯\n\n"
    "✦ SUP • CATA • CV • DV • MYST\n"
    " → Get access to all Cards across every Harem\n\n"
    "✦ NEW CARDS — AUTO UNLOCK\n"
    " → Every new Card added in the future is automatically included\n\n"
    "✦ 3× GIFT SYSTEM\n"
    " → Gift your Cards up to 3× — your own copy isn't deducted\n\n"
    "✦ ♾️ LIFETIME ACCESS\n"
    " → Pay once. Stay an Owner forever.\n\n"
    "━━━━━━━━━━━━━━━━━━\n\n"
    "💰 OWNER MODE — 20,000 Ks\n"
    "♾️ LIFETIME ACCESS\n\n"
    "𖤐 OWN MORE. UNLOCK MORE. PLAY MORE. 𖤐"
)
_NON_CNFT_TIERS = [t for t in RARITY_TIERS if t not in CNFT_TIERS]
RARITY_NUM_MAP = {
    str(i + 1): {
        "name": f"{RARITY_EMOJI[tier]} {f(RARITY_DISPLAY_NAME[tier])}",
        "value": _RARITY_VALUE_MAP[tier]
    }
    for i, tier in enumerate(_NON_CNFT_TIERS)
}
# Reverse lookup: canonical tier name -> its rarity number ("1".."4"). Used by /changeallrarity
# and anywhere we need to re-derive the current official display name for an existing tier.
RARITY_TIER_TO_NUM = {tier: str(i + 1) for i, tier in enumerate(_NON_CNFT_TIERS)}
# 🩹 Same {"name","value"} shape as RARITY_NUM_MAP, but keyed by CNFT tier name instead of a
# "1".."9" number — CNFT is deliberately kept OUT of RARITY_NUM_MAP/RARITY_TIER_TO_NUM (see
# comment above), but checksync (.check / /checksync / /syncfromcatch) still needs a real
# r_info dict when catch_bot's own reply reports a CNFT card. See _resolve_check_rarity below.
CNFT_RARITY_INFO = {
    tier: {
        "name": f"{RARITY_EMOJI[tier]} {f(RARITY_DISPLAY_NAME[tier])}",
        "value": _RARITY_VALUE_MAP[tier]
    }
    for tier in CNFT_TIERS
}

# ==========================================
# 💰 CCM + 🪙 GRAM CURRENCY SYSTEM
# ==========================================
# Two currencies, both stored as integers on users_catcher_col:
#   • 💰 ccm  (ccm_balance)  — the "earned" currency. Three sources, all tunable constants:
#       – /daily  — DAILY_MIN_MMK..DAILY_MAX_MMK (10–100 MMK-worth = 2,000–20,000 ccm), once per 24h
#       – trivia  — TRIVIA_DIFFICULTY_CONFIG (a few dozen ccm per win)
#       – catching ("fucking") a character — CATCH_CCM_MIN..CATCH_CCM_MAX, deliberately tiny
#   • 🪙 gram (gram_balance) — the value currency. /exchange turns ccm into grams at
#     CCM_PER_GRAM ccm = 1 g. Every card's WORTH is expressed in grams only, and
#     1 g = MMK_PER_GRAM MMK — so a card the owner prices at 500–700 g is a 500–700 MMK card.
#
# Card worth tables live in bot_settings_col as two singleton docs, edited ONLY through /setvalue
# and ONLY in grams:
#   • "gram_tier_values"  — Rarity 2 (CATAPHRACT) … 9 (COMMON), each a [min, max] range in grams,
#     keyed by RARITY_NUM_MAP's own "2".."9" numbering.
#   • "gram_event_values" — Rarity 1 (SUPREME) is priced per EVENT (one value in grams each), as a
#     list of {"event","value"} pairs so an event name containing "." can't be misread by Mongo
#     as a dotted field path.
# ⚠️ The older "ccm_tier_values" / "ccm_event_values" docs hold ccm-denominated numbers and are
# deliberately NOT read any more: reading "5000" (ccm) as "5000 g" would be a 200x pricing error.
# Re-enter prices with /setvalue. A tier/event with no price yet simply shows no worth line.
CCM_PER_GRAM = 200       # 💱 exchange rate: this many ccm buy exactly 1 gram
MMK_PER_GRAM = 1         # 🇲🇲 1 gram is worth this many MMK (owner's pricing basis)
GRAM_EMOJI = "🪙"        # gram's emoji — change it here and it changes everywhere

def fmt_gram(n):
    return f"{int(n):,} g"

# 🎁 /daily pays a random amount worth DAILY_MIN_MMK..DAILY_MAX_MMK, paid out in ccm at the rates
# above (10 MMK = 10 g = 2,000 ccm; 100 MMK = 100 g = 20,000 ccm) — so changing CCM_PER_GRAM or
# MMK_PER_GRAM re-prices the daily automatically.
DAILY_MIN_MMK = 10
DAILY_MAX_MMK = 100
DAILY_COOLDOWN_SECONDS = 86400
DAILY_STREAK_RESET_SECONDS = 172800   # miss more than a day beyond the cooldown -> streak restarts at 1

def daily_ccm_range():
    """(min_ccm, max_ccm) a /daily can pay, derived from the MMK range + exchange rates."""
    return (DAILY_MIN_MMK * CCM_PER_GRAM // MMK_PER_GRAM, DAILY_MAX_MMK * CCM_PER_GRAM // MMK_PER_GRAM)

# 🎴 A successful catch ("fuck") pays a small flat ccm amount — kept tiny on purpose
# (≤ DAILY_CATCH_LIMIT catches/day, so at most ~440 ccm ≈ 2 g a day from catching).
CATCH_CCM_MIN = 5
CATCH_CCM_MAX = 20

# 📋 Worth shown on /check until the owner prices a tier with /setvalue (a /setvalue'd value always
# wins). Anchored on "Divine = 500–700 g (= 500–700 MMK)" and scaled by each tier's relative
# weight in _RARITY_VALUE_MAP. This is DISPLAY ONLY — nothing is paid or charged from these numbers.
DEFAULT_GRAM_TIER_VALUES = {
    "2": (1000, 1400), "3": (700, 1000), "4": (500, 700), "5": (350, 500),
    "6": (200, 300), "7": (140, 200), "8": (85, 120), "9": (45, 60),
}
DEFAULT_SUPREME_GRAM_RANGE = (1500, 2000)   # SUPREME events with no /setvalue price yet

def format_worth_line(lo, hi):
    """🪙 ᴡᴏʀᴛʜ: 𝟱𝟬𝟬 ~ 𝟳𝟬𝟬 𝗚𝗿𝗮𝗺 — label in catch_bot's small-caps, value + unit in the bold math font."""
    amount = f(f"{lo:,}") if lo == hi else f"{f(f'{lo:,}')} ~ {f(f'{hi:,}')}"
    return f"{GRAM_EMOJI} {catchstyle_caps('worth')}: {amount} {f('Gram')}"

async def _get_gram_tier_values():
    """{"2": {"min","max"}, ..., "9": {...}} in GRAMS — only tiers the owner has /setvalue'd are
    present; a missing key means "not priced yet", not "priced at zero"."""
    doc = await bot_settings_col.find_one({"_id": "gram_tier_values"})
    return (doc or {}).get("values", {})

async def _get_gram_event_values():
    """{event_name: grams} for SUPREME (Rarity 1), reshaped from the stored
    {"events": [{"event","value"}, ...]} list into a dict."""
    doc = await bot_settings_col.find_one({"_id": "gram_event_values"})
    return {e["event"]: e["value"] for e in (doc or {}).get("events", []) if e.get("event")}

async def _set_gram_event_value(event_name, grams):
    """Upsert one SUPREME event's worth (in grams) into the gram_event_values list."""
    doc = await bot_settings_col.find_one({"_id": "gram_event_values"}) or {"events": []}
    events_list = doc.get("events", [])
    for e in events_list:
        if e.get("event") == event_name:
            e["value"] = grams
            break
    else:
        events_list.append({"event": event_name, "value": grams})
    await bot_settings_col.update_one({"_id": "gram_event_values"}, {"$set": {"events": events_list}}, upsert=True)

async def _card_worth_grams(rarity_tier, event_name):
    """(min_g, max_g) this card is worth: the owner's /setvalue price if set, else the default
    ladder (DEFAULT_GRAM_TIER_VALUES / DEFAULT_SUPREME_GRAM_RANGE). SUPREME has a single value per
    event, so min == max when it was /setvalue'd. None for CNFT / OTHER. Never raises."""
    try:
        if rarity_tier == "SUPREME":
            v = (await _get_gram_event_values()).get(event_name or "General")
            if v is not None:
                return (int(v), int(v))
            return DEFAULT_SUPREME_GRAM_RANGE
        num = RARITY_TIER_TO_NUM.get(rarity_tier)  # None for CNFT / OTHER — not priced by this system
        if not num:
            return None
        rng = (await _get_gram_tier_values()).get(num)
        if rng:
            lo, hi = int(rng.get("min", 0)), int(rng.get("max", 0))
        else:
            lo, hi = DEFAULT_GRAM_TIER_VALUES.get(num, (0, 0))
        if hi < lo:
            lo, hi = hi, lo
        return (lo, hi) if hi > 0 else None
    except Exception as e:
        print(f"_card_worth_grams error: {type(e).__name__}: {e}")
        return None

async def try_deduct_ccm(user_id, amount):
    """Atomically deduct `amount` 💰 ccm from user_id ONLY if they currently have enough —
    returns True on success, False if insufficient. The balance check and the deduction happen
    as a single atomic Mongo operation (find_one_and_update with the balance check baked into
    the filter itself), not a separate read-then-write — so two concurrent spends (e.g. a
    /giftccm confirm landing at the same moment as a trivia loss) can never both succeed and
    push the balance negative. Shared by /giftccm now, and meant to be the same primitive any
    future card-marketplace purchase flow uses for its own payment step."""
    result = await users_catcher_col.find_one_and_update(
        {"user_id": user_id, "ccm_balance": {"$gte": amount}},
        {"$inc": {"ccm_balance": -amount}}
    )
    return result is not None

# ♾️ OWNER_ID has an UNLIMITED gram wallet (per owner request, so the owner can hand grams out as gifts
# via /giftgram): every gram spend by the owner succeeds and deducts nothing, and refunds to the owner
# are no-ops. Grams the owner gives out are minted — each such /giftgram is logged with minted=True in
# gram_transfers. Applies to OWNER_ID only, not to /addowner grantees.
GRAM_UNLIMITED_OWNER = True

def has_unlimited_gram(user_id):
    return GRAM_UNLIMITED_OWNER and user_id == OWNER_ID

async def refund_gram(user_id, amount):
    """Give back grams that were taken for something that then failed. No-op for the unlimited owner
    (nothing was ever deducted from them)."""
    if amount > 0 and not has_unlimited_gram(user_id):
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"gram_balance": amount}})

async def try_deduct_gram(user_id, amount):
    """Atomic 🪙 gram spend — same compare-and-deduct primitive as try_deduct_ccm: the balance
    check is part of the update filter itself, so two simultaneous spends can never both succeed
    and push gram_balance negative. True = deducted, False = not enough. (The unlimited owner: always True.)"""
    if has_unlimited_gram(user_id):
        return True
    result = await users_catcher_col.find_one_and_update(
        {"user_id": user_id, "gram_balance": {"$gte": amount}},
        {"$inc": {"gram_balance": -amount}}
    )
    return result is not None

# ==========================================
# 🔒 LIMITED RARITIES — SUPREME (every event) + CATAPHRACT  (per owner request)
# ==========================================
#   • CATCH LIMIT: every card of these tiers can be caught at most LIMITED_TIER_SPAWN_LIMIT[tier]
#     times in total. This reuses the bot's existing per-character CatchLimit (spawn_limit vs
#     spawn_count — see get_spawn_eligible_characters): once a card has been caught that many
#     times it simply stops spawning. apply_limited_spawn_limits() sets/lowers spawn_limit to the
#     cap on EVERY such card — old ones and newly added ones alike — and the background loop
#     re-applies it every LIMIT_POLICY_INTERVAL_SECONDS, so a character added by /addchar,
#     /syncfromcatch or edited with /editchar can't escape it. A lower limit someone set on
#     purpose (e.g. 10) is respected; "infinite" (0) or anything above the cap is pulled down.
#   • PER-USER CAP: nobody may RECEIVE a copy of a limited card from another player once they hold
#     LIMITED_PER_USER_CAP copies of it — enforced on /gift (prompt + confirm) and on market bids
#     (can_receive_limited). Catching (/fuck) is NEVER blocked: winning a 4th copy by catching is
#     accepted. Any surplus that already exists — copies that arrived by gift / auction beyond the
#     cap — is removed automatically by limit_policy_loop: copies the user caught themselves
#     (harem entry has a chat_id) and market-listed copies are never touched; of the received
#     copies the OLDEST are kept up to the cap and the newest removed. Every removed copy is first
#     written to `limit_removed_cards`, so nothing is unrecoverable.
#   • The very FIRST excess-removal pass waits for the owner's one-tap approval (a preview is DMed,
#     or run /limitsreport) because it can delete real players' cards; once approved, later passes
#     are fully automatic. Set LIMIT_AUTO_DELETE = False to turn deletion off entirely.
LIMITED_TIER_SPAWN_LIMIT = {"SUPREME": 30, "CATAPHRACT": 30}
LIMITED_PER_USER_CAP = 3
LIMIT_POLICY_INTERVAL_SECONDS = 120     # re-apply the catch limits (new/old cards)
LIMIT_SWEEP_INTERVAL_SECONDS = 900      # per-user excess sweep
LIMIT_SWEEP_FIRST_DELAY_SECONDS = 150   # let boot settle first
LIMIT_PREVIEW_REMIND_SECONDS = 6 * 3600 # re-send the approval preview at most this often
LIMIT_AUTO_DELETE = True
LIMIT_MAX_REMOVALS_PER_SWEEP = 5000     # runaway guard: a single sweep never removes more than this
limit_removed_cards_col = db["limit_removed_cards"]

def is_limited_tier(tier):
    return tier in LIMITED_TIER_SPAWN_LIMIT

def count_copies(harem, char_id):
    return sum(1 for x in (harem or []) if isinstance(x, dict) and x.get("char_id") == char_id)

def effective_spawn_limit(requested, tier):
    """The catch limit a card of `tier` is allowed to have: the tier cap if it's 'infinite' (<=0)
    or above the cap, otherwise whatever was asked for."""
    cap = LIMITED_TIER_SPAWN_LIMIT.get(tier, 0)
    requested = int(requested or 0)
    if cap and (requested <= 0 or requested > cap):
        return cap
    return requested

def can_receive_limited(harem, char_id, tier):
    """False if getting one more copy of char_id would put this harem over the per-user cap."""
    return not (is_limited_tier(tier) and count_copies(harem, char_id) >= LIMITED_PER_USER_CAP)

def _doc_tier(doc):
    return doc.get("rarity_tier") or classify_rarity(doc.get("rarity"))

async def apply_limited_spawn_limits():
    """Sets spawn_limit to the tier cap on every SUPREME/CATAPHRACT card that is infinite or above
    it. Only candidates (limit unset / <=0 / above the highest cap) are even read. Returns how many
    cards were changed."""
    top = max(LIMITED_TIER_SPAWN_LIMIT.values())
    cands = await characters_base_col.find(
        {"$or": [{"spawn_limit": None}, {"spawn_limit": {"$lte": 0}}, {"spawn_limit": {"$gt": top}}]},
        {"char_id": 1, "rarity": 1, "rarity_tier": 1, "spawn_limit": 1}
    ).to_list(length=None)
    ops = []
    for d in cands:
        tier = _doc_tier(d)
        if not d.get("char_id") or not is_limited_tier(tier):
            continue
        new_limit = effective_spawn_limit(d.get("spawn_limit"), tier)
        if new_limit != (d.get("spawn_limit") or 0):
            ops.append(UpdateOne({"char_id": d["char_id"]}, {"$set": {"spawn_limit": new_limit}}))
    if ops:
        await characters_base_col.bulk_write(ops, ordered=False)
        await invalidate_character_caches(hard=False)
    return len(ops)

def plan_user_removals(harem, limited_ids):
    """Pure. Given one user's harem, returns {char_id: [entries to remove]}.
    A copy the user CAUGHT themselves (/fuck — the entry carries a chat_id) or that is listed on the
    market is never removed, and still counts toward the cap. Only copies that arrived from other
    players (gift / auction win / owner gift — no chat_id) are surplus: the OLDEST received copies are
    kept until the user is at LIMITED_PER_USER_CAP in total, the newer ones are removed."""
    by_char = {}
    for e in (harem or []):
        if isinstance(e, dict) and e.get("char_id") in limited_ids:
            by_char.setdefault(e["char_id"], []).append(e)
    plan = {}
    for cid, entries in by_char.items():
        if len(entries) <= LIMITED_PER_USER_CAP:
            continue
        untouchable = [e for e in entries if e.get("status") == "market" or e.get("chat_id") is not None]
        received = sorted((e for e in entries if e.get("status") != "market" and e.get("chat_id") is None),
                          key=lambda e: (e.get("caught_date") or 0))
        room = max(0, LIMITED_PER_USER_CAP - len(untouchable))
        surplus = received[room:]
        if surplus:
            plan[cid] = surplus
    return plan

async def _limited_char_ids():
    docs = await characters_base_col.find({}, {"char_id": 1, "rarity": 1, "rarity_tier": 1}).to_list(length=None)
    return {d["char_id"] for d in docs if d.get("char_id") and is_limited_tier(_doc_tier(d))}

async def sweep_limited_excess(dry_run=True, max_removals=None):
    """Finds (and, unless dry_run, removes) every copy above the per-user cap. Each user's harem
    is rewritten with a compare-and-set on the exact array that was read, so a catch/gift landing
    mid-sweep makes that one user's write fail harmlessly (retried next pass) instead of being lost.
    Removed copies are backed up to limit_removed_cards first. Returns a stats dict."""
    max_removals = LIMIT_MAX_REMOVALS_PER_SWEEP if max_removals is None else max_removals
    ids = await _limited_char_ids()
    stats = {"limited_cards": len(ids), "users": 0, "removed": 0, "skipped_race": 0,
             "per_char": {}, "top_users": [], "capped": False}
    if not ids:
        return stats
    batch = f"{int(time.time())}"
    per_user = []
    cursor = users_catcher_col.find({"harem.char_id": {"$in": list(ids)}}, {"user_id": 1, "harem": 1})
    async for udoc in cursor:
        plan = plan_user_removals(udoc.get("harem"), ids)
        if not plan:
            continue
        n = sum(len(v) for v in plan.values())
        if stats["removed"] + n > max_removals and not dry_run:
            stats["capped"] = True
            break
        stats["users"] += 1
        stats["removed"] += n
        for cid, ents in plan.items():
            stats["per_char"][cid] = stats["per_char"].get(cid, 0) + len(ents)
        per_user.append((udoc["user_id"], n))
        if dry_run:
            continue
        removed_ids = {id(e) for v in plan.values() for e in v}
        new_harem = [e for e in udoc["harem"] if id(e) not in removed_ids]
        backups = [{"user_id": udoc["user_id"], "char_id": cid, "entry": e, "reason": "per_user_cap",
                    "cap": LIMITED_PER_USER_CAP, "batch": batch, "removed_at": time.time()}
                   for cid, ents in plan.items() for e in ents]
        ins = await limit_removed_cards_col.insert_many(backups)
        res = await users_catcher_col.update_one(
            {"user_id": udoc["user_id"], "harem": udoc["harem"]}, {"$set": {"harem": new_harem}})
        if not res.matched_count:
            await limit_removed_cards_col.delete_many({"_id": {"$in": ins.inserted_ids}})
            stats["users"] -= 1
            stats["removed"] -= n
            stats["skipped_race"] += 1
            for cid, ents in plan.items():
                stats["per_char"][cid] -= len(ents)
                if stats["per_char"][cid] <= 0:
                    del stats["per_char"][cid]
    stats["top_users"] = sorted(per_user, key=lambda x: -x[1])[:5]
    return stats

def _limits_preview_text(stats, over_global):
    lines = [
        "🔒 <b>Limited rarity — Supreme / Cataphract</b>",
        f"• catch limit: <code>{max(LIMITED_TIER_SPAWN_LIMIT.values())}</code> per card · per-user cap: <code>{LIMITED_PER_USER_CAP}</code> copies",
        f"• limited cards: <code>{stats['limited_cards']}</code>",
    ]
    if stats["removed"]:
        lines.append(f"• <b>per-user excess:</b> <code>{stats['removed']}</code> copies held by <code>{stats['users']}</code> user(s) "
                     f"across <code>{len(stats['per_char'])}</code> card(s)")
        if stats["top_users"]:
            lines.append("  top: " + ", ".join(f"<code>{u}</code> ×{n}" for u, n in stats["top_users"]))
        lines.append("  <i>(only copies received by gift/market beyond the cap are removed, newest first — copies a user "
                     "caught with /fuck and market-listed copies are never touched; every removed copy is backed up "
                     "in limit_removed_cards)</i>")
    else:
        lines.append("• per-user excess: <code>0</code> ✅")
    if over_global:
        lines.append(f"• cards already past the global limit: <code>{over_global}</code> — they stop spawning; "
                     f"existing copies are NOT removed")
    return "\n".join(lines)

async def _count_over_global_limit():
    docs = await characters_base_col.find({"spawn_limit": {"$gt": 0}}, {"char_id": 1, "rarity": 1, "rarity_tier": 1,
                                                                         "spawn_limit": 1, "spawn_count": 1}).to_list(length=None)
    return sum(1 for d in docs if is_limited_tier(_doc_tier(d)) and (d.get("spawn_count") or 0) > (d.get("spawn_limit") or 0))

def _limits_approve_buttons():
    return [[Button.inline("✅ Delete excess + auto from now on", data="limitsweep_approve"),
             Button.inline("❌ Not now", data="limitsweep_skip")]]

async def limit_policy_loop():
    """Background: (1) keep every limited card's catch limit at its cap (new + old cards);
    (2) sweep per-user excess — first pass needs the owner's one-time approval (see block comment)."""
    await asyncio.sleep(LIMIT_SWEEP_FIRST_DELAY_SECONDS)
    last_sweep = 0.0
    while True:
        try:
            changed = await apply_limited_spawn_limits()
            if changed:
                print(f"🔒 [limits] catch limit applied to {changed} Supreme/Cataphract card(s).")
            if LIMIT_AUTO_DELETE and time.time() - last_sweep >= LIMIT_SWEEP_INTERVAL_SECONDS:
                last_sweep = time.time()
                state = await bot_settings_col.find_one({"_id": "limit_sweep_state"}) or {}
                if state.get("approved"):
                    stats = await sweep_limited_excess(dry_run=False)
                    if stats["removed"]:
                        print(f"🔒 [limits] removed {stats['removed']} surplus cop(ies) from {stats['users']} user(s).")
                        try:
                            await bot1.send_message(OWNER_ID, "🔒 <b>Auto limit sweep</b>\n" + _limits_preview_text(
                                {**stats, "removed": stats["removed"]}, 0).replace("per-user excess:", "removed now:"),
                                parse_mode='html')
                        except Exception:
                            pass
                else:
                    stats = await sweep_limited_excess(dry_run=True)
                    if not stats["removed"]:
                        await bot_settings_col.update_one({"_id": "limit_sweep_state"}, {"$set": {"approved": True}}, upsert=True)
                    elif time.time() - state.get("preview_sent_at", 0) >= LIMIT_PREVIEW_REMIND_SECONDS:
                        await bot_settings_col.update_one({"_id": "limit_sweep_state"}, {"$set": {"preview_sent_at": time.time()}}, upsert=True)
                        try:
                            await bot1.send_message(
                                OWNER_ID,
                                _limits_preview_text(stats, await _count_over_global_limit())
                                + "\n\n⚠️ <b>First-time approval needed</b> — this deletes players' cards.",
                                parse_mode='html', buttons=_limits_approve_buttons())
                        except Exception as e:
                            print(f"⚠️ [limits] couldn't DM the owner the preview: {type(e).__name__}")
        except Exception as e:
            print(f"⚠️ limit_policy_loop error: {type(e).__name__}: {e}")
        await asyncio.sleep(LIMIT_POLICY_INTERVAL_SECONDS)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]limitsreport(?:@\w+)?$', 'bot1')))
async def limits_report_command(event):
    if event.sender_id != OWNER_ID:
        return
    state = await bot_settings_col.find_one({"_id": "limit_sweep_state"}) or {}
    stats = await sweep_limited_excess(dry_run=True)
    await apply_limited_spawn_limits()
    text = _limits_preview_text(stats, await _count_over_global_limit())
    if state.get("approved"):
        text += "\n\n🤖 Auto-removal is <b>ON</b> (runs every " + f"{LIMIT_SWEEP_INTERVAL_SECONDS // 60} min)."
        return await event.reply(text, parse_mode='html')
    await event.reply(text + ("\n\n⚠️ Removal hasn't been approved yet." if stats["removed"] else ""),
                      parse_mode='html', buttons=_limits_approve_buttons() if stats["removed"] else None)

@bot1.on(events.CallbackQuery(pattern=r'^limitsweep_(approve|skip)$'))
async def limit_sweep_callback(event):
    if event.sender_id != OWNER_ID:
        return await event.answer("Owner only.", alert=True)
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)
    if action == "skip":
        await event.edit("❎ Nothing deleted. I'll ask again later (or run /limitsreport).", buttons=None)
        return await event.answer("OK")
    await event.answer("Working…")
    try:
        await bot_settings_col.update_one({"_id": "limit_sweep_state"}, {"$set": {"approved": True}}, upsert=True)
        stats = await sweep_limited_excess(dry_run=False)
        await event.edit(
            f"✅ <b>Done.</b> Removed <code>{stats['removed']}</code> surplus cop(ies) from <code>{stats['users']}</code> user(s)"
            + (f" · <code>{stats['skipped_race']}</code> skipped (busy, retried automatically)" if stats["skipped_race"] else "")
            + (" · ⚠️ stopped at the per-sweep safety cap, the rest follows automatically" if stats["capped"] else "")
            + "\n🤖 Auto-removal is ON now. Backups: <code>limit_removed_cards</code>.",
            parse_mode='html', buttons=None)
    except Exception as e:
        await report_system_error("limit_sweep_callback", str(e))
        await event.edit(f"❌ Failed: <code>{escape_html(str(e)[:200])}</code>", parse_mode='html', buttons=None)

# ==========================================
# 🎁 TAKE GRAM FREE — bot2's DM faucet (per owner request)
# ==========================================
# Under every successful catch ("fuck") message, below the 🛒 Buy & Sell button, there is a URL button
# "🎁 Take Gram Free.." that ANYONE in the chat can tap. It opens bot2's private chat
# (https://t.me/<bot2>?start=freegram) — Telegram shows Start if they never started it — and the
# /start that follows pays FREE_GRAM_MIN..FREE_GRAM_MAX grams, once per FREE_GRAM_COOLDOWN_SECONDS
# per Telegram user (24h, like /daily). It pays into the same gram_balance /balance and /exchange use.
# Needs the secondary bot (SECONDARY_BOT_TOKEN) — with no bot2 the button simply isn't shown.
# The claim is a compare-and-set on last_free_gram inside ONE Mongo update (same pattern as /daily), so
# repeated /start taps can never pay twice. Every payout is logged in free_gram_claims; globally banned
# users (/gban) are refused. Tune the amount with FREE_GRAM_MIN / FREE_GRAM_MAX below.
FREE_GRAM_MIN = 50
FREE_GRAM_MAX = 200
FREE_GRAM_COOLDOWN_SECONDS = 86400
FREE_GRAM_START_PAYLOAD = "freegram"
FREE_GRAM_BUTTON_LABEL = "🎁 Take Gram Free.."
free_gram_claims_col = db["free_gram_claims"]

def free_gram_url():
    """Deep link into bot2's DM, or None when bot2 isn't configured / hasn't connected yet."""
    if bot2 is None or not BOT2_USERNAME:
        return None
    return f"https://t.me/{BOT2_USERNAME}?start={FREE_GRAM_START_PAYLOAD}"

async def claim_free_gram(user_id, fullname):
    """-> ("ok", grams_paid, new_balance) | ("cooldown", seconds_left, 0) | ("banned", 0, 0)"""
    banned, _rec = is_gbanned(user_id)
    if banned:
        return "banned", 0, 0
    await ensure_user_registered(user_id, fullname)
    now = time.time()
    doc = await users_catcher_col.find_one({"user_id": user_id}, {"last_free_gram": 1}) or {}
    last = doc.get("last_free_gram", 0) or 0
    if now - last < FREE_GRAM_COOLDOWN_SECONDS:
        return "cooldown", int(FREE_GRAM_COOLDOWN_SECONDS - (now - last)), 0
    grams = random.randint(FREE_GRAM_MIN, FREE_GRAM_MAX)
    # compare-and-set: only pays if last_free_gram is still exactly what we just read
    cas = {"user_id": user_id, "last_free_gram": last} if last else {"user_id": user_id, "last_free_gram": {"$in": [0, None]}}
    claimed = await users_catcher_col.find_one_and_update(
        cas, {"$inc": {"gram_balance": grams}, "$set": {"last_free_gram": now}}, return_document=ReturnDocument.AFTER)
    if claimed is None:   # a concurrent /start got there first
        doc = await users_catcher_col.find_one({"user_id": user_id}, {"last_free_gram": 1}) or {}
        return "cooldown", int(FREE_GRAM_COOLDOWN_SECONDS - (time.time() - (doc.get("last_free_gram", now) or now))), 0
    try:
        await free_gram_claims_col.insert_one({"user_id": user_id, "grams": grams, "ts": now})
    except Exception as e:
        print(f"⚠️ free_gram_claims log failed (the payout itself succeeded): {type(e).__name__}: {e}")
    return "ok", grams, int(claimed.get("gram_balance", 0))

async def bot2_free_gram_handler(event):
    """bot2, private chat only: any /start (the Start button of the deep link) claims the free gram."""
    sender = await event.get_sender()
    if sender is None or getattr(sender, "bot", False):
        return
    user_id = event.sender_id
    name = " ".join(x for x in (getattr(sender, "first_name", None), getattr(sender, "last_name", None)) if x) or str(user_id)
    status, a, b = await claim_free_gram(user_id, name)
    buttons = [[Button.url("🎴 Open main bot", f"https://t.me/{BOT1_USERNAME}")]] if BOT1_USERNAME else None
    if status == "banned":
        return await event.reply("⛔ သင့်ကို ဒီ bot မှာ ပိတ်ပင်ထားပါတယ်။")
    if status == "cooldown":
        return await event.reply(
            f"⏳ <b>ယနေ့အတွက် ယူပြီးသားပါ။</b> နောက်တစ်ကြိမ် <code>{str(timedelta(seconds=max(1, a)))}</code> အကြာမှာ ပြန်ယူလို့ရပါမယ်။",
            parse_mode='html', buttons=buttons)
    await event.reply(
        f"🎁 <b>Free Gram ရပါပြီ!</b>\n"
        f"{GRAM_EMOJI} <code>+{a:,}</code> g\n"
        f"{GRAM_EMOJI} လက်ကျန်: <code>{b:,}</code> g\n\n"
        f"⏰ နောက် ၂၄ နာရီကြာမှ ထပ်ယူလို့ရပါမယ်။ Main bot မှာ /balance နဲ့ ကြည့်ပါ။",
        parse_mode='html', buttons=buttons)

if bot2 is not None:
    bot2.add_event_handler(bot2_free_gram_handler, events.NewMessage(
        incoming=True, pattern=r'^/start(?:@\w+)?(?:\s+\S+)?$', func=lambda e: e.is_private))

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
# 🩹 CHANGED (per owner request): force-join is now the BODgram_SF group chat —
# https://t.me/BODgram_SF (-1004478099253). Hardcoded on purpose, NOT read from the
# FORCE_SUB_CHAT_ID env var: an old value still set on Render would silently override this and keep
# gating on a previous chat. ⚠️ bot1 should be a member/ADMIN of this chat so the membership check
# can run (if it can't, the check fails open, i.e. nobody gets gated). Everyone who JOINS this chat
# is also offered the one-time welcome gift — see WELCOME GIFT below.
FORCE_SUB_CHAT_ID = -1004478099253
FORCE_SUB_USERNAME = "BODgram_SF"
FORCE_SUB_PUBLIC_LINK = "https://t.me/BODgram_SF"
# The daily stats report keeps going to the group it always went to (not to the force-sub chat).
# Set this to FORCE_SUB_CHAT_ID if you'd rather post it in the BODgram_SF chat instead.
DAILY_REPORT_CHAT_ID = -1003580630981
FORCE_SUB_MEMBERSHIP_TTL = 120  # seconds a "yes/no member" answer is cached per user
FORCE_SUB_PROMPT_COOLDOWN = 30  # seconds — don't re-nag the same user more than once per 5 min
FORCE_SUB_PROMPT_TTL = 30  # seconds — the join-nudge message deletes itself after this long

# 2026-08 UPDATE (per owner request): force-sub now gates EVERY normal player-facing command,
# not just a handful — that includes /w, /who, /waifu (previously ungated, now explicitly
# added below), plus every other read/play command in the game. Kept OUT on purpose:
#   • /start, /help — a not-yet-joined user still needs these to learn what the bot is and
#     get the join button in the first place. Gating these would strand new users with no
#     way to even find the group.
#   • every admin/owner-only command (/addchar, /xbot*, /haitime, etc.) — moot anyway, since
#     force_sub_gate() below already exempts OWNER_ID unconditionally before this set is
#     ever checked.
# NOTE: the old comment here listed catch/haido/trade/buy/sell/scrap/richest/leaderboard/lb —
# none of those commands exist in this bot anymore (trading was removed entirely, see the note
# near /gift), so that stale list has been replaced with the actual current command set below.
FORCE_SUB_GATED_COMMANDS = {
    "who", "w", "waifu",       # reveal/identify a spawn — explicitly requested
    "harem", "fav",            # collection vault
    "profile",                 # stats card
    "check",                   # character lookup
    "top", "gtop", "today",    # leaderboards
    "show", "cr",              # gallery browsing
    "hmode",                   # rarity filter
    "gift",
    "fuck", "morgan", "catch", # kept from the original set
    "triviatop", "triviarank",   # 🧠 trivia leaderboard / rank — same public-info reasoning as /top, /gtop
}
_FORCE_SUB_CMD_RE = re.compile(r'^[/.](\w+)')

force_sub_membership_cache = bot_state.force_sub_membership_cache  # user_id -> (is_member: bool, expiry_ts: float)
market_force_sub_membership_cache = bot_state.market_force_sub_membership_cache
force_sub_prompt_last_sent = bot_state.force_sub_prompt_last_sent  # user_id -> ts of the last join-nudge sent (anti-spam)
_force_sub_invite_link = FORCE_SUB_PUBLIC_LINK  # public group link — pre-seeded, so the ExportChatInviteRequest fallback below never needs to run

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
    Telegram with a fresh permissions lookup every single time.
    🩹 FIX (per owner report — a group member who WAS already in FORCE_SUB_CHAT_ID still got
    the "Hold Up! Join Our Group First" prompt): the old code treated ANY exception from
    get_permissions() — a real "not a member" (UserNotParticipantError) but ALSO a FloodWait,
    a not-yet-resolvable entity, or any other transient hiccup — as is_member=False, and then
    CACHED that false negative for FORCE_SUB_MEMBERSHIP_TTL seconds. That's exactly what a
    burst of simultaneous /catch attempts (a spawn race with several people firing at once)
    triggers: real members get wrongly told to join, and stay wrongly blocked for the next two
    minutes because the bad result got cached. Now only a confirmed UserNotParticipantError
    counts as "not a member" (and gets cached as such); any other error means we genuinely
    couldn't verify, so it fails OPEN (falls back to the last cached answer if there is one,
    else assumes membership) instead of wrongly gating a real member, and does NOT cache the
    uncertain result — the next attempt gets a real, fresh check instead of being stuck."""
    now = time.time()
    cached = force_sub_membership_cache.get(user_id)
    if cached and now < cached[1]:
        return cached[0]
    try:
        try:
            perms = await bot1.get_permissions(FORCE_SUB_CHAT_ID, user_id)
        except ValueError as ve:
            # Cold session cache: Telethon has no access_hash for the channel yet. Resolve it
            # once by its public username (works for bots too), then retry.
            if "Could not find the input entity" not in str(ve):
                raise
            await bot1.get_entity(FORCE_SUB_USERNAME)
            perms = await bot1.get_permissions(FORCE_SUB_CHAT_ID, user_id)
        is_member = perms is not None
    except errors.UserNotParticipantError:
        is_member = False
    except Exception as e:
        print(f"⚠️ is_force_sub_member: couldn't verify {user_id}, failing open ({e})")
        return cached[0] if cached else True
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
        f"🐉🦋 <b>{f('Hold Up!')}</b> {f('Join Our Group First')} 🦄\n"
        f"You'll need to be a member of our group to use this command.\n"
        f"Tap below to join, then send the command again."
    )
    buttons = [[Button.url("Join Group", link)]] if link else None
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


# ---- JOIN REWARD — REMOVED. This used to grant a currency reward and one random
# character card to anyone joining FORCE_SUB_CHAT_ID (via a ChatAction watcher on new joins,
# plus a startup backfill for existing members). That grant path is gone — nobody gets paid
# for joining anymore, and the currency system itself has been removed, so the related
# constant/flag this comment used to justify keeping are gone too. ----

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
# 🎁 WELCOME GIFT — 3 random Divine cards for every NEW member of the force-sub group (per owner request)
# ==========================================
# Who: anybody who JOINS WELCOME_GIFT_CHAT_ID (= the BODgram_SF force-sub group). Members who were
#      already in the group before this feature are not offered anything.
# How: the AUTO-NAME bot (bot2 — falls back to bot1 if no secondary bot is configured) posts, IN THE
#      GROUP CHAT, a welcome message with ✅ Accept / ❌ Decline buttons. Only the person it is addressed to
#      can press them. Accept → WELCOME_GIFT_COUNT random DIVINE cards (distinct) go into their harem and the
#      message becomes:
#          Welcome to Our Group Chat..
#          {mention} U got 3 Divine ⚜️.
#          <char id> <char id> <char id>
#      Decline → nothing is given (the gift is NOT used up, so they'd be offered it again if they ever re-join).
# Once ever: a marker document in `welcome_gifts` (_id = user id) is inserted BEFORE the cards are paid out;
#      the unique _id makes it impossible to claim twice, even with simultaneous taps or a leave/re-join. If
#      paying out fails, the marker is removed again so the person can simply tap Accept once more.
# Bound: the cards arrive "bound" (can't be sold on the market or re-gifted) when WELCOME_GIFT_BOUND is True —
#      3 free Divine cards are worth ~1,500+ g, and without this a throw-away account could join, collect and
#      pass them on. Set it to False if welcome cards should be freely tradable.
# Needs: the bot must be in the group and actually SEE the join (join/leave service messages must not be hidden,
#      or the bot has to be an admin).
from pymongo.errors import DuplicateKeyError
WELCOME_GIFT_CHAT_ID = FORCE_SUB_CHAT_ID
WELCOME_GIFT_COUNT = 3
WELCOME_GIFT_TIER = "DIVINE"
WELCOME_GIFT_BOUND = True
WELCOME_OFFER_DEDUP_SECONDS = 600
welcome_gifts_col = db["welcome_gifts"]
_welcome_recent = {}   # user id -> when the offer was last posted (a join can arrive as two events)

def pick_welcome_cards(roster, count=WELCOME_GIFT_COUNT, tier=WELCOME_GIFT_TIER):
    """Pure. `count` DIFFERENT random cards of `tier` (fewer if the roster has fewer, [] if none)."""
    pool = [c for c in (roster or []) if c.get("char_id") and _doc_tier(c) == tier]
    return random.sample(pool, min(count, len(pool)))

def _welcome_mention(user_id, name):
    return f'<a href="tg://user?id={user_id}">{escape_html(name or "New member")}</a>'

def welcome_result_text(mention, cards):
    ids = "  ".join(f"<code>{display_char_id(c['char_id'])}</code>" for c in cards)
    return (f"🎉 <b>Welcome to Our Group Chat..</b>\n"
            f"{mention} U got <b>{len(cards)} Divine</b> {RARITY_EMOJI.get('DIVINE', '')}.\n"
            f"{ids}")

def _welcome_buttons(user_id):
    return [[Button.inline("✅ Accept", data=f"wgift_accept_{user_id}"),
             Button.inline("❌ Decline", data=f"wgift_decline_{user_id}")]]

async def grant_welcome_gift(user_id, name):
    """-> ("ok", cards) | ("already", []) | ("none", []) | ("banned", [])"""
    banned, _rec = is_gbanned(user_id)
    if banned:
        return "banned", []
    cards = pick_welcome_cards(await get_all_characters_cached())
    if not cards:
        return "none", []
    try:   # the claim marker FIRST: the unique _id is what makes "once ever" airtight
        await welcome_gifts_col.insert_one({"_id": user_id, "ts": time.time(), "chars": [c["char_id"] for c in cards]})
    except DuplicateKeyError:
        return "already", []
    try:
        await ensure_user_registered(user_id, name or str(user_id))
        now = time.time()
        entries = []
        for c in cards:
            e = {"char_id": c["char_id"], "caught_date": now, "rarity": c.get("rarity"), "status": "vault"}
            if WELCOME_GIFT_BOUND:
                e["bound"] = True
                e["gifted_by"] = "welcome"
            entries.append(e)
        await users_catcher_col.update_one(
            {"user_id": user_id},
            {"$push": {"harem": {"$each": entries}}, "$inc": {"total_caught": len(entries), "total_gift_received": len(entries)}})
    except Exception:
        try:
            await welcome_gifts_col.delete_one({"_id": user_id})   # not paid out — let them tap Accept again
        except Exception as e2:
            await report_system_error("welcome gift marker rollback", f"user {user_id}: {e2}")
        raise
    return "ok", cards

async def welcome_join_handler(event):
    """A member joined WELCOME_GIFT_CHAT_ID → offer the gift (Accept / Decline) right there in the group."""
    if not (event.user_joined or event.user_added):
        return
    uids = list(getattr(event, "user_ids", None) or ([event.user_id] if event.user_id else []))
    users = {}
    try:
        for u in (await event.get_users() or []):
            users[u.id] = u
    except Exception:
        pass
    for uid in uids:
        if not uid or uid in bot_ids:
            continue
        u = users.get(uid)
        if u is None:
            try:   # the join event didn't carry the user object — look it up (may fail for a brand-new account)
                u = await event.client.get_entity(uid)
            except Exception:
                u = None
        if u is not None and getattr(u, "bot", False):
            continue
        if is_gbanned(uid)[0]:
            continue
        now = time.time()
        if now - _welcome_recent.get(uid, 0) < WELCOME_OFFER_DEDUP_SECONDS:
            continue
        if await welcome_gifts_col.find_one({"_id": uid}):
            continue   # already got it once — never again
        _welcome_recent[uid] = now
        if len(_welcome_recent) > 5000:
            for k in [k for k, t in _welcome_recent.items() if now - t > WELCOME_OFFER_DEDUP_SECONDS]:
                _welcome_recent.pop(k, None)
        name = " ".join(x for x in (getattr(u, "first_name", None), getattr(u, "last_name", None)) if x) or "New member"
        try:
            await event.client.send_message(
                event.chat_id,
                f"👋 <b>Welcome to Our Group Chat..</b>\n"
                f"{_welcome_mention(uid, name)}, 🎁 <b>{WELCOME_GIFT_COUNT} random Divine</b> {RARITY_EMOJI.get('DIVINE', '')} cards are waiting for you!\n"
                f"<i>Accept ကိုနှိပ်ပြီး ယူလိုက်ပါ — တစ်ကြိမ်သာ ရပါမယ်။</i>",
                parse_mode='html', buttons=_welcome_buttons(uid))
        except Exception as e:
            _welcome_recent.pop(uid, None)
            print(f"⚠️ welcome offer failed for {uid}: {type(e).__name__}: {e}")

async def welcome_callback_handler(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode("utf-8")
    uid = int(event.pattern_match.group(2))
    if event.sender_id != uid:
        return await event.answer("ဒီ gift က သင့်အတွက် မဟုတ်ပါ။", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)
    try:
        sender = await event.get_sender()
        name = " ".join(x for x in (getattr(sender, "first_name", None), getattr(sender, "last_name", None)) if x) or "New member"
    except Exception:
        name = "New member"
    mention = _welcome_mention(uid, name)
    if action == "decline":
        await event.edit(f"❎ {mention} declined the welcome gift.", parse_mode='html', buttons=None)
        return await event.answer("OK", alert=False)
    try:
        status, cards = await grant_welcome_gift(uid, name)
    except Exception as e:
        await report_system_error("welcome_callback_handler", f"{e}\nuser {uid}")
        return await event.answer("Hmm, something didn't work — tap Accept again.", alert=True)
    if status == "ok":
        await event.edit(welcome_result_text(mention, cards), parse_mode='html', buttons=None)
        return await event.answer("🎁 Enjoy!", alert=False)
    if status == "already":
        await event.edit(f"ℹ️ {mention} already received the welcome gift.", parse_mode='html', buttons=None)
        return await event.answer("You already got it.", alert=True)
    if status == "banned":
        return await event.answer("⛔ Not available.", alert=True)
    await event.answer("Divine cards မရှိသေးလို့ ပေးလို့မရသေးပါ — နောက်မှ ပြန်ကြိုးစားပါ။", alert=True)

# registered on the auto-name bot (bot2); bot1 only if there is no secondary bot — never both, so no double offers
_welcome_client = bot2 if bot2 is not None else bot1
_welcome_client.add_event_handler(welcome_join_handler, events.ChatAction(chats=WELCOME_GIFT_CHAT_ID))
_welcome_client.add_event_handler(welcome_callback_handler, events.CallbackQuery(pattern=r'^wgift_(accept|decline)_(\d+)$'))


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
                referral_note = "\n\n🎉 Your friend's linked now — that's one more for your referral count~ 🎁"
    bot_me = await bot1.get_me()
    welcome_msg = (
        f"Hey {mention} 👋\n\n"
        f"I'm Morgan — characters spawn in your group and it's a race to catch, figure out "
        f"who they are, and add them to your collection before anyone else does~\n\n"
        f"🎴 <b>Catch &amp; Collect</b> — characters drop in-chat, build your vault, climb the leaderboard.\n"
        f"🛡️ <b>Group Tools</b> — moderation built right in, so you don't need a second bot for that.\n\n"
        f"Oh, and you'll need to join our group before most of this works, okay?\n\n"
        f"Buttons below if you want to look around~"
        f"{referral_note}"
    )
    buttons = [
        [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
        [Button.url("🪐 Add Me To Your Group", f"https://t.me/{bot_me.username}?startgroup=true")],
        [Button.url("👥 Join Our Circle", "https://t.me/Comeback_BoD")]
    ]
    await event.respond(welcome_msg, parse_mode='html', buttons=buttons)

def get_help_text():
    return (
        f"⚙️ Here's what I can do~\n\n"
        f" <code>/info</code> [reply or @username] — peek at someone's profile card\n"
        f" <code>/weather</code> — live weather for Myanmar &amp; Thailand\n\n"
        f"📖 <i>Want the full list? Check <code>/introduce</code>~</i>"
    )



def get_collection_text():
    return (
        f"🎒 Your Collection~\n\n"
        f"🎒 <code>/harem</code>\nYour vault — everyone you've caught, all in one place.\n\n"
        f"⭐ <code>/fav [ID]</code>\nPin a favorite up top~\n\n"
        f"📊 <code>/profile</code>\nYour stats and collection at a glance.\n\n"
        f"🏆 <code>/top</code> / <code>/gtop</code>\nLocal and global leaderboards — see where you stand.\n\n"
        f"🔎 <code>/check [ID]</code>\nLook up a character and see who's got the most of them.\n\n"
        f"🖼 <code>/show</code>\nBrowse every character by rarity, full quality — ⬅️ Prev / ➡️ Next. DM only.\n\n"
        f"🔗 <code>/referral</code>\nYour invite link — bring friends, get credit for it~"
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'(?i)^[/.]help(?:@\w+)?$', 'bot1')))
async def help_command_handler(event):
    await event.reply(get_help_text(), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])


@bot1.on(events.CallbackQuery())
async def system_callback_router(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    if data == "nav_back_home":
        bot_me = await bot1.get_me()
        welcome_msg = (
            f"Still me~ Characters spawn in your groups for you to catch and collect — "
            f"that's the whole game."
        )
        buttons = [
            [Button.inline("⚙️ Commands", data="nav_help_main"), Button.inline("🎒 Collection", data="nav_collection_main")],
            [Button.url("Add Me To Your Group", f"https://t.me/{bot_me.username}?startgroup=true")],
            [Button.url("Join Our Circle", "https://t.me/Comeback_BoD")]
        ]
        return await event.edit(welcome_msg, parse_mode='html', buttons=buttons)
    elif data == "nav_help_main":
        return await event.edit(get_help_text(), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
    elif data == "nav_collection_main":
        return await event.edit(get_collection_text(), parse_mode='html', buttons=[[Button.inline("🔙 Back", data="nav_back_home")]])
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

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]today(?:@\w+)?$', 'bot1')))
async def today_command(event):
    text = await render_today_leaderboard()
    if text is None:
        return await event.reply("📭 <b>No catches today yet.</b>", parse_mode='html')
    await event.reply(text, parse_mode='html')

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
                # 📋 Keep active_groups (groups_col) — what /send reads to know which chats to
                # broadcast to — in sync with reality. 🩹 BUG FIX: nothing in this file was ever
                # writing to groups_col, so any group added after however it was last (manually)
                # populated just silently never existed for /send to try — no error, no mute,
                # it simply never attempted that chat_id at all. Done unconditionally, before
                # the notification dedup below, so a rapid remove+re-add never leaves this out.
                # 🛡️ chat.id < 0 is a sanity check, not expected to ever actually trip here (a
                # live ChatAction's chat.id is always correctly Telethon-marked) — added after
                # /syncgroups was found inserting malformed positive IDs via a different, less
                # reliable path (bot1.iter_dialogs()); this just keeps the same invariant
                # enforced everywhere something can write to groups_col.
                if isinstance(chat.id, int) and chat.id < 0:
                    try:
                        await groups_col.update_one(
                            {"chat_id": chat.id},
                            {"$set": {"chat_id": chat.id, "title": chat.title or "Unknown"}},
                            upsert=True
                        )
                    except Exception as e:
                        print(f"groups_col upsert error (chat {chat.id}): {e}")

                now_ts = time.time()
                last_ts = _recent_bot_added_chats.get(chat.id)
                if last_ts and (now_ts - last_ts) <= BOT_ADDED_DEDUP_WINDOW:
                    return
                _recent_bot_added_chats[chat.id] = now_ts
                
                # ✅ Member count
                member_count = "Unknown"
                try:
                    participants = await bot1.get_participants(chat.id, limit=0)
                    if hasattr(participants, 'total'):
                        member_count = f"{participants.total:,}"
                    elif isinstance(participants, list):
                        member_count = f"{len(participants):,}"
                except Exception as e:
                    print(f"Member count error: {e}")
                    try:
                        full_chat = await bot1.get_full_chat(chat.id)
                        if hasattr(full_chat, 'participants_count'):
                            member_count = f"{full_chat.participants_count:,}"
                    except Exception as e2:
                        print(f"Member count error (fallback): {e2}")
                        member_count = "N/A"
                
                # ✅ Invite link
                group_link = None
                try:
                    invite = await bot1(ExportChatInviteRequest(chat.id))
                    group_link = invite.link if invite else None
                except Exception:
                    group_link = "Cannot fetch (need admin rights)"
                if not group_link:
                    group_link = "Not available (or bot not admin)"
                
                # ✅ Owner ကို ပို့မယ့် Message
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
                return

        # ---------- BOT REMOVED FROM GROUP (kicked/banned/left) ----------
        # Mirrors the registration above — drop the chat from active_groups so /send stops
        # retrying (and failing on) a chat this bot isn't even in anymore.
        if (event.user_kicked or event.user_left) and any(uid == bot_me.id for uid in target_ids if uid):
            try:
                await groups_col.delete_one({"chat_id": chat.id})
            except Exception as e:
                print(f"groups_col delete error (chat {chat.id}): {e}")
            return
        
        # ---------- WELCOME & GOODBYE ကို လုံးဝ ဖယ်ရှားမယ် ----------
        # အောက်က ကျန်တဲ့ welcome/goodbye code တွေအကုန်ကို ဖယ်ရှားလိုက်မယ်
        # ဘယ်သူမှ join/leave လုပ်ရင် ဘာမှ မပို့တော့ဘူး
        return
        
    except Exception as e:
        await report_system_error("Welcome Goodbye Event", e)
# ==========================================
# SPAM FILTERS — rewritten (per owner report: people spam short / long messages and dodge the 8-minute mute)
# ==========================================
# Why the old filter was easy to dodge (all of these were real holes):
#   1. One fixed window: 13 messages in 60 s. Pace yourself at 12 a minute, forever, and you never trip it.
#   2. Every message counted the same: "a", "." or a 2,000-character wall of text = 1; a repeated message = 1.
#   3. Counted per (user, group), so 4 messages in each of 3 groups never added up.
#   4. A muted user's messages were simply ignored — no extension, no consequence — and the spawn counter
#      (global_message_counter_handler) still counted every one of them, so spam still paid off.
#   5. Same 8 minutes every time, however often you came back.
# What happens now:
#   • Each message gets a WEIGHT: junk counts DOUBLE — a very short message (≤ SPAM_SHORT_TEXT_MAX_CHARS
#     characters), a very long one (≥ SPAM_LONG_TEXT_MIN_CHARS), the same text as the user's previous message
#     within a minute, or a repeated pattern ("aaaa", "hahaha"). Stickers/media/normal text count 1.
#   • Two windows, summed over ALL groups together: a BURST (SPAM_MSG_THRESHOLD in SPAM_MSG_WINDOW_SECONDS)
#     and a SUSTAINED one (SPAM_SUSTAINED_THRESHOLD in SPAM_SUSTAINED_WINDOW_SECONDS) — the second one is
#     what catches the "just under the limit, all day" pacing.
#   • Repeat offenders: every trip inside SPAM_STRIKE_WINDOW_SECONDS doubles the mute
#     (8 → 16 → 32 → 60 min, capped at SPAM_MUTE_MAX_SECONDS).
#   • Spamming WHILE muted (SPAM_MUTED_FLOOD_THRESHOLD weighted messages in a minute) counts as another strike and
#     extends the mute. A muted user's /fuck /catch messages are deleted.
#   • The mute still blocks /fuck, /catch and /obtain in every group (the catch handler checks user_mute_until).
#   • Spam no longer feeds the SPAWN COUNTER either — see spawn_message_counts below.
SPAM_MSG_WINDOW_SECONDS = 60
SPAM_MSG_THRESHOLD = 13               # weighted messages in the burst window
SPAM_SUSTAINED_WINDOW_SECONDS = 300
SPAM_SUSTAINED_THRESHOLD = 50         # weighted messages in the sustained window (≈ 10 a minute held for 5 min)
SPAM_CATCH_MUTE_SECONDS = 480         # 8 minutes — the length of EVERY spam mute while SPAM_ESCALATE_MUTE is False
SPAM_MUTE_MAX_SECONDS = 3600          # only used when SPAM_ESCALATE_MUTE is True
SPAM_STRIKE_WINDOW_SECONDS = 3600     # only matters when SPAM_ESCALATE_MUTE is True
SPAM_MUTED_FLOOD_THRESHOLD = 8        # weighted messages in the burst window while ALREADY muted → extend (only if SPAM_EXTEND_WHILE_MUTED)
# 🩹 FIX (players were leaving bad reviews — "muted for 8 min, then it keeps growing"). Two things made a
# mute snowball past its 8 minutes, and both are now OFF by default (flip to True to get the old behaviour back):
#   • SPAM_ESCALATE_MUTE — each repeat offence inside an hour doubled the mute (8→16→32→60 min), and because
#     every strike refreshed the 1-hour window, anyone who kept getting caught never reset.
#   • SPAM_EXTEND_WHILE_MUTED — chatting fast while already muted counted as a NEW strike and pushed the end
#     time out again (8 → 21 → 52 → 110 min …). Also, messages sent during a mute used to keep filling the spam
#     history, so the moment the mute ended the very first message re-tripped the threshold and muted them again.
# With both off a mute is always exactly SPAM_CATCH_MUTE_SECONDS, nothing sent while muted is scored, and the
# user starts with a clean slate when it ends. Persistent offenders are the owner's call — use /gban.
SPAM_ESCALATE_MUTE = False
SPAM_EXTEND_WHILE_MUTED = False
SPAM_SHORT_TEXT_MAX_CHARS = 2
SPAM_LONG_TEXT_MIN_CHARS = 350
SPAM_JUNK_WEIGHT = 2
SPAM_MUTED_DELETE_COMMANDS = ('/fuck', '/catch', '/morgan', '/obtain')
SPAM_HISTORY_MAX = 400                # entries kept per user (a weight-2 message is 2 entries)
user_spam_strikes = {}                # user_id -> [strike count, last strike ts]
_spam_last_text = {}                  # user_id -> (normalized text, ts) — across all groups
_spam_last_prune = 0.0

def normalize_spam_text(text):
    """Pure. Lower-case with ALL whitespace removed ('Ha  Ha' == 'haha')."""
    return "".join((text or "").lower().split())

def is_repeated_pattern(norm):
    """Pure. 'aaaaa', '.....', 'hahaha', 'ababab' — a 1-4 character unit repeated 3+ times."""
    for unit in range(1, 5):
        if len(norm) >= 3 * unit and norm == (norm[:unit] * (len(norm) // unit + 1))[:len(norm)]:
            return True
    return False

def spam_message_weight(text, has_media, prev_norm, prev_ts, now):
    """Pure. 1 for a normal message / sticker / media, SPAM_JUNK_WEIGHT for short, very long, duplicate or
    repeated-pattern text."""
    norm = normalize_spam_text(text)
    if not norm:
        return 1
    if len(norm) <= SPAM_SHORT_TEXT_MAX_CHARS or len(norm) >= SPAM_LONG_TEXT_MIN_CHARS:
        return SPAM_JUNK_WEIGHT
    if prev_norm is not None and norm == prev_norm and now - prev_ts < SPAM_MSG_WINDOW_SECONDS:
        return SPAM_JUNK_WEIGHT
    if is_repeated_pattern(norm):
        return SPAM_JUNK_WEIGHT
    return 1

def spam_record(user_id, now, weight):
    """Adds this message (weight entries) to the user's history — shared by ALL groups — and returns
    (burst score, sustained score). The history stays a plain list of timestamps."""
    key = (user_id, "*")
    hist = [t for t in user_spam_data.get(key, []) if now - t < SPAM_SUSTAINED_WINDOW_SECONDS]
    hist.extend([now] * weight)
    hist = hist[-SPAM_HISTORY_MAX:]
    user_spam_data[key] = hist
    burst = sum(1 for t in hist if now - t < SPAM_MSG_WINDOW_SECONDS)
    return burst, len(hist)

def spam_next_mute(user_id, now):
    """Records a strike and returns (mute seconds, strike number): 8 min, then doubling per strike within
    SPAM_STRIKE_WINDOW_SECONDS, capped at SPAM_MUTE_MAX_SECONDS."""
    rec = user_spam_strikes.get(user_id)
    strikes = rec[0] + 1 if rec and now - rec[1] <= SPAM_STRIKE_WINDOW_SECONDS else 1
    user_spam_strikes[user_id] = [strikes, now]
    if not SPAM_ESCALATE_MUTE:
        return SPAM_CATCH_MUTE_SECONDS, strikes  # flat 8 minutes every time — no doubling
    return min(SPAM_MUTE_MAX_SECONDS, SPAM_CATCH_MUTE_SECONDS * (2 ** (strikes - 1))), strikes

def _spam_prune(now):
    global _spam_last_prune
    if now - _spam_last_prune < 600:
        return
    _spam_last_prune = now
    for k in [k for k, v in user_spam_data.items() if isinstance(k, tuple) and k[1] == "*" and (not v or now - v[-1] > SPAM_SUSTAINED_WINDOW_SECONDS)]:
        user_spam_data.pop(k, None)
    for k in [k for k, (n, ts) in _spam_last_text.items() if now - ts > SPAM_MSG_WINDOW_SECONDS]:
        _spam_last_text.pop(k, None)
    for k in [k for k, (c, ts) in user_spam_strikes.items() if now - ts > SPAM_STRIKE_WINDOW_SECONDS]:
        user_spam_strikes.pop(k, None)

@bot1.on(events.NewMessage)
async def spam_detection_and_mute(event):
    if event.is_private:
        return
    if event.sender_id in bot_ids or event.sender_id == OWNER_ID:
        return
    # Counts toward the spam score: text OR sticker OR any other media (photo, video, gif, voice, document…).
    if not event.text and not event.media:
        return
    user_id = event.sender_id
    now = time.time()
    _spam_prune(now)
    # Already muted and extensions are off: just keep the catch commands blocked. Messages sent during
    # the mute are NOT scored, so the mute ends on time and the user starts clean afterwards.
    if not SPAM_EXTEND_WHILE_MUTED and user_id in user_mute_until and now < user_mute_until[user_id]:
        if _extract_command_word(event.text) in SPAM_MUTED_DELETE_COMMANDS:
            try:
                await event.delete()
            except Exception:
                pass
        return
    text = event.raw_text or ""
    prev = _spam_last_text.get(user_id)
    weight = spam_message_weight(text, bool(event.media), prev[0] if prev else None, prev[1] if prev else 0, now)
    norm = normalize_spam_text(text)
    if norm:
        _spam_last_text[user_id] = (norm, now)
    burst, sustained = spam_record(user_id, now, weight)

    # Already muted (GLOBALLY): block the catch commands, and treat continued flooding as a further offence.
    if user_id in user_mute_until and now < user_mute_until[user_id]:
        if _extract_command_word(event.text) in SPAM_MUTED_DELETE_COMMANDS:
            try:
                await event.delete()
            except Exception:
                pass
        if burst >= SPAM_MUTED_FLOOD_THRESHOLD:
            seconds, strikes = spam_next_mute(user_id, now)
            user_mute_until[user_id] = max(user_mute_until[user_id], now + seconds)
            user_spam_data[(user_id, "*")] = []
            try:
                sender = await event.get_sender()
                mention = f"<a href='tg://user?id={user_id}'>{escape_html(sender.first_name)}</a>"
                await event.respond(
                    bq(f"<b>Notice:</b> {mention}, still spamming while muted — your /fuck block now lasts "
                       f"{int(user_mute_until[user_id] - now) // 60} more minutes (strike {strikes})."),
                    parse_mode='html')
            except Exception:
                pass
        return

    # Too many weighted messages — in the last minute OR sustained over the last 5 minutes, in all groups together.
    if burst >= SPAM_MSG_THRESHOLD or sustained >= SPAM_SUSTAINED_THRESHOLD:
        mute_seconds, strikes = spam_next_mute(user_id, now)
        user_mute_until[user_id] = now + mute_seconds
        user_spam_data[(user_id, "*")] = []  # start clean once the mute expires
        mute_minutes = mute_seconds // 60
        try:
            sender = await event.get_sender()
            mention = f"<a href='tg://user?id={user_id}'>{escape_html(sender.first_name)}</a>"
            repeat = f" (strike {strikes} — it doubles each time you do it again within an hour)" if (SPAM_ESCALATE_MUTE and strikes > 1) else ""
            await event.respond(
                bq(f"<b>Notice:</b> {mention}, slow down a little — "
                   f"/fuck is paused for you <b>in every group</b> for {mute_minutes} minutes{repeat}. "
                   f"It unlocks by itself when the time is up."),
                parse_mode='html')
        except Exception:
            pass
        try:
            await event.delete()   # the message that tripped the threshold
        except Exception:
            pass
        return

# ==========================================
# 🎲 SPAWN-COUNTER HYGIENE — spam must not pay (called by global_message_counter_handler)
# ==========================================
# The spawn counter used to count EVERY group message — one-letter messages, wall-of-text, repeats, even
# messages from users who were spam-muted — so spamming was the fastest way to force spawns, and staying under
# the mute threshold cost nothing. Now a message only advances the counter when it is a real contribution:
#   • the sender is not spam-muted;
#   • text has at least SPAWN_COUNT_MIN_CHARS visible characters, isn't a repeated pattern, and isn't the same text
#     the same user already got counted for in this chat within the last minute;
#   • the sender hasn't already moved the counter SPAWN_COUNT_USER_MAX_PER_MINUTE times in the last minute
#     in this chat (stickers/media are subject to this cap too).
# Normal conversation is unaffected; a spammer's extra messages simply stop counting.
SPAWN_COUNT_MIN_CHARS = 3
SPAWN_COUNT_USER_MAX_PER_MINUTE = 6
_spawn_count_user_times = {}   # (chat_id, user_id) -> [timestamps of counted messages]
_spawn_count_last_text = {}    # (chat_id, user_id) -> (normalized text, ts)

def spawn_message_counts(chat_id, user_id, text, now, muted=False):
    """True if this group message may advance the chat's spawn counter."""
    if muted:
        return False
    key = (chat_id, user_id)
    norm = normalize_spam_text(text)
    if norm:
        if len(norm) < SPAWN_COUNT_MIN_CHARS or is_repeated_pattern(norm):
            return False
        last = _spawn_count_last_text.get(key)
        if last and last[0] == norm and now - last[1] < SPAM_MSG_WINDOW_SECONDS:
            return False
    times = [t for t in _spawn_count_user_times.get(key, []) if now - t < SPAM_MSG_WINDOW_SECONDS]
    if len(times) >= SPAWN_COUNT_USER_MAX_PER_MINUTE:
        _spawn_count_user_times[key] = times
        return False
    times.append(now)
    _spawn_count_user_times[key] = times
    if norm:
        _spawn_count_last_text[key] = (norm, now)
    if len(_spawn_count_user_times) > 20000:
        for k in [k for k, v in _spawn_count_user_times.items() if not v or now - v[-1] > 120]:
            _spawn_count_user_times.pop(k, None)
            _spawn_count_last_text.pop(k, None)
    return True

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
    if not can_addchar(event.sender_id): return  # OWNER_ID or someone the owner added with /adduploader
    if is_duplicate_event(event): return
    input_text = event.pattern_match.group(1)
    if not input_text or '|' not in input_text:
        await event.reply(
            f"⚠️ <b>{f('Invalid format!')}</b>\n"
            f"📌 <b>{f('Usage')}:</b>\n"
            f"<code>/addchar Name | Category | Rarity_Number | Event | CatchLimit | ID</code>\n"
            f"<i>(Reply to a media file. Event, CatchLimit and ID are optional.)</i>\n\n"
            f"🔢 <b>{f('Rarity Tiers (1-4)')}:</b>\n"
            + "\n".join(
                f"<code>{num}</code> = {RARITY_NUM_MAP[num]['name']}"
                for num in sorted(RARITY_NUM_MAP.keys())
            ) + "\n\n"
            f"🎪 <b>Event:</b> free text, e.g. <code>Summer Festival</code> (leave blank/'-' for none)\n"
            f"🔁 <b>CatchLimit:</b> how many times total this character may be caught (0 or blank = infinite)\n"
            f"🆔 <b>ID:</b> pick the character's ID yourself, e.g. <code>1234</code> (letters/numbers only). "
            f"Leave blank or '-' for the next automatic ID. To set an ID without an event/limit: "
            f"<code>/addchar Name | Category | 1 | - | 0 | 1234</code>",
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
    # 🆔 Optional 6th part = manually chosen character ID. Same normalisation the lookup commands
    # use ("1234" -> "BOD1234", any case) so players keep seeing just the bare number.
    custom_id = None
    if len(parts) > 5 and parts[5].strip() and parts[5].strip() != "-":
        custom_id = normalize_char_id_input(parts[5])
        if not re.fullmatch(r'[A-Z0-9]{1,20}', custom_id):
            return await event.reply(
                f"❌ <b>Invalid ID.</b> Use letters/numbers only (max 20), e.g. <code>1234</code>.",
                parse_mode='html'
            )
        if await characters_base_col.find_one({"char_id": custom_id}, {"_id": 1}):
            return await event.reply(
                f"❌ ID <code>{escape_html(custom_id)}</code> is already used by another character. Pick a different one.",
                parse_mode='html'
            )
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
        if custom_id:
            # Re-check now (the upload above can take minutes) — must happen BEFORE
            # prewarm_media_identity_cache below ties this media to the ID.
            if await characters_base_col.find_one({"char_id": custom_id}, {"_id": 1}):
                raise RuntimeError(f"ID {custom_id} was taken by another character while uploading — pick a different ID")
            char_id = custom_id
        else:
            char_id = await _generate_new_char_id()
        prewarm_media_identity_cache(forwarded_msg, char_id)
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
            "spawn_limit": effective_spawn_limit(spawn_limit, classify_rarity(r_info["name"])),
            "photo_phash": photo_phash,
            "created_at": time.time(),  # 🔒 starts the NEW_CARD_PROTECTION_SECONDS window — see execute_star_shop_purchase()
            "added_by": event.sender_id  # owner or /adduploader user who ran /addchar
        }
        try:
            await characters_base_col.insert_one(character_data)
        except DuplicateKeyError:
            if custom_id:
                raise RuntimeError(f"ID {custom_id} is already used by another character")
            raise
        await invalidate_character_caches()
        spawn_limit = character_data["spawn_limit"]  # 🔒 may have been lowered to the limited-tier cap
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
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]workerping(?:@\w+)?$', 'bot1')))
async def worker_ping_command(event):
    """Owner-only: Check if all loaded worker clients are still alive/connected."""
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM for better visibility.", parse_mode='html')

    if not worker_pool_clients:
        return await event.reply("❌ No workers loaded. Run <code>/xbotloadworkers</code> first.", parse_mode='html')

    status_msg = await event.reply(f"⏳ Pinging {len(worker_pool_clients)} workers...", parse_mode='html')
    
    results = []
    alive = 0
    dead = 0

    for i, (client, label) in enumerate(worker_pool_clients):
        try:
            # Check if the client is physically connected
            if not client.is_connected():
                await client.connect()
            
            # Try to get the current user (this verifies the session is still valid)
            me = await client.get_me()
            username = f"@{me.username}" if me.username else f"ID {me.id}"
            results.append(f"✅ Worker {i+1} ({label}) is <b>ALIVE</b> ({username})")
            alive += 1
        except Exception as e:
            results.append(f"❌ Worker {i+1} ({label}) is <b>DEAD</b> / Disconnected (<code>{escape_html(str(e)[:50])}</code>)")
            dead += 1

    # Summary
    summary = f"📊 <b>Worker Pool Status</b>\n"
    summary += f"🟢 Alive: <code>{alive}</code>\n"
    summary += f"🔴 Dead/Error: <code>{dead}</code>\n"
    summary += f"━━━━━━━━━━━━━━━━\n"
    summary += "\n".join(results)

    await status_msg.edit(summary, parse_mode='html')
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
        update_fields["spawn_limit"] = effective_spawn_limit(max(0, int(new_limit_raw)), _doc_tier(char_doc))  # 🔒 Supreme/Cataphract can't be infinite
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
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addspecial(?:@\w+)?$', 'bot1')))
async def addspecial_toggle_command(event):
    global _addspecial_armed
    if event.sender_id != OWNER_ID: return
    _addspecial_armed = not _addspecial_armed
    if _addspecial_armed:
        await event.reply(
            "🔫 <b>/addspecial armed.</b> Forward each CNFT card announcement (media + caption) "
            "to this DM now, one at a time — every one recognized gets added automatically with "
            "<code>spawnable: false</code> (manual distribution only, never a random spawn). "
            "Send /addspecial again when you're done.",
            parse_mode='html'
        )
    else:
        await event.reply("🛑 <b>/addspecial disarmed.</b> Forwards are back to being ignored.", parse_mode='html')

@bot1.on(events.NewMessage(func=lambda e: e.is_private and e.sender_id == OWNER_ID and _addspecial_armed))
async def addspecial_ingest_handler(event):
    if is_duplicate_event(event): return
    parsed = parse_cnft_forward(event.raw_text or "")
    if not parsed:
        return  # armed, but this particular DM doesn't look like a CNFT announcement — ignore silently
    if not (event.photo or event.video or event.document):
        return await event.reply("⚠️ Recognized a CNFT caption but no media is attached — skipped.", parse_mode='html')
    char_id = f"CNFT{parsed['group_id']}{parsed['tier_letters']}"
    if await characters_base_col.find_one({"char_id": char_id}):
        return await event.reply(f"⚠️ <code>{char_id}</code> already exists — skipped (forwarded twice?).", parse_mode='html')
    try:
        forwarded_msg = await send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=event.media)
        prewarm_media_identity_cache(forwarded_msg, char_id)
        photo_phash = await compute_phash_for_message(event)
        rarity_tier = parsed["rarity_tier"]
        character_data = {
            "char_id": char_id,
            "name": parsed["name"],
            "category": parsed["anime"],
            "rarity": f"{RARITY_EMOJI[rarity_tier]} {rarity_tier}",
            "rarity_tier": rarity_tier,
            "storage_msg_id": forwarded_msg.id,
            "currency_value": _RARITY_VALUE_MAP[rarity_tier],
            "spawn_count": 0,
            "event": "General",
            "spawn_limit": 0,
            "spawnable": False,  # 🔑 excluded from trigger_dynamic_spawn's eligible_characters — manual distribution only
            "photo_phash": photo_phash,
            "created_at": time.time()
        }
        await characters_base_col.insert_one(character_data)
        await invalidate_character_caches()
        channel_note = ""
        if CHARACTER_CHANNEL_ID:
            try:
                channel_msg = await post_character_to_channel(character_data, is_new=True)
                await characters_base_col.update_one(
                    {"char_id": char_id},
                    {"$set": {"channel_posted": True, "channel_msg_id": channel_msg.id if channel_msg else None}}
                )
                channel_note = "\n📢 Channel: Posted ✅"
            except Exception as ce:
                await report_system_error(f"AddSpecial channel post ({char_id})", ce)
                channel_note = f"\n⚠️ Channel post failed: <code>{escape_html(str(ce))}</code>"
        await event.reply(
            f"💠 <b>CNFT added</b> (spawnable: false)\n"
            f"🆔 <code>{char_id}</code>\n"
            f"👤 <code>{escape_html(parsed['name'])}</code>\n"
            f"🫧 <code>{escape_html(parsed['anime'])}</code>\n"
            f"🏷️ {RARITY_EMOJI[rarity_tier]} {rarity_tier}"
            f"{channel_note}",
            parse_mode='html'
        )
    except Exception as e:
        await event.reply(f"❌ Failed to add <code>{char_id}</code>: <code>{escape_html(str(e))}</code>", parse_mode='html')

# ==========================================
# 📊 GLOBAL STATS (cached)
# ==========================================
_stats_cache = {"data": None, "cached_at": 0}
STATS_CACHE_TTL = 300  # 5 minutes

async def get_global_stats():
    """Compute all global stats with caching."""
    now = time.time()
    if _stats_cache["data"] is not None and (now - _stats_cache["cached_at"]) < STATS_CACHE_TTL:
        return _stats_cache["data"]

    # 1. All characters
    all_chars = await get_all_characters_cached()
    total_chars = len(all_chars)

    # 2. Count characters per rarity tier (from character DB)
    char_counts = {}
    for c in all_chars:
        tier = c.get("rarity_tier") or classify_rarity(c.get("rarity", ""))
        if tier and tier in RARITY_TIERS:
            char_counts[tier] = char_counts.get(tier, 0) + 1
        else:
            char_counts["OTHER"] = char_counts.get("OTHER", 0) + 1

    # 3. Total players
    total_players = await users_catcher_col.count_documents({})

    # 4. Total catches sum
    total_catches_agg = await users_catcher_col.aggregate([
        {"$group": {"_id": None, "total": {"$sum": "$total_caught"}}}
    ]).to_list(length=1)
    total_catches = total_catches_agg[0]["total"] if total_catches_agg else 0

    # 5. Catches breakdown by rarity (from harem)
    # We unwind harem, group by rarity string, then classify in Python
    catch_rarity_raw = await users_catcher_col.aggregate([
        {"$unwind": "$harem"},
        {"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}
    ]).to_list(length=None)
    catch_counts = {}
    for item in catch_rarity_raw:
        tier = classify_rarity(item["_id"])
        if tier in RARITY_TIERS:
            catch_counts[tier] = catch_counts.get(tier, 0) + item["count"]
        else:
            catch_counts["OTHER"] = catch_counts.get("OTHER", 0) + item["count"]

    # 6. Unique characters discovered (at least one copy in any harem)
    discovered_ids = await users_catcher_col.distinct("harem.char_id")
    discovered = len(discovered_ids)

    stats = {
        "total_players": total_players,
        "total_chars": total_chars,
        "char_counts": char_counts,          # tier -> count
        "total_catches": total_catches,
        "catch_counts": catch_counts,        # tier -> count
        "discovered": discovered,
        "discovery_rate": (discovered / total_chars * 100) if total_chars else 0,
    }
    _stats_cache["data"] = stats
    _stats_cache["cached_at"] = now
    return stats

def _progress_bar(pct, length=10):
    filled = int(round(pct / 100 * length))
    return "█" * filled + "░" * (length - filled)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]stats(?:@\w+)?$', 'bot1')))
async def stats_command_handler(event):
    if event.sender_id != OWNER_ID and event.sender_id not in added_owner_ids:
        # Allow only owner and added owners to see stats (or make it public? The sample seems admin-only; but we can allow anyone)
        # We'll allow everyone to see, but you can restrict if needed.
        pass  # For now, everyone can use it.

    stats = await get_global_stats()

    # Build output
    lines = []
    lines.append("📊 <b>GLOBAL COLLECTION STATS</b>")
    lines.append("")  # blank line

    # Active Agents
    lines.append(f"👥 <b>Active Agents:</b> <code>{stats['total_players']:,}</code> Players")
    lines.append("")  # blank

    # Character Database
    lines.append(f"🗄️ <b>CHARACTER DATABASE</b> <i>(/addchar total: {stats['total_chars']})</i>")
    # Sort tiers by our order (RARITY_TIERS) and include only those with count > 0
    for tier in RARITY_TIERS:
        cnt = stats["char_counts"].get(tier, 0)
        if cnt == 0:
            continue
        pct = (cnt / stats['total_chars'] * 100) if stats['total_chars'] else 0
        emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
        display_name = RARITY_DISPLAY_NAME.get(tier, tier.title())
        bar = _progress_bar(pct)
        lines.append(f"{emoji} <b>{display_name}</b> — <code>{cnt}</code>")
        lines.append(f"{bar} <code>{pct:.1f}%</code>")
    # Also show OTHER if any
    if stats["char_counts"].get("OTHER", 0) > 0:
        cnt = stats["char_counts"]["OTHER"]
        pct = (cnt / stats['total_chars'] * 100) if stats['total_chars'] else 0
        lines.append(f"❓ <b>OTHER</b> — <code>{cnt}</code>")
        lines.append(f"{_progress_bar(pct)} <code>{pct:.1f}%</code>")
    lines.append("")  # blank

    # Total Catches
    lines.append(f"🃏 <b>TOTAL CATCHES</b> <i>(all players combined: {stats['total_catches']})</i>")
    for tier in RARITY_TIERS:
        cnt = stats["catch_counts"].get(tier, 0)
        if cnt == 0:
            continue
        pct = (cnt / stats['total_catches'] * 100) if stats['total_catches'] else 0
        emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
        display_name = RARITY_DISPLAY_NAME.get(tier, tier.title())
        bar = _progress_bar(pct)
        lines.append(f"{emoji} <b>{display_name}</b> — <code>{cnt}</code>")
        lines.append(f"{bar} <code>{pct:.1f}%</code>")
    if stats["catch_counts"].get("OTHER", 0) > 0:
        cnt = stats["catch_counts"]["OTHER"]
        pct = (cnt / stats['total_catches'] * 100) if stats['total_catches'] else 0
        lines.append(f"❓ <b>OTHER/UNKNOWN</b> — <code>{cnt}</code>")
        lines.append(f"{_progress_bar(pct)} <code>{pct:.1f}%</code>")
    lines.append("")  # blank

    # Discovery Rate
    lines.append(f"🔎 <b>DISCOVERY RATE</b> <i>(unique characters caught at least once)</i>")
    bar = _progress_bar(stats['discovery_rate'])
    lines.append(f"{bar} <code>{stats['discovery_rate']:.1f}%</code>")
    lines.append(f"<code>{stats['discovered']}/{stats['total_chars']}</code> characters discovered by players")

    # Send
    await event.reply("\n".join(lines), parse_mode='html')
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]send(?:@\w+)?(?:\s+(.*))?$', 'bot1')))
async def broadcast(event):
    if event.sender_id != OWNER_ID: return
    reply_msg = await event.get_reply_message()
    command_text = event.pattern_match.group(1)
    if not reply_msg and not command_text: return
    success, fail, purged = 0, 0, 0
    failed_groups = []  # [(chat_id, title, reason)] — 🩹 BUG FIX: the old code tracked `fail`
    # but never showed it (always printed "Failed: None"), and the FloodWait retry's success
    # branch was `success += 104` (a stray typo) instead of += 1. Neither actually explained
    # WHY a specific group failed — this is what makes a "not muted but still didn't get it"
    # group diagnosable instead of just a number.
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
                success += 1
            except Exception as e2:
                fail += 1
                failed_groups.append((chat_id, g.get('title'), str(e2)))
        except (ValueError, errors.ChannelPrivateError, errors.ChannelInvalidError) as e:
            # 🩹 SELF-HEALING: this specific family means Telethon has no way to reach chat_id
            # at all anymore — a plain ValueError ("Could not find the input entity for
            # PeerUser(...)") is what a corrupted/stale chat_id looks like (Telethon falls back
            # to guessing it's a bare user ID, since a valid group/channel ID is always
            # negative), and ChannelPrivate/Invalid mean the bot's been removed outright.
            # NOT caught here on purpose: ChatWriteForbiddenError (could just be a temporary
            # mute/restriction while still a member) — that one stays a plain failure below,
            # never auto-purged, since the group might still recover on its own.
            fail += 1
            purged += 1
            failed_groups.append((chat_id, g.get('title'), f"{str(e)} [entry removed from active_groups]"))
            try:
                await groups_col.delete_one({"chat_id": chat_id})
            except Exception:
                pass
        except Exception as e:
            fail += 1
            failed_groups.append((chat_id, g.get('title'), str(e)))

    result_text = (
        f"<b>BROADCAST COMPLETE</b>\n✅ <b>Success:</b> <code>{success}</code>\n"
        f"❌ <b>Failed:</b> <code>{fail}</code>"
    )
    if purged:
        result_text += f" <i>(🗑️ {purged} unreachable — auto-removed from active_groups)</i>"
    if failed_groups:
        shown = failed_groups[:10]
        lines = [
            f"• <code>{cid}</code> {escape_html(title or 'Unknown')} — {escape_html(reason)}"
            for cid, title, reason in shown
        ]
        result_text += "\n\n<b>Failed groups:</b>\n" + "\n".join(lines)
        if len(failed_groups) > len(shown):
            result_text += f"\n…and {len(failed_groups) - len(shown)} more."
    await status_msg.edit(bq(result_text), parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncgroups(?:@\w+)?$', 'bot1')))
async def sync_groups_cmd(event):
    """Owner-only: reconciles active_groups (groups_col — what /send reads) against chat_ids
    this bot has DEFINITELY seen real message activity in.

    🩹 CHANGED (was bot1.iter_dialogs()): dialog listing turned out to be unreliable on this
    bot account — it was producing malformed/positive "chat_ids" that Telethon then reads as a
    PeerUser (a private user), since a valid Telegram group/channel ID is always negative. Every
    /send to one of those failed with "Could not find the input entity for PeerUser(...)", and
    the sync itself would silently die partway through with no error shown (iter_dialogs can be
    slow/flaky for a bot session), which is why it looked "stuck" after the first message.

    groups_counters_col is populated purely from real incoming group messages (event.chat_id —
    always correctly typed by Telethon, since it comes straight off a live update, not a
    dialog-list guess) — see global_message_counter_handler near trigger_dynamic_spawn. That
    makes it a far more reliable "what groups is this bot actually in" source. The one gap this
    leaves: a group added so recently it hasn't had a single message yet — but that's already
    covered separately, immediately, by the ChatAction handler (welcome_goodbye) the moment the
    bot is added. This command is only the one-time catch-up for chats from before that existed.
    """
    if event.sender_id != OWNER_ID: return
    status = await event.reply("🔄 <b>Syncing active_groups from known chat activity...</b>", parse_mode='html')
    try:
        known_chat_ids = await groups_counters_col.distinct("chat_id")
        # Telegram group/channel IDs are always negative — anything else is exactly the kind of
        # corrupted entry that caused this whole mess, so it never even gets considered "known".
        known_chat_ids = [cid for cid in known_chat_ids if isinstance(cid, int) and cid < 0]

        if not known_chat_ids:
            return await status.edit(
                "⚠️ <b>groups_counters_col came back empty — that looks wrong</b> "
                "(hundreds of groups should have counter entries by now), so I didn't touch "
                "active_groups at all rather than risk wiping it on a bad read. Check the DB "
                "connection and try again.",
                parse_mode='html'
            )

        added, updated, skipped = 0, 0, 0
        for chat_id in known_chat_ids:
            try:
                title = "Unknown"
                try:
                    entity = await bot1.get_entity(chat_id)
                    title = getattr(entity, 'title', None) or "Unknown"
                except Exception:
                    pass  # keep "Unknown" — a title lookup failing shouldn't skip registration
                result = await groups_col.update_one(
                    {"chat_id": chat_id},
                    {"$set": {"chat_id": chat_id, "title": title}},
                    upsert=True
                )
                if result.upserted_id is not None:
                    added += 1
                elif result.modified_count:
                    updated += 1
            except Exception as e:
                skipped += 1
                print(f"sync_groups_cmd per-chat error ({chat_id}): {e}")

        # Anything in groups_col that isn't in the known-active set — including every
        # malformed positive-ID entry from the old iter_dialogs() bug — gets dropped here.
        # ($nin against a non-empty list of negatives naturally excludes those too.)
        removed = 0
        stale = await groups_col.count_documents({"chat_id": {"$nin": known_chat_ids}})
        if stale:
            await groups_col.delete_many({"chat_id": {"$nin": known_chat_ids}})
            removed = stale

        await status.edit(
            f"✅ <b>Group sync complete.</b>\n"
            f"➕ New: <code>{added}</code>\n"
            f"🔄 Updated: <code>{updated}</code>\n"
            f"🗑️ Removed (invalid/stale): <code>{removed}</code>\n"
            + (f"⚠️ Skipped (error): <code>{skipped}</code>\n" if skipped else "")
            + f"📊 Total tracked now: <code>{len(known_chat_ids)}</code>",
            parse_mode='html'
        )
    except Exception as e:
        # 🛡️ RELIABILITY: whatever else goes wrong, the status message ALWAYS gets a final
        # answer — this is exactly what silently "stopped" last time instead of reporting why.
        print(f"sync_groups_cmd error: {e}")
        try:
            await status.edit(f"❌ <b>Sync failed:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')
        except Exception:
            pass

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]joinpublic(?:@\w+)?\s+(\S+)$', 'bot1')))
async def join_public_channel(event):
    """Owner-only: joins a PUBLIC channel using its @username, without an invite link."""
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM for safety.", parse_mode='html')

    username = event.pattern_match.group(1).strip()
    if not username.startswith('@'):
        username = '@' + username

    status = await event.reply(f"⏳ Resolving <code>{username}</code> and joining with all workers...", parse_mode='html')

    # Resolve the entity (public channels can be resolved by anyone)
    try:
        entity = await bot1.get_entity(username)
    except Exception as e:
        return await status.edit(f"❌ Failed to resolve <code>{username}</code>: <code>{escape_html(str(e))}</code>", parse_mode='html')

    # Check if workers are loaded
    if not worker_pool_clients:
        return await status.edit("❌ No worker pool loaded. Run <code>/xbotloadworkers</code> first.", parse_mode='html')

    joined = 0
    total = len(worker_pool_clients)
    
    from telethon.tl.functions.channels import JoinChannelRequest
    from telethon.errors.rpcerrorlist import UserAlreadyParticipantError

    for i, (client, label) in enumerate(worker_pool_clients):
        try:
            await client(JoinChannelRequest(entity))
            joined += 1
            await asyncio.sleep(0.3)  # Pace to avoid flood
        except UserAlreadyParticipantError:
            joined += 1  # Already inside, count as success
        except Exception as e:
            print(f"⚠️ Join error for {label}: {e}")
            # Continue to the next worker
    
    await status.edit(
        f"✅ Done! Sent join requests to <code>{joined}/{total}</code> workers for <code>{username}</code>.\n"
        f"Now run <code>/xbotresync</code> or <code>/xbotimportall</code> again.",
        parse_mode='html'
    )

def _at_catch_limit(char):
    limit = char.get("spawn_limit", 0)
    return bool(limit and limit > 0 and char.get("spawn_count", 0) >= limit)

async def owner_spawn_specific(chat_id, arg):
    """The ONLY way SUPREME / CATAPHRACT cards ever spawn: /fspawn <char id> (any card) or /fspawn sup | cata
    (a random Supreme / Cataphract that still has catch-limit room). Posts it straight away — no rarity quiz.
    Returns (ok, text for the owner)."""
    roster = await get_all_characters_cached()
    key = (arg or "").strip().lower()
    tier_kw = {"sup": "SUPREME", "supreme": "SUPREME", "cata": "CATAPHRACT", "cataphract": "CATAPHRACT"}
    if key in tier_kw:
        tier = tier_kw[key]
        pool = [c for c in roster if c.get("spawnable", True) and _doc_tier(c) == tier and not _at_catch_limit(c)]
        if not pool:
            return False, f"⚠️ No {tier} card is available (none exist, or every one is at its catch limit)."
        chosen = random.choice(pool)
    else:
        cid = normalize_char_id_input(arg)
        chosen = next((c for c in roster if c.get("char_id") == cid), None)
        if chosen is None:
            return False, f"⚠️ Character <code>{escape_html(str(arg))}</code> not found."
        if not chosen.get("spawnable", True):
            return False, "⚠️ That card is not spawnable (special CNFT card)."
        if _at_catch_limit(chosen):
            return False, (f"⚠️ <b>{escape_html(chosen.get('name', cid))}</b> already reached its catch limit "
                           f"({chosen.get('spawn_count', 0)}/{chosen.get('spawn_limit', 0)}) — raise it with /editchar first.")
    ok = await release_spawn(chat_id, chosen)
    if ok:
        return True, f"🎯 Spawned <b>{escape_html(chosen.get('name', ''))}</b> (<code>{display_char_id(chosen['char_id'])}</code>, {_doc_tier(chosen)})."
    return False, "⚠️ Couldn't post the spawn here (see the error report)."

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](fspawn|haii)(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def force_spawn_by_owner(event):
    """/fspawn (or /haii) — spawn a random card by the normal pattern. /fspawn <char id> or /fspawn sup | cata —
    spawn that specific card (the only way Supreme / Cataphract ever appear)."""
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
    specific = (event.pattern_match.group(2) or "").strip()
    if specific:
        async with spawn_locks[chat_id]:
            if chat_id in active_group_spawns:
                return await event.reply("⚠️ A spawn is already active in this chat.", parse_mode='html')
            _ok, text = await owner_spawn_specific(chat_id, specific)
        return await event.reply(text, parse_mode='html')
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

# 🩹 CHANGED (owner request): was 1800s (30min) stale / 300s (5min) poll. A stuck/uncaught
# active_group_spawns entry (message deleted mid-catch, a bug, whatever) permanently blocks
# every future spawn in that chat — trigger_dynamic_spawn's very first line is "if chat_id in
# active_group_spawns: return" — so the longer this window is, the longer any one bad entry
# can silently sit there looking like "spawns just don't happen here" with zero visible error.
# 120s is a practical floor: low enough to self-heal fast, but still gives a real player in a
# normal-paced chat a fighting chance to actually catch a spawn before it's swept as a ghost.
# Going lower risks clearing spawns out from under someone mid-attempt — say if you want it
# tighter still. Poll interval tightened to match (checking every 5min made a 30min threshold
# fine, but would leave a 120s threshold enforced up to 5min late).
GHOST_SPAWN_STALE_SECONDS = 120
GHOST_SPAWN_POLL_SECONDS = 60

@bot1.on(events.NewMessage(incoming=True))
async def global_message_counter_handler(event):
    if not CHANNEL_WORK_ENABLED: return  # 🚦 /channelwork off (manual, or auto during a sync) — no NEW spawns
    if event.is_private or event.chat_id == SPECIFIC_CONTROL_GROUP: return
    chat_id = event.chat_id
    if chat_id in active_group_spawns or chat_id in pending_rarity_quiz: return
    # 🎲 spam must not pay: junk / duplicate / over-rate / spam-muted messages don't advance the counter
    _uid = event.sender_id
    if _uid is not None and not spawn_message_counts(chat_id, _uid, event.raw_text or "", time.time(),
                                                      muted=(_uid in user_mute_until and time.time() < user_mute_until[_uid])):
        return
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
            eligible_characters = get_spawn_eligible_characters(characters_list)  # skips /addspecial CNFT cards + anything at its CatchLimit
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
                # 🩹 Tier first, then a card inside it — see pick_character_by_tier for why the
                # old per-card weighting made SUPREME/CATAPHRACT spawn far too often.
                chosen_char = pick_character_by_tier(candidates, RARITY_WEIGHTS, chat_id=chat_id)
                # ✅ Rarity gate ကို RARITY_GATE_TIERS ထဲပါတဲ့ Rarity တွေအတွက်သာ ဖွင့်မယ်
                tier = classify_rarity(chosen_char.get("rarity", ""))
                if tier in RARITY_GATE_TIERS:
                    ok = await start_rarity_gate_quiz(chat_id, chosen_char)
                else:
                    ok = await release_spawn(chat_id, chosen_char)
                if ok:
                    return
                if ok is None:
                    # release_spawn/start_rarity_gate_quiz hit "can't write in this chat" and
                    # already left + reported it once. The chat is the problem, not the
                    # character, so retrying with another pick would just repeat the same
                    # failure (and spam another alert) for no benefit.
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
    if chat_id in active_group_spawns:
        print(f"ℹ️ release_spawn: chat {chat_id} already has a live spawn — skipping release of {chosen_char.get('char_id')}")
        return False
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
            f"{rarity_emoji} ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!🧃",
            "ᴀᴅᴅ ᴛʜɪs ᴄʜᴀʀᴀᴄᴛᴇʀ ᴛᴏ ʏᴏᴜʀ ʜᴀʀᴇᴍ ᴜsɪɴɢ /fuck [ɴᴀᴍᴇ].."
        ]
        artist_credit = artist_line(artist_raw, prefix="\n", suffix="")
        if artist_credit:
            spawn_lines.append(artist_credit)
        spawn_text = "\n".join(spawn_lines)
        # 🖤 Promo button under every normal spawn. Used to be a direct link straight to
        # CNFT_PROMO_GROUP_URL; now it's a callback that opens the OWNER MODE promo in DM
        # instead (see owner_mode_show_callback below, and OWNER_MODE_* near CNFT_TIERS).
        # 🩹 FIX: raw TL types (types.KeyboardButtonCallback / KeyboardButtonRow / ReplyInlineMarkup)
        # are missing on Telethon 1.45.0 / layer 229, which made every spawn crash with
        # "module 'telethon.types' has no attribute 'KeyboardButtonCallback'". Button.inline is the
        # high-level API and builds the right markup for whichever Telethon build is installed.
        spawn_buttons = [[Button.inline("𝘽𝙐𝙔 〆 𝙊𝙒𝙉𝙀𝙍 𝙈𝙊𝘿𝙀", data=b"ownermode_show")]]

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
            # 📸 FIX (owner report — CRITICAL SYSTEM ERROR flood): if this chat allows text but
            # blocks this media type specifically, fall back to a text-only spawn instead of
            # failing/alerting (see _is_media_forbidden_error above). If text-only ALSO fails,
            # that's errors.ChatWriteForbiddenError (bot can't post here at all) — left to raise
            # normally so release_spawn's own except clause below can leave the chat.
            try:
                return await bot1.send_message(chat_id, spawn_text, parse_mode='html', file=media, spoiler=True, buttons=spawn_buttons)
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
                try:
                    return await bot1.send_message(chat_id, spawn_text, parse_mode='html', file=media, buttons=spawn_buttons)
                except Exception as e2:
                    if not _is_media_forbidden_error(e2):
                        raise
            except Exception as e:
                if not _is_media_forbidden_error(e):
                    raise
            print(f"ℹ️ release_spawn: chat {chat_id} blocks this media type — posting spawn as text-only instead.")
            return await bot1.send_message(chat_id, spawn_text, parse_mode='html', buttons=spawn_buttons)

        spawn_msg = await send_with_char_media(chosen_char["char_id"], chosen_char["storage_msg_id"], _post_spawn)
        if spawn_msg is None:
            # 🩹 One more genuinely fresh attempt before giving up (the first one may have hit a
            # transient fetch error right after a deploy/reconnect — see get_char_display_media).
            # This matters most for a SOLVED rarity gate, which has exactly one character to
            # release and shows the player "I got lost on my way to you" if this returns False.
            _CHAR_PHOTO_CACHE.pop(chosen_char["char_id"], None)
            await asyncio.sleep(1.5)
            spawn_msg = await send_with_char_media(chosen_char["char_id"], chosen_char["storage_msg_id"], _post_spawn)
        if spawn_msg is None:
            fetch_reason = _CHAR_PHOTO_LAST_ERROR.pop(chosen_char["char_id"], "no exception — the message came back empty / without media")
            msg = (f"storage media missing for char_id={chosen_char.get('char_id')} (storage_msg_id={chosen_char.get('storage_msg_id')}) — "
                   f"fetch result: {fetch_reason}. Spawn skipped, will retry with another character.")
            print(f"⚠️ Spawn Reliability: {msg}")
            await report_system_error(f"release_spawn (chat {chat_id})", msg)
            return False

        active_group_spawns[chat_id] = {
            "spawn_msg_id": spawn_msg.id,
            "char_id": chosen_char["char_id"],
            "name": chosen_char["name"],
            "category": chosen_char["category"],
            "rarity": rarity_display,
            "event": event_name,
            "artist": chosen_char.get("artist"),
            "spawn_time": time.time(),
            "revealed": False,
            "claimed": False
        }
        return True
    except errors.ChatWriteForbiddenError:
        # 🚪 Chat is muted/restricted for the bot — leave + one alert (see
        # _handle_write_forbidden), and return None (NOT False) so trigger_dynamic_spawn knows
        # to stop retrying entirely instead of burning through 4 more characters against a chat
        # it can no longer post in.
        await _handle_write_forbidden(chat_id, f"release_spawn (chat {chat_id}, char {chosen_char.get('char_id')})")
        return None
    except Exception as e:
        print(f"Spawn Error Tracker: {e}")
        await report_system_error(f"release_spawn (chat {chat_id}, char {chosen_char.get('char_id')})", e)
        return False


# ==========================================
# 🖤 OWNER MODE PROMO — fired by the "BUY OWNER MODE" callback button under every spawn (see
# spawn_buttons in release_spawn above). Tapping it DMs the tapper the sales copy + a Purchase
# button (opens a chat with OWNER_MODE_CONTACT_USERNAME) and a Translate button that flips the
# same message between OWNER_MODE_TEXT_MY and OWNER_MODE_TEXT_EN in place. This is advertising
# only, same as the old CNFT button — no card or access is actually granted by the bot itself;
# whoever answers OWNER_MODE_CONTACT_USERNAME's DMs handles the real sale by hand.
#
# Every tap (not just first-time) is logged to owner_mode_clicks_col so /count can report how
# much interest the promo is getting — see owner_mode_count_cmd below.
# ==========================================
def _owner_mode_buttons(translated: bool):
    """Purchase (url) row + Translate<->Original (callback) row shown under the promo text."""
    rows = [
        [Button.url(f"📩 PURCHASE — @{OWNER_MODE_CONTACT_USERNAME}", f"https://t.me/{OWNER_MODE_CONTACT_USERNAME}")],
    ]
    if translated:
        rows.append([Button.inline("🔙 မြန်မာ", data="ownermode_original")])
    else:
        rows.append([Button.inline("🌐 Translate to English", data="ownermode_translate_en")])
    return rows

async def _log_owner_mode_click(event):
    """Best-effort tap log — a logging failure should never block the promo from showing."""
    try:
        clicker = await event.get_sender()
    except Exception:
        clicker = None
    try:
        fullname = None
        if clicker is not None:
            fullname = (getattr(clicker, "first_name", "") or "").strip()
            if getattr(clicker, "last_name", None):
                fullname = f"{fullname} {clicker.last_name}".strip()
        await owner_mode_clicks_col.insert_one({
            "user_id": event.sender_id,
            "username": getattr(clicker, "username", None),
            "fullname": fullname or None,
            "chat_id": event.chat_id,   # group the spawn button was tapped in
            "clicked_at": datetime.utcnow(),
        })
    except Exception as e:
        print(f"owner_mode_clicks log error: {e}")

@bot1.on(events.CallbackQuery(pattern=r'^ownermode_show$'))
async def owner_mode_show_callback(event):
    await _log_owner_mode_click(event)
    try:
        await bot1.send_message(
            event.sender_id, OWNER_MODE_TEXT_MY, parse_mode='html',
            buttons=_owner_mode_buttons(translated=False)
        )
        await event.answer("📩 DM ထဲကို ပို့ပေးလိုက်ပါပြီ။")
    except Exception:
        # Most likely PeerIdInvalidError/ValueError — the tapper has never started the bot in
        # DM, so bot1 has no route to message them first. Fall back to posting the promo right
        # here in the group instead — the tap is already logged above either way.
        try:
            await bot1.send_message(
                event.chat_id, OWNER_MODE_TEXT_MY, parse_mode='html',
                buttons=_owner_mode_buttons(translated=False)
            )
            await event.answer()
        except Exception as e:
            print(f"owner_mode_show group fallback error: {e}")
            await event.answer("⚠️ Owner Mode ကို ဒီအချိန်မှာ မပြနိုင်ပါ — နောက်မှ ထပ်ကြိုးစားပါ။", alert=True)

@bot1.on(events.CallbackQuery(pattern=r'^ownermode_translate_en$'))
async def owner_mode_translate_callback(event):
    try:
        await event.edit(OWNER_MODE_TEXT_EN, parse_mode='html', buttons=_owner_mode_buttons(translated=True))
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^ownermode_original$'))
async def owner_mode_original_callback(event):
    try:
        await event.edit(OWNER_MODE_TEXT_MY, parse_mode='html', buttons=_owner_mode_buttons(translated=False))
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]count(?:@\w+)?$', 'bot1')))
async def owner_mode_count_cmd(event):
    """Owner-only: how many people have opened the OWNER MODE promo (total taps + unique
    users), pulled straight from owner_mode_clicks_col."""
    if event.sender_id != OWNER_ID: return
    total_taps = await owner_mode_clicks_col.count_documents({})
    unique_users = len(await owner_mode_clicks_col.distinct("user_id"))
    await event.reply(
        f"𖤐 <b>OWNER MODE — Promo Taps</b>\n"
        f"👥 Unique users: <code>{unique_users}</code>\n"
        f"🔘 Total taps: <code>{total_taps}</code>",
        parse_mode='html'
    )


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
            try:
                sent = await bot1.send_message(chat_id, quiz_text, file=media, buttons=buttons, parse_mode='html')
            except Exception as e:
                if not _is_media_forbidden_error(e):
                    raise
                # 📸 Same fallback as release_spawn (see _is_media_forbidden_error): this chat
                # blocks the quiz illustration's media type specifically. The illustration is
                # optional decoration, so just post the quiz as text-only instead of failing the
                # whole gate. A genuine full write-ban still raises normally (caught by this
                # function's own except errors.ChatWriteForbiddenError below).
                print(f"ℹ️ start_rarity_gate_quiz: chat {chat_id} blocks this media type — posting quiz as text-only instead.")
                sent = await bot1.send_message(chat_id, quiz_text, buttons=buttons, parse_mode='html')
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
    except errors.ChatWriteForbiddenError:
        await _handle_write_forbidden(chat_id, f"start_rarity_gate_quiz (chat {chat_id}, char {chosen_char.get('char_id')})")
        return None
    except Exception as e:
        print(f"Rarity Gate Quiz Error: {e}")
        return False

async def _delete_message_later(chat_id, msg_id, delay):
    """Deletes one of the bot's own messages after `delay` seconds; failures are ignored."""
    try:
        await asyncio.sleep(delay)
        await bot1.delete_messages(chat_id, [msg_id])
    except Exception:
        pass

@bot1.on(events.CallbackQuery(pattern=r'^rgate_(-?\d+)_(\d)$'))
async def rarity_gate_answer_callback(event):
    """🩹 REWORKED (2026-09, owner request):
      • Once the gate is answered its message is DELETED (it used to stay behind, edited into a
        "found the answer" note, cluttering the chat right above the spawn it unlocked).
      • With RARITY_GATE_WRONG_ANSWER_CLOSES_GATE, a WRONG tap ends the gate for everyone: the
        tapper is told they were wrong, the chat gets a short notice (auto-deleted after
        RARITY_GATE_FAIL_NOTICE_SECONDS), and the character is NOT released — it isn't consumed
        either (spawn_count only moves on a real catch), so it can still come up in a later gate.
    The first tap to reach the lock decides the outcome; anyone slower gets "too late"."""
    chat_id = int(event.pattern_match.group(1))
    chosen_idx = int(event.pattern_match.group(2))
    quiz = pending_rarity_quiz.get(chat_id)
    if not quiz or quiz.get("solved"):
        return await event.answer("⌛ …too late, this one's already decided.", alert=True)
    if time.time() - quiz["quiz_time"] > RARITY_GATE_TIMEOUT_SECONDS:
        return await event.answer("⌛ …time slipped away.", alert=True)
    is_correct = (chosen_idx == quiz["correct_index"])

    if not RARITY_GATE_WRONG_ANSWER_CLOSES_GATE:
        # Older rule: ONE attempt per person (right or wrong), the gate stays open for everyone
        # else. Check-and-mark with no await between them so a double-tap can't sneak in a second try.
        attempted_users = quiz.setdefault("attempted_users", set())
        if event.sender_id in attempted_users:
            return await event.answer("⚠️ …only one try, remember?", alert=True)
        attempted_users.add(event.sender_id)
        if not is_correct:
            return await event.answer("❌ …not quite. no second chances.", alert=True)

    async with spawn_locks[chat_id]:
        quiz = pending_rarity_quiz.get(chat_id)
        if not quiz or quiz.get("solved"):
            return await event.answer("⌛ …too late, this one's already decided.", alert=True)
        quiz["solved"] = True  # decided — one way or the other, nobody else gets a say
        tapper_id = event.sender_id
        if not is_correct and pending_rarity_quiz.get(chat_id) is quiz:
            del pending_rarity_quiz[chat_id]  # gate is over; the chat can spawn normally again

    mention = await get_html_mention(event, tapper_id)

    if not is_correct:
        await event.answer("❌ …wrong answer. the gate is closed now.", alert=True)
        try:
            await event.edit(
                f"❌ <b>{mention} tapped the wrong answer…</b>\n"
                f"<i>the gate closes. nobody meets me this time.</i>",
                parse_mode='html',
                buttons=None
            )
            asyncio.create_task(_delete_message_later(chat_id, quiz["msg_id"], RARITY_GATE_FAIL_NOTICE_SECONDS))
        except Exception:
            # Couldn't turn it into a notice (edit failed) — just make sure the gate message goes away.
            asyncio.create_task(_delete_message_later(chat_id, quiz["msg_id"], 0))
        return

    await event.answer("✅ …found me. I'm on my way~", alert=True)
    # The gate message has done its job — delete it before the spawn appears.
    try:
        await bot1.delete_messages(chat_id, [quiz["msg_id"]])
    except Exception:
        pass
    try:
        released_ok = await release_spawn(chat_id, quiz["char"])
    finally:
        # Held until here (not deleted at solve time) so no OTHER spawn can start in this chat
        # while release_spawn is still posting this one.
        if pending_rarity_quiz.get(chat_id) is quiz:
            del pending_rarity_quiz[chat_id]
    if not released_ok:
        try:
            await bot1.send_message(
                chat_id,
                f"⚠️ <b>{mention} found the answer, but I got lost on my way to you…</b>\n"
                f"<i>Nothing was lost, though — a new someone will slip in again soon.</i>",
                parse_mode='html'
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
    option_labels = [".", ".", ".", "."]
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



# ==========================================
# 🧠 TRIVIA — a standalone, group-wide "first correct tap wins" auto-spawn, fully independent
# of character spawns (own message counter, own pending-state dict, own timeout watcher — same
# separation-of-concerns as the rarity-gate quiz above, just triggered by ordinary chat
# activity instead of a Rarity 1-4 pick).
#
# 🆙 UPGRADED (ported from main_pyန.py): 5 difficulty tiers, 🌟 Golden Questions, Trivia
# Points + an 18-step rank ladder, a points-based Global Top 50, /triviarank, /ftrivia,
# /triviaspawn on|off, and bulk question import (/addtriviabulk, /listtriviabank,
# /deltriviabank). The one deliberate difference from main_pyန.py: this file's economy is
# 💰 ccm (users_catcher_col.ccm_balance), not ⭐ Stars — main_pyန.py's star_balance /
# vlt_balance / star_debt / Premium / Casino / Limited-Editions systems don't exist here, so
# every payout and penalty below is in ccm and those extras are left out. Tune the per-tier
# ccm_min / ccm_max / ccm_penalty numbers in TRIVIA_DIFFICULTY_CONFIG to taste.
#
# Question bank: trivia_bank_col. Older questions saved by the previous /addtrivia have NO
# "difficulty" field — they're treated as NORMAL (see _trivia_diff_query) so nothing already
# in the database goes quiet.
# ==========================================
TRIVIA_SPAWN_MIN_MSGS = 45   # min group messages between trivia spawns (per chat)
TRIVIA_SPAWN_MAX_MSGS = 55   # max group messages between trivia spawns (per chat) — averages ~50
TRIVIA_TIMEOUT_SECONDS = 120  # answering window, starting from the options reveal (not the post)
TRIVIA_OPTIONS_REVEAL_DELAY = 5   # seconds the question sits alone, no options/buttons yet —
# stops reflex mash-tapping from landing a lucky guess before anyone's actually read it.

# 🌟 GOLDEN QUESTION — rare, visually distinct round that pays the ccm range ×N for whatever
# difficulty got rolled. Only the ccm payout is boosted; Trivia Points stay what the tier gives.
GOLDEN_QUESTION_CHANCE = 0.10       # 10% of trivia spawns
GOLDEN_QUESTION_MULTIPLIER = 5      # 💰 ccm reward range ×5 for that one round only
GOLDEN_QUESTION_EMOJI = "🌟"

# 🎚️ DIFFICULTY TIERS — each draws from its own slice of the question bank.
# ccm_min/ccm_max = win range · points = Trivia Points on a win · wrong_penalty = Trivia Points
# lost on a wrong tap · ccm_penalty = ccm lost on a wrong tap (never below a 0 balance).
# Top-10 players lose DOUBLE on a wrong tap (both penalties).
# 💱 With grams (200 ccm = 1 g = 1 MMK) the old payouts of 200–1,500 ccm per win were worth 1–7.5 g
# EACH — far too generous now that trivia is the only way to earn ccm. Cut to a tenth (≈80 ccm ≈ 0.4 g
# per average win, ≈112 ccm with golden rounds). Tune ccm_min / ccm_max / ccm_penalty here — this
# table is trivia's payout; /daily and catching have their own constants (DAILY_*, CATCH_CCM_*).
TRIVIA_DIFFICULTY_CONFIG = {
    "EASY":         {"label": "Easy",         "emoji": "🟢", "weight": 12, "ccm_min": 20,  "ccm_max": 40,  "points": 5,  "wrong_penalty": 2,  "ccm_penalty": 4},
    "NORMAL":       {"label": "Normal",       "emoji": "🔵", "weight": 27, "ccm_min": 45,  "ccm_max": 65,  "points": 8,  "wrong_penalty": 4,  "ccm_penalty": 9},
    "HARD":         {"label": "Hard",         "emoji": "🟠", "weight": 28, "ccm_min": 70,  "ccm_max": 90,  "points": 12, "wrong_penalty": 6,  "ccm_penalty": 14},
    "VERY_HARD":    {"label": "Very Hard",    "emoji": "🔴", "weight": 20, "ccm_min": 95,  "ccm_max": 120, "points": 18, "wrong_penalty": 9,  "ccm_penalty": 19},
    "EXTREME_HARD": {"label": "Extreme Hard", "emoji": "🟣", "weight": 13, "ccm_min": 125, "ccm_max": 150, "points": 25, "wrong_penalty": 13, "ccm_penalty": 25},
}
TRIVIA_DIFFICULTY_ORDER = ["EASY", "NORMAL", "HARD", "VERY_HARD", "EXTREME_HARD"]
TRIVIA_LEGACY_DIFFICULTY = "NORMAL"  # questions saved before tiers existed (no "difficulty" field) count as this
TRIVIA_OPTION_COUNT = 4  # options are always shuffled and re-indexed at spawn time

def weighted_random_trivia_difficulty():
    weights = [TRIVIA_DIFFICULTY_CONFIG[d]["weight"] for d in TRIVIA_DIFFICULTY_ORDER]
    return random.choices(TRIVIA_DIFFICULTY_ORDER, weights=weights, k=1)[0]

def normalize_trivia_difficulty_arg(raw):
    """'very hard' / 'Very-Hard' / 'VERYHARD' / 'extreme' / 'medium' -> canonical tier key, else None."""
    squashed = re.sub(r'[\s_\-]+', '', (raw or '')).upper()
    if not squashed:
        return None
    for key in TRIVIA_DIFFICULTY_CONFIG:
        if re.sub(r'[\s_\-]+', '', key).upper() == squashed:
            return key
    return {"MEDIUM": "NORMAL", "EXTREME": "EXTREME_HARD", "INSANE": "EXTREME_HARD"}.get(squashed)

def _trivia_diff_query(difficulty):
    """Mongo filter for one tier. The legacy tier also matches old docs with no difficulty field."""
    if difficulty == TRIVIA_LEGACY_DIFFICULTY:
        return {"$or": [{"difficulty": difficulty}, {"difficulty": {"$exists": False}}]}
    return {"difficulty": difficulty}

# 🏆 TRIVIA RANK LADDER — 18 tiers of cumulative Trivia Points
TRIVIA_RANKS = [
    (0,    "🌱 Newbie"),
    (100,  "🥉 Bronze Brain"),
    (300,  "🥈 Silver Scholar"),
    (500,  "🥇 Gold Genius"),
    (700,  "💎 Diamond Mind"),
    (900,  "👑 Quiz Master"),
    (1100, "🏆 Legend"),
    (1300, "⚡ Grandmaster"),
    (1500, "🌟 Celestial"),
    (1700, "🔥 Immortal"),
    (1900, "🌌 Transcendent"),
    (2100, "♾️ Omniscient"),
    (2300, "👁️ All-Seeing"),
    (2500, "🌠 Sovereign"),
    (2700, "🔱 Demiurge"),
    (2900, "🕳️ Singularity"),
    (3100, "☄️ Ascendant"),
    (3300, "🌈 Paragon"),
]

def get_trivia_rank_info(points):
    """-> (rank_number, rank_name, this_rank_floor_points, next_rank_points_or_None)"""
    idx = 0
    for i, (threshold, _name) in enumerate(TRIVIA_RANKS):
        if points >= threshold:
            idx = i
    floor_points, rank_name = TRIVIA_RANKS[idx]
    next_points = TRIVIA_RANKS[idx + 1][0] if idx + 1 < len(TRIVIA_RANKS) else None
    return idx + 1, rank_name, floor_points, next_points

def build_trivia_progress_bar(points, floor_points, next_points, length=10):
    if next_points is None:
        return "█" * length
    span = next_points - floor_points
    if span <= 0:
        return "█" * length
    progressed = max(0, min(span, points - floor_points))
    filled = max(0, min(length, round(length * progressed / span)))
    return "█" * filled + "░" * (length - filled)

def trivia_difficulty_list_text():
    return " / ".join(
        f"{TRIVIA_DIFFICULTY_CONFIG[d]['emoji']}{TRIVIA_DIFFICULTY_CONFIG[d]['label']} "
        f"{TRIVIA_DIFFICULTY_CONFIG[d]['ccm_min']}-{TRIVIA_DIFFICULTY_CONFIG[d]['ccm_max']}💰"
        for d in TRIVIA_DIFFICULTY_ORDER
    )

# Static fallback bank — intentionally empty, filled via /addtriviabulk (or /addtrivia)
TRIVIA_QUESTION_BANK = {
    "EASY": [], "NORMAL": [], "HARD": [], "VERY_HARD": [], "EXTREME_HARD": [],
}

# Fancy-font helpers used by the redesigned trivia messages. main.py's small_caps() already
# maps every letter (including 's' -> 'ꜱ'), so small_caps_full is just an alias here.
def small_caps_full(text):
    return small_caps(text)

_SANS_BOLD_ITALIC_TRANS = str.maketrans(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
    ''.join(chr(0x1D63C + i) for i in range(26)) + ''.join(chr(0x1D656 + i) for i in range(26))
)
def sans_bold_italic(text):
    """Mathematical Sans-Serif Bold Italic (ASCII letters only)."""
    return text.translate(_SANS_BOLD_ITALIC_TRANS)

# 🌸 TRIVIA HOST — the questions are "asked" by an anime girl persona (flavor text only; no
# gameplay change). Rename her via TRIVIA_HOST_NAME, or edit/add lines in the pools below —
# one is picked at random each time. {mention} is filled with the winner's clickable name and
# {mult} with the Golden multiplier.
TRIVIA_HOST_NAME = "Sakura"
TRIVIA_INTRO_LINES = [
    "Kyaa~ minna-san! Sakura has a question for you! (◕‿◕✿)",
    "Ehehe~ think you can answer Sakura's question? (｡•̀ᴗ-)✧",
    "Ne ne~ let's see who's the smartest one today! ✨",
    "Ara ara~ a new question has arrived, senpai-tachi~ 💕",
    "Fufu~ Sakura made this one just for you! (⁄ ⁄>⁄ ▽ ⁄<⁄ ⁄)",
]
TRIVIA_GOLDEN_INTRO_LINES = [
    "Kyaaa!! It's a GOLDEN QUESTION! Sakura prepared a super special prize~ (≧▽≦)♡",
    "Sugoi sugoi~! A golden question just appeared — ×{mult} rewards for the winner! ✨",
]
TRIVIA_WIN_LINES = [
    "Sugoi~!! {mention}-senpai got it right! (ﾉ◕ヮ◕)ﾉ*:･ﾟ✧",
    "Yatta~! {mention} is so smart, Sakura is impressed! (*≧ω≦)",
    "Kyaa~ {mention}-senpai was the fastest! Sakura is so happy! ♡(ˆ⌣ˆ)",
]
TRIVIA_GOLDEN_WIN_LINES = [
    "Kyaaa~!! {mention}-senpai took Sakura's golden prize! (≧◡≦) ♡",
    "Sugoi sugoi!! {mention} won the GOLDEN question! ✨(ﾉ◕ヮ◕)ﾉ✨",
]
TRIVIA_TIMEOUT_LINES = [
    "Aww... nobody got it in time (´；ω；`)",
    "Mou~ nobody answered... Sakura is sad (；へ：)",
    "Eeh?! Nobody? Sakura will ask again later~ (｡•́︿•̀｡)",
]

# ⚙️ Auto-spawn toggle (default ON) — /triviaspawn on|off, persisted in bot_settings_col
_cached_trivia_enabled = True

async def load_trivia_settings_cache():
    global _cached_trivia_enabled
    try:
        doc = await bot_settings_col.find_one({"_id": "trivia_spawn_enabled"})
        if doc is not None and "enabled" in doc:
            _cached_trivia_enabled = bool(doc["enabled"])
    except Exception as e:
        print(f"load_trivia_settings_cache error: {e}")

async def get_trivia_pool(difficulty):
    """DB questions for this tier (+ the empty static safety-net list). Can legitimately be
    empty — trigger_trivia_spawn falls back across the other tiers instead of crashing."""
    custom = await trivia_bank_col.find(_trivia_diff_query(difficulty), {"_id": 0}).to_list(length=None)
    static = TRIVIA_QUESTION_BANK.get(difficulty) or []
    return (custom or []) + static

async def get_trivia_position(points):
    """(position, total) — this user's standing among everyone with trivia_points > 0."""
    total = await users_catcher_col.count_documents({"trivia_points": {"$gt": 0}})
    position = await users_catcher_col.count_documents({"trivia_points": {"$gt": points}}) + 1
    return position, total

async def get_current_trivia_top10_ids():
    top_users = await users_catcher_col.find(
        {"trivia_points": {"$gt": 0}}, {"user_id": 1}
    ).sort("trivia_points", -1).limit(10).to_list(length=10)
    return {u["user_id"] for u in top_users}

def _trivia_lb_button_rows():
    return [[Button.inline("🏆 Global Top 50", data="trivialb")]]

async def trigger_trivia_spawn(chat_id, forced_difficulty=None, force_golden=False):
    """Posts one TRIVIA_OPTION_COUNT-option round in chat_id at a weighted-random difficulty
    (or forced_difficulty, for the owner's /ftrivia). First correct tap wins that tier's ccm
    range + Trivia Points; everyone else gets exactly one attempt, right or wrong. Two-stage
    post — question alone first, options+buttons TRIVIA_OPTIONS_REVEAL_DELAY seconds later."""
    if chat_id in pending_trivia_quiz:
        return
    try:
        difficulty = forced_difficulty if forced_difficulty in TRIVIA_DIFFICULTY_CONFIG else weighted_random_trivia_difficulty()
        cfg = TRIVIA_DIFFICULTY_CONFIG[difficulty]
        bank = await get_trivia_pool(difficulty)
        if not bank:
            # Chosen tier is empty — try the other tiers before giving up, so a partially
            # stocked bank still fires instead of the group going quiet.
            for fallback_difficulty in TRIVIA_DIFFICULTY_ORDER:
                if fallback_difficulty == difficulty:
                    continue
                fallback_bank = await get_trivia_pool(fallback_difficulty)
                if fallback_bank:
                    difficulty, cfg, bank = fallback_difficulty, TRIVIA_DIFFICULTY_CONFIG[fallback_difficulty], fallback_bank
                    break
        if not bank:
            return  # nothing added anywhere yet — skip this cycle quietly
        q = random.choice(bank)
        options = q["options"][:]
        correct_answer_text = options[q["correct_index"]]
        random.shuffle(options)
        correct_index = options.index(correct_answer_text)

        is_golden = force_golden or random.random() < GOLDEN_QUESTION_CHANCE
        ccm_min = cfg["ccm_min"] * GOLDEN_QUESTION_MULTIPLIER if is_golden else cfg["ccm_min"]
        ccm_max = cfg["ccm_max"] * GOLDEN_QUESTION_MULTIPLIER if is_golden else cfg["ccm_max"]

        host = escape_html(TRIVIA_HOST_NAME)
        if is_golden:
            title_line = f"{GOLDEN_QUESTION_EMOJI} {sans_bold_italic(TRIVIA_HOST_NAME + '-chan Golden Quiz')} {GOLDEN_QUESTION_EMOJI}"
            intro_line = random.choice(TRIVIA_GOLDEN_INTRO_LINES).format(mult=GOLDEN_QUESTION_MULTIPLIER)
        else:
            title_line = f"🌸 {sans_bold_italic(TRIVIA_HOST_NAME + '-chan Quiz Time')} 🌸"
            intro_line = random.choice(TRIVIA_INTRO_LINES)
        header = (
            f"{title_line}\n"
            f"💬 <i>{escape_html(intro_line)}</i>\n\n"
            f"{cfg['emoji']} {small_caps_full(cfg['label'] + ' difficulty')}\n"
            f"❓ <b>{escape_html(q['question'])}</b>"
        )
        keycaps = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣"]
        options_text = "\n".join(
            f"{keycaps[i] if i < len(keycaps) else str(i + 1) + '.'}  {escape_html(opt)}" for i, opt in enumerate(options)
        )
        stage1_text = (
            f"{header}\n\n"
            f"👀 <i>{host}: \"Read it carefully, okay? I'll show the choices in {TRIVIA_OPTIONS_REVEAL_DELAY}s~ (´,,•ω•,,)♡\"</i>"
        )
        stage2_text = (
            f"{header}\n\n"
            f"{options_text}\n\n"
            f"⏱ {small_caps_full('time')}: {TRIVIA_TIMEOUT_SECONDS}s\n"
            f"💰 {small_caps_full('reward')}: {ccm_min:,}-{ccm_max:,} {small_caps_full('ccm')} + {cfg['points']} {small_caps_full('rank pts')}\n"
            f"🎯 <i>{host}: \"Be the first to tap the right answer, senpai~ I'm cheering for you! ٩(ˊᗜˋ*)و\"</i>"
        )
        buttons = [[Button.inline(str(i + 1), data=f"triv_{chat_id}_{i}") for i in range(len(options))]]
        # 🌸 Host picture: if the owner has added any via /addtriviamedia, one random item is
        # sent WITH the question (as its caption) and the later options/result edits then edit
        # that caption. Telegram caps captions at 1024 chars, so if the longest version of the
        # text wouldn't fit, the picture goes out on its own first and the text follows as a
        # normal message. Any media failure falls back to the plain text-only post below.
        sent = None
        try:
            media_pool = await trivia_media_col.find({}, {"file_id": 1}).to_list(length=None)
        except Exception as e:
            media_pool = []
            print(f"Trivia media lookup error: {e}")
        if media_pool:
            media_file_id = random.choice(media_pool)["file_id"]
            plain_len = len(re.sub(r'<[^>]+>', '', max(stage1_text, stage2_text, key=len)))
            try:
                if plain_len <= 1000:
                    sent = await bot1.send_message(chat_id, stage1_text, parse_mode='html', file=media_file_id)
                else:
                    await bot1.send_file(chat_id, media_file_id)
                    sent = await bot1.send_message(chat_id, stage1_text, parse_mode='html')
            except errors.ChatWriteForbiddenError:
                raise
            except Exception as e:
                sent = None
                print(f"Trivia media send failed, falling back to text-only: {type(e).__name__}: {e}")
        if sent is None:
            sent = await bot1.send_message(chat_id, stage1_text, parse_mode='html')

        # Set immediately (before the reveal delay) so the "one trivia at a time per chat"
        # guard also covers the reveal window; "revealed": False keeps stray taps inert.
        quiz_state = {
            "options": options,
            "correct_index": correct_index,
            "question": q["question"],
            "difficulty": difficulty,
            "msg_id": sent.id,
            "quiz_time": time.time(),
            "solved": False,
            "attempted_users": set(),
            "revealed": False,
            "is_golden": is_golden,
            "ccm_min": ccm_min,
            "ccm_max": ccm_max,
        }
        pending_trivia_quiz[chat_id] = quiz_state

        await asyncio.sleep(TRIVIA_OPTIONS_REVEAL_DELAY)
        if pending_trivia_quiz.get(chat_id) is not quiz_state:
            return  # force-cleared/replaced during the delay — bail out quietly

        try:
            await bot1.edit_message(chat_id, sent.id, stage2_text, parse_mode='html', buttons=buttons)
        except errors.MessageNotModifiedError:
            pass
        # Answering window starts at reveal, not at the original post.
        quiz_state["quiz_time"] = time.time()
        quiz_state["revealed"] = True
        asyncio.create_task(trivia_quiz_timeout_watcher(chat_id, sent.id))
    except errors.ChatWriteForbiddenError:
        pending_trivia_quiz.pop(chat_id, None)
        await _handle_write_forbidden(chat_id, f"trigger_trivia_spawn (chat {chat_id})")
    except Exception as e:
        pending_trivia_quiz.pop(chat_id, None)  # never leave a stuck guard behind on error
        print(f"Trivia Spawn Error: {e}")

# 🧠 Trivia's own message-count trigger — fully independent of global_message_counter_handler
# (character spawns): separate counter, separate random target. Skips quietly while a character
# spawn or rarity-gate quiz is already up in that chat, purely so the group isn't juggling two
# competing "tap this" prompts at once. Does nothing while /triviaspawn is off.
@bot1.on(events.NewMessage(incoming=True))
async def trivia_message_counter_handler(event):
    if not _cached_trivia_enabled or not CHANNEL_WORK_ENABLED: return  # 🚦 same gate as character spawns — see CHANNEL_WORK_ENABLED above
    if event.is_private or event.chat_id == SPECIFIC_CONTROL_GROUP: return
    chat_id = event.chat_id
    if chat_id in pending_trivia_quiz or chat_id in active_group_spawns or chat_id in pending_rarity_quiz:
        return
    target = trivia_spawn_targets.get(chat_id)
    if not target:
        target = random.randint(TRIVIA_SPAWN_MIN_MSGS, TRIVIA_SPAWN_MAX_MSGS)
        trivia_spawn_targets[chat_id] = target
    new_count = trivia_spawn_counters.get(chat_id, 0) + 1
    trivia_spawn_counters[chat_id] = new_count
    if new_count >= target:
        trivia_spawn_counters[chat_id] = 0
        trivia_spawn_targets.pop(chat_id, None)  # re-rolled fresh next cycle
        await trigger_trivia_spawn(chat_id)

@bot1.on(events.CallbackQuery(pattern=r'^triv_(-?\d+)_(\d)$'))
async def trivia_answer_callback(event):
    chat_id = int(event.pattern_match.group(1))
    chosen_idx = int(event.pattern_match.group(2))
    quiz = pending_trivia_quiz.get(chat_id)
    if not quiz or quiz.get("solved") or not quiz.get("revealed"):
        return await event.answer("⌛ ဒီ Trivia မေးခွန်း ပြီးသွားပါပြီ။", alert=True)
    if time.time() - quiz["quiz_time"] > TRIVIA_TIMEOUT_SECONDS:
        return await event.answer("⌛ အချိန်ကုန်သွားပါပြီ။", alert=True)
    # 🔒 One attempt per person — check-and-mark with no await in between.
    attempted_users = quiz.setdefault("attempted_users", set())
    if event.sender_id in attempted_users:
        return await event.answer("⚠️ သင့်မှာ ဒီမေးခွန်းအတွက် တစ်ကြိမ်ပဲ ဖြေခွင့်ရှိပါတယ်။", alert=True)
    attempted_users.add(event.sender_id)
    cfg = TRIVIA_DIFFICULTY_CONFIG[quiz.get("difficulty", "EASY")]

    if chosen_idx != quiz["correct_index"]:
        points_penalty = cfg["wrong_penalty"]
        ccm_penalty = cfg["ccm_penalty"]
        is_top10 = False
        new_points = None
        paid_now = 0
        try:
            wrong_user = await users_catcher_col.find_one({"user_id": event.sender_id})
            current_points = (wrong_user or {}).get("trivia_points", 0)
            current_ccm = (wrong_user or {}).get("ccm_balance", 0)
            is_top10 = event.sender_id in await get_current_trivia_top10_ids()
            if is_top10:
                points_penalty *= 2
                ccm_penalty *= 2
            new_points = max(0, current_points - points_penalty)
            paid_now = max(0, min(current_ccm, ccm_penalty))  # never pushes the balance below 0
            inc_ops = {"trivia_wrong": 1}
            if paid_now > 0:
                inc_ops["ccm_balance"] = -paid_now
            await users_catcher_col.update_one(
                {"user_id": event.sender_id},
                {"$set": {"trivia_points": new_points}, "$inc": inc_ops},
                upsert=True
            )
        except Exception as e:
            print(f"Trivia wrong-answer penalty error: {e}")
        points_note = f"(now {new_points})" if new_points is not None else "(couldn't update)"
        return await event.answer(
            f"❌ မှားသွားပါပြီ။ Rank Points −{points_penalty}{' (Top 10 x2)' if is_top10 else ''} {points_note}"
            f" | 💰−{paid_now:,} ccm\n"
            f"နောက်ထပ် အခွင့်အရေး မရတော့ပါ။",
            alert=True
        )

    async with spawn_locks[chat_id]:
        quiz = pending_trivia_quiz.get(chat_id)
        if not quiz or quiz.get("solved"):
            return await event.answer("⌛ တစ်ယောက်ယောက်က အရင်ဖြေပြီးသွားပါပြီ။", alert=True)
        quiz["solved"] = True
        winner_id = event.sender_id
    mention = await get_html_mention(event, winner_id)

    is_golden = quiz.get("is_golden", False)
    reward = random.randint(quiz.get("ccm_min", cfg["ccm_min"]), quiz.get("ccm_max", cfg["ccm_max"]))
    points_earned = cfg["points"]

    points_before = 0
    points_after = points_earned
    try:
        winner_doc_before = await users_catcher_col.find_one({"user_id": winner_id})
        points_before = (winner_doc_before or {}).get("trivia_points", 0)
        points_after = points_before + points_earned
        await users_catcher_col.update_one(
            {"user_id": winner_id},
            {"$inc": {"ccm_balance": reward, "trivia_points": points_earned, "trivia_correct": 1}},
            upsert=True
        )
    except Exception as e:
        print(f"Trivia ccm/points reward error: {e}")

    rank_before_idx, _rb_name, _rb_floor, _rb_next = get_trivia_rank_info(points_before)
    rank_after_idx, rank_after_name, floor_after, next_after = get_trivia_rank_info(points_after)
    bar = build_trivia_progress_bar(points_after, floor_after, next_after)
    progress_line = (
        f"{bar}  {points_after} pts (MAX 🏆)" if next_after is None
        else f"{bar}  {points_after}/{next_after} pts"
    )
    rank_up_line = f"🎉 {small_caps_full('rank up')}!\n" if rank_after_idx > rank_before_idx else ""
    trivia_position, trivia_total = await get_trivia_position(points_after)

    try:
        await event.edit(
            f"✅ {sans_bold_italic('Correct!')}\n"
            f"🌸 <i>{(random.choice(TRIVIA_GOLDEN_WIN_LINES) if is_golden else random.choice(TRIVIA_WIN_LINES)).format(mention=mention)}</i>\n\n"
            f"🏆 {small_caps_full('winner')}: {mention}\n"
            f"✔ {small_caps_full('answer')}: {escape_html(quiz['options'][quiz['correct_index']])}\n\n"
            f"💰 {small_caps_full('reward')}: +{reward:,} {small_caps_full('ccm')}\n"
            f"🧠 {small_caps_full('rank pts')}: +{points_earned}\n\n"
            f"{rank_up_line}"
            f"🏅 {small_caps_full('rank')} {rank_after_idx}/{len(TRIVIA_RANKS)}: {rank_after_name}\n"
            f"{progress_line}\n"
            f"🌍 {small_caps_full('position')}: #{trivia_position} / {trivia_total}",
            parse_mode='html',
            buttons=_trivia_lb_button_rows()
        )
    except Exception:
        pass

    if is_golden:
        announce = (
            f"{GOLDEN_QUESTION_EMOJI} <b>GOLDEN QUESTION WON!</b> {GOLDEN_QUESTION_EMOJI}\n"
            f"🌸 <i>Kyaaa~ {mention} took {escape_html(TRIVIA_HOST_NAME)}'s golden prize!</i> <code>+{reward:,}💰</code> (≧◡≦)♡"
        )
    else:
        announce = (
            f"🌸 <i>Yatta~! {mention} won {escape_html(TRIVIA_HOST_NAME)}'s quiz!</i>\n"
            f"💰 +{reward:,} · 🧠 +{points_earned} pts"
        )
    if rank_after_idx > rank_before_idx:
        announce += f"\n🎉 <i>Rank up! Sugoi~ you're now {rank_after_name}!</i>"
    try:
        await bot1.send_message(chat_id, announce, parse_mode='html')
    except Exception:
        pass

    await event.answer(f"✅ မှန်ပါတယ်! +{reward:,}💰  +{points_earned} pts ရရှိပါပြီ!", alert=True)
    if pending_trivia_quiz.get(chat_id) is quiz:
        del pending_trivia_quiz[chat_id]

async def trivia_quiz_timeout_watcher(chat_id, msg_id):
    try:
        await asyncio.sleep(TRIVIA_TIMEOUT_SECONDS)
        quiz = pending_trivia_quiz.get(chat_id)
        if not quiz or quiz.get("solved") or quiz.get("msg_id") != msg_id:
            return
        del pending_trivia_quiz[chat_id]
        try:
            await bot1.edit_message(
                chat_id, msg_id,
                f"⏰ <b>ဘယ်သူမှ အချိန်မီ မဖြေနိုင်ခဲ့ပါဘူး။</b>\n"
                f"🌸 <i>{random.choice(TRIVIA_TIMEOUT_LINES)}</i>\n"
                f"✅ <b>အဖြေမှန်က:</b> {escape_html(quiz['options'][quiz['correct_index']])}",
                parse_mode='html',
                buttons=_trivia_lb_button_rows()
            )
        except Exception:
            pass
    except Exception as e:
        # 🛡️ a leftover pending_trivia_quiz entry silently blocks every future round in that
        # chat — never leave one stuck behind, no matter what goes wrong above.
        print(f"Trivia Timeout Watcher Error: {e}")
        if pending_trivia_quiz.get(chat_id, {}).get("msg_id") == msg_id:
            del pending_trivia_quiz[chat_id]

# ---- Global Trivia Top 50 — paginated, 10 rows/page, ranked by Trivia Points ----
TRIVIA_LB_PAGE_SIZE = 10
TRIVIA_LB_TOTAL = 50

async def render_trivia_leaderboard_page(page):
    """(text, buttons) for one 0-indexed page of the Global Top 50 Trivia Points leaderboard
    (0 = ranks 1-10 ... 4 = ranks 41-50). Re-fetched fresh on every call. Same layout as
    main_pyန.py. Projection: only the 3 fields used below — without it every call pulls each
    user's FULL document (incl. their whole harem array) for up to 50 users (slow)."""
    top_users = await users_catcher_col.find(
        {"trivia_points": {"$gt": 0}}, {"user_id": 1, "fullname": 1, "trivia_points": 1, "_id": 0}
    ).sort("trivia_points", -1).limit(TRIVIA_LB_TOTAL).to_list(length=TRIVIA_LB_TOTAL)
    total = len(top_users)
    start = page * TRIVIA_LB_PAGE_SIZE
    page_rows = top_users[start:start + TRIVIA_LB_PAGE_SIZE]

    if not page_rows:
        body = "😶 <i>No Trivia ranks yet — be the first to answer one!</i>" if page == 0 else "<i>No more entries.</i>"
    else:
        lines = []
        for i, u in enumerate(page_rows):
            rank = start + i + 1
            uname = escape_html(clean_display_name(u.get("fullname"), fallback=f"Agent {u['user_id']}"))
            mention = f"<a href='tg://user?id={u['user_id']}'>{uname}</a>"
            pts = u.get("trivia_points", 0)
            _, rank_name, _, _ = get_trivia_rank_info(pts)
            lines.append(f"<b>{rank}.</b> {mention} — {rank_name} (<code>{pts} pts</code>)")
        body = "\n".join(lines)
    text = "🏆 <b>GLOBAL TRIVIA LEADERBOARD</b>\n\n" + body

    # Everyone who has ever answered anything, win or lose — created the first time someone
    # answers, so it's a broader number than the 50 shown above.
    global_participants = await users_catcher_col.count_documents({"trivia_points": {"$exists": True}})

    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Previous", data=f"trivialb_pg_{page - 1}"))
    if start + TRIVIA_LB_PAGE_SIZE < total:
        nav_row.append(Button.inline("Next ▶", data=f"trivialb_pg_{page + 1}"))
    buttons = []
    if nav_row:
        buttons.append(nav_row)
    buttons.append([Button.inline(f"🌍 Globally: {global_participants:,}", data="trivia_global_count_noop")])
    return text, buttons

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]triviatop(?:@\w+)?$', 'bot1')))
async def trivia_top_handler(event):
    text, buttons = await render_trivia_leaderboard_page(0)
    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.CallbackQuery(pattern=r'^trivialb$'))
async def trivia_leaderboard_open_callback(event):
    """The "🏆 Global Top 50" button under a trivia result — always opens fresh at page 0."""
    text, buttons = await render_trivia_leaderboard_page(0)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^trivialb_pg_(\d+)$'))
async def trivia_leaderboard_page_callback(event):
    page = int(event.pattern_match.group(1))
    text, buttons = await render_trivia_leaderboard_page(page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()
    except Exception as e:
        await event.answer(f"❌ Error: {e}", alert=True)

@bot1.on(events.CallbackQuery(pattern=r'^trivia(?:_global_count)?_noop$'))
async def trivia_noop_callback(event):
    await event.answer()  # purely informational row — just acks the tap

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]triviarank(?:@\w+)?$', 'bot1')))
async def trivia_rank_handler(event):
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    points = (user_doc or {}).get("trivia_points", 0)
    rank_idx, rank_name, floor_points, next_points = get_trivia_rank_info(points)
    bar = build_trivia_progress_bar(points, floor_points, next_points)
    progress_line = (
        f"{bar}  <code>{points} pts (MAX 🏆)</code>" if next_points is None
        else f"{bar}  <code>{points}/{next_points} pts</code>"
    )
    trivia_position, trivia_total = await get_trivia_position(points)
    await event.reply(
        f"🧠 <b>{mention}'s Trivia Rank</b>\n\n"
        f"🏅 <b>Rank {f(str(rank_idx))}/{f(str(len(TRIVIA_RANKS)))}:</b> {rank_name}\n"
        f"{progress_line}\n"
        f"🌍 <b>Position:</b> <code>#{trivia_position} / {trivia_total}</code>",
        parse_mode='html',
        buttons=_trivia_lb_button_rows()
    )

# ---- Owner controls ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]triviaspawn(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def trivia_spawn_toggle_handler(event):
    if event.sender_id != OWNER_ID: return
    global _cached_trivia_enabled
    arg = (event.pattern_match.group(1) or "").strip().lower()
    if not arg:
        status = "✅ ON" if _cached_trivia_enabled else "❌ OFF"
        return await event.reply(
            f"🧠 <b>Trivia Auto-Spawn:</b> {status}\n"
            f"<i>Every group gets a random {TRIVIA_OPTION_COUNT}-option question roughly every "
            f"{TRIVIA_SPAWN_MIN_MSGS}-{TRIVIA_SPAWN_MAX_MSGS} messages, at a random difficulty:</i>\n"
            f"<code>{trivia_difficulty_list_text()}</code>\n\n"
            f"<b>Usage:</b> <code>/triviaspawn on</code> / <code>/triviaspawn off</code>\n"
            f"<b>Testing:</b> <code>/ftrivia [difficulty] [golden]</code> — e.g. <code>/ftrivia hard golden</code>",
            parse_mode='html'
        )
    if arg not in ("on", "off"):
        return await event.reply("❌ <code>/triviaspawn on</code> ဒါမှမဟုတ် <code>/triviaspawn off</code> လိုပဲ ရိုက်ပါ။", parse_mode='html')
    _cached_trivia_enabled = (arg == "on")
    try:
        await bot_settings_col.update_one(
            {"_id": "trivia_spawn_enabled"},
            {"$set": {"enabled": _cached_trivia_enabled}},
            upsert=True
        )
    except Exception as e:
        print(f"triviaspawn toggle persist error: {e}")
    await event.reply(f"✅ <b>Trivia Auto-Spawn is now {'ON ✅' if _cached_trivia_enabled else 'OFF ❌'}</b>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]ftrivia(?:@\w+)?(?:\s+(\S+))?(?:\s+(\S+))?$', 'bot1')))
async def force_trivia_by_owner(event):
    if event.sender_id != OWNER_ID: return
    if event.chat_id in pending_trivia_quiz:
        return await event.reply("⚠️ ဒီချက်မှာ Trivia တစ်ခုကို လက်ရှိမေးနေဆဲပါ။", parse_mode='html')
    raw_args = [a for a in (event.pattern_match.group(1), event.pattern_match.group(2)) if a]
    force_golden = any(a.strip().lower() == "golden" for a in raw_args)
    difficulty_args = [a for a in raw_args if a.strip().lower() != "golden"]
    raw_arg = difficulty_args[0] if difficulty_args else ""
    forced = normalize_trivia_difficulty_arg(raw_arg) if raw_arg else None
    if raw_arg and not forced:
        return await event.reply(
            f"❌ Unknown difficulty. Usage: <code>/ftrivia [{'|'.join(TRIVIA_DIFFICULTY_ORDER)}] [golden]</code>",
            parse_mode='html'
        )
    await trigger_trivia_spawn(event.chat_id, forced_difficulty=forced, force_golden=force_golden)

# ---- /addtrivia [difficulty]: owner-only, step-by-step authoring of ONE question. DM-only so
# nobody in the group sees the answer being typed. Difficulty defaults to Normal. For many
# questions at once use /addtriviabulk. ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addtrivia(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def add_trivia_handler(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_private:
        return await event.reply(
            "⚠️ <b>Please DM me /addtrivia</b> — questions are authored privately so nobody in the group sees the answer being typed.",
            parse_mode='html'
        )
    raw_diff = event.pattern_match.group(1) or ""
    difficulty = normalize_trivia_difficulty_arg(raw_diff) if raw_diff else TRIVIA_LEGACY_DIFFICULTY
    if not difficulty:
        return await event.reply(
            f"❌ Unknown difficulty. Usage: <code>/addtrivia [{'|'.join(TRIVIA_DIFFICULTY_ORDER)}]</code>",
            parse_mode='html'
        )
    dcfg = TRIVIA_DIFFICULTY_CONFIG[difficulty]
    option_labels = [chr(ord('A') + i) for i in range(TRIVIA_OPTION_COUNT)]
    try:
        async with bot1.conversation(event.chat_id, timeout=300) as conv:
            await conv.send_message(
                f"🧠 <b>New Trivia Question — {dcfg['emoji']} {dcfg['label']}</b>\n\n"
                "Send me the <b>question</b> as plain text.\n\n"
                "Send /cancel anytime to stop.",
                parse_mode='html'
            )
            q_msg = await conv.get_response()
            if (q_msg.raw_text or "").strip().lower() == "/cancel":
                return await conv.send_message("❌ Cancelled.")
            question_text = (q_msg.raw_text or "").strip()
            if not question_text:
                return await conv.send_message("❌ I need question text. Cancelled — run /addtrivia again.")

            options = []
            for label in option_labels:
                await conv.send_message(f"✏️ Send <b>Option {label}</b>:", parse_mode='html')
                opt_msg = await conv.get_response()
                opt_text = (opt_msg.raw_text or "").strip()
                if opt_text.lower() == "/cancel":
                    return await conv.send_message("❌ Cancelled.")
                if not opt_text:
                    return await conv.send_message("❌ Empty option. Cancelled — run /addtrivia again.")
                options.append(opt_text)

            await conv.send_message(
                f"✅ Which option is <b>correct</b>? Reply with {', '.join(option_labels[:-1])}, or {option_labels[-1]}.",
                parse_mode='html'
            )
            correct_msg = await conv.get_response()
            correct_letter = (correct_msg.raw_text or "").strip().upper()
            if correct_letter == "/CANCEL":
                return await conv.send_message("❌ Cancelled.")
            if correct_letter not in option_labels:
                return await conv.send_message(f"❌ That's not one of {'/'.join(option_labels)}. Cancelled — run /addtrivia again.")
            correct_index = option_labels.index(correct_letter)

            await trivia_bank_col.insert_one({
                "question": question_text,
                "options": options,
                "correct_index": correct_index,
                "difficulty": difficulty,
                "created_by": event.sender_id,
                "created_at": time.time(),
            })

            preview = f"❓ <b>{escape_html(question_text)}</b>\n\n" + "\n".join(
                f"{lbl}. {escape_html(opt)}" + (" ✅" if i == correct_index else "")
                for i, (lbl, opt) in enumerate(zip(option_labels, options))
            )
            await conv.send_message(preview, parse_mode='html')
            await conv.send_message(
                f"✅ <b>Saved!</b> Added to the {dcfg['emoji']} <b>{dcfg['label']}</b> trivia rotation — "
                f"💰 <code>{dcfg['ccm_min']}-{dcfg['ccm_max']}</code> ccm for a correct answer.",
                parse_mode='html'
            )
    except asyncio.TimeoutError:
        await event.reply("⌛ <b>Timed out waiting for your answer.</b> Run /addtrivia again.", parse_mode='html')
    except Exception as e:
        print(f"add_trivia_handler error: {e}")
        await event.reply(f"❌ <b>Something went wrong:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')

# ---- 🌸 Host pictures: /addtriviamedia, /listtriviamedia, /deltriviamedia (owner-only) ----
# Stored as Bot-API-style file ids (tl_utils.pack_bot_file_id) in trivia_media_col — they stay
# valid for this bot, so nothing needs re-uploading after a restart/redeploy. Each trivia
# spawn picks one at random; with none stored, trivia is text-only exactly as before.
def _trivia_media_kind_label(kind):
    return {"photo": "🖼 photo", "gif": "🎞 GIF", "video": "🎬 video"}.get(kind, kind)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addtriviamedia(?:@\w+)?$', 'bot1')))
async def add_trivia_media_handler(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_private:
        return await event.reply("⚠️ <b>Please DM me /addtriviamedia</b>", parse_mode='html')
    added = 0
    try:
        async with bot1.conversation(event.chat_id, timeout=300) as conv:
            await conv.send_message(
                f"🌸 <b>Add {escape_html(TRIVIA_HOST_NAME)}'s trivia pictures</b>\n\n"
                "Send me photos, GIFs or videos — <b>as many as you like, one after another</b>. "
                "One random item is shown with each trivia question.\n\n"
                "Send <b>/done</b> when you're finished, or /cancel to stop.\n"
                "<i>Tip: send them as photos/GIFs, not as files.</i>",
                parse_mode='html'
            )
            while True:
                resp = await conv.get_response()
                text = (resp.raw_text or "").strip().lower()
                if text in ("/done", "/cancel"):
                    break
                media = resp.photo or resp.gif or resp.video
                if not media:
                    await resp.reply("❌ That's not a photo, GIF or video. Send another one, or /done.")
                    continue
                kind = "photo" if resp.photo else ("gif" if resp.gif else "video")
                try:
                    file_id = tl_utils.pack_bot_file_id(media)
                    await trivia_media_col.insert_one({
                        "file_id": file_id, "kind": kind,
                        "created_by": event.sender_id, "created_at": time.time(),
                    })
                    added += 1
                    await resp.reply(f"✅ Saved ({_trivia_media_kind_label(kind)}) — {added} added so far. Send more, or /done.")
                except Exception as e:
                    print(f"addtriviamedia save error: {e}")
                    await resp.reply(f"❌ Couldn't save that one: <code>{escape_html(str(e))}</code>", parse_mode='html')
            total = await trivia_media_col.count_documents({})
            await conv.send_message(
                f"🌸 <b>Done!</b> Added <code>{added}</code> this time — <code>{total}</code> in the trivia rotation now.",
                parse_mode='html'
            )
    except asyncio.TimeoutError:
        total = await trivia_media_col.count_documents({})
        await event.reply(f"⌛ <b>Timed out.</b> Added <code>{added}</code> — <code>{total}</code> in the rotation now.", parse_mode='html')
    except Exception as e:
        print(f"add_trivia_media_handler error: {e}")
        await event.reply(f"❌ <b>Something went wrong:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]listtriviamedia(?:@\w+)?(?:\s+(\d+))?$', 'bot1')))
async def list_trivia_media_handler(event):
    if event.sender_id != OWNER_ID: return
    items = await trivia_media_col.find({}, {"kind": 1, "file_id": 1}).sort("created_at", 1).to_list(length=None)
    num_arg = event.pattern_match.group(1)
    if num_arg:
        n = int(num_arg)
        if n < 1 or n > len(items):
            return await event.reply(f"❌ No item #{n}. There are {len(items)}.", parse_mode='html')
        item = items[n - 1]
        try:
            return await bot1.send_file(event.chat_id, item["file_id"], caption=f"#{n} — {_trivia_media_kind_label(item.get('kind'))}\nDelete: /deltriviamedia {n}")
        except Exception as e:
            return await event.reply(f"❌ Couldn't send #{n}: <code>{escape_html(str(e))}</code>", parse_mode='html')
    if not items:
        return await event.reply("🌸 <b>No trivia pictures yet.</b>\nAdd some with /addtriviamedia — trivia stays text-only until then.", parse_mode='html')
    kinds = Counter(i.get("kind", "?") for i in items)
    breakdown = " · ".join(f"{_trivia_media_kind_label(k)} {c}" for k, c in kinds.items())
    await event.reply(
        f"🌸 <b>Trivia pictures: {len(items)}</b>\n{breakdown}\n\n"
        f"<b>Preview:</b> <code>/listtriviamedia [number]</code>\n"
        f"<b>Delete:</b> <code>/deltriviamedia [number]</code> or <code>/deltriviamedia all confirm</code>",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]deltriviamedia(?:@\w+)?\s+(\S+)(?:\s+(\S+))?$', 'bot1')))
async def del_trivia_media_handler(event):
    if event.sender_id != OWNER_ID: return
    first = event.pattern_match.group(1).lower()
    if first == "all":
        count = await trivia_media_col.count_documents({})
        if (event.pattern_match.group(2) or "").lower() != "confirm":
            return await event.reply(
                f"⚠️ <b>This deletes ALL {count} trivia picture(s).</b>\nRun <code>/deltriviamedia all confirm</code> to confirm.",
                parse_mode='html'
            )
        result = await trivia_media_col.delete_many({})
        return await event.reply(f"🗑️ Removed <code>{result.deleted_count}</code> picture(s). Trivia is text-only again.", parse_mode='html')
    if not first.isdigit():
        return await event.reply("❌ Expected a number, or <code>all confirm</code>.", parse_mode='html')
    n = int(first)
    items = await trivia_media_col.find({}, {"_id": 1}).sort("created_at", 1).to_list(length=None)
    if n < 1 or n > len(items):
        return await event.reply(f"❌ No item #{n}. There are {len(items)}.", parse_mode='html')
    await trivia_media_col.delete_one({"_id": items[n - 1]["_id"]})
    await event.reply(f"🗑️ Removed #{n}. <code>{len(items) - 1}</code> left.", parse_mode='html')

# ---- Bulk question import ----
def parse_bulk_trivia_text(raw_text):
    """Parses pipe-delimited bulk trivia text, ONE question per line:
    'Question | Option 1 | Option 2 | Option 3 | Option 4 | 1'  (last field = 1-4 or A-D).
    Blank lines and lines starting with # are skipped. Returns (valid_docs, parse_errors)."""
    expected_fields = 1 + TRIVIA_OPTION_COUNT + 1
    letter_map = {chr(ord('A') + i): i for i in range(TRIVIA_OPTION_COUNT)}
    valid = []
    parse_errors = []
    for line_no, raw_line in enumerate(raw_text.splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        parts = [p.strip() for p in line.split("|")]
        if len(parts) != expected_fields:
            parse_errors.append((line_no, raw_line, f"expected {expected_fields} parts, got {len(parts)}"))
            continue
        question = parts[0]
        options = parts[1:1 + TRIVIA_OPTION_COUNT]
        correct_raw = parts[-1]
        if not question or any(not opt for opt in options):
            parse_errors.append((line_no, raw_line, "question/option text can't be empty"))
            continue
        correct_norm = correct_raw.strip().upper()
        correct_index = None
        if correct_norm.isdigit() and 1 <= int(correct_norm) <= TRIVIA_OPTION_COUNT:
            correct_index = int(correct_norm) - 1
        elif correct_norm in letter_map:
            correct_index = letter_map[correct_norm]
        if correct_index is None:
            digits = "/".join(str(i + 1) for i in range(TRIVIA_OPTION_COUNT))
            parse_errors.append((line_no, raw_line, f"last field must be {digits} or A-D"))
            continue
        valid.append({"question": question, "options": options, "correct_index": correct_index})
    return valid, parse_errors

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]addtriviabulk(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def add_trivia_bulk_handler(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_private:
        return await event.reply("⚠️ <b>Please DM me /addtriviabulk</b>", parse_mode='html')
    difficulty = normalize_trivia_difficulty_arg(event.pattern_match.group(1) or "")
    if not difficulty:
        return await event.reply(
            f"📦 <b>Bulk-add Trivia questions</b>\n\n"
            f"<b>Usage:</b> <code>/addtriviabulk [difficulty]</code>\n"
            f"<b>Difficulty:</b> {' / '.join(TRIVIA_DIFFICULTY_ORDER)}",
            parse_mode='html'
        )
    cfg = TRIVIA_DIFFICULTY_CONFIG[difficulty]
    try:
        async with bot1.conversation(event.chat_id, timeout=600) as conv:
            await conv.send_message(
                f"📦 <b>Bulk Add Trivia — {cfg['emoji']} {cfg['label']}</b>\n\n"
                f"Send me ALL your questions now (as a message or a .txt file), <b>one per line</b>:\n"
                f"<code>Question | Option 1 | Option 2 | Option 3 | Option 4 | 1</code>\n"
                f"<i>Last field = the correct option (1-4 or A-D).</i>\n\n"
                f"Send /cancel to stop.",
                parse_mode='html'
            )
            resp = await conv.get_response()
            if (resp.raw_text or "").strip().lower() == "/cancel":
                return await conv.send_message("❌ Cancelled.")
            if resp.document:
                try:
                    file_bytes = await bot1.download_media(resp, file=bytes)
                    raw_text = file_bytes.decode('utf-8-sig', errors='replace')  # -sig: strips the BOM Windows Notepad adds
                except Exception as e:
                    return await conv.send_message(f"❌ Couldn't read that file: <code>{escape_html(str(e))}</code>", parse_mode='html')
            else:
                raw_text = resp.raw_text or ""
            if not raw_text.strip():
                return await conv.send_message("❌ That was empty. Cancelled.")

            valid, parse_errors = parse_bulk_trivia_text(raw_text)
            existing_questions = set()
            try:
                existing_docs = await trivia_bank_col.find(
                    _trivia_diff_query(difficulty), {"_id": 0, "question": 1}
                ).to_list(length=None)
                existing_questions = {d["question"].strip().lower() for d in existing_docs}
            except Exception as e:
                print(f"addtriviabulk existing-dedup lookup error: {e}")

            to_insert = []
            seen_in_batch = set()
            skipped_dupes = 0
            for doc in valid:
                key = doc["question"].strip().lower()
                if key in existing_questions or key in seen_in_batch:
                    skipped_dupes += 1
                    continue
                seen_in_batch.add(key)
                doc["difficulty"] = difficulty
                doc["created_by"] = event.sender_id
                doc["created_at"] = time.time()
                to_insert.append(doc)

            inserted_count = 0
            if to_insert:
                try:
                    result = await trivia_bank_col.insert_many(to_insert)
                    inserted_count = len(result.inserted_ids)
                except Exception as e:
                    return await conv.send_message(f"❌ Insert failed: <code>{escape_html(str(e))}</code>", parse_mode='html')

            summary = f"✅ <b>Added {inserted_count} question(s) to {cfg['emoji']} {cfg['label']}.</b>\n"
            if skipped_dupes:
                summary += f"⏭️ Skipped {skipped_dupes} duplicate question(s).\n"
            if parse_errors:
                shown = parse_errors[:15]
                err_lines = "\n".join(f"  Line {ln}: {reason}" for ln, _raw, reason in shown)
                more = f"\n  ...and {len(parse_errors) - 15} more" if len(parse_errors) > 15 else ""
                summary += f"❌ <b>{len(parse_errors)} line(s) had problems:</b>\n<code>{escape_html(err_lines + more)}</code>\n"
            await conv.send_message(summary, parse_mode='html')
    except asyncio.TimeoutError:
        await event.reply("⌛ <b>Timed out.</b> Run /addtriviabulk again.", parse_mode='html')
    except Exception as e:
        print(f"add_trivia_bulk_handler error: {e}")
        await event.reply(f"❌ <b>Something went wrong:</b> <code>{escape_html(str(e))}</code>", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]listtriviabank(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def list_trivia_bank_handler(event):
    if event.sender_id != OWNER_ID: return
    raw_arg = event.pattern_match.group(1) or ""
    if not raw_arg:
        lines = []
        for d in TRIVIA_DIFFICULTY_ORDER:
            dcfg = TRIVIA_DIFFICULTY_CONFIG[d]
            custom_count = await trivia_bank_col.count_documents(_trivia_diff_query(d))
            static_count = len(TRIVIA_QUESTION_BANK.get(d) or [])
            lines.append(f"{dcfg['emoji']} <b>{dcfg['label']}:</b> {custom_count} custom + {static_count} built-in = <code>{custom_count + static_count}</code>")
        return await event.reply("🧠 <b>Trivia Question Bank — Overview</b>\n\n" + "\n".join(lines), parse_mode='html')
    difficulty = normalize_trivia_difficulty_arg(raw_arg)
    if not difficulty:
        return await event.reply(f"❌ Unknown difficulty. Usage: <code>/listtriviabank [{'|'.join(TRIVIA_DIFFICULTY_ORDER)}]</code>", parse_mode='html')
    cfg = TRIVIA_DIFFICULTY_CONFIG[difficulty]
    custom = await trivia_bank_col.find(_trivia_diff_query(difficulty), {"question": 1}).sort("created_at", 1).to_list(length=None)
    shown = custom[:30]
    lines = [f"<code>{i + 1}.</code> {escape_html(q['question'][:70])}" for i, q in enumerate(shown)]
    more = f"\n<i>...and {len(custom) - 30} more.</i>" if len(custom) > 30 else ""
    await event.reply(
        f"🧠 <b>Custom {cfg['emoji']} {cfg['label']} Trivia ({len(custom)})</b>\n" +
        ("\n".join(lines) if lines else "<i>None yet.</i>") + more,
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]deltriviabank(?:@\w+)?\s+(\S+)\s+(\S+)(?:\s+(\S+))?$', 'bot1')))
async def del_trivia_bank_handler(event):
    if event.sender_id != OWNER_ID: return
    difficulty = normalize_trivia_difficulty_arg(event.pattern_match.group(1))
    if not difficulty:
        return await event.reply("❌ Unknown difficulty.", parse_mode='html')
    second_arg = event.pattern_match.group(2)
    if second_arg.lower() == "all":
        third_arg = (event.pattern_match.group(3) or "").lower()
        cfg = TRIVIA_DIFFICULTY_CONFIG[difficulty]
        count = await trivia_bank_col.count_documents(_trivia_diff_query(difficulty))
        if third_arg != "confirm":
            return await event.reply(
                f"⚠️ <b>This deletes ALL {count} question(s) in {cfg['emoji']} {cfg['label']}.</b>\n"
                f"Run <code>/deltriviabank {difficulty.lower()} all confirm</code> to confirm.",
                parse_mode='html'
            )
        result = await trivia_bank_col.delete_many(_trivia_diff_query(difficulty))
        return await event.reply(f"🗑️ <b>Wiped {cfg['emoji']} {cfg['label']}:</b> <code>{result.deleted_count}</code> question(s) removed.", parse_mode='html')
    if not second_arg.isdigit():
        return await event.reply("❌ Expected a question number, or 'all'.", parse_mode='html')
    position = int(second_arg)
    custom = await trivia_bank_col.find(_trivia_diff_query(difficulty), {"question": 1}).sort("created_at", 1).to_list(length=None)
    if position < 1 or position > len(custom):
        return await event.reply(f"❌ No question #{position} in {difficulty}.", parse_mode='html')
    target = custom[position - 1]
    await trivia_bank_col.delete_one({"_id": target["_id"]})
    await event.reply(f"🗑️ <b>Removed:</b> {escape_html(target['question'][:80])}", parse_mode='html')



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
MEDIA_IDENTIFY_CACHE_TTL = 604800  # 7 days — POSITIVE matches only, see find_character_by_media below
# 🩹 FIX (2026-09, owner report — /w says "not recognized" on a character that IS in the roster
# and DOES have a synced/warmed phash): a "no match" result used to be cached under the SAME
# 7-day TTL as a real match. If /w was ever tried on a piece of media before that character was
# imported (or before its phash/import briefly failed), that single negative result stuck around
# for a FULL WEEK — nothing in the codebase ever clears a None entry early (see the orphan-cleanup
# in warm_media_identity_cache_from_db below, which only ever touches entries with a real char_id).
# So a later successful /syncfromcatch + /warmmediacache changed nothing: find_character_by_media
# short-circuits on the cached None BEFORE it ever re-downloads/re-hashes/re-scans, so the fix
# never even gets a chance to run. Negative results now expire in minutes instead of a week.
MEDIA_IDENTIFY_NEGATIVE_CACHE_TTL = 300  # 5 minutes
_MEDIA_ID_CACHE = {}  # media_key -> (char_id_or_None, cached_at)

def get_media_identity_key(media_msg):
    """A stable identifier for the exact underlying Telegram file behind this message's
    photo/video — used to cache /who results so the SAME reposted/forwarded file doesn't pay
    the full download+hash+scan cost every single time a different person asks about it.
    Deliberately NOT Message.file.id: that's Telethon's old Bot-API-style file-ID wrapper,
    which Telethon's own FAQ says is unmaintained, 'may not work', and 'will be removed in
    future versions'. The raw MTProto photo.id / document.id used here is what Telegram itself
    assigns per uploaded file and is what actually stays identical across forwards/reposts of
    the exact same file — a screenshot or re-compression is legitimately a NEW file (new id)
    and correctly gets its own fresh hash rather than a wrongly-reused cache entry."""
    if media_msg.photo:
        return f"photo:{media_msg.photo.id}"
    if media_msg.document:
        return f"doc:{media_msg.document.id}"
    return None

async def _persist_media_identity(key, char_id, storage_msg_id=None):
    """Best-effort write of one file-identity -> char_id mapping to Mongo (see
    media_identity_col). Never raises — a failed write only means that one entry gets
    re-derived after the next restart instead of loading instantly."""
    try:
        await media_identity_col.update_one(
            {"_id": key},
            {"$set": {"char_id": char_id, "storage_msg_id": storage_msg_id, "updated_at": time.time()}},
            upsert=True
        )
    except Exception as e:
        print(f"⚠️ media identity persist failed for {key}: {e}")

def _schedule_persist_media_identity(key, char_id, storage_msg_id=None):
    """Fire-and-forget wrapper so sync call sites (prewarm_media_identity_cache) can persist too."""
    try:
        asyncio.get_running_loop().create_task(_persist_media_identity(key, char_id, storage_msg_id))
    except RuntimeError:
        pass  # no running loop (shouldn't happen inside a handler) — in-memory entry still works

async def load_media_identity_cache_from_db():
    """🗂️ THE fix for "after every deploy I have to wait for the media cache to fill" (2026-09):
    _MEDIA_ID_CACHE used to be in-memory only, so a deploy wiped it and /who had to download +
    hash media from scratch until warm_media_identity_cache_from_db had crawled the whole
    roster again. The mapping (raw Telegram photo/document id -> char_id) is stable across
    restarts, so it's now persisted in media_identity_col and read back here with ONE Mongo
    query at boot — /who resolves every previously-seen file instantly, before the bot has even
    finished connecting to Telegram. Returns how many entries were loaded."""
    loaded = 0
    now = time.time()
    async for doc in media_identity_col.find({}, {"char_id": 1}):
        if doc.get("char_id"):
            _MEDIA_ID_CACHE[doc["_id"]] = (doc["char_id"], now)
            loaded += 1
    return loaded

def prewarm_media_identity_cache(stored_msg, char_id):
    """⚡ PERF FIX (owner report — /who on a repost of catch_bot's own media is still slow even
    though characters_base_col already has this exact character's phash on file): every import
    path forwards media by REFERENCE (file=<original message's media object>), never by
    re-downloading + re-uploading raw bytes — see store_character_from_check /
    auto_import_character_from_catchbot / add_character / addspecial_ingest_handler. That means
    the copy we just stored in SPECIFIC_CONTROL_GROUP shares the EXACT SAME underlying MTProto
    photo.id/document.id as whatever it was forwarded from (catch_bot's own reply, its channel
    post, etc.) — not just a visually-identical copy, the literal same file Telegram-side.

    _MEDIA_ID_CACHE (used by find_character_by_media, i.e. /who) was previously only warmed
    REACTIVELY — the first time someone actually replied /who to a given file. So even for a
    character whose phash has been sitting in the database for ages, the very FIRST /who anyone
    ever ran against a repost of it still paid the full download+hash+scan cost, once, before
    the cache could kick in for everyone after. Calling this right after every import means
    that same file's identity is registered the moment it enters the roster — the very first
    /who on a repost of it (from catch_bot, from a channel, from anywhere) can already resolve
    as a plain dict lookup, with nothing to download at all.

    💾 UPDATE (2026-09): this registration is now also written to Mongo (media_identity_col), so
    it survives restarts — see load_media_identity_cache_from_db."""
    try:
        key = get_media_identity_key(stored_msg)
        if key:
            _MEDIA_ID_CACHE[key] = (char_id, time.time())
            _schedule_persist_media_identity(key, char_id, getattr(stored_msg, "id", None))
    except Exception:
        pass  # cache warming must never break an import

async def warm_media_identity_cache_from_db(progress_status=None, force=False):
    """Backfills _MEDIA_ID_CACHE (and its persistent copy in media_identity_col) for the roster.

    🩹 REWORKED (2026-09, owner report — "after every deploy I have to wait for the media cache
    to fill up"): this used to re-crawl the WHOLE roster from Telegram on every boot, because
    the cache it fills only lived in memory. Two changes:
      1. The cache is persisted (see load_media_identity_cache_from_db), so a normal boot only
         has to fetch the characters that are NOT indexed yet — usually none, sometimes the
         handful imported since the last run. `force=True` (the manual /warmmediacache) still
         re-crawls everything.
      2. Every fetched entry is written to Mongo in the same pass, in bulk.
    Batch-fetches up to 200 messages per Telegram API call (get_messages' own limit); a
    FloodWaitError is waited out and retried instead of dooming that batch (the older version
    treated the very first flood wait as "skip this batch forever" and ended up warming one
    batch's worth out of thousands). Orphans — index entries whose character was /delchar'd —
    are dropped on the way."""
    docs = await characters_base_col.find({}, {"char_id": 1, "storage_msg_id": 1, "_id": 0}).to_list(length=None)
    roster_ids = {d["char_id"] for d in docs if d.get("char_id")}

    # Drop index entries whose character no longer exists (memory + Mongo).
    orphans = [k for k, v in list(_MEDIA_ID_CACHE.items()) if v[0] and v[0] not in roster_ids]
    if orphans:
        for k in orphans:
            _MEDIA_ID_CACHE.pop(k, None)
        try:
            await media_identity_col.delete_many({"_id": {"$in": orphans}})
        except Exception as e:
            print(f"⚠️ media identity orphan cleanup failed: {e}")

    # 🩹 FIX (2026-09, see MEDIA_IDENTIFY_NEGATIVE_CACHE_TTL above): a manual FULL re-crawl
    # (force=True, i.e. the owner running /warmmediacache — typically right after a big
    # /syncfromcatch) is exactly the moment any leftover "no match" results from BEFORE this
    # batch of characters existed should be thrown away too, not just left to time out on their
    # own. Negatives already expire fast on their own now, but there's no reason to make the
    # owner wait even those few minutes right after they've just fixed the roster.
    if force:
        stale_negatives = [k for k, v in list(_MEDIA_ID_CACHE.items()) if v[0] is None]
        for k in stale_negatives:
            _MEDIA_ID_CACHE.pop(k, None)
        if stale_negatives:
            print(f"🚀 [media cache] Cleared {len(stale_negatives)} stale 'not recognized' cache entries before re-indexing.")

    covered = set() if force else {v[0] for v in _MEDIA_ID_CACHE.values() if v[0]}
    todo = [d for d in docs if d.get("storage_msg_id") and d.get("char_id") and d["char_id"] not in covered]
    id_to_char = {d["storage_msg_id"]: d["char_id"] for d in todo}
    all_ids = list(id_to_char.keys())
    if not all_ids:
        print(f"🚀 [media cache] All {len(roster_ids)} characters already indexed (loaded from Mongo) — nothing to warm.")
        return 0, 0

    warmed = 0
    total_batches = max(1, (len(all_ids) + 199) // 200)
    for batch_num, i in enumerate(range(0, len(all_ids), 200), start=1):
        batch_ids = all_ids[i:i + 200]
        messages = None
        for attempt in range(5):  # absorbs normal flood waits; caps out so a persistent, non-flood failure still moves on instead of looping forever
            try:
                messages = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=batch_ids)
                break
            except FloodWaitError as e:
                print(f"⏳ [media cache] FloodWait on batch {batch_num}/{total_batches}: sleeping {e.seconds}s before retrying...")
                await asyncio.sleep(e.seconds + 1)
            except Exception as e:
                print(f"⚠️ warm_media_identity_cache_from_db: batch {batch_num}/{total_batches} fetch failed: {type(e).__name__}: {e}")
                await asyncio.sleep(2)
        ops = []
        if messages:
            for m in messages:
                if not m:
                    continue  # storage message deleted from SPECIFIC_CONTROL_GROUP — nothing to warm
                char_id = id_to_char.get(m.id)
                if not char_id:
                    continue
                key = get_media_identity_key(m)
                if key:
                    _MEDIA_ID_CACHE[key] = (char_id, time.time())
                    ops.append(UpdateOne(
                        {"_id": key},
                        {"$set": {"char_id": char_id, "storage_msg_id": m.id, "updated_at": time.time()}},
                        upsert=True
                    ))
                    warmed += 1
        if ops:
            try:
                await media_identity_col.bulk_write(ops, ordered=False)
            except Exception as e:
                print(f"⚠️ media identity bulk persist failed (batch {batch_num}): {e}")
        if progress_status:
            try:
                await progress_status.edit(f"⏳ Warming /who's file-identity cache... {warmed}/{len(all_ids)} (batch {batch_num}/{total_batches})")
            except Exception:
                pass
        await asyncio.sleep(0.3)  # gentle pacing between batches — avoids tripping FloodWait in the first place
    print(f"🚀 [media cache] Indexed {warmed}/{len(all_ids)} characters' file identities (persisted to Mongo) — /who on a repost of any of them resolves as a plain dict lookup.")
    return warmed, len(all_ids)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]warmmediacache$', 'bot1')))
async def warm_media_cache_command(event):
    """Manual FULL re-crawl of the file-identity index (force=True) — mainly useful right after
    a big /syncfromcatch or /xbotimportall run. A normal boot no longer needs it: the index is
    persisted in Mongo and only genuinely new characters are fetched (see
    _startup_media_identity_warm)."""
    if event.sender_id != OWNER_ID: return
    status = await event.reply("⏳ Re-indexing /who's file identities from the whole roster...")
    warmed, total = await warm_media_identity_cache_from_db(progress_status=status, force=True)
    await status.edit(
        f"✅ Indexed {warmed}/{total} characters. Reposts of their stored media now resolve "
        f"instantly via /who — no download or hashing needed.\n"
        f"💾 Saved to Mongo — survives restarts, no need to run this after a deploy."
    )

# ---- Boot-time sequence for the /who index + roster cache. Replaces the old bare
# asyncio.create_task(warm_media_identity_cache_from_db()) in start_system(), which had a
# race: it was scheduled BEFORE bot1 had connected/signed in, so every one of its
# get_messages() calls failed instantly with "Cannot send requests while disconnected", was
# swallowed by the per-batch except, and the "startup warm-up" silently warmed nothing at all
# — leaving the owner to babysit /warmmediacache after every deploy. ----
BOT1_READY = None  # asyncio.Event, created in start_system(), set by run_bot1_forever once bot1 is signed in

async def _startup_media_identity_warm():
    try:
        loaded = await load_media_identity_cache_from_db()
        print(f"🚀 [media cache] Loaded {loaded} persisted file identities from Mongo — /who can already resolve them, no wait.")
    except Exception as e:
        print(f"⚠️ [media cache] could not load persisted file identities: {type(e).__name__}: {e}")
    try:
        await get_all_characters_cached()  # roster in memory before the first /who or spawn check needs it
    except Exception as e:
        print(f"⚠️ [media cache] roster preload failed: {e}")
    if BOT1_READY is not None:
        try:
            await asyncio.wait_for(BOT1_READY.wait(), timeout=600)
        except asyncio.TimeoutError:
            print("⚠️ [media cache] bot1 never became ready within 10 minutes — skipping the Telegram-side warm-up.")
            return
    await asyncio.sleep(5)  # let the reconnect settle and any burst of post-deploy traffic pass first
    try:
        await warm_media_identity_cache_from_db()
    except Exception as e:
        print(f"⚠️ [media cache] warm-up failed: {type(e).__name__}: {e}")

_HASH_INDEX = {"src": None, "entries": [], "exact": {}}

def _get_hash_index(characters_list):
    """([(hash_as_int, char_doc), ...], {hash_as_int: first char_doc with that hash}) for the
    given roster list, rebuilt only when the roster list object itself changes (i.e. after a
    refresh/invalidation — see get_all_characters_cached), never per request."""
    if _HASH_INDEX["src"] is characters_list:
        return _HASH_INDEX["entries"], _HASH_INDEX["exact"]
    entries, exact = [], {}
    for char in characters_list:
        char_hash = char.get("photo_phash")
        if not char_hash:
            continue
        try:
            value = int(char_hash, 16)
        except Exception:
            continue
        entries.append((value, char))
        exact.setdefault(value, char)
    _HASH_INDEX["src"] = characters_list
    _HASH_INDEX["entries"] = entries
    _HASH_INDEX["exact"] = exact
    return entries, exact

async def find_character_by_media(media_msg):
    """Core perceptual-hash character lookup — given a Telethon message with a photo/video,
    returns the best-matching character doc (or None). Shared by _identify_media_and_reply
    (the /who-style public lookup) and add_artist_handler's reply-based shortcut.

    🩹 PERF FIX (owner report — /who takes several seconds on anything that isn't bot1's own
    live spawn): checks an in-memory cache keyed by the raw Telegram file id FIRST, before
    touching the download/hash/scan pipeline at all. The very first /who on a brand-new file
    still pays the full cost (that part is unavoidable — nothing can know what an image
    contains without looking at it), but every subsequent /who on that SAME file — the common
    case for a reposted or forwarded spawn image that several different people ask about — now
    resolves from a plain dict lookup instead of re-downloading and re-hashing from scratch."""
    # ⏱️ TEMP DIAGNOSTICS — see the matching note in compute_phash_for_message. This times the
    # cache check, the roster fetch, and the scan loop separately, on top of that function's own
    # download/hash breakdown, so a still-slow /who is fully accounted for start to finish.
    t_start = time.time()
    media_key = get_media_identity_key(media_msg)
    if media_key:
        cached = _MEDIA_ID_CACHE.get(media_key)
        if cached:
            cached_char_id, cached_at = cached
            # 🩹 See MEDIA_IDENTIFY_NEGATIVE_CACHE_TTL above — a "no match" is trusted for a much
            # shorter window than a real match, so a stale negative can't outlive a fresh sync/warm.
            ttl = MEDIA_IDENTIFY_CACHE_TTL if cached_char_id is not None else MEDIA_IDENTIFY_NEGATIVE_CACHE_TTL
            if (time.time() - cached_at) >= ttl:
                cached = None
        if cached:
            cached_char_id = cached[0]
            if cached_char_id is None:
                print(f"⏱️ find_character_by_media: cache hit (no match) in {time.time() - t_start:.2f}s")
                return None
            # Re-check against the live (still-cached-separately) character list rather than
            # trusting the id blindly — if that character was /delchar'd since we cached this,
            # fall through and recompute fresh instead of returning a dangling reference.
            # ⚡ O(1) lookup (was a scan over the whole ~7000-character roster on EVERY cache hit —
            # and cache hits are now the common case, since the file-identity index persists across restarts)
            char = await get_character_by_id_cached(cached_char_id)
            if char is not None:
                print(f"⏱️ find_character_by_media: cache hit ({cached_char_id}) in {time.time() - t_start:.2f}s")
                return char

    try:
        incoming_hash = await compute_phash_for_message(media_msg)
    except Exception as e:
        print(f"find_character_by_media hash error: {e}")
        return None
    t_hashed = time.time()
    if not incoming_hash:
        return None
    characters_list = await get_all_characters_cached()
    t_roster = time.time()
    try:
        incoming_int = int(incoming_hash, 16)
    except Exception:
        return None
    # ⚡ PERF (2026-09): the roster's hashes are parsed from hex to int ONCE per roster refresh
    # (see _get_hash_index), not once per comparison per request — this used to re-run int(hex)
    # ~7000 times on every single uncached /who. An exact (distance-0) match, the usual case
    # for a repost, is a plain dict lookup; only a near-miss falls through to the popcount
    # scan. Same result as before either way: first character in roster order wins ties.
    hash_entries, hash_exact = _get_hash_index(characters_list)
    best_match, best_distance = None, IDENTIFY_HAMMING_THRESHOLD + 1
    exact_hit = hash_exact.get(incoming_int)
    if exact_hit is not None:
        best_match, best_distance = exact_hit, 0
    else:
        for char_int, char in hash_entries:
            dist = _bit_count(incoming_int ^ char_int)
            if dist < best_distance:
                best_distance, best_match = dist, char
    t_scanned = time.time()
    print(f"⏱️ find_character_by_media (roster={len(characters_list)}, best_distance={best_distance}): "
          f"hash_stage={t_hashed - t_start:.2f}s, roster_fetch={t_roster - t_hashed:.2f}s, "
          f"scan={t_scanned - t_roster:.2f}s, TOTAL={t_scanned - t_start:.2f}s")

    if media_key:
        _MEDIA_ID_CACHE[media_key] = (best_match["char_id"] if best_match else None, time.time())
        if best_match:
            # 💾 Persist positive matches so this exact file is instant after the next deploy too
            # (a "no match" stays memory-only — the roster may gain that character later).
            _schedule_persist_media_identity(media_key, best_match["char_id"])
    return best_match

async def _identify_media_and_reply(event, media_msg):
    user_id = event.sender_id
    is_cd, _ = await is_on_cooldown(user_id, "identify_repost", IDENTIFY_COOLDOWN_SECONDS)
    if is_cd:
        return

    # ✅ STEP 1: ကိုယ်ပိုင် Database ကို အရင်ဆုံး စစ်ပါ (ဒါက ပိုတိကျပြီး forward path နဲ့ အတူတူပါ)
    best_match = await find_character_by_media(media_msg)
    if best_match:
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
            fuck_command = f"/fuck {best_match['name']}"
            catch_command = f"/catch {best_match['name']}"
            reveal_text = (
                f"<b>ငါတွေ့ပီ 🔎</b>\n\n"
                f"<b>Name:</b> <b>{escape_html(best_match['name'])}</b>\n"
                f"🔖 <b>Character ID:</b> <code>{display_char_id(best_match['char_id'])}</code>\n"
                f"🍹 <b>Anime:</b> {escape_html(best_match.get('category', '?'))}\n"
                f"{rarity_emoji} <b>Rarity:</b> {best_match.get('rarity', '?')}\n"
                f"{event_display}\n"
                f"{artist_line(best_match)}\n\n"
                f"<code>{escape_html(catch_command)}</code>\n\n"
                f"Have a good life."
            )
            if not await reply_with_copy_buttons(
                event, reveal_text,
                [[("🤍 /fuck", fuck_command), (" /catch ", catch_command)]],
                location="identify_media_copy_buttons"
            ):
                await event.reply(
                    reveal_text + f"\n\n<code>{escape_html(fuck_command)}</code>\n<code>{escape_html(catch_command)}</code>",
                    parse_mode='html'
                )
        except Exception as e:
            print(f"identify reply error: {e}")
        return

    # ✅ STEP 2: ကိုယ်ပိုင် DB မှာ မတွေ့ရင် "This one isn't recognized" ပြန်ပါ (cross-bot lookup
    # removed — /catch and /fuck media is identical now, no need to guess which other bot a
    # spawn "belongs" to)
    return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')

# ---- /who (aliases: /w, /waifu) ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:who|w|waifu)(?:@\w+)?$', 'bot1')))
async def who_reveal_handler(event):
    user_id = event.sender_id
    chat_id = event.chat_id
    # 🩹 CHANGED (per owner request): /who, /w, /waifu are now exempt from the spam-mute —
    # a spam-muted user can still identify a spawn, they just still can't claim it (/fuck
    # stays blocked below in catch_handler). No mute check here anymore.

    # 🩹 CHANGED (per owner request): used to skip entirely when this was a reply to ANOTHER
    # bot's own message — added earlier to avoid bot1 chiming in on a different collector
    # bot's spawn in shared groups. That skip is now removed: a direct .w/.who reply to
    # another bot's media went completely silent (not even "This one isn't recognized"),
    # while forwarding the same media first and replying to the forward worked fine — an
    # inconsistent, confusing gap. Every reply (bot sender or human sender) now falls
    # through the same way below, and either gets recognized from our own DB or gets the
    # normal "not recognized" reply. A bare /who with no reply (e.g. media-as-caption) is
    # unaffected either way and still works as before.
    if event.is_reply:
        replied_msg = await event.get_reply_message()
        if not replied_msg:
            return

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
            # 🕵️ ANTI-SNIPE: a SEPARATE bot with admin in the group auto-replies to .w/.who
            # with the name the moment anyone asks — code here can't stop that bot from
            # answering, so instead the reveal text below appends CATCH_REQUIRED_SUFFIX (see
            # its comment near normalize_name) to the commands it hands out. The rival bot
            # doesn't know that suffix is required and will never include it, so its answers
            # keep failing catch_handler's check while ours keep working.
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
                reveal_lines += [
                    "",
                    f"<code>/fuck {escape_html(char_name)}{CATCH_REQUIRED_SUFFIX}</code>",
                    f"<code>/catch {escape_html(char_name)}{CATCH_REQUIRED_SUFFIX}</code>",
                    "",
                    "…say it, and I'm yours."
                ]
                reveal_text = "\n".join(reveal_lines)
                # 🩹 FIX (2026-09, owner report — "copy buttons don't show up"): see
                # reply_with_copy_buttons — the deployed Telethon (1.45.0 / layer 229) has no
                # KeyboardButtonCopy, so the buttons are now sent through the Bot API instead.
                if not await reply_with_copy_buttons(
                    event, reveal_text,
                    [[
                        (f"🤍 it's me, {char_name}", f"/fuck {char_name}{CATCH_REQUIRED_SUFFIX}"),
                        ("/catch", f"/catch {char_name}{CATCH_REQUIRED_SUFFIX}"),
                    ]],
                    location="who_reveal_copy_buttons"
                ):
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

XBOT_IDENTIFY_HAMMING_THRESHOLD = 20  # 🩹 FIX: was 30 — loose enough that two genuinely
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

# 🩹 FIX (per owner report — CNFT characters failing checksync): map_catch_bot_rarity above
# deliberately excludes the 3 CNFT tiers (see CNFT_TIERS' comment) since /addchar's numeric
# picker must never grow CNFT options. But CNFT cards DO legitimately show up in a live
# ".check <id>" reply once they've already been added via /addspecial — catch_bot happily
# reports back whatever rarity IT has on file for that id, CNFT included. The two shapes seen
# in practice:
#   1) The full subtier text, e.g. "💠 RARITY: CNFT SS" — classify_rarity already matches this
#      fine against RARITY_TIERS, so just look the classified tier up in CNFT_RARITY_INFO.
#   2) A BARE "CNFT" with no SS/S/A suffix at all (seen on at least some cards/renders) —
#      classify_rarity can't tell which of the 3 subtiers that is, and neither can we. Rather
#      than guess (or, worse, silently downgrading an already-correctly-tiered CNFT card to
#      COMMON on every resync), this keeps whatever CNFT subtier that char_id is ALREADY
#      stored as, if it exists. Only returns None (truly unrecognized) when neither applies —
#      i.e. a BRAND NEW character whose only rarity signal is a bare, subtier-less "CNFT".
def _resolve_check_rarity(rarity_raw: str, existing_char_doc: Optional[dict]) -> Optional[dict]:
    """Resolves catch_bot's raw .check/sync rarity text to an r_info dict ({"name","value"}),
    the same shape RARITY_NUM_MAP entries have. Tries the normal 9-tier mapping first, then
    falls back to CNFT handling (see block comment above). Returns None if genuinely
    unrecognized — callers are responsible for their own 'unrecognized rarity, defaulted to
    lowest tier' reporting + fallback in that case (RARITY_NUM_MAP[str(len(_NON_CNFT_TIERS))],
    i.e. COMMON — NOT len(RARITY_TIERS), which now overshoots RARITY_NUM_MAP's 1-9 keys since
    the 3 CNFT tiers were appended to RARITY_TIERS)."""
    rarity_num = map_catch_bot_rarity(rarity_raw)
    if rarity_num:
        return RARITY_NUM_MAP[rarity_num]
    tier = classify_rarity(rarity_raw)
    if tier in CNFT_TIERS:
        return CNFT_RARITY_INFO[tier]
    if "CNFT" in (rarity_raw or "").translate(_FANCY_TO_PLAIN).upper():
        if existing_char_doc and existing_char_doc.get("rarity_tier") in CNFT_TIERS:
            existing_tier = existing_char_doc["rarity_tier"]
            return {
                "name": existing_char_doc.get("rarity") or CNFT_RARITY_INFO[existing_tier]["name"],
                "value": existing_char_doc.get("currency_value", CNFT_RARITY_INFO[existing_tier]["value"])
            }
    return None

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
        prewarm_media_identity_cache(forwarded_msg, char_id)
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
    # 🩹 PERF FIX (owner report — /who is still slow for anything that isn't bot1's own live
    # spawn even with Redis gone entirely): xbot_hashes_col has grown into the thousands after
    # repeated /xbotscan and /xbotresync runs across every monitored channel's full history —
    # this loop used to keep comparing against EVERY remaining document even after already
    # finding a perfect (distance-0) match, when nothing left in the collection could possibly
    # beat that. Breaking out the moment distance hits 0 is always correct (0 is the best any
    # Hamming distance can ever be) and turns the common case — the exact same spawn image
    # getting reposted and re-checked many times, which is most of real /who traffic — from a
    # full scan of the whole collection into stopping the instant the right entry is reached.
    best_match, best_distance = None, XBOT_IDENTIFY_HAMMING_THRESHOLD + 1
    try:
        hash_value_int = int(hash_value, 16)
    except Exception:
        hash_value_int = None
    for item in all_hashes:
        if hash_value_int is not None:
            try:
                dist = _bit_count(hash_value_int ^ int(item.get("hash") or "", 16))
            except Exception:
                dist = 999
        else:
            dist = hamming_distance(hash_value, item.get("hash"))
        if dist < best_distance:
            best_distance, best_match = dist, item
            if best_distance == 0:
                break
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

XBOT_MEDIA_IDENTIFY_CACHE_TTL = 3600  # 1 hour — see get_media_identity_key/_xbot_identify_fallback_and_reply below
_XBOT_MEDIA_ID_CACHE = {}  # media_key -> ({"name":..., "source_bot":...} or None, cached_at)

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
    the same/near-identical artwork for a character could return the wrong bot's entry.

    🩹 PERF FIX (same class of issue as find_character_by_media's own media-id cache above):
    a busy group commonly has SEVERAL different players reply "/who"/.w to the exact same
    other-bot spawn image within the same spawn window, racing to catch it. Before this, EVERY
    one of those calls re-downloaded the media from Telegram and re-hashed it from scratch —
    get_cached_xbot_lookup only cached the hash->character LOOKUP (keyed by the hash value,
    60s TTL), not the download+hash step itself. Checking the raw Telegram file id first (same
    get_media_identity_key used for our own characters) skips straight to the cached name/bot
    on a repeat query, with no download or hashing at all."""
    media_key = get_media_identity_key(media_msg)
    name = source_bot = None
    if media_key:
        cached = _XBOT_MEDIA_ID_CACHE.get(media_key)
        if cached and (time.time() - cached[1]) < XBOT_MEDIA_IDENTIFY_CACHE_TTL:
            cached_doc = cached[0]
            if cached_doc is None:
                return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')
            name, source_bot = cached_doc.get("name"), cached_doc.get("source_bot")

    if not name:
        hash_val = await compute_phash_for_message(media_msg)
        if not hash_val:
            return await event.reply("❓ <b>This one isn't recognized.</b>", parse_mode='html')
        doc = await get_cached_xbot_lookup(hash_val, source_bot_filter=known_source_bot)
        if media_key:
            _XBOT_MEDIA_ID_CACHE[media_key] = (
                {"name": doc["name"], "source_bot": doc.get("source_bot", "unknown")} if doc else None,
                time.time()
            )
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
    reveal_text += "Have a good life."

    if final_command:
        if await reply_with_copy_buttons(
            event, reveal_text, [[(f"📋 {final_command}", final_command)]],
            location="xbot_identify_copy_buttons"
        ):
            return
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
    # 🩹 FIX (owner report — self-heal kept creating BOD10000+ Common copies of characters that
    # already exist in the 1-9999 range with the exact same media): before building a brand new
    # character, check whether this exact Telegram file already belongs to one in the roster (the
    # persisted /who file-identity index). If so, hand that character back instead — the caller
    # then applies the edit it was about (rename / rarity / event / ...) to the REAL character
    # rather than to a fresh duplicate. Anything already duplicated is folded together with
    # /findmediadupes + /mergemediadupes.
    try:
        _media_key = get_media_identity_key(msg)
        if _media_key:
            _existing_id = (_MEDIA_ID_CACHE.get(_media_key) or (None, 0))[0]
            if not _existing_id:
                _idx = await media_identity_col.find_one({"_id": _media_key}, {"char_id": 1})
                _existing_id = (_idx or {}).get("char_id")
            if _existing_id:
                _existing = await characters_base_col.find_one({"char_id": _existing_id})
                if _existing:
                    print(f"🩹 self-heal: media already belongs to {_existing_id} — reusing it instead of creating a duplicate.")
                    return _existing
    except Exception as e:
        print(f"⚠️ self-heal media pre-check failed (falling through to normal creation): {type(e).__name__}: {e}")
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
        r_info = _resolve_check_rarity(rarity_raw, None) if rarity_raw else None
        if not r_info:
            r_info = RARITY_NUM_MAP[str(len(_NON_CNFT_TIERS))]  # lowest of the 9 base tiers (Common)
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

# ==========================================
# 🔁 /syncfromcatch — FULL RE-SYNC STRAIGHT FROM catch_bot VIA ".check <id>", DM'd 1..9999
# through monitor_userbot (a real user account — catch_bot won't answer a bot account).
#
# WHY THIS EXISTS ALONGSIDE THE AUTO-IMPORT ABOVE: auto_import_character_from_catchbot only
# ever sees catch_bot's own log-channel POSTS (new/renamed/rarity-changed/etc.), replayed via
# /xbotimportall. That's naturally lossy — a post the listener was offline for, a bug that
# skipped one, an edit chain that desynced (see _resolve_imported_character's docstring for
# the full story) — all leave SOME characters out of step with what catch_bot actually has on
# file right now. ".check <id>" sidesteps all of that: it asks catch_bot directly, live, "what
# IS true for id N right now" — no history to have missed, nothing to have desynced. Slower
# (has to walk one ID at a time, paced to stay flood-safe) but authoritative, so whatever it
# returns always OVERWRITES whatever we already had for that id, no matter the source.
#
# char_id is deliberately made f"BOD{id}" — catch_bot's own numbering, not our usual random
# _generate_new_char_id() — so a character's ID is identical on both bots after this runs
# (players already only ever see the bare number — see display_char_id/normalize_char_id_input).
# ==========================================
# ==========================================
# 🚦 /channelwork on|off — the real, owner-visible gate on automatic per-message spawning
# (character spawns AND the trivia auto-spawn), replacing what used to be a docs-only promise:
# SYNC_IN_PROGRESS below was already being SET correctly across a /syncfromcatch run, but
# nothing ever actually CHECKED it inside global_message_counter_handler — so "spawns are
# paused during sync" never really happened, and a heavy sync + normal spawn/catch/who traffic
# fighting over the same Mongo/Telegram/userbot-session resources at once is exactly what made
# both feel "extremely slow" (see also the invalidate_character_caches soft-mode fix below,
# the OTHER half of that same slowdown). CHANNEL_WORK_ENABLED is the fix: an explicit,
# persisted flag checked at the top of every automatic per-message spawn trigger, which the
# owner can also flip by hand with /channelwork on / /channelwork off for any other reason
# (maintenance, a big /editchar pass, anything) — it's never JUST an internal sync detail.
# Scope is deliberately narrow: this only gates NEW automatic spawns being created. An
# already-live spawn (character or trivia) can still be caught/answered normally while
# channel work is off — nobody loses a catch mid-flight just because a sync started.
# ==========================================
CHANNEL_WORK_ENABLED = True
_channel_work_changed_at = None    # epoch seconds this was last flipped, either way
_channel_work_changed_reason = None  # "manual" (owner ran /channelwork) or "syncfromcatch"/"syncfromcatch_parallel" (auto-paused)

async def load_channel_work_cache():
    """Loads any persisted /channelwork state at boot (see load_trivia_settings_cache — same
    pattern). If the bot restarted mid-sync, load_and_start_monitor_userbot's resume block
    below re-runs _run_catchbot_sync, which turns this back off itself — so there's no separate
    'was a sync active' check needed here."""
    global CHANNEL_WORK_ENABLED, _channel_work_changed_at, _channel_work_changed_reason
    try:
        doc = await bot_settings_col.find_one({"_id": "channel_work_enabled"})
        if doc is not None and "enabled" in doc:
            CHANNEL_WORK_ENABLED = bool(doc["enabled"])
            _channel_work_changed_at = doc.get("changed_at")
            _channel_work_changed_reason = doc.get("reason")
    except Exception as e:
        print(f"load_channel_work_cache error: {e}")

async def _set_channel_work(enabled: bool, reason: str):
    global CHANNEL_WORK_ENABLED, _channel_work_changed_at, _channel_work_changed_reason
    CHANNEL_WORK_ENABLED = enabled
    _channel_work_changed_at = time.time()
    _channel_work_changed_reason = reason
    try:
        await bot_settings_col.update_one(
            {"_id": "channel_work_enabled"},
            {"$set": {"enabled": enabled, "changed_at": _channel_work_changed_at, "reason": reason}},
            upsert=True
        )
    except Exception as e:
        print(f"_set_channel_work persist error: {e}")

def _format_duration_since(ts):
    if not ts:
        return "unknown"
    secs = max(0, int(time.time() - ts))
    if secs < 60: return f"{secs}s"
    if secs < 3600: return f"{secs // 60}m"
    if secs < 86400: return f"{secs // 3600}h {(secs % 3600) // 60}m"
    return f"{secs // 86400}d {(secs % 86400) // 3600}h"

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]channelwork(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def channel_work_toggle_command(event):
    if event.sender_id != OWNER_ID: return
    arg = (event.pattern_match.group(1) or "").strip().lower()
    if not arg:
        status = "✅ ON — spawns running normally" if CHANNEL_WORK_ENABLED else "⛔ OFF — automatic spawns paused"
        since = _format_duration_since(_channel_work_changed_at)
        reason_note = f" (reason: {_channel_work_changed_reason})" if _channel_work_changed_reason else ""
        sync_note = "\n🔁 A /syncfromcatch run is currently active." if SYNC_IN_PROGRESS else ""
        return await event.reply(
            f"🚦 <b>Channel Work:</b> {status}\n"
            f"⏱ Since: {since} ago{reason_note}{sync_note}\n\n"
            f"<b>Usage:</b> <code>/channelwork on</code> / <code>/channelwork off</code>\n"
            f"<i>Note: /syncfromcatch and /syncfromcatch_parallel turn this off automatically "
            f"while they run, and back on when they finish or are cancelled.</i>",
            parse_mode='html'
        )
    if arg not in ("on", "off"):
        return await event.reply("❌ <code>/channelwork on</code> or <code>/channelwork off</code> only.", parse_mode='html')
    await _set_channel_work(arg == "on", reason="manual")
    await event.reply(
        f"✅ <b>Channel Work is now {'ON ✅ — spawns resumed' if arg == 'on' else 'OFF ⛔ — automatic spawns paused'}</b>",
        parse_mode='html'
    )

CATCH_BOT_ID = 6157455819  # catch_bot's own Telegram user id — used below to verify a reply in
# CATCHBOT_SYNC_CHAT_ID actually came from catch_bot itself, not some other message in that chat
# 🩹 CHANGED (per owner request): ".check <id>" used to always be DM'd straight to CATCH_BOT_ID.
# Now sent to CATCHBOT_SYNC_CHAT_ID instead, which can be any chat — a DM (the old behavior,
# the default below) or a real group catch_bot is active in.
# ⚠️ OWNER: replace the value below with the actual chat_id you want ".check" run in (a
# negative number for a group/supergroup, e.g. -1001234567890). Left equal to CATCH_BOT_ID
# (DM) until you do — I don't have that chat_id to fill in for you.
CATCHBOT_SYNC_CHAT_ID = CATCH_BOT_ID
SYNC_IN_PROGRESS = False   # 🚦 checked at the top of global_message_counter_handler — every
# automatic spawn, in every group, is paused for as long as this is True. A 9999-ID sweep is
# heavy on Mongo/Telegram/the userbot session all by itself; per owner request, nothing should
# also be spawning (and racing catches, quiz gates, etc.) on top of that at the same time.
CATCHBOT_SYNC_DELAY_SECONDS = 2        # pacing between ".check" requests — flood-safe, per owner
CATCHBOT_SYNC_REPLY_TIMEOUT = 20       # seconds to wait for catch_bot's reply before calling this id a miss
# 🩹 CHANGED (per owner request): min/max used to be a hardcoded 1..6756 — catch_bot's own
# profile confirmed its real total was 6756 at the time; ids beyond that were found to just be
# catch_bot re-serving images ALREADY seen at a lower id under a brand-new number (see
# CNFT4971/8115 in the owner's report — same "Eren Yeager" artwork, two different ids, one BELOW
# 6756 and one above). catch_bot's own roster keeps growing though, so both ends are now movable
# by the owner with /syncfromcatchrange <min> <max> instead of editing code — the two numbers
# below are just the starting defaults, overwritten in-memory at boot by
# load_catchbot_sync_range_cache() (see that function, just below) from whatever's saved in
# bot_settings_col, the same pattern load_rarity_weight_cache() uses for /spawnweight.
CATCHBOT_SYNC_MIN_ID = 1
CATCHBOT_SYNC_MAX_ID = 6756

async def load_catchbot_sync_range_cache():
    """Loads any owner-saved /syncfromcatchrange override for CATCHBOT_SYNC_MIN_ID/MAX_ID.
    Called once at boot, BEFORE load_and_start_monitor_userbot() (see start_system()) so that an
    interrupted /syncfromcatch run resumed automatically at boot already sees the right window.
    Until the owner ever runs /syncfromcatchrange, the hardcoded defaults above are left as-is."""
    global CATCHBOT_SYNC_MIN_ID, CATCHBOT_SYNC_MAX_ID
    try:
        doc = await bot_settings_col.find_one({"_id": "catchbot_sync_range"})
        if doc and isinstance(doc.get("min_id"), int) and isinstance(doc.get("max_id"), int) \
                and 1 <= doc["min_id"] <= doc["max_id"]:
            CATCHBOT_SYNC_MIN_ID = doc["min_id"]
            CATCHBOT_SYNC_MAX_ID = doc["max_id"]
    except Exception as e:
        print(f"load_catchbot_sync_range_cache error: {e}")
# 🩹 "...(or until no more replies)": not every id in 1..9999 necessarily HAS a character (gaps
# are normal), so a single miss can't mean "the roster ended here". Only treat it as the end
# once catch_bot has failed to return a real character this many times IN A ROW — high enough
# that an ordinary run of empty/unused ids never trips it by accident, but still low enough to
# save hours of grinding through empty ids once we're genuinely past the end of the roster.
CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP = 60
# If a "miss" reply looks like catch_bot's OWN rate-limit/cooldown notice rather than a genuine
# "no character here", we back off and retry the SAME id instead of counting it as empty —
# wording unknown in advance, so this is a generic keyword sniff, not an exact match.
CATCHBOT_SYNC_COOLDOWN_HINTS = ("cooldown", "please wait", "slow down", "too fast", "try again in", "rate limit", "flood")
CATCHBOT_SYNC_COOLDOWN_BACKOFF = 5
CATCHBOT_SYNC_COOLDOWN_MAX_RETRIES = 3
_catchbot_sync_cancel_requested = False  # checked inside the loop — see /syncfromcatchcancel

# Recognized Unicode ranges for "this character is an emoji" — covers everything catch_bot has
# been observed wrapping event tags in (🥷 🍷 🎉 🟡 🪞 ...) plus the section-marker emoji it uses
# elsewhere (💰 🌎 🎖 ➥). Telegram premium/custom emoji still carry a normal placeholder emoji
# character in the raw text underneath the special rendering, so this catches those too with no
# extra handling needed — event.raw_text always contains that placeholder character.
_EMOJI_RANGES = (
    (0x2190, 0x21FF), (0x2300, 0x23FF), (0x25A0, 0x27BF), (0x2900, 0x29FF),
    (0x2B00, 0x2BFF), (0x1F000, 0x1FFFF),
)
_VARIATION_SELECTORS = ("\uFE0F", "\uFE0E")  # invisible — 🎖 and 🎖️ must compare equal

def _is_emoji_char(ch: str) -> bool:
    cp = ord(ch)
    return any(lo <= cp <= hi for lo, hi in _EMOJI_RANGES)

def _event_wrapper_emoji(line: str) -> Optional[str]:
    """catch_bot always wraps an event tag in the SAME emoji at both the START and END of the
    line — '🥷𝑵𝒊𝒏𝒋𝒂🥷', '🍷𝑪𝒍𝒂𝒔𝒔𝒊𝒄🍷', etc. That exact pairing — not the line's position, and
    not its wording — is the real signal that a line is an event tag. It's what correctly
    tells an event line apart from the Value line that follows when there's NO event: that
    line also starts with an emoji ('💰 Vᴀʟᴜᴇ: 110 ~ 230 CC') but never ENDS with one (it ends
    in a currency code) — so it can never be mistaken for an event tag by this check, even
    though position alone isn't reliable once blank lines get involved.
    Returns the matched wrapper emoji, or None if `line` isn't wrapped this way."""
    if not line or not _is_emoji_char(line[0]) or not _is_emoji_char(line[-1]):
        return None
    lead = ""
    for ch in line:
        if _is_emoji_char(ch):
            lead += ch
        else:
            break
    trail = ""
    for ch in reversed(line):
        if _is_emoji_char(ch):
            trail += ch
        else:
            break
    trail = trail[::-1]
    inner = line[len(lead): len(line) - len(trail)]
    if not inner.strip():
        return None  # the whole line is just emoji, no actual tag text — not a real event
    lead_norm = "".join(c for c in lead if c not in _VARIATION_SELECTORS)
    trail_norm = "".join(c for c in trail if c not in _VARIATION_SELECTORS)
    return lead_norm if lead_norm and lead_norm == trail_norm else None

def parse_catchbot_check(text: str) -> Optional[dict]:
    """Parses catch_bot's DM reply to '.check <id>', e.g.:
        OwO! Check out this character!
        Bleach
        1: Retsu Unohana [🥷]
        (🪞 𝙍𝘼𝙍𝙄𝙏𝙔: Supreme)
        🥷𝑵𝒊𝒏𝒋𝒂🥷
        💰 Vᴀʟᴜᴇ: 5000 ~ 15000 CCT
        🌎 ᴄᴀᴜɢʜᴛ ɢʟᴏʙᴀʟʟʏ: 30 ᴛɪᴍᴇs
        ...
    Returns {"id": int, "name": str, "category": str, "rarity_raw": str, "event": Optional[str]}
    or None if `text` isn't a valid character-card reply at all (catch_bot's "no character at
    this id" / a cooldown notice / anything else that isn't this shape).

    Deliberately SEARCHES for the "<id>: <name>" line instead of assuming a fixed line index,
    and stops looking for rarity the first time it sees a "RARITY" line (any font — see
    classify_rarity's same _FANCY_TO_PLAIN trick) — both make this robust to catch_bot
    prepending an extra line we don't know about yet (a banner, a notice, ...), without needing
    to know its exact wording up front."""
    if not text or not text.strip():
        return None
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    if len(lines) < 3:
        return None
    id_name_idx, char_num, name = None, None, None
    for idx in range(min(4, len(lines))):
        m = re.match(r'^(\d+)\s*:\s*(.+)$', lines[idx])
        if m:
            id_name_idx, char_num, name = idx, int(m.group(1)), m.group(2).strip()
            break
    if id_name_idx is None or not name:
        return None  # no "N: Name" line at all — not a character reply (e.g. "no character at that id")
    category = lines[id_name_idx - 1] if id_name_idx > 0 else "Unknown"
    rarity_raw, rarity_idx = None, None
    for idx in range(id_name_idx + 1, len(lines)):
        plain = lines[idx].translate(_FANCY_TO_PLAIN).upper()
        if "RARITY" in plain and ":" in lines[idx]:
            raw = lines[idx].rsplit(":", 1)[1].strip()
            if raw.endswith(")"):
                raw = raw[:-1].strip()
            rarity_raw, rarity_idx = raw, idx
            break
    if not rarity_raw:
        return None  # no rarity line found — bail rather than guess at a fake rarity
    # Event: an optional single line right after rarity, wrapped in the SAME emoji at both
    # ends (see _event_wrapper_emoji's docstring for why that's the real signal here).
    event = None
    if rarity_idx + 1 < len(lines) and _event_wrapper_emoji(lines[rarity_idx + 1]):
        event = lines[rarity_idx + 1]
    return {"id": char_num, "name": name, "category": category, "rarity_raw": rarity_raw, "event": event}

# ==========================================
# 🎪 EVENT EMOJI MAP + BULK EVENT SET (owner-only)
# ==========================================
# catch_bot ရဲ့ .check reply မှာ character name က "Gojo Satoru [🗡]" ဆိုတဲ့ပုံစံနဲ့ လာတယ် —
# အဲ့ဒီ [emoji] က event ရဲ့ emoji ဖြစ်တယ်။ ဒီ section က owner ကို:
#   1. emoji -> event-name map ကို /seteventmap နဲ့ သတ်မှတ်ခွင့်ပြုတယ်
#   2. /syncevents နဲ့ existing character အားလုံးရဲ့ event field ကို bulk-apply လုပ်တယ်
#   3. (store_character_from_check ထဲ hook ထည့်ထားတာကြောင့် — sweep worker တိုင်း ဒီလမ်းကြောင်းကိုသုံးတယ်)
#      .check import/sync အသစ်တိုင်း auto-map ဖြစ်ပြီး event field ကို map ထဲက name နဲ့
#      တန်းသတ်မှတ်ပေးတယ်
# ==========================================

async def _get_event_emoji_map() -> dict:
    """{emoji: event_name} — bot_settings_col._id='event_emoji_map' ထဲက map ကို ပြန်ပေးတယ်။"""
    doc = await bot_settings_col.find_one({"_id": "event_emoji_map"})
    return dict((doc or {}).get("map", {}))


def _extract_name_emoji_tag(name: str) -> Optional[str]:
    """'Gojo Satoru [🗡]' -> '🗡'. [X] suffix မရှိရင် None။ Variation selector ('🎖' vs '🎖️')
    ကို strip လုပ်ထားတာကြောင့် နှစ်မျိုးလုံး တူတူပဲ match လုပ်ပါတယ် — _normalize_catchbot_name
    ရဲ့ normalization နဲ့ တူတူပါ။"""
    if not name:
        return None
    m = re.search(r'\[([^\]]+)\]\s*$', str(name))
    if not m:
        return None
    cleaned = "".join(c for c in m.group(1).strip() if c not in _VARIATION_SELECTORS)
    return cleaned or None


async def _resolve_event_from_name_emoji(name: str) -> Optional[str]:
    """Name ရဲ့ [emoji] ကို owner map ထဲမှာ ရှာပြီး mapped event name ကို ပြန်ပေးတယ်။
    Name မှာ bracket tag မရှိရင်၊ ဒါမှမဟုတ် tag က map ထဲမှာ မရှိရင် None။"""
    tag = _extract_name_emoji_tag(name)
    if not tag:
        return None
    return (await _get_event_emoji_map()).get(tag)


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]seteventmap(?:@\w+)?(?:\s+([\s\S]*))?$', 'bot1')))
async def set_event_emoji_map_command(event):
    """Owner-only. Name ရဲ့ [emoji] tag -> event name map ကို သတ်မှတ်တယ်။ Format: တစ်လိုင်းကို
    `<emoji> = <event name>` (သို့မဟုတ် `<emoji> <event name>`)။ Command argument အနေနဲ့ရိုက်ထည့်ပါ၊
    ဒါမှမဟုတ် paste လုပ်ထားတဲ့ list တစ်ခုကို reply ပြီး /seteventmap ရိုက်ပါ။

    ဥပမာ:
        🗡 = 🗡Knight🗡
        🥷 = 🥷Ninja🥷
        🍷 = 🍷Classic🍷
    """
    if event.sender_id != OWNER_ID:
        return
    raw = (event.pattern_match.group(1) or "").strip()
    if not raw and event.is_reply:
        replied = await event.get_reply_message()
        raw = (replied.text or "").strip() if replied else ""
    if not raw:
        current = await _get_event_emoji_map()
        if not current:
            return await event.reply(
                "📋 <b>Event emoji map မရှိသေးပါ။</b>\n\n"
                "<b>Usage:</b> တစ်လိုင်းစီ <code>&lt;emoji&gt; = &lt;event name&gt;</code>:\n"
                "<pre>🗡 = 🗡Knight🗡\n🥷 = 🥷Ninja🥷\n🍷 = 🍷Classic🍷</pre>\n"
                "ပြီးရင် <code>/syncevents</code> နဲ့ character အားလုံးရဲ့ event field ကို apply လုပ်ပါ။",
                parse_mode='html'
            )
        lines = [f"  <code>{escape_html(emoji)}</code> → <code>{escape_html(name)}</code>"
                 for emoji, name in current.items()]
        return await event.reply(
            f"📋 <b>Current event emoji map ({len(current)}):</b>\n" + "\n".join(lines) +
            "\n\nအသစ်ပြောင်းချင်ရင် <code>/seteventmap</code> နဲ့ list အသစ်ပို့ပါ၊ apply လုပ်ချင်ရင် <code>/syncevents</code>။",
            parse_mode='html'
        )

    new_map = {}
    invalid = []
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "=" in line:
            emoji_part, name_part = line.split("=", 1)
        else:
            parts = line.split(None, 1)
            if len(parts) < 2:
                invalid.append(line)
                continue
            emoji_part, name_part = parts[0], parts[1]
        emoji_part, name_part = emoji_part.strip(), name_part.strip()
        if not emoji_part or not name_part:
            invalid.append(line)
            continue
        # Variation selectors ကို normalize — 🎖 နဲ့ 🎖️ ကို တူတူ map ဖြစ်စေချင်တာ
        emoji_norm = "".join(c for c in emoji_part if c not in _VARIATION_SELECTORS)
        if not emoji_norm:
            invalid.append(line)
            continue
        new_map[emoji_norm] = name_part

    if not new_map:
        return await event.reply(
            "❌ Valid pair မတွေ့ပါ။ Format: <code>&lt;emoji&gt; = &lt;event name&gt;</code>, တစ်လိုင်းစီ။",
            parse_mode='html'
        )

    await bot_settings_col.update_one(
        {"_id": "event_emoji_map"},
        {"$set": {"map": new_map, "updated_at": time.time()}},
        upsert=True
    )
    preview = "\n".join(f"  <code>{escape_html(e)}</code> → <code>{escape_html(n)}</code>"
                        for e, n in new_map.items())
    reply = (
        f"✅ <b>Event emoji map saved ({len(new_map)} pairs).</b>\n"
        f"<blockquote>{preview}</blockquote>\n"
        f"ယခု <code>/syncevents</code> ကို run ပြီး existing character အားလုံးရဲ့ event ကို apply လုပ်ပါ။"
    )
    if invalid:
        reply += f"\n\n⚠️ {len(invalid)} line(s) ကို parse မလုပ်နိုင်လို့ ချန်ခဲ့တယ်။"
    await event.reply(reply, parse_mode='html')


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncevents(?:@\w+)?$', 'bot1')))
async def sync_events_command(event):
    """Owner-only. characters_base_col ထဲက character တိုင်းကို ဖတ်၊ name ရဲ့ [emoji] tag ကို
    ဆွဲထုတ်၊ owner map ထဲမှာ ရှာပြီး event field ကို mapped name နဲ့ update လုပ်တယ်။
    [emoji] မရှိတဲ့၊ ဒါမှမဟုတ် map ထဲမရှိတဲ့ character တွေကို ဘာမှမထိဘူး။

    "အကုန်လုံး Simple ဖြစ်နေတယ်" ဆိုတဲ့ bulk-sync ပြဿနာကို ဖြေရှင်းတဲ့ command — character
    ရာနဲ့ချီ /editchar လုပ်နေစရာမလိုပဲ map တစ်ခုတည်း သတ်မှတ်ပြီး ဒါကို run ရုံပါ။"""
    if event.sender_id != OWNER_ID:
        return
    emoji_map = await _get_event_emoji_map()
    if not emoji_map:
        return await event.reply(
            "❌ <b>Event emoji map မသတ်မှတ်ရသေးပါ။</b>\n"
            "အရင် <code>/seteventmap</code> သုံးပါ၊ ဥပမာ:\n"
            "<pre>🗡 = 🗡Knight🗡\n🥷 = 🥷Ninja🥷</pre>",
            parse_mode='html'
        )

    status = await event.reply(
        f"⏳ Name ရဲ့ emoji tag တွေကနေ events ကို sync လုပ်နေပါတယ် ({len(emoji_map)} mappings)...",
        parse_mode='html'
    )

    # Character တိုင်းကို တစ်ခါ query မလုပ်ပဲ — event တစ်ခုစီအတွက် char_ids စုပြီး bulk update
    # တစ်ခါတည်း လုပ်တယ်။
    updates_by_event: Dict[str, List[str]] = {}
    unmapped_tags: Counter = Counter()
    total_scanned = 0
    async for char in characters_base_col.find({}, {"char_id": 1, "name": 1, "event": 1}):
        total_scanned += 1
        tag = _extract_name_emoji_tag(char.get("name", ""))
        if not tag:
            continue
        mapped_event = emoji_map.get(tag)
        if not mapped_event:
            unmapped_tags[tag] += 1
            continue
        if char.get("event") != mapped_event:
            updates_by_event.setdefault(mapped_event, []).append(char["char_id"])

    total_updated = 0
    for event_name, char_ids in updates_by_event.items():
        # $in list ကြီးလွန်းရင် query က နှေးတာကြောင့် chunk ဖြတ်တယ်။
        for i in range(0, len(char_ids), 1000):
            chunk = char_ids[i:i + 1000]
            result = await characters_base_col.update_many(
                {"char_id": {"$in": chunk}},
                {"$set": {"event": event_name}}
            )
            total_updated += result.modified_count

    await invalidate_character_caches()

    lines = [
        f"✅ <b>Event sync ပြီးပါပြီ!</b>\n",
        f"📊 <b>Scanned:</b> <code>{total_scanned}</code> characters",
        f"📝 <b>Updated:</b> <code>{total_updated}</code> characters\n",
    ]
    if updates_by_event:
        lines.append("🎪 <b>Event အလိုက်:</b>")
        for event_name, char_ids in sorted(updates_by_event.items(), key=lambda kv: -len(kv[1])):
            lines.append(f"  {escape_html(event_name)} → <code>{len(char_ids)}</code>")
    else:
        lines.append("<i>ဘာမှ update လုပ်စရာမလိုပါ — mapped tag ရှိတဲ့ character တိုင်း event မှန်နေပြီ။</i>")
    if unmapped_tags:
        lines.append(f"\n⚠️ <b>Unmapped tag {len(unmapped_tags)} မျိုး</b> character တွေမှာ တွေ့တယ် (map ထဲမပါ):")
        for tag, count in unmapped_tags.most_common(10):
            lines.append(f"  <code>{escape_html(tag)}</code> × {count} — တကယ့် event ဖြစ်ရင် /seteventmap မှာ ထည့်ပါ")
    await status.edit("\n".join(lines), parse_mode='html')

async def store_character_from_check(info: dict, reply_msg, client=None) -> str:
    """Given parsed .check info (see parse_catchbot_check) and catch_bot's reply message
    itself (for its attached media), forwards the media to SPECIFIC_CONTROL_GROUP for storage
    (via monitor_userbot — the session that actually received reply_msg, so it's the only one
    holding a valid file_reference for it, same reasoning as auto_import_character_from_catchbot
    above), computes its dHash, and upserts characters_base_col keyed on char_id = f"BOD{id}".

    INTENTIONALLY authoritative: if BOD{id} already exists (from an earlier /addchar, an
    earlier /syncfromcatch run, or the log-channel auto-import), this OVERWRITES its name/
    category/rarity/event/media/hash with whatever .check says right now — a live .check
    against catch_bot itself outranks anything we inferred indirectly. spawn_count/spawn_limit/
    created_at are left untouched on an update (only $set with fields we actually have new data
    for), so re-running the sync never resets a character's catch history or CatchLimit.
    Returns "imported" (brand-new char_id) or "updated" (char_id already existed)."""
    char_id = f"BOD{info['id']}"
    existing = await characters_base_col.find_one({"char_id": char_id})
    r_info = _resolve_check_rarity(info["rarity_raw"], existing)
    if not r_info:
        is_cd, _ = await is_on_cooldown(0, "catchbot_sync_bad_rarity", 600)
        if not is_cd:
            await report_system_error(
                "store_character_from_check",
                f"Unrecognized catch_bot rarity '{info['rarity_raw']}' for {char_id} "
                f"({info['name']}) — defaulted to the lowest tier. Fix with /editchar."
            )
        r_info = RARITY_NUM_MAP[str(len(_NON_CNFT_TIERS))]  # lowest of the 9 base tiers (Common)
    # 🎪 Auto-apply owner's emoji->event map when the character name has an [emoji] tag.
    # catch_bot's .check reply sometimes carries the event line as plain text ("Simple") rather
    # than an emoji-wrapped tag, which _event_wrapper_emoji (and so parse_catchbot_check) can't
    # recognize as a real event at all. The name's [emoji] tag is a per-character signal that's
    # always present regardless of that, so it's checked against the owner's map here and takes
    # priority when a mapping exists; falls through to whatever parse_catchbot_check found (or
    # "General") when the tag is absent or unmapped.
    mapped_event = await _resolve_event_from_name_emoji(info["name"])
    resolved_event = mapped_event or info.get("event") or "General"
    while True:
        try:
            forwarded_msg = await asyncio.wait_for(
                send_safe_message(client or monitor_userbot, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media),
                timeout=240
            )
            break
        except FloodWaitError as e:
            print(f"⏳ [catchbot sync] FloodWait forwarding media for {char_id}: sleeping {e.seconds}s...")
            await asyncio.sleep(e.seconds + 1)
    prewarm_media_identity_cache(forwarded_msg, char_id)
    photo_phash = await compute_phash_for_message(reply_msg)
    character_data = {
        "char_id": char_id,
        "name": info["name"],
        "name_normalized": _normalize_catchbot_name(info["name"]),
        "category": info["category"],
        "rarity": r_info["name"],
        "rarity_tier": classify_rarity(r_info["name"]),
        "storage_msg_id": forwarded_msg.id,
        "currency_value": r_info["value"],
        "event": resolved_event,
        "photo_phash": photo_phash,
        "auto_imported_from": "catch_bot",
        "source_rarity": info["rarity_raw"],
        "synced_via_check": True,
        "last_synced_at": time.time(),
    }
    if existing:
        # 🩹 FIX (per owner report): store_character_from_check already overwrote every FIELD
        # (name/category/rarity/event/hash/storage_msg_id) on an existing char_id, but never
        # deleted the OLD forwarded media message in SPECIFIC_CONTROL_GROUP first — so if
        # catch_bot's id got reused for a totally different character (e.g. BOD1234 was
        # "makima", a later /syncfromcatch finds catch_bot's current 1234 is "naruto"), the
        # stale makima media just sat there orphaned forever instead of being cleaned up.
        # Delete it now, before writing the new data in — "old media out, new media in".
        old_storage_msg_id = existing.get("storage_msg_id")
        if old_storage_msg_id and old_storage_msg_id != forwarded_msg.id:
            try:
                await bot1.delete_messages(SPECIFIC_CONTROL_GROUP, [old_storage_msg_id])
            except Exception as e:
                print(f"⚠️ [catchbot sync] failed to delete stale media for {char_id} "
                      f"(old msg {old_storage_msg_id}): {e}")
        await characters_base_col.update_one({"char_id": char_id}, {"$set": character_data})
        outcome = "updated"
    else:
        character_data.update({"spawn_count": 0, "spawn_limit": 0, "created_at": time.time()})
        await characters_base_col.insert_one(character_data)
        outcome = "imported"
    _CHAR_PHOTO_CACHE.pop(char_id, None)
    await invalidate_character_caches(hard=False)  # 🩹 PERF FIX — see invalidate_character_caches docstring
    return outcome

async def _check_one_catchbot_id(char_num: int, client=None) -> str:
    """Sends '.check <char_num>' to catch_bot via monitor_userbot, in CATCHBOT_SYNC_CHAT_ID
    (see that constant above — a DM by default, or a real group once the owner sets it). A
    fresh conversation() is opened per id rather than one held open for the whole 1..9999 run —
    simpler to reason about, sidesteps Conversation's max_messages ceiling over a run this
    long, and makes the cooldown-retry loop below trivial (just re-enter).
    Returns one of:
        'imported' / 'updated' — see store_character_from_check
        'miss'    — no reply within CATCHBOT_SYNC_REPLY_TIMEOUT, or the reply wasn't a valid
                    character card at all (catch_bot has nothing at this id)
        'error'   — unexpected exception; already reported to the owner"""
    for attempt in range(CATCHBOT_SYNC_COOLDOWN_MAX_RETRIES + 1):
        try:
            async with (client or monitor_userbot).conversation(CATCHBOT_SYNC_CHAT_ID, timeout=CATCHBOT_SYNC_REPLY_TIMEOUT) as conv:
                while True:
                    try:
                        await conv.send_message(f".check {char_num}")
                        break
                    except FloodWaitError as e:
                        print(f"⏳ [catchbot sync] FloodWait sending .check {char_num}: sleeping {e.seconds}s...")
                        await asyncio.sleep(e.seconds + 1)
                # 🩹 CHANGED (per owner request): CATCHBOT_SYNC_CHAT_ID can now be a real GROUP
                # instead of a private 1:1 DM with catch_bot — other people/other bots can post
                # in that same chat while we're waiting, so a plain get_response() (which just
                # returns "the next message in this chat," from whoever) is no longer enough on
                # its own. This loops on get_response(), discarding anything NOT actually sent
                # by catch_bot (CATCH_BOT_ID), until either a genuine reply from catch_bot shows
                # up or the overall CATCHBOT_SYNC_REPLY_TIMEOUT budget for this one id runs out.
                # A plain DM (the default) still behaves exactly as before — the only message
                # possible in that chat IS from catch_bot, so this loop exits on the first one.
                deadline = time.time() + CATCHBOT_SYNC_REPLY_TIMEOUT
                reply = None
                while True:
                    remaining = deadline - time.time()
                    if remaining <= 0:
                        break
                    try:
                        candidate = await conv.get_response(timeout=remaining)
                    except asyncio.TimeoutError:
                        break
                    if candidate.sender_id == CATCH_BOT_ID:
                        reply = candidate
                        break
                    # Not catch_bot — someone/something else posted in this chat; keep waiting
                    # on whatever's left of this id's timeout budget instead of counting it.
                if reply is None:
                    return "miss"
            caption = reply.raw_text or ""
            info = parse_catchbot_check(caption)
            if not info:
                if any(hint in caption.lower() for hint in CATCHBOT_SYNC_COOLDOWN_HINTS):
                    print(f"⏳ [catchbot sync] cooldown-looking reply at id {char_num} "
                          f"(attempt {attempt + 1}) — backing off {CATCHBOT_SYNC_COOLDOWN_BACKOFF}s and retrying.")
                    await asyncio.sleep(CATCHBOT_SYNC_COOLDOWN_BACKOFF)
                    continue  # retry the SAME id — it was never actually checked
                return "miss"
            if not (reply.photo or reply.video or reply.document):
                if client is None:
                    await report_system_error(
                        "_check_one_catchbot_id",
                        f"id {char_num}: parsed a valid check reply but it carried no media — skipped."
                    )
                else:  # pool worker: the pool run reports aggregated errors, not one DM per id
                    print(f"⚠️ [sync pool] id {char_num}: valid check reply but no media — skipped.")
                return "error"
            return await store_character_from_check(info, reply, client=client)
        except Exception as e:
            if client is None:
                await report_system_error("_check_one_catchbot_id", f"id {char_num}: {e}")
            else:
                print(f"⚠️ [sync pool] id {char_num}: {type(e).__name__}: {str(e)[:150]}")
            return "error"
    # exhausted the cooldown retries. Single-account sweep: move on as a miss (unchanged). Pool
    # worker: report 'cooldown' instead, so it can never be mistaken for the end of the roster.
    return "cooldown" if client is not None else "miss"

def _catchbot_sync_counts_lines(counts: dict) -> str:
    return (
        f"📨 Checked: {counts.get('checked', 0)}\n"
        f"🆕 Imported: {counts.get('imported', 0)}\n"
        f"🔄 Updated: {counts.get('updated', 0)}\n"
        f"➖ No character at id: {counts.get('misses', 0)}\n"
        f"⚠️ Errors: {counts.get('errors', 0)}"
    )

CATCHBOT_SYNC_HARD_CEILING = 200000  # 🩹 sanity backstop ONLY — see the loop below. Never meant
# to be reached in practice (CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP consecutive misses should
# always end a real run long before this); it just guarantees the loop can't run forever if
# something genuinely pathological happens (e.g. catch_bot answering every single id somehow).

async def _run_catchbot_sync(start_id: int, status_chat_id=None, status_msg_id=None, max_workers=None):
    """The actual sweep, from start_id up to catch_bot's REAL last id — not a fixed number.

    🩹 CHANGED (per owner request — "sync from 1 to whatever catch_bot's actual last id is"):
    this used to stop hard at CATCHBOT_SYNC_MAX_ID (an owner-set number that only reflects
    whatever catch_bot's roster size WAS the last time /syncfromcatchrange was run — anything
    catch_bot added since then was silently never checked). Now the loop itself is open-ended:
    it just keeps going, id after id, and only stops on CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP
    consecutive misses (the same "assume we've run off the end of the roster" signal it always
    used) or a cancel — never on a fixed ceiling. CATCHBOT_SYNC_MAX_ID is auto-extended (in
    memory AND persisted, so /syncfromcatchrange/status/pruneoutofrange all see it too) the
    moment a real character turns up past it, so it keeps tracking catch_bot's ACTUAL current
    extent instead of a number the owner has to remember to bump by hand.

    Resumable (checkpointed to bot_settings_col after every id, same pattern as
    _run_bulk_import above) and safe to kick off either from the /syncfromcatch command or
    automatically at boot if a previous run got interrupted mid-way — see the resume block
    added in load_and_start_monitor_userbot()."""
    global SYNC_IN_PROGRESS, _catchbot_sync_cancel_requested, CATCHBOT_SYNC_MAX_ID
    if SYNC_IN_PROGRESS:
        return  # already running (e.g. resumed at startup right as the owner also fired the command) — never overlap
    SYNC_IN_PROGRESS = True
    _catchbot_sync_cancel_requested = False
    # 🧵 More than one userbot available (or the monitor userbot is gone but workers exist)?
    # Then the shared-queue pool engine below does the sweep — same checkpoint document, same
    # end-of-roster rule, just N accounts pulling ids in parallel. Otherwise: unchanged single-
    # account sweep. SYNC_IN_PROGRESS stays claimed across the hand-off; the pool run clears it.
    try:
        _pool_workers = await _sync_collect_workers(max_workers)
    except Exception as e:
        print(f"⚠️ [sync] couldn't collect workers ({type(e).__name__}: {e}) — single-account sweep")
        _pool_workers = []
    _monitor_ok = bool(monitor_userbot and monitor_userbot.is_connected())
    if _pool_workers and (len(_pool_workers) > 1 or not _monitor_ok):
        return await _run_catchbot_sync_pool(start_id, status_chat_id, status_msg_id, _pool_workers)
    await _set_channel_work(False, reason="syncfromcatch")  # 🚦 real pause now — see CHANNEL_WORK_ENABLED above
    state = await bot_settings_col.find_one({"_id": "catchbot_sync_state"}) or {}
    counts = {
        "checked": state.get("checked", 0), "imported": state.get("imported", 0),
        "updated": state.get("updated", 0), "misses": state.get("misses", 0),
        "errors": state.get("errors", 0),
    }
    await bot_settings_col.update_one(
        {"_id": "catchbot_sync_state"},
        {"$set": {"active": True, "started_at": state.get("started_at", time.time())}},
        upsert=True
    )
    consecutive_misses = 0
    last_id_done = start_id - 1
    last_real_hit_id = state.get("last_real_hit_id", CATCHBOT_SYNC_MIN_ID - 1)
    was_cancelled = False
    try:
        for char_num in range(start_id, CATCHBOT_SYNC_HARD_CEILING + 1):
            if _catchbot_sync_cancel_requested:
                was_cancelled = True
                break
            outcome = await _check_one_catchbot_id(char_num)
            counts["checked"] += 1
            last_id_done = char_num
            if outcome in ("imported", "updated"):
                counts[outcome] += 1
                consecutive_misses = 0
                last_real_hit_id = char_num
                if char_num > CATCHBOT_SYNC_MAX_ID:
                    # 🆕 catch_bot's roster has grown past what we knew about — extend the
                    # window now (persisted) so status/range/pruneoutofrange stay honest even
                    # if this run gets interrupted right after this id.
                    CATCHBOT_SYNC_MAX_ID = char_num
                    await bot_settings_col.update_one(
                        {"_id": "catchbot_sync_range"},
                        {"$set": {"max_id": CATCHBOT_SYNC_MAX_ID}},
                        upsert=True
                    )
            elif outcome == "miss":
                counts["misses"] += 1
                consecutive_misses += 1
            else:  # "error" — transient (network hiccup, forwarding failure, ...); doesn't
                # signal "we've run off the end of the roster", so it never touches the streak.
                counts["errors"] += 1
            await bot_settings_col.update_one(
                {"_id": "catchbot_sync_state"},
                {"$set": {"last_checked_id": last_id_done, "last_real_hit_id": last_real_hit_id, **counts}}
            )
            if status_chat_id and status_msg_id and counts["checked"] % 25 == 0:
                try:
                    await bot1.edit_message(
                        status_chat_id, status_msg_id,
                        f"⏳ <b>Sync running…</b> id <code>{char_num}</code> "
                        f"(last confirmed real id: <code>{last_real_hit_id}</code>)\n"
                        f"{_catchbot_sync_counts_lines(counts)}",
                        parse_mode='html'
                    )
                except Exception:
                    pass
            if consecutive_misses >= CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP:
                print(f"🔁 [catchbot sync] {consecutive_misses} consecutive misses — assuming end "
                      f"of catch_bot's roster around id {char_num} (last real id: {last_real_hit_id}), stopping.")
                break
            await asyncio.sleep(CATCHBOT_SYNC_DELAY_SECONDS)
        else:
            # Only reachable by actually exhausting CATCHBOT_SYNC_HARD_CEILING, which should
            # never happen in normal operation — see that constant's own comment above.
            await report_system_error(
                "_run_catchbot_sync",
                f"Hit the {CATCHBOT_SYNC_HARD_CEILING} hard ceiling without a real end-of-roster "
                f"miss streak — stopping as a safety measure. Last real id seen: {last_real_hit_id}."
            )
    except Exception as e:
        await report_system_error("_run_catchbot_sync", str(e))
    finally:
        SYNC_IN_PROGRESS = False
        await bot_settings_col.update_one({"_id": "catchbot_sync_state"}, {"$set": {"active": False}})
        await _set_channel_work(True, reason="sync finished")  # 🚦 resume automatic spawns

    if was_cancelled:
        summary = (
            f"🛑 <b>Sync stopped</b> at id <code>{last_id_done}</code> "
            f"(checkpoint saved — /syncfromcatch will resume from here)\n"
            f"🎯 Last confirmed real id: <code>{last_real_hit_id}</code>\n"
            f"{_catchbot_sync_counts_lines(counts)}\n"
            f"🚦 Spawns are back on."
        )
    else:
        summary = (
            f"✅ <b>Full catch_bot sync complete!</b> Checked through id <code>{last_id_done}</code>, "
            f"catch_bot's last real character is id <code>{last_real_hit_id}</code>.\n"
            f"{_catchbot_sync_counts_lines(counts)}\n"
            f"🚦 Spawns are back on."
        )
    try:
        if status_chat_id and status_msg_id:
            await bot1.edit_message(status_chat_id, status_msg_id, summary, parse_mode='html')
        else:
            await bot1.send_message(OWNER_ID, summary, parse_mode='html')
    except Exception:
        await bot1.send_message(OWNER_ID, summary, parse_mode='html')

# ------------------------------------------------------------------------------------------
# 🧵 POOL ENGINE — the same sweep as _run_catchbot_sync, but N userbot accounts pull ids from
# ONE shared queue instead of one account walking 1..N alone.
#   • Work-stealing, not fixed ranges: a slow / flood-waited account never holds the others up,
#     and nobody gets a slice of ids past the end of the roster.
#   • Each account is paced individually at CATCHBOT_SYNC_DELAY_SECONDS (its own single-account
#     rate); a cooldown reply from catch_bot backs that account off (doubling, capped at 60s).
#   • An id that hits a cooldown / transient error goes back on the queue for ANY worker
#     (CATCHBOT_SYNC_POOL_ID_RETRIES tries) and is only then reported as failed — never silently
#     counted as a miss, so it can't fake an end-of-roster either.
#   • A worker that fails CATCHBOT_SYNC_POOL_MAX_WORKER_ERRORS times in a row retires itself.
#   • End of roster = CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP ids past the highest real hit, same
#     rule as the single-account sweep. Checkpoint = lowest id below which EVERYTHING is done
#     (the "watermark"), stored in the same catchbot_sync_state doc, so /syncfromcatchstatus and
#     boot-time resume keep working.
# ------------------------------------------------------------------------------------------
CATCHBOT_SYNC_POOL_MAX_WORKER_ERRORS = 5
CATCHBOT_SYNC_POOL_ID_RETRIES = 4
CATCHBOT_SYNC_POOL_CHECKPOINT_EVERY = 1.0   # s
CATCHBOT_SYNC_POOL_STATUS_EVERY = 6.0       # s between status-message edits

async def _sync_collect_workers(max_workers=None):
    """monitor_userbot + the worker pool, connected, de-duplicated by Telegram account.
    At boot the sync can resume before the pool finished loading, so wait for it (≤90s)."""
    for _ in range(90):
        if _worker_pool_loaded:
            break
        await asyncio.sleep(1)
    cands = []
    if monitor_userbot and monitor_userbot.is_connected():
        cands.append((monitor_userbot, "monitor_userbot"))
    cands += list(worker_pool_clients)
    out, seen = [], set()
    for client, label in cands:
        try:
            if not client.is_connected():
                await client.connect()
            me = await client.get_me()
        except Exception as e:
            print(f"⚠️ [sync pool] {label}: unusable ({type(e).__name__}) — skipped")
            continue
        if me.id in seen:
            continue
        seen.add(me.id)
        out.append((client, label))
    if max_workers:
        out = out[:max(1, int(max_workers))]
    if len(out) > 1 and CATCHBOT_SYNC_CHAT_ID != CATCH_BOT_ID:
        # Safety: in a shared GROUP, Conversation.get_response() hands back the next message in
        # the chat from whoever — with several accounts asking at once, one account would pick
        # up catch_bot's answer to ANOTHER account's .check. In a DM every account has its own
        # private chat with catch_bot, so there's no mix-up. Group mode therefore stays single-account.
        print("⚠️ [sync pool] CATCHBOT_SYNC_CHAT_ID is a group chat — using ONE userbot only "
              "(parallel accounts need the default DM with catch_bot so replies can't get mixed up).")
        out = out[:1]
    return out

async def _sync_worker_preflight(client):
    """None = this account is ready for the sweep. Otherwise a short reason string. Checks the
    two things every worker needs: it can see + post in the storage group (media is forwarded
    there BY REFERENCE, so it must be the account that received the .check reply), and it can
    reach catch_bot. Also fixes the usual cause of both failing — a fresh StringSession has an
    empty entity cache — by listing dialogs once."""
    async def _inner():
        if not client.is_connected():
            await client.connect()
        if not await client.is_user_authorized():
            return "session no longer authorized — re-add it"
        async def _known(peer):
            try:
                await client.get_input_entity(peer)
                return True
            except ValueError:
                return False
        if not (await _known(SPECIFIC_CONTROL_GROUP) and await _known(CATCHBOT_SYNC_CHAT_ID)):
            try:
                await client.get_dialogs()
            except Exception as e:
                print(f"⚠️ [sync pool] get_dialogs failed: {type(e).__name__}")
        if not await _known(SPECIFIC_CONTROL_GROUP):
            return "not in the storage group (SPECIFIC_CONTROL_GROUP) — add this account there"
        if not await _known(CATCHBOT_SYNC_CHAT_ID):
            if CATCHBOT_SYNC_CHAT_ID == CATCH_BOT_ID:
                try:   # resolve catch_bot by @username, using what bot1 already knows about it
                    u = await bot1.get_entity(CATCH_BOT_ID)
                    if getattr(u, "username", None):
                        await client.get_entity(u.username)
                except Exception as e:
                    print(f"⚠️ [sync pool] couldn't resolve catch_bot by username: {type(e).__name__}")
            if not await _known(CATCHBOT_SYNC_CHAT_ID):
                return "can't reach catch_bot / the sync chat — open catch_bot from this account once (or join the sync group)"
        if CATCHBOT_SYNC_CHAT_ID == CATCH_BOT_ID:
            hist = await client.get_messages(CATCHBOT_SYNC_CHAT_ID, limit=1)
            if not hist:  # never talked to catch_bot from this account — same /start warm-up the old parallel sync did
                await client.send_message(CATCHBOT_SYNC_CHAT_ID, "/start")
                await asyncio.sleep(1.5)
        m = await client.send_message(SPECIFIC_CONTROL_GROUP, "🔧 worker check")  # real write test…
        try:
            await client.delete_messages(SPECIFIC_CONTROL_GROUP, [m.id])          # …removed straight away
        except Exception:
            pass
        return None
    try:
        return await asyncio.wait_for(_inner(), timeout=180)
    except asyncio.TimeoutError:
        return "timed out while checking"
    except FloodWaitError as e:
        return f"flood wait {e.seconds}s — retry shortly"
    except Exception as e:
        return f"{type(e).__name__}: {str(e)[:80]}"

async def _run_catchbot_sync_pool(start_id: int, status_chat_id, status_msg_id, workers):
    """SYNC_IN_PROGRESS is already claimed by _run_catchbot_sync; cleared in the finally below."""
    global SYNC_IN_PROGRESS, CATCHBOT_SYNC_MAX_ID
    was_cancelled = False
    aborted = None
    tasks, reporter = [], None
    failed_ids: list = []
    skipped: list = []
    usable: list = []
    counts = {"checked": 0, "imported": 0, "updated": 0, "misses": 0, "errors": 0}
    S = {"watermark": start_id, "last_real": CATCHBOT_SYNC_MIN_ID - 1}   # replaced with the full dict below once the run is set up
    t_start = time.time()
    try:
        await _set_channel_work(False, reason="syncfromcatch")
        pre = await asyncio.gather(*[_sync_worker_preflight(c) for c, _l in workers], return_exceptions=True)
        for (c, l), r in zip(workers, pre):
            if r is None:
                usable.append((c, l))
            else:
                skipped.append((l, r if isinstance(r, str) else type(r).__name__))
        if not usable:
            aborted = "no userbot passed the pre-flight check (see /xbotworkers check)"
        state = await bot_settings_col.find_one({"_id": "catchbot_sync_state"}) or {}
        counts.update({k: state.get(k, 0) for k in counts})
        checked_at_start = counts["checked"]
        await bot_settings_col.update_one(
            {"_id": "catchbot_sync_state"},
            {"$set": {"active": True, "started_at": state.get("started_at", time.time()), "workers": len(usable)}},
            upsert=True)
        S.update({"next_id": start_id, "inflight": 0, "done": set(), "hit": start_id - 1,
                  "last_real": state.get("last_real_hit_id", CATCHBOT_SYNC_MIN_ID - 1),
                  "last_ckpt": 0.0, "alive": len(usable)})
        retry_q: list = []

        def _limit():
            return S["hit"] + CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP

        def _take():
            if _catchbot_sync_cancel_requested:
                return None
            if retry_q:
                return retry_q.pop(0)
            if S["next_id"] > _limit() or S["next_id"] > CATCHBOT_SYNC_HARD_CEILING:
                return None
            nid = S["next_id"]
            S["next_id"] += 1
            return (nid, 0)

        async def _checkpoint(force=False):
            now = time.time()
            if not force and now - S["last_ckpt"] < CATCHBOT_SYNC_POOL_CHECKPOINT_EVERY:
                return
            S["last_ckpt"] = now
            try:
                await bot_settings_col.update_one(
                    {"_id": "catchbot_sync_state"},
                    {"$set": {"last_checked_id": S["watermark"] - 1, "last_real_hit_id": S["last_real"],
                              "failed_ids": failed_ids[-500:], **counts}})
            except Exception as e:
                print(f"⚠️ [sync pool] checkpoint write failed: {type(e).__name__}")

        async def _finalize(cid, outcome):
            global CATCHBOT_SYNC_MAX_ID
            counts["checked"] += 1
            if outcome in ("imported", "updated"):
                counts[outcome] += 1
                S["hit"] = max(S["hit"], cid)
                S["last_real"] = max(S["last_real"], cid)
                if cid > CATCHBOT_SYNC_MAX_ID:
                    CATCHBOT_SYNC_MAX_ID = cid
                    try:
                        await bot_settings_col.update_one({"_id": "catchbot_sync_range"},
                                                          {"$set": {"max_id": CATCHBOT_SYNC_MAX_ID}}, upsert=True)
                    except Exception:
                        pass
            elif outcome == "miss":
                counts["misses"] += 1
            else:  # "failed" — retries used up; recorded so it can be redone with /checksync <id>
                counts["errors"] += 1
                failed_ids.append(cid)
            S["done"].add(cid)
            while S["watermark"] in S["done"]:
                S["done"].discard(S["watermark"])
                S["watermark"] += 1
            await _checkpoint()

        async def _worker(idx, client, label):
            errs = 0
            cd_streak = 0
            await asyncio.sleep(idx * CATCHBOT_SYNC_DELAY_SECONDS / max(1, len(usable)))  # spread the first requests out
            while True:
                item = _take()
                if item is None:
                    if _catchbot_sync_cancel_requested or S["inflight"] == 0:
                        return
                    await asyncio.sleep(0.5)   # others still in flight — a hit could extend the roster
                    continue
                cid, attempt = item
                S["inflight"] += 1
                try:
                    outcome = await _check_one_catchbot_id(cid, client=client)
                except asyncio.CancelledError:
                    S["inflight"] -= 1
                    raise
                except Exception as e:
                    print(f"⚠️ [sync pool] {label} id {cid}: {type(e).__name__}: {str(e)[:120]}")
                    outcome = "error"
                S["inflight"] -= 1
                if outcome in ("imported", "updated", "miss"):
                    errs = 0
                    cd_streak = 0
                    await _finalize(cid, outcome)
                else:  # 'cooldown' or 'error' — back on the shared queue for anyone
                    if outcome == "cooldown":
                        cd_streak += 1
                    else:
                        errs += 1
                    if attempt + 1 < CATCHBOT_SYNC_POOL_ID_RETRIES:
                        retry_q.append((cid, attempt + 1))
                    else:
                        await _finalize(cid, "failed")
                    if errs >= CATCHBOT_SYNC_POOL_MAX_WORKER_ERRORS:
                        S["alive"] -= 1
                        print(f"🛑 [sync pool] {label} retired after {errs} errors in a row.")
                        return
                    if outcome == "cooldown":
                        await asyncio.sleep(min(60, CATCHBOT_SYNC_COOLDOWN_BACKOFF * (2 ** min(cd_streak, 4))))
                await asyncio.sleep(CATCHBOT_SYNC_DELAY_SECONDS)

        def _render(final=False):
            elapsed = max(1.0, time.time() - t_start)
            rate = (counts["checked"] - checked_at_start) / elapsed * 60
            eta = ""
            remaining = max(0, CATCHBOT_SYNC_MAX_ID - S["watermark"] + 1)
            if rate > 0 and remaining:
                eta = f" · ~{remaining / rate:.0f} min left to id {CATCHBOT_SYNC_MAX_ID}"
            return (f"⏳ <b>Sync running</b> — <code>{S['alive']}</code>/{len(usable)} userbots\n"
                    f"✅ everything up to id <code>{S['watermark'] - 1}</code> done · last real id <code>{S['last_real']}</code>\n"
                    f"⚡ {rate:.0f} ids/min{eta}\n"
                    f"{_catchbot_sync_counts_lines(counts)}")

        async def _reporter():
            while True:
                await asyncio.sleep(CATCHBOT_SYNC_POOL_STATUS_EVERY)
                if status_chat_id and status_msg_id:
                    try:
                        await bot1.edit_message(status_chat_id, status_msg_id, _render(), parse_mode='html')
                    except Exception:
                        pass

        if usable:
            print(f"🧵 [sync pool] starting at id {start_id} with {len(usable)} userbot(s): "
                  + ", ".join(l for _c, l in usable))
            tasks = [asyncio.create_task(_worker(i, c, l)) for i, (c, l) in enumerate(usable)]
            reporter = asyncio.create_task(_reporter())
            await asyncio.gather(*tasks, return_exceptions=True)
            was_cancelled = _catchbot_sync_cancel_requested
            finished_roster = (not retry_q) and S["next_id"] > _limit()
            if not was_cancelled and not finished_roster:
                aborted = "every userbot retired after repeated errors"
            await _checkpoint(force=True)
    except Exception as e:
        aborted = f"{type(e).__name__}: {e}"
        await report_system_error("_run_catchbot_sync_pool", str(e))
    finally:
        for t in tasks:
            t.cancel()
        if reporter:
            reporter.cancel()
        SYNC_IN_PROGRESS = False
        try:
            await bot_settings_col.update_one({"_id": "catchbot_sync_state"}, {"$set": {"active": False}})
        except Exception:
            pass
        await _set_channel_work(True, reason="sync finished")

    mins = (time.time() - t_start) / 60
    extra = ""
    if skipped:
        extra += "\n⚠️ Skipped userbots:\n" + "\n".join(f"  • {escape_html(l)} — {escape_html(r)}" for l, r in skipped)
    if failed_ids:
        shown = ", ".join(str(i) for i in failed_ids[:30]) + (" …" if len(failed_ids) > 30 else "")
        extra += f"\n❗ Failed ids ({len(failed_ids)}) — redo each with <code>/checksync &lt;id&gt;</code>: <code>{shown}</code>"
    resume_id = S["watermark"]
    if aborted:
        summary = (f"🛑 <b>Sync stopped: {escape_html(aborted)}</b> after {mins:.1f} min.\n"
                   f"Everything up to id <code>{resume_id - 1}</code> is done — continue with <code>/syncfromcatch {resume_id}</code>.\n"
                   f"{_catchbot_sync_counts_lines(counts)}{extra}\n🚦 Spawns are back on.")
    elif was_cancelled:
        summary = (f"🛑 <b>Sync stopped</b> after {mins:.1f} min. Everything up to id <code>{resume_id - 1}</code> is done — "
                   f"continue with <code>/syncfromcatch {resume_id}</code>.\n"
                   f"{_catchbot_sync_counts_lines(counts)}{extra}\n🚦 Spawns are back on.")
    else:
        summary = (f"✅ <b>Full catch_bot sync complete!</b> {len(usable)} userbots · {mins:.1f} min · "
                   f"last real id <code>{S['last_real']}</code>.\n"
                   f"{_catchbot_sync_counts_lines(counts)}{extra}\n🚦 Spawns are back on.")
    try:
        if status_chat_id and status_msg_id:
            await bot1.edit_message(status_chat_id, status_msg_id, summary, parse_mode='html')
        else:
            await bot1.send_message(OWNER_ID, summary, parse_mode='html')
    except Exception:
        try:
            await bot1.send_message(OWNER_ID, summary, parse_mode='html')
        except Exception:
            pass

async def _start_catchbot_sync_from_event(event, explicit_start=None, max_workers=None):
    """Shared by /syncfromcatch and /syncfromcatch_parallel [n]."""
    monitor_ok = bool(monitor_userbot and monitor_userbot.is_connected())
    if not monitor_ok and not worker_pool_clients:
        return await event.reply(
            "❌ No userbot is connected. Use /xbotsetsession (monitor userbot) or "
            "/xbotaddworker &lt;session&gt; first — <code>.check</code> has to be sent from a REAL "
            "user account, catch_bot won't answer a bot account.",
            parse_mode='html'
        )
    if SYNC_IN_PROGRESS:
        return await event.reply(
            "⏳ A /syncfromcatch run is already in progress. Use /syncfromcatchstatus to check "
            "progress, or /syncfromcatchcancel to stop it.",
            parse_mode='html'
        )
    if CSB_RUNNING:
        return await event.reply("⏳ A /csb bulk checksync is running — wait for it (or <code>/csb stop</code>) before starting /syncfromcatch.", parse_mode='html')
    if explicit_start:
        # 🩹 CHANGED: no longer clamped to CATCHBOT_SYNC_MAX_ID on the top end — the sync is
        # open-ended now (see _run_catchbot_sync), so an explicit start past the last-known max
        # is a perfectly normal way to probe further out, not a mistake to correct.
        start_id = max(CATCHBOT_SYNC_MIN_ID, int(explicit_start))
        # Explicit id given — treat as a fresh run from THERE, not a resume: reset counters.
        await bot_settings_col.update_one(
            {"_id": "catchbot_sync_state"},
            {"$set": {"active": True, "last_checked_id": start_id - 1, "checked": 0, "imported": 0,
                       "updated": 0, "misses": 0, "errors": 0, "started_at": time.time()}},
            upsert=True
        )
    else:
        state = await bot_settings_col.find_one({"_id": "catchbot_sync_state"})
        if state and state.get("active") and state.get("last_checked_id"):
            # 🩹 Only clamped on the MIN end now — the owner may have raised the min with
            # /syncfromcatchrange since this checkpoint was saved. No max-side clamp: the sync
            # is open-ended (see _run_catchbot_sync), so resuming past the old max is correct,
            # not something to correct.
            start_id = max(CATCHBOT_SYNC_MIN_ID, state["last_checked_id"] + 1)
        else:
            start_id = CATCHBOT_SYNC_MIN_ID
            await bot_settings_col.update_one(
                {"_id": "catchbot_sync_state"},
                {"$set": {"active": True, "last_checked_id": start_id - 1, "checked": 0, "imported": 0,
                           "updated": 0, "misses": 0, "errors": 0, "started_at": time.time()}},
                upsert=True
            )
    n_accts = (1 if monitor_ok else 0) + len(worker_pool_clients)
    if max_workers:
        n_accts = min(n_accts, int(max_workers))
    status_msg = await event.reply(
        f"⏳ <b>Starting full catch_bot sync</b> from id <code>{start_id}</code> with up to "
        f"<code>{n_accts}</code> userbot(s)...\n"
        f"🚦 Channel Work paused — automatic spawns paused until this finishes (/channelwork to check).\n"
        f"Each account is paced at {CATCHBOT_SYNC_DELAY_SECONDS}s/request; with several loaded (/xbotworkers) "
        f"they share one queue of ids. Open-ended: it keeps going until "
        f"{CATCHBOT_SYNC_CONSECUTIVE_MISS_STOP} consecutive empty ids in a row — i.e. until it "
        f"actually reaches catch_bot's real last id, whatever that currently is. If the bot "
        f"restarts, it'll resume from here automatically next time it boots, or whenever you "
        f"run /syncfromcatch again.",
        parse_mode='html'
    )
    asyncio.create_task(_run_catchbot_sync(start_id, status_chat_id=event.chat_id,
                                           status_msg_id=status_msg.id, max_workers=max_workers))

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncfromcatch(?:\s+(\d+))?(?:@\w+)?$', 'bot1')))
async def sync_from_catch_command(event):
    if event.sender_id != OWNER_ID:
        return
    if is_duplicate_event(event):
        return
    await _start_catchbot_sync_from_event(event, explicit_start=event.pattern_match.group(1))

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncfromcatch_parallel(?:\s+(\d+))?(?:@\w+)?$', 'bot1')))
async def sync_from_catch_parallel_command(event):
    """/syncfromcatch_parallel [n] — same engine as /syncfromcatch, limited to the first n
    userbots. (The old fixed-range version of this command was replaced by the shared-queue
    engine: it split 1..9999 evenly so workers handed ids past the real end sat out a 20s
    timeout per id, its cooldown retry was a no-op inside a for-loop, and it had no checkpoint.)"""
    if event.sender_id != OWNER_ID:
        return
    if is_duplicate_event(event):
        return
    n = event.pattern_match.group(1)
    await _start_catchbot_sync_from_event(event, max_workers=int(n) if n else None)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncfromcatchstatus(?:@\w+)?$', 'bot1')))
async def sync_from_catch_status_command(event):
    if event.sender_id != OWNER_ID:
        return
    state = await bot_settings_col.find_one({"_id": "catchbot_sync_state"})
    if not state:
        return await event.reply("📭 /syncfromcatch has never been run yet.")
    running = ("🟢 running" if SYNC_IN_PROGRESS
               else ("🟡 marked active (will resume on next restart)" if state.get("active") else "⚪ finished"))
    await event.reply(
        f"🔁 <b>Catch Sync Status</b>\n"
        f"Status: {running}\n"
        f"🎯 Started from: <code>{CATCHBOT_SYNC_MIN_ID}</code> · last known real id: <code>{CATCHBOT_SYNC_MAX_ID}</code>\n"
        f"📍 Last checked id: <code>{state.get('last_checked_id', 0)}</code> "
        f"(last confirmed real id: <code>{state.get('last_real_hit_id', '?')}</code>)\n"
        f"{_catchbot_sync_counts_lines(state)}",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncfromcatchrange(?:\s+(\d+)\s+(\d+))?(?:@\w+)?$', 'bot1')))
async def sync_from_catch_range_command(event):
    """Lets the owner set /syncfromcatch's start id and its LAST KNOWN real id — persisted to
    bot_settings_col (see load_catchbot_sync_range_cache, loaded at boot) so it survives a
    restart. Bare /syncfromcatchrange (no numbers) just reports the current numbers.

    🩹 CHANGED: max no longer caps where a sync run stops — the sync is open-ended now (see
    _run_catchbot_sync) and auto-extends this same max value itself the moment it finds a real
    character past it. Setting it by hand here is only useful as a manual override (e.g. after
    /pruneoutofrange, or to force /syncfromcatchstatus's display back down)."""
    global CATCHBOT_SYNC_MIN_ID, CATCHBOT_SYNC_MAX_ID
    if event.sender_id != OWNER_ID:
        return
    new_min_raw, new_max_raw = event.pattern_match.group(1), event.pattern_match.group(2)
    if not new_min_raw:
        return await event.reply(
            f"🔁 Current /syncfromcatch range: <code>{CATCHBOT_SYNC_MIN_ID}-{CATCHBOT_SYNC_MAX_ID}</code>\n"
            f"Use <code>/syncfromcatchrange &lt;min&gt; &lt;max&gt;</code> to change it, e.g. "
            f"<code>/syncfromcatchrange 1 7000</code>.",
            parse_mode='html'
        )
    new_min, new_max = int(new_min_raw), int(new_max_raw)
    if new_min < 1 or new_max < new_min:
        return await event.reply("❌ Need 1 ≤ min ≤ max.")
    if SYNC_IN_PROGRESS:
        return await event.reply(
            "⏳ A /syncfromcatch run is currently in progress — stop it with /syncfromcatchcancel "
            "first, so a run doesn't finish partway through the old window."
        )
    CATCHBOT_SYNC_MIN_ID, CATCHBOT_SYNC_MAX_ID = new_min, new_max
    await bot_settings_col.update_one(
        {"_id": "catchbot_sync_range"},
        {"$set": {"min_id": new_min, "max_id": new_max}},
        upsert=True
    )
    await event.reply(
        f"✅ /syncfromcatch range set to <code>{new_min}-{new_max}</code>.\n"
        f"Run /syncfromcatch to sync it (starts fresh from <code>{new_min}</code> unless you give "
        f"it an explicit start id), or /pruneoutofrange to remove existing BOD ids/cards that now "
        f"fall outside this window.",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]syncfromcatchcancel(?:@\w+)?$', 'bot1')))
async def sync_from_catch_cancel_command(event):
    global _catchbot_sync_cancel_requested
    if event.sender_id != OWNER_ID:
        return
    if not SYNC_IN_PROGRESS:
        return await event.reply("📭 No /syncfromcatch run is currently in progress.")
    _catchbot_sync_cancel_requested = True
    await event.reply(
        "🛑 Marked for stop. It'll finish its current id (within "
        f"~{CATCHBOT_SYNC_REPLY_TIMEOUT}s) and then stop — the checkpoint is saved, so "
        "/syncfromcatch will resume from here next time you run it. Spawns resume immediately once it stops."
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]checksync\s+(\d+)$', 'bot1')))
async def checksync_command(event):
    """Manually re-runs .check <id> -> catch_bot -> store_character_from_check for ONE id on
    demand, instead of waiting for a full /syncfromcatch pass — e.g. to fix a single entry
    whose stored name/media doesn't actually match what catch_bot currently reports for that
    number (a misalignment from the old, non-atomic _generate_new_char_id race — see its
    comment — where the channel listener could have claimed BOD<n> for an unrelated character
    before /syncfromcatch ever got there). Since store_character_from_check always targets
    char_id = f"BOD{id}" and OVERWRITES every field when that id already exists, this is
    naturally self-correcting: whatever was there before (right or wrong) gets replaced with
    catch_bot's current, authoritative answer for that specific number."""
    if event.sender_id != OWNER_ID: return
    if not monitor_userbot or not monitor_userbot.is_connected():
        return await event.reply("❌ Monitor userbot isn't connected. Use /xbotsetsession first.")
    char_num = int(event.pattern_match.group(1))
    status = await event.reply(f"⏳ Sending <code>.check {char_num}</code> to catch_bot...", parse_mode='html')
    outcome = await _check_one_catchbot_id(char_num)
    if outcome in ("imported", "updated"):
        await status.edit(f"✅ <code>BOD{char_num}</code> {outcome} from catch_bot's current data for id {char_num}.", parse_mode='html')
    elif outcome == "miss":
        await status.edit(f"❌ No reply from catch_bot, or id {char_num} isn't a valid character.")
    else:
        await status.edit(f"❌ Error checking id {char_num} — see owner DM / logs for details.")

# ==========================================
# 📦 /csb — BULK /checksync (per owner request)
# ==========================================
# Reply to a message that contains character ids with /csb and every id is re-checked against
# catch_bot — the exact same _check_one_catchbot_id → store_character_from_check pipeline as
# /checksync <id>, so each one imports a new card or OVERWRITES the existing BOD<id> with catch_bot's
# current answer. The ids can be separated by spaces, commas or new lines and may be ranges
# (5670-5690); words like BOD5671 work too. They can also be typed right after the command:
# /csb 5671 5672 6000-6010.
#   • Speed: all connected userbots (monitor + the /xbotaddworker pool) pull ids from ONE shared queue,
#     each paced at CATCHBOT_SYNC_DELAY_SECONDS — the same engine idea as the /syncfromcatch pool.
#   • An id that hits a catch_bot cooldown or a hiccup goes back on the queue for any worker
#     (CSB_RETRIES_PER_ID tries) and only then counts as failed; a worker that errors
#     CATCHBOT_SYNC_POOL_MAX_WORKER_ERRORS times in a row retires itself.
#   • Live progress with a 🛑 Stop button (or /csb stop). /csb retry re-runs only the ids that failed.
#   • Won't start while a full /syncfromcatch is running (and /syncfromcatch won't start while this runs).
#   • Unlike a full sweep it does NOT pause automatic spawns (same as a single /checksync).
CSB_MAX_IDS = 2000
CSB_RETRIES_PER_ID = 3
CSB_PROGRESS_EVERY = 5.0
CSB_RUNNING = False
_csb_cancel = False
_csb_last_failed: list = []

_CSB_RANGE_RE = re.compile(r'(?<!\d)(\d{1,9})\s*(?:-|–|—|~|\.\.)\s*(\d{1,9})(?!\d)')
_CSB_NUM_RE = re.compile(r'(?<!\d)\d{1,9}(?!\d)')

def parse_csb_ids(text, lo=None, hi=None, max_ids=None):
    """Pure. Pulls character ids out of free text. Returns (ids, ignored, truncated):
    ids = unique, in order of appearance, each within lo..hi; ignored = how many numbers were outside
    that window (counts, years, chat ids… that merely look like ids); truncated = the list was cut at max_ids."""
    lo = CATCHBOT_SYNC_MIN_ID if lo is None else lo
    hi = CATCHBOT_SYNC_HARD_CEILING if hi is None else hi
    max_ids = CSB_MAX_IDS if max_ids is None else max_ids
    text = text or ""
    ids, seen, ignored, truncated = [], set(), 0, False

    def add(n):
        nonlocal ignored, truncated
        if n < lo or n > hi:
            ignored += 1
            return
        if n in seen:
            return
        if len(ids) >= max_ids:
            truncated = True
            return
        seen.add(n)
        ids.append(n)

    pos = 0
    for m in re.finditer(_CSB_RANGE_RE.pattern + "|" + _CSB_NUM_RE.pattern, text):
        if m.group(1) is not None and m.group(2) is not None:      # a range like 5670-5690
            a, b = sorted((int(m.group(1)), int(m.group(2))))
            if b - a > max_ids * 5:
                ignored += 1
                continue
            for n in range(a, b + 1):
                add(n)
        else:
            add(int(m.group(0)))
    return ids, ignored, truncated

def fmt_id_ranges(ids, limit=600):
    """[5671, 5672, 5673, 5680] -> '5671-5673, 5680' (kept under `limit` characters)."""
    ids = sorted(set(ids))
    parts, i = [], 0
    while i < len(ids):
        j = i
        while j + 1 < len(ids) and ids[j + 1] == ids[j] + 1:
            j += 1
        parts.append(str(ids[i]) if i == j else f"{ids[i]}-{ids[j]}")
        i = j + 1
    out, used = [], 0
    for k, s in enumerate(parts):
        if used + len(s) + 2 > limit:
            out.append(f"… +{len(parts) - k} more")
            break
        out.append(s)
        used += len(s) + 2
    return ", ".join(out)

def _csb_progress_text(total, done, res, alive, n_workers, elapsed):
    rate = done / max(1.0, elapsed) * 60
    eta = f" · ~{(total - done) / rate:.0f} min left" if rate > 0 and done < total else ""
    return (f"⏳ <b>/csb</b> — <code>{done}</code>/<code>{total}</code> ids · <code>{alive}</code>/{n_workers} userbots\n"
            f"✅ imported <code>{len(res['imported'])}</code> · 🔄 updated <code>{len(res['updated'])}</code> · "
            f"🚫 not found <code>{len(res['miss'])}</code> · ❗ failed <code>{len(res['failed'])}</code>\n"
            f"⚡ {rate:.0f} ids/min{eta}")

def _csb_summary_text(total, res, n_workers, minutes, cancelled, aborted, skipped, remaining):
    head = (f"🛑 <b>/csb stopped</b>" if cancelled else f"❌ <b>/csb stopped: {escape_html(aborted)}</b>" if aborted
            else "✅ <b>/csb complete</b>")
    done = sum(len(v) for v in res.values())
    lines = [f"{head} — <code>{done}</code>/<code>{total}</code> ids · {n_workers} userbot(s) · {minutes:.1f} min"]
    for key, icon, label in (("imported", "✅", "imported (new)"), ("updated", "🔄", "updated"),
                             ("miss", "🚫", "not found on catch_bot"), ("failed", "❗", "failed")):
        if res[key]:
            lines.append(f"{icon} {label} (<code>{len(res[key])}</code>): <code>{fmt_id_ranges(res[key])}</code>")
    if remaining:
        lines.append(f"⏭️ not reached (<code>{len(remaining)}</code>): <code>{fmt_id_ranges(remaining)}</code> — reply /csb with these again")
    if res["failed"]:
        lines.append("↻ <code>/csb retry</code> re-runs only the failed ids.")
    if skipped:
        lines.append("⚠️ Skipped userbots:\n" + "\n".join(f"  • {escape_html(l)} — {escape_html(r)}" for l, r in skipped))
    return "\n".join(lines)

async def _run_csb(ids, status_chat_id, status_msg_id, workers):
    """CSB_RUNNING is already claimed by csb_command; cleared in the finally below."""
    global CSB_RUNNING, _csb_cancel, _csb_last_failed
    t0 = time.time()
    res = {"imported": [], "updated": [], "miss": [], "failed": []}
    S = {"i": 0, "inflight": 0, "alive": 0}
    retry_q, usable, skipped = [], [], []
    tasks, reporter, aborted = [], None, None
    _csb_cancel = False
    try:
        if len(workers) > 1:
            pre = await asyncio.gather(*[_sync_worker_preflight(c) for c, _l in workers], return_exceptions=True)
            for (c, l), r in zip(workers, pre):
                if r is None:
                    usable.append((c, l))
                else:
                    skipped.append((l, r if isinstance(r, str) else type(r).__name__))
        else:
            usable = list(workers)
        if not usable:
            aborted = "no userbot passed the pre-flight check (see /xbotworkers check)"
        else:
            S["alive"] = len(usable)

            def _take():
                if _csb_cancel:
                    return None
                if retry_q:
                    return retry_q.pop(0)
                if S["i"] < len(ids):
                    cid = ids[S["i"]]
                    S["i"] += 1
                    return (cid, 0)
                return None

            def _done_count():
                return sum(len(v) for v in res.values())

            async def _worker(idx, client, label):
                errs = cd_streak = 0
                await asyncio.sleep(idx * CATCHBOT_SYNC_DELAY_SECONDS / max(1, len(usable)))
                while True:
                    item = _take()
                    if item is None:
                        if _csb_cancel or S["inflight"] == 0:
                            return
                        await asyncio.sleep(0.5)      # others still in flight — one of them may re-queue an id
                        continue
                    cid, attempt = item
                    S["inflight"] += 1
                    try:
                        outcome = await _check_one_catchbot_id(cid, client=client)
                    except asyncio.CancelledError:
                        S["inflight"] -= 1
                        raise
                    except Exception as e:
                        print(f"⚠️ [csb] {label} id {cid}: {type(e).__name__}: {str(e)[:120]}")
                        outcome = "error"
                    S["inflight"] -= 1
                    if outcome in ("imported", "updated", "miss"):
                        errs = cd_streak = 0
                        res[outcome].append(cid)
                    else:                                  # 'cooldown' / 'error' -> back on the shared queue for anyone
                        if outcome == "cooldown":
                            cd_streak += 1
                        else:
                            errs += 1
                        if attempt + 1 < CSB_RETRIES_PER_ID:
                            retry_q.append((cid, attempt + 1))
                        else:
                            res["failed"].append(cid)
                        if errs >= CATCHBOT_SYNC_POOL_MAX_WORKER_ERRORS:
                            S["alive"] -= 1
                            print(f"🛑 [csb] {label} retired after {errs} errors in a row.")
                            return
                        if outcome == "cooldown":
                            await asyncio.sleep(min(60, CATCHBOT_SYNC_COOLDOWN_BACKOFF * (2 ** min(cd_streak, 4))))
                    await asyncio.sleep(CATCHBOT_SYNC_DELAY_SECONDS)

            async def _reporter():
                while True:
                    await asyncio.sleep(CSB_PROGRESS_EVERY)
                    try:
                        await bot1.edit_message(status_chat_id, status_msg_id,
                                                _csb_progress_text(len(ids), _done_count(), res, S["alive"], len(usable), time.time() - t0),
                                                parse_mode='html', buttons=[[Button.inline("🛑 Stop", data="csb_stop")]])
                    except Exception:
                        pass

            tasks = [asyncio.create_task(_worker(i, c, l)) for i, (c, l) in enumerate(usable)]
            reporter = asyncio.create_task(_reporter())
            await asyncio.gather(*tasks, return_exceptions=True)
            if not _csb_cancel and (retry_q or _done_count() < len(ids)):
                aborted = "every userbot retired after repeated errors"
    except Exception as e:
        aborted = f"{type(e).__name__}: {e}"
        await report_system_error("_run_csb", str(e))
    finally:
        for t in tasks:
            t.cancel()
        if reporter:
            reporter.cancel()
        CSB_RUNNING = False
    handled = {x for v in res.values() for x in v}
    remaining = [x for x in ids if x not in handled]
    _csb_last_failed = list(res["failed"])
    summary = _csb_summary_text(len(ids), res, len(usable), (time.time() - t0) / 60, _csb_cancel, aborted, skipped, remaining)
    _csb_cancel = False
    try:
        await bot1.edit_message(status_chat_id, status_msg_id, summary, parse_mode='html', buttons=None)
    except Exception:
        try:
            await bot1.send_message(OWNER_ID, summary, parse_mode='html')
        except Exception:
            pass

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]csb(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def csb_command(event):
    """/csb — reply to a message full of ids (or type them after the command). /csb stop · /csb retry."""
    global CSB_RUNNING, _csb_cancel
    if event.sender_id != OWNER_ID:
        return
    if is_duplicate_event(event):
        return
    arg = (event.pattern_match.group(1) or "").strip()
    if arg.lower() == "stop":
        if not CSB_RUNNING:
            return await event.reply("📭 No /csb run is in progress.")
        _csb_cancel = True
        return await event.reply("🛑 Stopping after the ids currently being checked…")
    if CSB_RUNNING:
        return await event.reply("⏳ A /csb run is already going — wait for it, or stop it with the 🛑 button / <code>/csb stop</code>.", parse_mode='html')
    if SYNC_IN_PROGRESS:
        return await event.reply("⏳ A full /syncfromcatch is running — wait for it or /syncfromcatchcancel first.")
    if arg.lower() == "retry":
        ids, ignored, truncated = list(_csb_last_failed), 0, False
        if not ids:
            return await event.reply("📭 No failed ids from the last /csb run.")
    else:
        text = arg
        if event.is_reply:
            replied = await event.get_reply_message()
            text = ((getattr(replied, "raw_text", None) or getattr(replied, "message", None) or "") + "\n" + arg).strip()
        ids, ignored, truncated = parse_csb_ids(text)
        if not ids:
            return await event.reply(
                "📦 <b>/csb</b> — bulk /checksync\n"
                "ID တွေပါတဲ့ message ကို <b>Reply</b> လုပ်ပြီး <code>/csb</code> ရိုက်ပါ (space / comma / line ခြားလို့ရတယ်၊ "
                "<code>5670-5690</code> လို range လည်းရတယ်)။ ဒါမှမဟုတ် <code>/csb 5671 5672 6000-6010</code>။\n"
                "<code>/csb stop</code> · <code>/csb retry</code> (failed တွေကိုပဲ ပြန်လုပ်)",
                parse_mode='html')
    if not monitor_userbot and not worker_pool_clients:
        return await event.reply("❌ No userbot is connected. Use /xbotsetsession or /xbotaddworker first.")
    CSB_RUNNING = True            # claimed BEFORE any await below, so a second /csb can't slip in
    try:
        all_workers = await _sync_collect_workers(None)
        if not all_workers:
            CSB_RUNNING = False
            return await event.reply("❌ No userbot is usable right now (see /xbotworkers check).")
        workers = all_workers[:max(1, min(len(ids), len(all_workers)))]
        notes = []
        if ignored:
            notes.append(f"{ignored} number(s) outside {CATCHBOT_SYNC_MIN_ID}–{CATCHBOT_SYNC_HARD_CEILING} ignored")
        if truncated:
            notes.append(f"list cut at {CSB_MAX_IDS} ids — send the rest again afterwards")
        status = await event.reply(
            f"⏳ <b>/csb</b> — checking <code>{len(ids)}</code> id(s) with <code>{len(workers)}</code> userbot(s)…"
            + (f"\n<i>{'; '.join(notes)}</i>" if notes else ""),
            parse_mode='html', buttons=[[Button.inline("🛑 Stop", data="csb_stop")]])
        asyncio.create_task(_run_csb(ids, event.chat_id, status.id, workers))
    except Exception:
        CSB_RUNNING = False
        raise

@bot1.on(events.CallbackQuery(pattern=r'^csb_stop$'))
async def csb_stop_callback(event):
    global _csb_cancel
    if event.sender_id != OWNER_ID:
        return await event.answer("Owner only.", alert=True)
    if not CSB_RUNNING:
        return await event.answer("Already finished.", alert=False)
    _csb_cancel = True
    await event.answer("Stopping…", alert=False)

# ==========================================
# 💾 /save — passively captures a HUMAN manually typing .check <n> to catch_bot, instead of
# only the bot's own automated .check calls. Screenshots from the owner showed catch_bot
# replying to .check commands right inside CATCHBOT_SYNC_CHAT_ID (a real group in this setup,
# not just a private DM — see that constant's comment) — so a person (the owner themselves, or
# anyone else in that chat) can already trigger catch_bot's reply just by typing there, with no
# bot involvement at all. When armed, this captures THAT reply too and runs it through the
# exact same store_character_from_check pipeline /syncfromcatch and /checksync use — so a
# manual spot-check (like the Alisa Mikhailovna id 5450 vs 7318 comparison) gets saved without
# the owner having to separately run /checksync afterward.
# ==========================================
_save_mode_armed = False

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]save\s+(on|off)$', 'bot1')))
async def save_mode_toggle_command(event):
    global _save_mode_armed
    if event.sender_id != OWNER_ID: return
    _save_mode_armed = event.pattern_match.group(1).lower() == "on"
    if _save_mode_armed:
        await event.reply(
            f"💾 <b>/save armed.</b> Any .check reply from catch_bot seen in "
            f"<code>{CATCHBOT_SYNC_CHAT_ID}</code> — sent by you, by /syncfromcatch, by anyone "
            f"— gets captured and saved automatically now, overwriting whatever's currently "
            f"stored for that id. Send <code>/save off</code> to stop.",
            parse_mode='html'
        )
    else:
        await event.reply("🛑 <b>/save disarmed.</b>")

async def passive_catchbot_check_capture(event):
    """Registered on monitor_userbot (see register_userbot_handlers) for every message FROM
    catch_bot it can see. Only acts while _save_mode_armed is True, only in
    CATCHBOT_SYNC_CHAT_ID, and only when the message catch_bot is replying to was itself a
    plain ".check <n>" — anything else (an unrelated reply, a .check with extra text, etc.) is
    ignored so this can't misfire on other traffic in a shared group."""
    if not _save_mode_armed:
        return
    if event.chat_id != CATCHBOT_SYNC_CHAT_ID:
        return
    if not event.is_reply:
        return
    try:
        replied = await event.get_reply_message()
    except Exception:
        return
    if not replied or not re.match(r'^\.check\s+\d+$', (replied.raw_text or "").strip(), re.IGNORECASE):
        return
    if not (event.photo or event.video or event.document):
        return
    info = parse_catchbot_check(event.raw_text or "")
    if not info:
        return
    try:
        outcome = await store_character_from_check(info, event)
        print(f"💾 [/save] passively captured id {info.get('id')} -> {outcome}")
    except Exception as e:
        print(f"⚠️ [/save] failed to capture id {info.get('id')}: {e}")

# (the old fixed-range /syncfromcatch_parallel lived here — replaced by the shared-queue pool engine above)
# Kept: still read by the char-id range helpers below (/mergenamedupes etc.) as "the highest id catch_bot could ever use".
CATCHBOT_SYNC_PARALLEL_MAX_ID = 9999

def _char_id_sort_key(char_id):
    """Sorts BOD##### ids numerically (so BOD100 correctly comes before BOD99, unlike plain
    string sorting) — used by /mergenamedupes to pick the LOWEST/earliest-confirmed id in a
    duplicate group as the canonical survivor. Anything not matching BOD##### (CNFT cards,
    migrated B0001-style ids) sorts after, alphabetically among themselves — duplicates in
    practice only ever come from /syncfromcatch's plain BOD numbering anyway."""
    m = re.match(r'^BOD(\d+)$', char_id, re.IGNORECASE)
    return (0, int(m.group(1))) if m else (1, char_id)

async def _real_catch_count(char_id):
    """How many copies of char_id are actually sitting in players' harems right now."""
    result = await users_catcher_col.aggregate(
        [
            {"$project": {"harem.char_id": 1}},
            {"$unwind": "$harem"},
            {"$match": {"harem.char_id": char_id}},
            {"$count": "total"},
        ],
        allowDiskUse=True
    ).to_list(length=1)
    return result[0]["total"] if result else 0

async def _execute_char_merge(groups, cmd_name):
    """Shared merge executor for /mergenamedupes and /mergemediadupes — same canonical-selection,
    harem/fav reassignment (nobody loses a card), and cleanup regardless of how the duplicate
    groups were found (exact media identity vs matching name/category/rarity).

    🩹 UPGRADED (owner report — self-heal left BOD10000+ copies of characters that already exist
    in the 1-9999 range, same media, sitting at Common): merging must not just repoint char_id.
      • Every reassigned harem entry also takes the CANONICAL card's rarity — otherwise a player
        who held the Common duplicate would keep a harem entry that says "Common" for a card that
        is really Supreme (entries store their own rarity string, see perform_catch).
      • Market listings pointing at a duplicate are repointed too, so an auction never ends
        handing out a character id that no longer exists.
      • The /who file-identity index is repointed to the canonical card, so a repost of that
        media resolves to the survivor immediately instead of to a deleted id.
      • spawn_count is set from the REAL number of copies in harems after the merge (what
        /refillcatch computes), not the sum of two possibly-drifted counters."""
    merged_groups, removed_chars, reassigned_harem_entries, failed = 0, 0, 0, []
    for char_ids in groups.values():
        shown_ids = sorted(char_ids, key=_char_id_sort_key)
        canonical, duplicates = shown_ids[0], shown_ids[1:]
        try:
            docs = await characters_base_col.find({"char_id": {"$in": char_ids}}).to_list(length=None)
            canon_doc = next((d for d in docs if d["char_id"] == canonical), None)
            canon_rarity = (canon_doc or {}).get("rarity")
            canon_storage_id = (canon_doc or {}).get("storage_msg_id")
            harem_set = {"harem.$[elem].char_id": canonical}
            listing_set = {"char_id": canonical}
            if canon_rarity:
                harem_set["harem.$[elem].rarity"] = canon_rarity
                listing_set["rarity"] = canon_rarity
            for dup_id in duplicates:
                result = await users_catcher_col.update_many(
                    {"harem.char_id": dup_id},
                    {"$set": harem_set},
                    array_filters=[{"elem.char_id": dup_id}]
                )
                reassigned_harem_entries += result.modified_count
                await users_catcher_col.update_many({"fav_card": dup_id}, {"$set": {"fav_card": canonical}})
                # Reassigns fav_cards array entries too. If a player happened to have BOTH
                # dup_id and canonical favourited already, this can leave canonical listed
                # twice — harmless (just shows once extra when cycling favourites) and
                # self-heals the next time they run /fav, which de-dupes on set.
                await users_catcher_col.update_many(
                    {"fav_cards": dup_id},
                    {"$set": {"fav_cards.$[elem]": canonical}},
                    array_filters=[{"elem": dup_id}]
                )
                try:
                    await market_listings_col.update_many({"char_id": dup_id}, {"$set": listing_set})
                except Exception as e:
                    print(f"⚠️ {cmd_name}: market listing repoint failed for {dup_id}: {e}")
                try:
                    await media_identity_col.update_many({"char_id": dup_id}, {"$set": {"char_id": canonical}})
                except Exception as e:
                    print(f"⚠️ {cmd_name}: media identity repoint failed for {dup_id}: {e}")
                for k, v in list(_MEDIA_ID_CACHE.items()):
                    if v[0] == dup_id:
                        _MEDIA_ID_CACHE[k] = (canonical, v[1])
                dup_doc = next((d for d in docs if d["char_id"] == dup_id), None)
                dup_storage_id = (dup_doc or {}).get("storage_msg_id")
                # Never delete a storage message the survivor is also pointing at.
                if dup_storage_id and dup_storage_id != canon_storage_id:
                    try:
                        await bot1.delete_messages(SPECIFIC_CONTROL_GROUP, [dup_storage_id])
                    except Exception:
                        pass
                await characters_base_col.delete_one({"char_id": dup_id})
                _CHAR_PHOTO_CACHE.pop(dup_id, None)
                removed_chars += 1
            real_count = await _real_catch_count(canonical)
            await characters_base_col.update_one({"char_id": canonical}, {"$set": {"spawn_count": real_count}})
            merged_groups += 1
        except Exception as e:
            failed.append(f"{display_char_id(canonical)}: {e}")
            print(f"⚠️ {cmd_name} failed for group canonical={canonical}: {e}")

    await invalidate_character_caches()
    result_lines = [
        f"✅ <b>Merged {merged_groups}/{len(groups)} duplicate group(s)</b>",
        f"🗑️ Removed {removed_chars} redundant character record(s)",
        f"👤 Reassigned {reassigned_harem_entries} player harem entr(y/ies) to their canonical ID",
    ]
    if failed:
        result_lines.append(f"❌ <b>Failed ({len(failed)}):</b> <code>{'; '.join(failed[:10])}</code>")
    result_lines.append("Run /warmmediacache to refresh the identity cache now that duplicates are gone.")
    return "\n".join(result_lines)

# ==========================================
# 🖼️ MEDIA-BASED duplicates (self-heal leftovers)
# ------------------------------------------
# Owner report: the channel self-heal (_create_orphan_imported_character) sometimes builds a brand
# new character (BOD10000+, rarity Common) from a channel post whose media is the EXACT SAME
# Telegram file as a character that already exists in the normal 1-9999 range. Result: two roster
# entries, one file. Deleting the extra one outright would take cards away from every player who
# happened to catch it, so /mergemediadupes folds it INTO the original instead — every copy a
# player owns (and any favourite / market listing) is repointed to the original card, nobody's
# collection shrinks.
#
# "Same media" here means the exact same underlying Telegram photo/document id
# (get_media_identity_key) — not a look-alike — read from each character's stored copy in
# SPECIFIC_CONTROL_GROUP. Safety rules on top of that:
#   • The survivor is the lowest id inside the catch_bot sync range (BOD1..9999). Anything OUTSIDE
#     that range (BOD10000+, non-BOD ids) with the same file gets merged into it.
#   • Two characters that are BOTH inside the sync range are never merged with each other (that
#     would break number parity with catch_bot; /syncfromcatch would just recreate the deleted
#     one) — such groups are only reported.
#   • Anything special (CNFT tiers / spawnable=False) is never touched.
# ==========================================
_MEDIA_SCAN_CACHE = {"at": 0.0, "keys": {}}
MEDIA_SCAN_CACHE_TTL = 900  # reuse a fresh scan for 15 min so /findmediadupes -> /mergemediadupes confirm doesn't crawl twice

def _is_catchbot_range_id(char_id):
    m = re.match(r'^BOD(\d+)$', str(char_id), re.IGNORECASE)
    if not m:
        return False
    return CATCHBOT_SYNC_MIN_ID <= int(m.group(1)) <= max(CATCHBOT_SYNC_MAX_ID, CATCHBOT_SYNC_PARALLEL_MAX_ID)

async def _scan_roster_media_keys(progress_status=None, use_cache=True):
    """{char_id: exact-file identity key} for every character whose stored media can still be
    fetched from SPECIFIC_CONTROL_GROUP. Batch-fetches 200 per call with flood-wait handling, the
    same way warm_media_identity_cache_from_db does."""
    if use_cache and (time.time() - _MEDIA_SCAN_CACHE["at"]) < MEDIA_SCAN_CACHE_TTL and _MEDIA_SCAN_CACHE["keys"]:
        return dict(_MEDIA_SCAN_CACHE["keys"])
    docs = await characters_base_col.find({}, {"char_id": 1, "storage_msg_id": 1, "_id": 0}).to_list(length=None)
    storage_to_chars = {}
    for d in docs:
        if d.get("storage_msg_id") and d.get("char_id"):
            storage_to_chars.setdefault(d["storage_msg_id"], []).append(d["char_id"])
    all_ids = list(storage_to_chars.keys())
    keys = {}
    total_batches = max(1, (len(all_ids) + 199) // 200)
    for batch_num, i in enumerate(range(0, len(all_ids), 200), start=1):
        batch_ids = all_ids[i:i + 200]
        messages = None
        for _attempt in range(5):
            try:
                messages = await bot1.get_messages(SPECIFIC_CONTROL_GROUP, ids=batch_ids)
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
            except Exception as e:
                print(f"⚠️ _scan_roster_media_keys: batch {batch_num}/{total_batches} failed: {type(e).__name__}: {e}")
                await asyncio.sleep(2)
        for m in (messages or []):
            if not m:
                continue  # storage message no longer exists
            key = get_media_identity_key(m)
            if not key:
                continue
            for cid in storage_to_chars.get(m.id, []):
                keys[cid] = key
        if progress_status and batch_num % 5 == 0:
            try:
                await progress_status.edit(f"⏳ Media ဖိုင်တွေကို စစ်နေပါတယ်... batch {batch_num}/{total_batches}")
            except Exception:
                pass
        await asyncio.sleep(0.3)
    _MEDIA_SCAN_CACHE["at"] = time.time()
    _MEDIA_SCAN_CACHE["keys"] = dict(keys)
    return keys

async def _plan_media_merge(keys):
    """Turns a {char_id: media key} scan into a safe merge plan. Returns
    (plan, info, kept_separate, skipped_special): plan = list of [canonical, dup, dup, ...]."""
    by_key = {}
    for cid, key in keys.items():
        by_key.setdefault(key, []).append(cid)
    by_key = {k: v for k, v in by_key.items() if len(v) > 1}
    if not by_key:
        return [], {}, [], 0
    all_ids = [c for ids in by_key.values() for c in ids]
    docs = await characters_base_col.find(
        {"char_id": {"$in": all_ids}},
        {"char_id": 1, "name": 1, "rarity": 1, "rarity_tier": 1, "spawnable": 1}
    ).to_list(length=None)
    info = {d["char_id"]: d for d in docs}
    plan, kept_separate, skipped_special = [], [], 0
    for ids in by_key.values():
        ids = [c for c in ids if c in info]  # ignore anything deleted since the scan
        if len(ids) < 2:
            continue
        if any(info[c].get("spawnable") is False or str(info[c].get("rarity_tier", "")).startswith("CNFT") for c in ids):
            skipped_special += 1
            continue
        ids_sorted = sorted(ids, key=_char_id_sort_key)
        anchors = [c for c in ids_sorted if _is_catchbot_range_id(c)]
        if anchors:
            canonical = anchors[0]
            if len(anchors) > 1:
                kept_separate.append(anchors)
            removable = [c for c in ids_sorted if c not in anchors]
        else:
            canonical = ids_sorted[0]
            removable = ids_sorted[1:]
        if removable:
            plan.append([canonical] + removable)
    return plan, info, kept_separate, skipped_special

def _describe_media_plan(plan, info, limit=15):
    lines = []
    for ids in plan[:limit]:
        canonical, dups = ids[0], ids[1:]
        cinfo = info.get(canonical, {})
        dup_txt = ", ".join(f"{display_char_id(d)} ({strip_rarity_number(info.get(d, {}).get('rarity', '?'))})" for d in dups)
        lines.append(
            f"  {dup_txt} → {display_char_id(canonical)} "
            f"({strip_rarity_number(cinfo.get('rarity', '?'))}) {escape_html(str(cinfo.get('name', '?'))[:30])}"
        )
    if len(plan) > limit:
        lines.append(f"  …and {len(plan) - limit} more group(s)")
    return "\n".join(lines)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]findmediadupes(?:@\w+)?$', 'bot1')))
async def find_media_duplicate_chars_command(event):
    """Read-only report of characters that share the exact same media file — see the block
    comment above. Run this first, then /mergemediadupes."""
    if event.sender_id != OWNER_ID: return
    status = await event.reply("⏳ Character တိုင်းရဲ့ media ဖိုင်ကို စစ်နေပါတယ် (တစ်ကြိမ်လုပ်ရင် ခဏကြာနိုင်ပါတယ်)...")
    keys = await _scan_roster_media_keys(progress_status=status, use_cache=False)
    plan, info, kept_separate, skipped_special = await _plan_media_merge(keys)
    if not plan and not kept_separate:
        return await status.edit(f"✅ Media တူနေတဲ့ duplicate မတွေ့ပါ ({len(keys)} characters စစ်ပြီး)။")
    lines = [f"⚠️ <b>{len(plan)} duplicate group(s)</b> ပေါင်းလို့ရပါတယ် ({len(keys)} characters စစ်ပြီး):"]
    if plan:
        lines.append(f"<code>{_describe_media_plan(plan)}</code>")
    if kept_separate:
        lines.append(f"\nℹ️ {len(kept_separate)} group မှာ character နှစ်ခုစလုံး catch_bot range (1-{max(CATCHBOT_SYNC_MAX_ID, CATCHBOT_SYNC_PARALLEL_MAX_ID)}) ထဲမှာမို့ မထိပါဘူး (နံပါတ်တိုက်ဆိုင်မှု မပျက်စေချင်လို့)။")
    if skipped_special:
        lines.append(f"ℹ️ {skipped_special} group ကို CNFT/special ပါလို့ ကျော်ထားတယ်။")
    if plan:
        lines.append("\nပေါင်းဖို့: <code>/mergemediadupes confirm</code> — player တွေရဲ့ card မလျော့ပါဘူး၊ duplicate ကိုင်ထားသူတွေ ရှိသမျှ မူရင်း card ကို ပြောင်းပေးမယ်။")
    await status.edit("\n".join(lines), parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mergemediadupes(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def merge_media_duplicate_chars_command(event):
    """Folds every same-media duplicate (typically self-heal's BOD10000+ leftovers) INTO the
    original character. Preview first; add `confirm` to run it. Players keep every copy they own."""
    if event.sender_id != OWNER_ID: return
    confirmed = bool(event.pattern_match.group(1))
    status = await event.reply("⏳ Media ဖိုင်တူတဲ့ duplicate တွေကို ရှာနေပါတယ်...")
    keys = await _scan_roster_media_keys(progress_status=status, use_cache=confirmed)
    plan, info, kept_separate, skipped_special = await _plan_media_merge(keys)
    if not plan:
        note = f"\nℹ️ {len(kept_separate)} group က range ထဲမှာ နှစ်ခုစလုံးရှိလို့ မထိပါဘူး။" if kept_separate else ""
        return await status.edit(f"✅ ပေါင်းစရာ duplicate မရှိပါ။{note}")
    total_redundant = sum(len(g) - 1 for g in plan)
    if not confirmed:
        return await status.edit(
            f"⚠️ <b>{len(plan)} group</b> ({total_redundant} redundant character) ကို မူရင်း id ထဲ ပေါင်းမှာပါ:\n\n"
            f"<code>{_describe_media_plan(plan)}</code>\n\n"
            f"👤 Duplicate ကို ကိုင်ထားတဲ့ player တွေရဲ့ card တွေ (favourite / market listing အပါအဝင်) "
            f"မူရင်း card ဆီ ပြောင်းသွားမယ် — ဘယ်သူမှ card မဆုံးရှုံးပါဘူး၊ ရှိပြီးသား rarity ကတော့ မူရင်း card ရဲ့ rarity ဖြစ်သွားမယ်။\n\n"
            f"ဆက်လုပ်ဖို့: <code>/mergemediadupes confirm</code>  (အလိုအလျောက် ပြန်ဖြေမရပါဘူး)",
            parse_mode='html'
        )
    await status.edit(f"🔄 <b>{len(plan)} group ကို ပေါင်းနေပါတယ်...</b>", parse_mode='html')
    result_text = await _execute_char_merge({i: ids for i, ids in enumerate(plan)}, "/mergemediadupes")
    _MEDIA_SCAN_CACHE["at"] = 0.0  # roster changed — next scan must be fresh
    await status.edit(result_text, parse_mode='html')

# ==========================================
# 🔗 NAME + PHASH duplicates (self-heal leftovers that /findmediadupes cannot see)
# ------------------------------------------
# Owner report: self-heal built BOD10000+ copies (rarity Common, anime "Unknown") of cards that
# /syncfromcatch later fetched properly under their real id (BOD1..BOD9999, full anime / event /
# rarity). /findmediadupes only pairs characters that share the EXACT same Telegram file id, and
# a channel post's media is a different upload from catch_bot's .check reply, so those two
# never matched and the players who caught the BOD10000+ copy kept holding it.
#
# This pairs them on what the owner actually sees instead: SAME NAME + SAME PHASH.
#   • Survivor ("canonical") = a character with id BOD1..BOD9999 that was CONFIRMED by a real
#     .check reply (synced_via_check is True). An unconfirmed in-range id is never a survivor.
#   • Redundant copy = a BOD id ABOVE that range. Non-BOD ids and CNFT / spawnable=False
#     characters are never touched.
#   • Name = compared without case, invisible characters and trailing "[emoji]" / "[tag]"
#     groups, because .check bakes the event tag into the name ("Goji [🍷]") while the log
#     post stores it bare ("Goji").
#   • Phash = exact by default (`/mergenamephashdupes 3` allows up to 3 differing bits; hard
#     ceiling NPH_MAX_ALLOWED_DIST). Two survivors with the same name+phash = ambiguous, so
#     that copy is reported and left alone.
#   • Only machine-created copies (auto_healed / auto_imported_from) merge by default. A card
#     the owner added by hand with /addchar is only included with the `all` argument.
# Merging reuses _execute_char_merge (every player's copy is repointed to the survivor and takes
# its rarity; favourites, market listings and the /who index follow). Extra safety here:
# spawns are paused while it runs, copies in a live spawn/quiz are skipped, every removed
# record + its holders is saved to `char_merge_backup` first (no backup = no merge), and a
# second pass re-checks that nobody is still holding a removed id.
# ==========================================
NPH_CANON_MAX_ID = 9999
NPH_NEAR_INFO_DIST = 8       # report-only: how many more copies WOULD match at <= this distance
NPH_MAX_ALLOWED_DIST = 12    # the optional distance argument is clamped to this
_NPH_MERGE_RUNNING = False
char_merge_backup_col = db["char_merge_backup"]

def _nph_bod_num(char_id):
    m = re.match(r'^BOD(\d+)$', str(char_id or ""), re.IGNORECASE)
    return int(m.group(1)) if m else None

def _nph_canon_ceiling():
    return max(NPH_CANON_MAX_ID, CATCHBOT_SYNC_MAX_ID, CATCHBOT_SYNC_PARALLEL_MAX_ID)

def _nph_base_name(name):
    """Comparison key: case/invisible-char normalised, trailing [tag] groups removed, then the
    same punctuation-insensitive folding the other duplicate finders use."""
    n = _normalize_catchbot_name(name or "")
    prev = None
    while prev != n:
        prev = n
        n = re.sub(r'\s*\[[^\]]*\]\s*$', '', n)
    return normalize_name(n)

def _nph_dist(hash_a, hash_b):
    """Hamming distance, or None when the two hashes can't be compared (missing, or different
    lengths — an old 64-bit hash against a 256-bit one gives a meaningless number)."""
    if not hash_a or not hash_b or len(str(hash_a)) != len(str(hash_b)):
        return None
    d = hamming_distance(hash_a, hash_b)
    return None if d >= 999 else d

def _nph_is_special(d):
    return d.get("spawnable") is False or str(d.get("rarity_tier", "")).startswith("CNFT")

def _nph_plan(docs, max_dist=0, include_manual=False):
    """Pure function (no DB, no Telegram): decides which high-id copies fold into which
    confirmed low-id character. Returns a dict — see the keys at the bottom."""
    ceiling = _nph_canon_ceiling()
    stats = Counter()
    by_id = {}
    canon_by_name, canon_by_phash, dup_docs = {}, {}, []
    for d in docs:
        cid = d.get("char_id")
        if not cid or _nph_is_special(d):
            continue
        by_id[cid] = d
        num = _nph_bod_num(cid)
        if num is None:
            stats["non_bod_skipped"] += 1
            continue
        if num <= ceiling:
            if d.get("synced_via_check") is True:
                key = _nph_base_name(d.get("name"))
                if key:
                    canon_by_name.setdefault(key, []).append(d)
                if d.get("photo_phash"):
                    canon_by_phash.setdefault(str(d["photo_phash"]).lower(), []).append(d)
            continue  # an in-range id is never a redundant copy
        dup_docs.append(d)

    plan, near, ambiguous, phash_only, manual = {}, [], [], [], []
    stats["high_id_total"] = len(dup_docs)
    for d in sorted(dup_docs, key=lambda x: _char_id_sort_key(x["char_id"])):
        cid = d["char_id"]
        machine = bool(d.get("auto_healed") or d.get("auto_imported_from"))
        key = _nph_base_name(d.get("name"))
        ph = d.get("photo_phash")
        if not key:
            stats["no_name"] += 1
            continue
        cands = canon_by_name.get(key) or []
        if not cands:
            stats["no_name_match"] += 1
            if ph:
                other = canon_by_phash.get(str(ph).lower())
                if other:
                    phash_only.append((cid, other[0]["char_id"]))
            continue
        if not ph:
            stats["dup_no_phash"] += 1
            continue
        scored = []
        for c in cands:
            dist = _nph_dist(ph, c.get("photo_phash"))
            if dist is not None:
                scored.append((dist, c))
        if not scored:
            stats["phash_not_comparable"] += 1
            continue
        scored.sort(key=lambda x: (x[0], _char_id_sort_key(x[1]["char_id"])))
        best = scored[0][0]
        if best > max_dist:
            if best <= NPH_NEAR_INFO_DIST:
                near.append((cid, scored[0][1]["char_id"], best))
            else:
                stats["phash_differs"] += 1
            continue
        tied = [c["char_id"] for dist, c in scored if dist == best]
        if len(tied) > 1:
            ambiguous.append((cid, tied))
            continue
        if not machine and not include_manual:
            manual.append(cid)
            continue
        plan.setdefault(tied[0], []).append(cid)
    return {"plan": plan, "near": near, "ambiguous": ambiguous, "phash_only": phash_only,
            "manual": manual, "stats": stats, "docs": by_id}

_NPH_PROJECTION = {
    "char_id": 1, "name": 1, "rarity": 1, "rarity_tier": 1, "photo_phash": 1, "synced_via_check": 1,
    "auto_healed": 1, "auto_imported_from": 1, "spawnable": 1, "_id": 0,
}

async def _nph_scan(max_dist, include_manual):
    docs = await characters_base_col.find({}, _NPH_PROJECTION).to_list(length=None)
    return _nph_plan(docs, max_dist, include_manual), len(docs)

async def _nph_holders(char_ids):
    """{char_id: {user_id: copies}} — who is holding these ids right now (one aggregation)."""
    out = {}
    ids = list(char_ids)
    if not ids:
        return out
    pipeline = [
        {"$match": {"harem.char_id": {"$in": ids}}},
        {"$project": {"user_id": 1, "harem.char_id": 1}},
        {"$unwind": "$harem"},
        {"$match": {"harem.char_id": {"$in": ids}}},
        {"$group": {"_id": {"c": "$harem.char_id", "u": "$user_id"}, "n": {"$sum": 1}}},
    ]
    async for row in users_catcher_col.aggregate(pipeline, allowDiskUse=True):
        out.setdefault(row["_id"]["c"], {})[row["_id"]["u"]] = row["n"]
    return out

def _nph_live_char_ids():
    """Ids that are on screen right now (a live spawn or an unsolved rarity-gate quiz)."""
    ids = set()
    for sp in list(active_group_spawns.values()):
        if isinstance(sp, dict) and sp.get("char_id"):
            ids.add(sp["char_id"])
    for q in list(pending_rarity_quiz.values()):
        cid = ((q or {}).get("char") or {}).get("char_id") if isinstance(q, dict) else None
        if cid:
            ids.add(cid)
    return ids

def _nph_parse_args(raw):
    """-> (max_dist, include_manual, confirmed, error_or_None)"""
    max_dist, include_manual, confirmed = 0, False, False
    for tok in (raw or "").split():
        t = tok.lower()
        if t == "confirm":
            confirmed = True
        elif t == "all":
            include_manual = True
        elif t.isdigit():
            max_dist = min(int(t), NPH_MAX_ALLOWED_DIST)
        else:
            return 0, False, False, f"မသိတဲ့ argument: {tok}"
    return max_dist, include_manual, confirmed, None

def _nph_cmd_suffix(max_dist, include_manual):
    return (f" {max_dist}" if max_dist else "") + (" all" if include_manual else "")

def _nph_line(dup, canon, docs):
    dd, cd = docs.get(dup, {}), docs.get(canon, {})
    return (f"  {display_char_id(dup)} ({strip_rarity_number(dd.get('rarity', '?'))}) → "
            f"{display_char_id(canon)} ({strip_rarity_number(cd.get('rarity', '?'))}) "
            f"{escape_html(str(cd.get('name', '?'))[:26])}")

def _nph_render(res, total, holders, max_dist, include_manual, limit=15):
    plan, docs, st = res["plan"], res["docs"], res["stats"]
    n_dups = sum(len(v) for v in plan.values())
    lines = [f"🔎 <b>Name + phash duplicate စစ်ချက်</b> (roster {total} ခု၊ id {_nph_canon_ceiling()} အထက် {st['high_id_total']} ခု)"]
    if plan:
        healed = sum(1 for ds in plan.values() for d in ds if docs[d].get("auto_healed"))
        lines.append(f"✅ <b>ပေါင်းလို့ရ: {len(plan)} card ထဲကို duplicate {n_dups} ခု</b> (auto-heal {healed} · တခြား import {n_dups - healed})")
        if holders is not None:
            copies = sum(sum(u.values()) for u in holders.values())
            owners = len({uid for u in holders.values() for uid in u})
            with_holders = sum(1 for ds in plan.values() for d in ds if holders.get(d))
            lines.append(f"👤 duplicate ကို ကိုင်ထားတာ: player {owners} ယောက်၊ copy {copies} ခု ({with_holders} id မှာ ကိုင်သူရှိ) — အဲ့ဒါတွေ မူရင်း id ဆီ ရွှေ့မယ်")
        pairs = [(d, c) for c, ds in plan.items() for d in ds]
        pairs.sort(key=lambda p: _char_id_sort_key(p[0]))
        lines.append("<code>" + "\n".join(_nph_line(d, c, docs) for d, c in pairs[:limit]) + "</code>")
        if len(pairs) > limit:
            lines.append(f"  …နောက်ထပ် {len(pairs) - limit} ခု")
    else:
        lines.append("✅ ပေါင်းစရာ (name + phash တူ) duplicate မတွေ့ပါ။")
    notes = []
    if res["near"]:
        notes.append(f"• name တူ phash နည်းနည်းကွာ (≤{NPH_NEAR_INFO_DIST} bit): {len(res['near'])} ခု — မပေါင်းပါ၊ ကြည့်ချင်ရင် <code>/findnamephashdupes {NPH_NEAR_INFO_DIST}</code>")
    if res["ambiguous"]:
        notes.append(f"• မူရင်း card နှစ်ခုကျော် တူနေလို့ မရွေးနိုင်: {len(res['ambiguous'])} ခု")
    if res["manual"]:
        notes.append(f"• /addchar နဲ့ လက်ဖြင့်ထည့်ထားတာ: {len(res['manual'])} ခု — မထိပါ (ထည့်ချင်ရင် <code>all</code>)")
    if st["dup_no_phash"]:
        notes.append(f"• duplicate မှာ phash မရှိ: {st['dup_no_phash']} ခု (/rehashall လိုနိုင်)")
    if st["phash_not_comparable"]:
        notes.append(f"• phash အရှည်မတူ (hash အဟောင်း): {st['phash_not_comparable']} ခု (/rehashall လိုနိုင်)")
    if st["phash_differs"]:
        notes.append(f"• name တူပေမယ့် ပုံကွာ (မတူတဲ့ card): {st['phash_differs']} ခု")
    if res["phash_only"]:
        ex = ", ".join(f"{display_char_id(d)}→{display_char_id(c)}" for d, c in res["phash_only"][:4])
        notes.append(f"• phash တူပေမယ့် name ကွာ: {len(res['phash_only'])} ခု — မထိပါ ({ex})")
    if st["no_name_match"]:
        notes.append(f"• အောက်က range မှာ name တူတဲ့ confirmed card မရှိ: {st['no_name_match']} ခု (card အသစ်အစစ်ဖြစ်နိုင်/ မ sync ရသေး)")
    if notes:
        lines.append("\n<b>မပေါင်းဘဲ ကျန်တာ</b>\n" + "\n".join(notes))
    if plan:
        lines.append(f"\nပေါင်းဖို့: <code>/mergenamephashdupes{_nph_cmd_suffix(max_dist, include_manual)} confirm</code>")
    text = "\n".join(lines)
    return text if len(text) <= 3900 else text[:3850] + "\n…"

async def _nph_edit(status, event, text):
    try:
        await status.edit(text, parse_mode='html')
    except Exception:
        try:
            await event.reply(text, parse_mode='html')
        except Exception as e:
            print(f"⚠️ nph reply failed: {type(e).__name__}: {e}")

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]findnamephashdupes(?:@\w+)?((?:\s+\S+)*)$', 'bot1')))
async def find_namephash_dupes_command(event):
    """Read-only. Counts name+phash duplicates and shows who would be affected."""
    if event.sender_id != OWNER_ID: return
    max_dist, include_manual, _confirmed, err = _nph_parse_args(event.pattern_match.group(1))
    if err:
        return await event.reply(f"❌ {escape_html(err)}\nသုံးပုံ: <code>/findnamephashdupes [0-{NPH_MAX_ALLOWED_DIST}] [all]</code>", parse_mode='html')
    status = await event.reply("⏳ Roster ကို name + phash နဲ့ စစ်နေပါတယ်...")
    try:
        res, total = await _nph_scan(max_dist, include_manual)
        dup_ids = [d for ds in res["plan"].values() for d in ds]
        holders = await _nph_holders(dup_ids)
        await _nph_edit(status, event, _nph_render(res, total, holders, max_dist, include_manual))
    except Exception as e:
        await _nph_edit(status, event, f"❌ Scan error: <code>{escape_html(type(e).__name__)}: {escape_html(str(e)[:200])}</code>")

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mergenamephashdupes(?:@\w+)?((?:\s+\S+)*)$', 'bot1')))
async def merge_namephash_dupes_command(event):
    """Folds every high-id copy into its confirmed low-id twin. Without `confirm` it only
    previews. See the block comment above for the rules and the safety net."""
    global _NPH_MERGE_RUNNING
    if event.sender_id != OWNER_ID: return
    max_dist, include_manual, confirmed, err = _nph_parse_args(event.pattern_match.group(1))
    if err:
        return await event.reply(f"❌ {escape_html(err)}\nသုံးပုံ: <code>/mergenamephashdupes [0-{NPH_MAX_ALLOWED_DIST}] [all] [confirm]</code>", parse_mode='html')
    if _NPH_MERGE_RUNNING:
        return await event.reply("⏳ /mergenamephashdupes တစ်ခု run နေဆဲပါ။")
    if confirmed and SYNC_IN_PROGRESS:
        return await event.reply("⛔ /syncfromcatch run နေတုန်း မပေါင်းပါဘူး (id တွေ ပြောင်းနေနိုင်လို့)။ Sync ပြီးမှ ပြန်လုပ်ပါ။")
    status = await event.reply("⏳ Name + phash နဲ့ duplicate ရှာနေပါတယ်...")
    _NPH_MERGE_RUNNING = True
    paused_by_us = False
    try:
        if confirmed and CHANNEL_WORK_ENABLED:
            # 🚦 no NEW spawns while ids are being rewritten (already-live spawns are handled below)
            await _set_channel_work(False, reason="mergenamephashdupes")
            paused_by_us = True
        res, total = await _nph_scan(max_dist, include_manual)
        plan, docs = res["plan"], res["docs"]
        if not confirmed:
            dup_ids = [d for ds in plan.values() for d in ds]
            holders = await _nph_holders(dup_ids)
            return await _nph_edit(status, event, _nph_render(res, total, holders, max_dist, include_manual))

        live = _nph_live_char_ids()
        live_skipped = [d for ds in plan.values() for d in ds if d in live]
        plan = {c: [d for d in ds if d not in live] for c, ds in plan.items()}
        plan = {c: ds for c, ds in plan.items() if ds}
        if plan:  # the survivors must still exist right now (deleted since the scan = never merge into a ghost)
            still = {d["char_id"] async for d in characters_base_col.find(
                {"char_id": {"$in": list(plan)}, "synced_via_check": True}, {"char_id": 1, "_id": 0})}
            plan = {c: ds for c, ds in plan.items() if c in still}
        if not plan:
            note = f"\nℹ️ live spawn ထဲမှာ ရှိနေလို့ ကျော်ထားတာ {len(live_skipped)} ခု — နောက်မှ ပြန်လုပ်ပါ။" if live_skipped else ""
            return await _nph_edit(status, event, f"✅ ပေါင်းစရာ duplicate မရှိပါ။{note}")

        all_dups = [d for ds in plan.values() for d in ds]
        await _nph_edit(status, event, f"🔄 <b>{len(plan)} card ထဲကို duplicate {len(all_dups)} ခု ပေါင်းနေပါတယ်...</b>\n(backup သိမ်းပြီး စမယ်)")
        holders = await _nph_holders(all_dups)
        full_docs = await characters_base_col.find({"char_id": {"$in": all_dups}}).to_list(length=None)
        full_by_id = {d["char_id"]: d for d in full_docs}
        batch = time.time()
        canon_of = {d: c for c, ds in plan.items() for d in ds}
        backups = [{
            "batch": batch, "cmd": "/mergenamephashdupes", "dup_id": d, "merged_into": canon_of[d],
            "dup_doc": full_by_id.get(d),
            "holders": [{"user_id": u, "copies": n} for u, n in holders.get(d, {}).items()],
        } for d in all_dups]
        try:
            await char_merge_backup_col.insert_many(backups)
        except Exception as e:
            # no backup -> no merge. Nothing has been touched yet.
            return await _nph_edit(status, event, f"❌ Backup မသိမ်းနိုင်လို့ မပေါင်းပါဘူး (ဘာမှမထိရသေးပါ): <code>{escape_html(type(e).__name__)}: {escape_html(str(e)[:200])}</code>")

        groups = {c: [c] + ds for c, ds in plan.items()}
        result_text = await _execute_char_merge(groups, "/mergenamephashdupes")
        # second pass: anything that slipped in while it ran (a gift/trade of a removed id) is repointed too
        left = await _nph_holders(all_dups)
        mop_note = ""
        if left:
            groups2 = {c: g for c, g in groups.items() if any(d in left for d in g[1:])}
            await _execute_char_merge(groups2, "/mergenamephashdupes (pass 2)")
            still_left = await _nph_holders(all_dups)
            mop_note = (f"\n🧹 Pass 2: {sum(sum(u.values()) for u in left.values())} copy ကျန်နေလို့ ထပ်ရွှေ့ပြီး"
                        + (f" — ⚠️ {sum(sum(u.values()) for u in still_left.values())} ကျန်သေးတယ်" if still_left else " — ကျန်တာမရှိတော့ပါ"))
        _MEDIA_SCAN_CACHE["at"] = 0.0
        extra = f"\n🗄️ Backup: <code>char_merge_backup</code> (batch <code>{int(batch)}</code>, {len(backups)} record)"
        if live_skipped:
            extra += f"\nℹ️ live spawn ထဲမှာရှိလို့ ကျော်ထားတာ {len(live_skipped)} ခု — နောက်တစ်ခါ ထပ်run ပါ။"
        await _nph_edit(status, event, result_text + mop_note + extra)
    except Exception as e:
        print(f"⚠️ /mergenamephashdupes failed: {type(e).__name__}: {e}")
        await _nph_edit(status, event, f"❌ <b>Error:</b> <code>{escape_html(type(e).__name__)}: {escape_html(str(e)[:250])}</code>\n/findnamephashdupes နဲ့ ပြန်စစ်ပြီး ထပ်run လို့ရပါတယ် (ပေါင်းပြီးသားတွေက idempotent ပါ)။")
    finally:
        _NPH_MERGE_RUNNING = False
        if paused_by_us and _channel_work_changed_reason == "mergenamephashdupes":
            await _set_channel_work(True, reason="mergenamephashdupes finished")

# ==========================================
# 🔑 /takess — Owner Only: Retrieve the last saved userbot session (DM only)
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]takess(?:@\w+)?$', 'bot1')))
async def owner_take_session(event):
    # 1. Owner စစ်
    if event.sender_id != OWNER_ID:
        return

    # 2. DM မှသာ ခွင့်ပြုမယ်
    if not event.is_private:
        return await event.reply("⚠️ ဒီ Command ကို Bot ၏ DM (Private Chat) တွင်သာ သုံးနိုင်ပါသည်။", parse_mode='html')

    # 3. Duplicate Event ကာကွယ်
    if is_duplicate_event(event):
        return

    # 4. နောက်ဆုံး Session ကို ရှာမယ် (xbot_monitor_session ID နဲ့ သိမ်းထားတာ)
    try:
        doc = await bot_settings_col.find_one({"_id": "xbot_monitor_session"})
    except Exception as e:
        return await event.reply(f"❌ Session ရှာဖွေနေစဉ် အမှားရှိသွားသည်: <code>{escape_html(str(e))}</code>", parse_mode='html')

    # 5. Session မရှိရင် ပြန်ကြားမယ်
    if not doc or not doc.get("session"):
        return await event.reply(
            "📭 <b>Session မတွေ့ပါ။</b>\n"
            "အရင်ဆုံး <code>/xbotsetsession [string_session]</code> နဲ့ သိမ်းဆည်းပါ။",
            parse_mode='html'
        )

    # 6. Session Data ကို ပြန်ယူမယ်
    session_string = doc.get("session")
    
    # 7. သိမ်းဆည်းခဲ့တဲ့ အချိန်ကိုပါ ပြန်ပြမယ် (သိမ်းထားရင်)
    timestamp = doc.get("updated_at") or doc.get("set_at")  # field name က ရှိသလိုပါ
    if timestamp:
        dt = datetime.fromtimestamp(timestamp, TZ).strftime("%Y-%m-%d %H:%M:%S")
        time_str = f"📅 <b>သိမ်းဆည်းခဲ့သည့်အချိန်:</b> <code>{dt}</code>\n"
    else:
        time_str = ""

    # 8. လုံခြုံရေးအတွက် Session String ကို Code Block နဲ့ ပြမယ် (Copy ကူးလို့ရအောင်)
    await event.reply(
        f"🔑 <b>Userbot Session ကို တွေ့ရှိပါပြီ!</b>\n"
        f"{time_str}"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<code>{escape_html(session_string)}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>⚠️ ဒီ Session String ကို လုံခြုံစွာ သိမ်းဆည်းပါ။ ဘယ်သူ့ကိုမှ မပြပါနဲ့။</i>",
        parse_mode='html'
    )
# ==========================================
# 🧬 NAME-BASED duplicates — exact-media matching alone misses cases like catch_bot re-issuing
# "the same" character under a new id
# with a DIFFERENT video edit/upload — not a byte-identical file, so no shared identity, but
# unmistakably the same character (same name/anime/rarity) to a human. This groups on THOSE
# fields instead. Riskier than exact-media matching — two genuinely different characters COULD
# coincidentally share name+category+rarity — so /findnamedupes is report-only; review it before
# running /mergenamedupes.
# ==========================================
async def _find_duplicate_char_groups_by_name():
    docs = await characters_base_col.find(
        {}, {"char_id": 1, "name": 1, "category": 1, "rarity_tier": 1, "_id": 0}
    ).to_list(length=None)
    groups = {}
    for d in docs:
        key = (
            normalize_name(d.get("name", "")),
            normalize_name(d.get("category", "")),
            d.get("rarity_tier", "")
        )
        if not key[0]:
            continue  # no name at all — nothing meaningful to group on
        groups.setdefault(key, []).append(d["char_id"])
    return {k: v for k, v in groups.items() if len(v) > 1}

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]findnamedupes(?:@\w+)?$', 'bot1')))
async def find_name_duplicate_chars_command(event):
    """Read-only report — see _find_duplicate_char_groups_by_name. Name/category/rarity matching
    has a higher false-positive risk than exact-media matching, so review this list before
    running /mergenamedupes."""
    if event.sender_id != OWNER_ID: return
    status = await event.reply("⏳ Scanning the roster for characters sharing the same name/anime/rarity...")
    groups = await _find_duplicate_char_groups_by_name()
    if not groups:
        return await status.edit("✅ No name-based duplicates found.")
    total_redundant = sum(len(g) - 1 for g in groups.values())
    lines = [f"⚠️ <b>{len(groups)} name-based group(s)</b>, {total_redundant} redundant character record(s):"]
    for char_ids in list(groups.values())[:20]:
        sample = await characters_base_col.find_one({"char_id": char_ids[0]})
        name = sample.get("name", "?") if sample else "?"
        shown_ids = sorted(char_ids, key=_char_id_sort_key)
        lines.append(f"  • {escape_html(name)}: {', '.join(f'<code>{display_char_id(c)}</code>' for c in shown_ids)}")
    if len(groups) > 20:
        lines.append(f"  … and {len(groups) - 20} more group(s)")
    lines.append("\n⚠️ Same name+anime+rarity, but NOT verified to be the exact same media file — double-check a few before merging. Run <code>/mergenamedupes confirm</code> once you're confident.")
    await status.edit("\n".join(lines), parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]mergenamedupes(?:@\w+)?(?:\s+(confirm))?$', 'bot1')))
async def merge_name_duplicate_chars_command(event):
    if event.sender_id != OWNER_ID: return
    confirmed = bool(event.pattern_match.group(1))
    status = await event.reply("⏳ Scanning for name-based duplicates...")
    groups = await _find_duplicate_char_groups_by_name()
    if not groups:
        return await status.edit("✅ No name-based duplicates found — nothing to merge.")
    total_redundant = sum(len(g) - 1 for g in groups.values())

    if not confirmed:
        preview_lines = []
        for char_ids in list(groups.values())[:15]:
            shown_ids = sorted(char_ids, key=_char_id_sort_key)
            canonical, dupes = shown_ids[0], shown_ids[1:]
            preview_lines.append(f"  {', '.join(display_char_id(c) for c in dupes)} → {display_char_id(canonical)}")
        more = f"\n  ...and {len(groups) - 15} more group(s)" if len(groups) > 15 else ""
        return await event.reply(
            f"⚠️ <b>About to merge {len(groups)} name-based group(s)</b> ({total_redundant} redundant "
            f"character record(s)) down to their lowest/earliest id:\n\n"
            f"<code>{chr(10).join(preview_lines)}{more}</code>\n\n"
            f"These matched on name+anime+rarity ONLY, not exact media — please have skimmed "
            f"/findnamedupes's list first. Every owned copy in every player's /harem — and any "
            f"Favourite — gets reassigned to the canonical id first; nobody loses a card.\n\n"
            f"Reply <code>/mergenamedupes confirm</code> to proceed. Not reversible automatically.",
            parse_mode='html'
        )

    await status.edit(f"🔄 <b>Merging {len(groups)} name-based group(s)...</b>", parse_mode='html')
    result_text = await _execute_char_merge(groups, "/mergenamedupes")
    await status.edit(result_text, parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]pruneunconfirmed(?:\s+(\d+))?(?:\s+(confirm))?$', 'bot1')))
async def prune_unconfirmed_command(event):
    """Removes BOD<n> characters (n <= max_id, default CATCHBOT_SYNC_MAX_ID) that have NEVER
    actually been confirmed by a real .check <n> reply from catch_bot (synced_via_check isn't
    True — see store_character_from_check) — i.e. something sitting at a number inside catch_bot's
    real range that got there some OTHER way (the old racy channel-listener counter fixed in
    _generate_new_char_id, a historical bulk edit, etc.) and was never actually verified against
    what catch_bot currently has at that specific number.
    ⚠️ This only READS existing check history — it doesn't check anything itself. Run
    /syncfromcatch (however long that takes on however many accounts you're comfortable with)
    or spot-check individual ids with /checksync first, so synced_via_check is actually
    up to date before pruning by it. Same ownership-safety + preview-then-confirm shape used
    elsewhere in this file — never deletes a character a real player already has in their /harem."""
    if event.sender_id != OWNER_ID: return
    max_id = int(event.pattern_match.group(1)) if event.pattern_match.group(1) else CATCHBOT_SYNC_MAX_ID
    confirmed = bool(event.pattern_match.group(2))
    docs = await characters_base_col.find(
        {"char_id": {"$regex": r"^BOD\d+$"}}, {"char_id": 1, "synced_via_check": 1}
    ).to_list(length=None)
    unconfirmed = []
    for d in docs:
        try:
            num = int(d["char_id"][3:])
        except ValueError:
            continue
        if num <= max_id and not d.get("synced_via_check"):
            unconfirmed.append(d["char_id"])
    if not unconfirmed:
        return await event.reply(f"✅ Every BOD id 1-{max_id} already has a confirmed .check match — nothing to prune.")
    owned = set()
    for i in range(0, len(unconfirmed), 500):
        batch = unconfirmed[i:i + 500]
        async for holder in users_catcher_col.find({"harem.char_id": {"$in": batch}}, {"harem.char_id": 1}):
            for h in holder.get("harem", []):
                if isinstance(h, dict) and h.get("char_id") in batch:
                    owned.add(h["char_id"])
    # 🩹 CHANGED (per owner request): this used to skip anything a player already owned,
    # leaving stale/never-confirmed characters (e.g. old-system /addchar entries that got
    # dumped into the wrong rarity before catch_bot numbering existed) permanently stuck in
    # the roster just because someone had caught one. Now everything unconfirmed is deleted
    # regardless of ownership — see the harem/favourites cleanup right below, which pulls
    # these char_ids out of every owner's collection first so nothing dangling is left behind.
    to_delete = unconfirmed

    if not confirmed:
        owned_note = (
            f"⚠️ {len(owned)} are owned by real players — they will be DELETED too, and "
            f"removed from those players' /harem and favourites.\n"
            if owned else ""
        )
        return await event.reply(
            f"⚠️ <b>{len(unconfirmed)} character(s)</b> in the 1-{max_id} range have never been "
            f"confirmed by a real .check reply from catch_bot.\n"
            f"{owned_note}"
            f"🗑️ {len(to_delete)} total will be removed.\n\n"
            f"Reply <code>/pruneunconfirmed {max_id} confirm</code> to proceed.",
            parse_mode='html'
        )

    status = await event.reply(f"🔄 Pruning {len(to_delete)} unconfirmed character(s)...")
    if to_delete:
        # Pull every copy of these char_ids out of every player's harem/favourites BEFORE the
        # character docs themselves are deleted, so /harem, /profile, gifting, etc. never trip
        # over a harem entry pointing at a char_id that no longer exists.
        await users_catcher_col.update_many(
            {"harem.char_id": {"$in": to_delete}},
            {"$pull": {"harem": {"char_id": {"$in": to_delete}}}}
        )
        await users_catcher_col.update_many(
            {"fav_card": {"$in": to_delete}},
            {"$unset": {"fav_card": ""}}
        )
        await users_catcher_col.update_many(
            {"fav_cards": {"$in": to_delete}},
            {"$pull": {"fav_cards": {"$in": to_delete}}}
        )
    removed = 0
    for cid in to_delete:
        try:
            doc = await characters_base_col.find_one({"char_id": cid})
            if doc and doc.get("storage_msg_id"):
                try:
                    await bot1.delete_messages(SPECIFIC_CONTROL_GROUP, [doc["storage_msg_id"]])
                except Exception:
                    pass
            await characters_base_col.delete_one({"char_id": cid})
            _CHAR_PHOTO_CACHE.pop(cid, None)
            removed += 1
        except Exception as e:
            print(f"⚠️ /pruneunconfirmed failed for {cid}: {e}")
    await invalidate_character_caches()
    await status.edit(
        f"✅ Removed {removed}/{len(to_delete)} unconfirmed character(s) "
        f"({len(owned)} were owned — pulled from harems/favourites too).\n"
        f"Run /warmmediacache to refresh the identity cache.",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]pruneoutofrange(?:\s+(confirm))?$', 'bot1')))
async def prune_out_of_range_command(event):
    """Removes BOD<n> characters where n falls OUTSIDE the current /syncfromcatch window
    (CATCHBOT_SYNC_MIN_ID..CATCHBOT_SYNC_MAX_ID) — e.g. after the owner narrows or shifts the
    range with /syncfromcatchrange and wants ids that used to be in-scope, but no longer are,
    cleaned up too. Same ownership-safety + preview-then-confirm shape as /pruneunconfirmed:
    never deletes a character a real player already has in their /harem, whatever its id."""
    if event.sender_id != OWNER_ID: return
    confirmed = bool(event.pattern_match.group(1))
    docs = await characters_base_col.find(
        {"char_id": {"$regex": r"^BOD\d+$"}}, {"char_id": 1}
    ).to_list(length=None)
    out_of_range = []
    for d in docs:
        try:
            num = int(d["char_id"][3:])
        except ValueError:
            continue
        if num < CATCHBOT_SYNC_MIN_ID or num > CATCHBOT_SYNC_MAX_ID:
            out_of_range.append(d["char_id"])
    if not out_of_range:
        return await event.reply(
            f"✅ Every BOD id is already inside the {CATCHBOT_SYNC_MIN_ID}-{CATCHBOT_SYNC_MAX_ID} "
            f"range — nothing to prune."
        )
    owned = set()
    for i in range(0, len(out_of_range), 500):
        batch = out_of_range[i:i + 500]
        async for holder in users_catcher_col.find({"harem.char_id": {"$in": batch}}, {"harem.char_id": 1}):
            for h in holder.get("harem", []):
                if isinstance(h, dict) and h.get("char_id") in batch:
                    owned.add(h["char_id"])
    # 🩹 CHANGED (per owner request): same reasoning as /pruneunconfirmed above — ownership no
    # longer protects an out-of-range character from deletion. Harem/favourites are cleaned up
    # for every affected owner before the character docs are removed.
    to_delete = out_of_range

    if not confirmed:
        owned_note = (
            f"⚠️ {len(owned)} are owned by real players — they will be DELETED too, and "
            f"removed from those players' /harem and favourites.\n"
            if owned else ""
        )
        return await event.reply(
            f"⚠️ <b>{len(out_of_range)} character(s)</b> fall outside the current "
            f"<code>{CATCHBOT_SYNC_MIN_ID}-{CATCHBOT_SYNC_MAX_ID}</code> sync range.\n"
            f"{owned_note}"
            f"🗑️ {len(to_delete)} total will be removed.\n\n"
            f"Reply <code>/pruneoutofrange confirm</code> to proceed.",
            parse_mode='html'
        )

    status = await event.reply(f"🔄 Pruning {len(to_delete)} out-of-range character(s)...")
    if to_delete:
        await users_catcher_col.update_many(
            {"harem.char_id": {"$in": to_delete}},
            {"$pull": {"harem": {"char_id": {"$in": to_delete}}}}
        )
        await users_catcher_col.update_many(
            {"fav_card": {"$in": to_delete}},
            {"$unset": {"fav_card": ""}}
        )
        await users_catcher_col.update_many(
            {"fav_cards": {"$in": to_delete}},
            {"$pull": {"fav_cards": {"$in": to_delete}}}
        )
    removed = 0
    for cid in to_delete:
        try:
            doc = await characters_base_col.find_one({"char_id": cid})
            if doc and doc.get("storage_msg_id"):
                try:
                    await bot1.delete_messages(SPECIFIC_CONTROL_GROUP, [doc["storage_msg_id"]])
                except Exception:
                    pass
            await characters_base_col.delete_one({"char_id": cid})
            _CHAR_PHOTO_CACHE.pop(cid, None)
            removed += 1
        except Exception as e:
            print(f"⚠️ /pruneoutofrange failed for {cid}: {e}")
    await invalidate_character_caches()
    await status.edit(
        f"✅ Removed {removed}/{len(to_delete)} out-of-range character(s) "
        f"({len(owned)} were owned — pulled from harems/favourites too).\n"
        f"Run /warmmediacache to refresh the identity cache.",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]clearxbothashes(?:\s+(confirm))?$', 'bot1')))
async def clear_xbot_hashes_command(event):
    """xbot_hashes_col is a SEPARATE lookup index (hash -> name/source_bot) used only for
    recognizing OTHER bots' characters via /xbotcheck-style cross-bot identify — it has nothing
    to do with your own roster (characters_base_col), harem, or spawns, so clearing it can never
    cost a player a card. Safe to wipe any time; /xbotresync rebuilds it from scratch."""
    if event.sender_id != OWNER_ID: return
    confirmed = bool(event.pattern_match.group(1))
    total = await xbot_hashes_col.count_documents({})
    if not confirmed:
        return await event.reply(
            f"⚠️ This deletes all <b>{total}</b> xbot_hashes_col record(s) (cross-bot identify "
            f"index only — separate from your own characters/harem, nobody's collection is "
            f"affected). Reply <code>/clearxbothashes confirm</code> to proceed.",
            parse_mode='html'
        )
    result = await xbot_hashes_col.delete_many({})
    await event.reply(f"✅ Cleared {result.deleted_count} xbot_hashes_col record(s).")

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]relinkid\s+(\S+)$', 'bot1')))
async def relink_id_command(event):
    """Manual fallback for exactly the case being reported: catch_bot posts a media UPDATE for
    an EXISTING id, but for whatever reason it wasn't auto-recognized as one (see
    _maybe_sync_image_update — this does the identical storage-side work by hand). Reply to the
    message with the NEW media, e.g. `/relinkid BOD4971`, and that existing character's stored
    media is swapped in place — no new character, no new id, no duplicate."""
    if event.sender_id != OWNER_ID: return
    char_id = event.pattern_match.group(1).upper()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        return await event.reply(f"❌ <code>{char_id}</code> not found.", parse_mode='html')
    if not event.is_reply:
        return await event.reply("↩️ Reply to the message that has the NEW media for this character.")
    reply_msg = await event.get_reply_message()
    if not (reply_msg.photo or reply_msg.video or reply_msg.document):
        return await event.reply("❌ That message has no media.")
    try:
        forwarded_msg = await send_safe_message(bot1, SPECIFIC_CONTROL_GROUP, "", file=reply_msg.media)
        new_hash = await compute_phash_for_message(reply_msg)
        await characters_base_col.update_one(
            {"char_id": char_id},
            {"$set": {"storage_msg_id": forwarded_msg.id, "photo_phash": new_hash}}
        )
        _CHAR_PHOTO_CACHE.pop(char_id, None)
        prewarm_media_identity_cache(forwarded_msg, char_id)
        await invalidate_character_caches()
        await event.reply(f"✅ Re-linked <code>{char_id}</code>'s media in place — no new character created.", parse_mode='html')
    except Exception as e:
        await event.reply(f"❌ Failed: <code>{escape_html(str(e))}</code>", parse_mode='html')

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
    r_info = _resolve_check_rarity(new_rarity_raw, imported)
    if not r_info:
        await bot1.send_message(
            OWNER_ID,
            f"⚠️ <b>Rarity sync skipped</b> — <code>{escape_html(imported['char_id'])}</code> "
            f"<code>{escape_html(name)}</code>: unrecognized rarity <code>{escape_html(new_rarity_raw)}</code>.",
            parse_mode='html'
        )
        return True
    await characters_base_col.update_one(
        {"_id": imported["_id"]},
        {"$set": {"rarity": r_info["name"], "rarity_tier": classify_rarity(r_info["name"]), "source_rarity": new_rarity_raw}}
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

# ==========================================================================================
# ⚡ AUTO NAME REVEAL FOR catch_bot SPAWNS (per owner request)
# ------------------------------------------------------------------------------------------
# WHAT: the moment catch_bot (CATCH_BOT_ID) drops a spawn — media + the "... has spawned in
# the chat!" caption — in ANY chat, reply to that spawn with the same reveal card /w gives
# (ငါတွေ့ပီ 🔎 · Name · ID · Anime · Rarity · event · /catch <name>). Nobody has to type /w.
#
# HOW bot1 GETS HERE: nonhuman_sender_gate (BOT-SENDER GATE block, right after bot1's creation)
# is bot1's first NewMessage handler; it hands catch_bot's spawn media to
# autoname_catchbot_spawn_handler below and stops propagation, so catch_bot's messages never
# reach any other handler (spawn counters included).
#
# WHAT IT DOES NOT TOUCH: only catch_bot's OWN posts trigger this (sender_id == CATCH_BOT_ID).
# Media a user posts, reposts or forwards is ignored here and keeps going through /who exactly
# as before. bot1's own spawns are ignored too — their caption looks the same, but the sender
# is bot1, not catch_bot.
#
# WHY IT'S CHEAP:
#   * Lookup = find_character_by_media(), the SAME pipeline /who uses: raw file-id cache
#     first (dict lookup, no download), then phash. A spawn image catch_bot re-serves is
#     therefore usually a plain dict hit.
#   * In-flight coalescing: the same file spawning in 50 chats at once is hashed ONCE.
#   * A small semaphore caps concurrent cold lookups so a burst can't starve the event loop.
#   * (chat_id, msg_id) de-dupe, so bot1 AND the monitor userbot both seeing one spawn can't
#     produce two replies.
#   * One shared keep-alive HTTPS client for the Bot API send (no TLS handshake per reveal).
#   * Every cache here is bounded and self-pruning.
#
# WHAT IT NEVER DOES: reply from the userbot account. When the monitor userbot is the one that
# saw the spawn, the reply still goes out from bot1 — and if bot1 isn't in that chat (or can't
# write there) the chat is remembered as "dead" for AUTONAME_DEAD_CHAT_TTL and skipped silently.
# It also never leaves a chat over a send failure (unlike _handle_write_forbidden).
#
# UNKNOWN CARD: stays silent (no "not recognized" spam in every group). Players tell the owner;
# once the card is added, a stale "no match" for that file is re-checked after
# AUTONAME_NEG_RECHECK_SECONDS instead of waiting out the 5-minute negative cache.
#
# ⚠️ TELEGRAM-SIDE REQUIREMENT (code can't change this): bots do NOT receive other bots'
# messages in groups by default. For bot1 to SEE catch_bot's spawn it needs, in @BotFather,
# "Bot-to-Bot Communication Mode" enabled, AND in the group: bot1 is admin + Group Privacy off.
# Where that isn't true, only the monitor userbot (if it is a member of that group) can see it.
# ==========================================================================================
AUTONAME_ENABLED = True                # owner switch: /autoname on|off (persisted, see below)
AUTONAME_LOOKUP_TIMEOUT = 12           # s — a reveal later than this is useless, spawn is over
AUTONAME_MAX_CONCURRENT_LOOKUPS = 4    # cold (download+hash) lookups allowed at once
AUTONAME_NEG_RECHECK_SECONDS = 30      # a cached "no match" older than this is re-checked
AUTONAME_DEAD_CHAT_TTL = 1800          # s — skip a chat bot1 can't post in for this long
AUTONAME_MAX_FLOOD_WAIT = 5            # s — longer flood waits: drop the reveal, it's stale
AUTONAME_HTTP_TIMEOUT = 8

_AUTONAME_SEEN = {}        # (chat_id, msg_id) -> ts  — de-dupe across bot1 + userbot
_AUTONAME_INFLIGHT = {}    # media_key -> asyncio.Task — lookup coalescing
_AUTONAME_DEAD_CHATS = {}  # (bot_name, chat_id) -> until_ts
_AUTONAME_STATS = Counter()
_autoname_sem = None       # created lazily INSIDE the running loop (safe on every Python version)
_autoname_http = None
_autoname_last_alert = 0.0

async def load_autoname_setting():
    """Loads the persisted /autoname switch at boot (same pattern as load_channel_work_cache)."""
    global AUTONAME_ENABLED
    try:
        doc = await bot_settings_col.find_one({"_id": "autoname_enabled"})
        if doc is not None and "enabled" in doc:
            AUTONAME_ENABLED = bool(doc["enabled"])
    except Exception as e:
        print(f"load_autoname_setting error: {e}")

async def _set_autoname(enabled: bool):
    global AUTONAME_ENABLED
    AUTONAME_ENABLED = enabled
    try:
        await bot_settings_col.update_one(
            {"_id": "autoname_enabled"},
            {"$set": {"enabled": enabled, "changed_at": time.time()}},
            upsert=True
        )
    except Exception as e:
        print(f"_set_autoname persist error: {e}")

# ---- Spawn caption detection --------------------------------------------------------------
# catch_bot sprinkles invisible characters (zero-width space/non-joiner, word joiner, BOM)
# through its caption, so a plain substring test never matches. Normalization: drop every
# control/format/space/combining character, fold the small-caps letters (ᴀ ʙ ᴄ ...) to plain
# ASCII, lower-case. What's left of "ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ" is "hasspawnedinthechat" —
# immune to whatever gets inserted between the letters, and to the changing rarity emoji.
_AUTONAME_SMALLCAPS = str.maketrans({
    "ᴀ": "a", "ʙ": "b", "ᴄ": "c", "ᴅ": "d", "ᴇ": "e", "ꜰ": "f", "ɢ": "g", "ʜ": "h",
    "ɪ": "i", "ᴊ": "j", "ᴋ": "k", "ʟ": "l", "ᴍ": "m", "ɴ": "n", "ᴏ": "o", "ᴘ": "p",
    "ǫ": "q", "ʀ": "r", "ꜱ": "s", "ᴛ": "t", "ᴜ": "u", "ᴠ": "v", "ᴡ": "w", "ʏ": "y", "ᴢ": "z",
})
# Either phrase alone is enough (both appear in the real caption) — if catch_bot rewords one
# half, the other still matches.
_AUTONAME_SPAWN_MARKERS = ("spawnedinthechat", "yourharemusing/catch")

def _autoname_norm(text):
    if not text:
        return ""
    kept = []
    for ch in text:
        cat = unicodedata.category(ch)
        if cat[0] in ("C", "Z") or cat in ("Mn", "Me"):
            continue
        kept.append(ch)
    return "".join(kept).translate(_AUTONAME_SMALLCAPS).translate(_FANCY_TO_PLAIN).lower()

def is_catchbot_spawn_caption(caption):
    n = _autoname_norm(caption)
    return any(marker in n for marker in _AUTONAME_SPAWN_MARKERS)

def _autoname_event_filter(e):
    """Cheap SYNC pre-filter (runs before the handler is even scheduled): catch_bot's own
    photo/video, in a non-private chat. Anything else never costs a coroutine."""
    try:
        if e.sender_id != CATCH_BOT_ID or e.is_private:
            return False
        m = e.message
        return bool((m.photo or m.video) and not m.sticker)
    except Exception:
        return False

# ---- Bounded bookkeeping ------------------------------------------------------------------
def _autoname_mark_seen(chat_id, msg_id):
    """True the first time (chat_id, msg_id) is seen, False for a duplicate delivery."""
    key = (chat_id, msg_id)
    if key in _AUTONAME_SEEN:
        return False
    now = time.time()
    _AUTONAME_SEEN[key] = now
    if len(_AUTONAME_SEEN) > 4000:
        cutoff = now - 300
        for k in [k for k, t in _AUTONAME_SEEN.items() if t < cutoff]:
            _AUTONAME_SEEN.pop(k, None)
        if len(_AUTONAME_SEEN) > 4000:  # everything is recent — drop the oldest half
            for k in list(_AUTONAME_SEEN)[:2000]:
                _AUTONAME_SEEN.pop(k, None)
    return True

def _autoname_bot_names():
    names = ["bot1"]
    if bot2 is not None:
        names.append("bot2")
    return names

def _autoname_mark_dead(bot_name, chat_id):
    """Per-bot: bot1 not being able to post in a chat must NOT stop bot2 from trying."""
    now = time.time()
    _AUTONAME_DEAD_CHATS[(bot_name, chat_id)] = now + AUTONAME_DEAD_CHAT_TTL
    if len(_AUTONAME_DEAD_CHATS) > 5000:
        for k in [k for k, until in _AUTONAME_DEAD_CHATS.items() if until < now]:
            _AUTONAME_DEAD_CHATS.pop(k, None)

def _autoname_is_dead(bot_name, chat_id):
    until = _AUTONAME_DEAD_CHATS.get((bot_name, chat_id))
    if until is None:
        return False
    if until < time.time():
        _AUTONAME_DEAD_CHATS.pop((bot_name, chat_id), None)
        return False
    return True

def _autoname_all_bots_dead(chat_id):
    """True when every configured bot is known to be unable to post here -> skip the lookup."""
    return all(_autoname_is_dead(n, chat_id) for n in _autoname_bot_names())

async def _autoname_alert_once(location, detail):
    """Owner alert for genuinely unexpected failures — at most one per 15 minutes in total,
    so a persistent problem can never turn into an alert per spawn."""
    global _autoname_last_alert
    print(f"⚠️ {location}: {detail}")
    now = time.time()
    if now - _autoname_last_alert < 900:
        return
    _autoname_last_alert = now
    await report_system_error(location, detail)

# ---- Lookup ---------------------------------------------------------------------------------
def _get_autoname_sem():
    global _autoname_sem
    if _autoname_sem is None:
        _autoname_sem = asyncio.Semaphore(AUTONAME_MAX_CONCURRENT_LOOKUPS)
    return _autoname_sem

async def _autoname_lookup(msg):
    """Character doc for this spawn's media, or None. Shares find_character_by_media's caches
    with /who, coalesces concurrent lookups of the same file, and caps cold-lookup concurrency."""
    key = get_media_identity_key(msg)
    if key is None:
        return None
    # A "no match" is normally trusted for 5 minutes (MEDIA_IDENTIFY_NEGATIVE_CACHE_TTL). Here
    # it's re-checked after AUTONAME_NEG_RECHECK_SECONDS so a card the owner just added is
    # recognized almost immediately instead of staying "unknown" for minutes.
    cached = _MEDIA_ID_CACHE.get(key)
    if cached and cached[0] is None and (time.time() - cached[1]) > AUTONAME_NEG_RECHECK_SECONDS:
        _MEDIA_ID_CACHE.pop(key, None)

    task = _AUTONAME_INFLIGHT.get(key)
    if task is None:
        async def _run():
            async with _get_autoname_sem():
                return await find_character_by_media(msg)
        task = asyncio.ensure_future(_run())
        _AUTONAME_INFLIGHT[key] = task

        def _done(t, k=key):
            _AUTONAME_INFLIGHT.pop(k, None)
            if not t.cancelled():
                t.exception()  # mark retrieved — a late failure must not log "never retrieved"
        task.add_done_callback(_done)
    # shield: one waiter timing out must not cancel the lookup the other waiters share
    return await asyncio.wait_for(asyncio.shield(task), AUTONAME_LOOKUP_TIMEOUT)

# ---- Reveal card (same layout as _identify_media_and_reply's) -------------------------------
def _autoname_build_text(char):
    tier = classify_rarity(char.get("rarity", ""))
    rarity_emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
    ev = char.get("event")
    event_line = escape_html(ev) if ev and ev != "General" else "➖"
    name = char.get("name") or "?"
    lines = [
        "<b>ငါတွေ့ပီ 🔎</b>",
        "",
        f"<b>Name:</b> <b>{escape_html(name)}</b>",
        f"🔖 <b>Character ID:</b> <code>{display_char_id(char.get('char_id'))}</code>",
        f"🍹 <b>Anime:</b> {escape_html(str(char.get('category') or '?'))}",
        f"{rarity_emoji} <b>Rarity:</b> {escape_html(str(char.get('rarity') or '?'))}",
        event_line,
    ]
    artist = artist_line(char, suffix="")
    if artist:
        lines.append(artist)
    lines += ["", f"<code>{escape_html('/catch ' + name)}</code>", "", "Have a good life."]
    return "\n".join(lines)

# ---- Send -------------------------------------------------------------------------------------
_AUTONAME_DEAD_HINTS = (
    "chat not found", "bot was kicked", "bot is not a member", "not enough rights",
    "have no rights to send", "chat_write_forbidden", "bot was blocked", "peer_id_invalid",
    "chat_send_plain_forbidden",
)
_AUTONAME_DEAD_ERRORS = tuple(
    getattr(errors, n) for n in (
        "ChatWriteForbiddenError", "ChannelPrivateError", "UserBannedInChannelError",
        "ChatAdminRequiredError", "PeerIdInvalidError",
    ) if hasattr(errors, n)
)

async def _get_autoname_http():
    global _autoname_http
    if _autoname_http is None:
        import httpx  # already a dependency — see bot_api_send_with_copy_buttons
        _autoname_http = httpx.AsyncClient(
            timeout=AUTONAME_HTTP_TIMEOUT,
            limits=httpx.Limits(max_keepalive_connections=10, keepalive_expiry=60),
        )
    return _autoname_http

async def _autoname_send_via(bot_name, client, bot_token, chat_id, reply_to, text_html, copy_text):
    """Posts the reveal as ONE specific bot, replying to the spawn. Preferred route: Bot API with
    a one-tap 'copy /catch' button (the deployed Telethon has no KeyboardButtonCopy — see
    reply_with_copy_buttons) over one shared keep-alive client. Falls back to a plain Telethon
    send (the /catch line is <code>, which is tap-to-copy on its own).
    Returns True if sent, False if THIS bot can't post in this chat (caller tries the next bot)."""
    payload = {
        "chat_id": chat_id,
        "text": text_html,
        "parse_mode": "HTML",
        "reply_parameters": {"message_id": reply_to, "allow_sending_without_reply": True},
        "reply_markup": {"inline_keyboard": [[{"text": "📋 /catch", "copy_text": {"text": copy_text}}]]},
    }
    url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
    for attempt in (1, 2):
        data = None
        try:
            http = await _get_autoname_http()
            resp = await http.post(url, json=payload)
            data = resp.json()
        except Exception as e:
            print(f"autoname Bot API request failed ({bot_name}): {type(e).__name__}")  # never print e: URL holds the token
        if data is None:
            break  # network hiccup — try the plain Telethon send below
        if data.get("ok"):
            return True
        code = data.get("error_code")
        desc = (data.get("description") or "").lower()
        if code == 429 and attempt == 1:
            wait = (data.get("parameters") or {}).get("retry_after", 1)
            if wait <= AUTONAME_MAX_FLOOD_WAIT:
                await asyncio.sleep(wait + 0.2)
                continue
            return False
        if code in (401, 403) or any(h in desc for h in _AUTONAME_DEAD_HINTS):
            _autoname_mark_dead(bot_name, chat_id)
            return False
        break  # anything else (e.g. buttons rejected) — plain send below

    try:
        await client.send_message(chat_id, text_html, reply_to=reply_to, parse_mode='html')
        return True
    except FloodWaitError as fw:
        if fw.seconds <= AUTONAME_MAX_FLOOD_WAIT:
            await asyncio.sleep(fw.seconds + 0.2)
            try:
                await client.send_message(chat_id, text_html, reply_to=reply_to, parse_mode='html')
                return True
            except Exception:
                return False
        return False
    except _AUTONAME_DEAD_ERRORS:
        _autoname_mark_dead(bot_name, chat_id)
        return False
    except Exception as e:
        # ValueError = this client has never seen this chat (typical when it isn't a member)
        if isinstance(e, ValueError):
            _autoname_mark_dead(bot_name, chat_id)
            return False
        raise

async def _autoname_send(chat_id, reply_to, text_html, copy_text):
    """bot1 first, bot2 only if bot1 can't post in this chat. THE one place that decides who
    answers — it doesn't matter which client saw the spawn (bot1, bot2 or the monitor userbot;
    _autoname_mark_seen already collapses those to a single run), so both bots present -> bot1
    replies and bot2 stays silent. Returns True if a reveal was sent."""
    bots = [("bot1", bot1, MAIN_BOT_TOKEN)]
    if bot2 is not None:
        bots.append(("bot2", bot2, SECONDARY_BOT_TOKEN))
    for bot_name, client, token in bots:
        if _autoname_is_dead(bot_name, chat_id):
            continue
        try:
            if await _autoname_send_via(bot_name, client, token, chat_id, reply_to, text_html, copy_text):
                return True
        except Exception as e:
            print(f"⚠️ autoname send via {bot_name} raised: {type(e).__name__}")
            continue  # try the next bot rather than losing the whole reveal
    return False

# ---- The handler ------------------------------------------------------------------------------
async def autoname_catchbot_spawn_handler(event):
    """bot1 reaches this through nonhuman_sender_gate (the first NewMessage handler, which
    hands catch_bot's spawn media here and then stops propagation — so it deliberately has NO
    @bot1.on decorator of its own). monitor_userbot registers it directly (see
    register_userbot_handlers). The (chat, msg) de-dupe makes it safe for both to fire."""
    if not AUTONAME_ENABLED:
        return
    t0 = time.time()
    try:
        msg = event.message
        chat_id = event.chat_id
        if chat_id == SPECIFIC_CONTROL_GROUP:
            return
        if not is_catchbot_spawn_caption(msg.raw_text):
            return  # some other catch_bot media (a .check card, a harem page, ...)
        if not _autoname_mark_seen(chat_id, msg.id):
            _AUTONAME_STATS["duplicate"] += 1
            return
        if _autoname_all_bots_dead(chat_id):
            _AUTONAME_STATS["skipped_dead_chat"] += 1
            return
        _AUTONAME_STATS["spawns_seen"] += 1

        try:
            char = await _autoname_lookup(msg)
        except asyncio.TimeoutError:
            _AUTONAME_STATS["lookup_timeout"] += 1
            print(f"⏱️ [autoname] lookup timed out in chat {chat_id}")
            return
        if not char:
            _AUTONAME_STATS["unknown_card"] += 1
            print(f"❓ [autoname] unknown card in chat {chat_id} (msg {msg.id}) — not in roster")
            return

        # Same guard as /who: don't confirm a character that's sitting behind an unsolved
        # rarity-gate quiz somewhere — that would leak the answer.
        char_id = char.get("char_id")
        for quiz in list(pending_rarity_quiz.values()):
            if not quiz.get("solved") and quiz.get("char", {}).get("char_id") == char_id:
                _AUTONAME_STATS["held_by_rarity_gate"] += 1
                return

        name = char.get("name") or ""
        if not name:
            return
        if await _autoname_send(chat_id, msg.id, _autoname_build_text(char), f"/catch {name}"):
            _AUTONAME_STATS["revealed"] += 1
            print(f"🔎 [autoname] {chat_id}: {name} in {time.time() - t0:.2f}s")
        else:
            _AUTONAME_STATS["send_failed"] += 1
    except Exception as e:
        _AUTONAME_STATS["errors"] += 1
        await _autoname_alert_once("autoname_catchbot_spawn_handler", f"{type(e).__name__}: {e}")

# bot2's ONLY handler: catch_bot's spawn media -> the same reveal pipeline. Registered here rather
# than up next to bot2's creation because _autoname_event_filter doesn't exist yet at that point
# in the file (func= is evaluated at import time). Runs as its own task, exactly like bot1's gate.
async def bot2_spawn_gate(event):
    try:
        task = asyncio.ensure_future(autoname_catchbot_spawn_handler(event))
        _BOTGATE_BG_TASKS.add(task)   # strong ref — asyncio only keeps weak refs to tasks
        task.add_done_callback(lambda t: (_BOTGATE_BG_TASKS.discard(t), t.cancelled() or t.exception()))
    except Exception as e:
        print(f"⚠️ bot2 gate: could not hand spawn to autoname: {type(e).__name__}: {e}")

if bot2 is not None:
    bot2.add_event_handler(bot2_spawn_gate, events.NewMessage(incoming=True, func=_autoname_event_filter))

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]autoname(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def autoname_toggle_command(event):
    if event.sender_id != OWNER_ID:
        return
    arg = (event.pattern_match.group(1) or "").strip().lower()
    if arg in ("on", "off"):
        await _set_autoname(arg == "on")
        return await event.reply(
            f"✅ <b>Auto name reveal is now {'ON ✅' if arg == 'on' else 'OFF ⛔'}</b>", parse_mode='html'
        )
    if arg:
        return await event.reply("❌ <code>/autoname on</code>, <code>/autoname off</code> or just <code>/autoname</code>.", parse_mode='html')
    s = _AUTONAME_STATS
    userbot_note = "✅ connected" if (monitor_userbot and monitor_userbot.is_connected()) else "❌ not connected"
    if bot2 is None:
        bot2_note = "⛔ disabled (SECONDARY_BOT_TOKEN not set)"
    elif bot2.is_connected():
        bot2_note = f"✅ @{BOT2_USERNAME}" if BOT2_USERNAME else "✅ connected"
    else:
        bot2_note = "❌ disconnected"
    await event.reply(
        f"<b>🔎 Auto name reveal:</b> {'ON ✅' if AUTONAME_ENABLED else 'OFF ⛔'}\n"
        f"Spawns seen: <code>{s['spawns_seen']}</code> · revealed: <code>{s['revealed']}</code>\n"
        f"Unknown card: <code>{s['unknown_card']}</code> · held by rarity gate: <code>{s['held_by_rarity_gate']}</code>\n"
        f"Send failed: <code>{s['send_failed']}</code> · lookup timeout: <code>{s['lookup_timeout']}</code> · errors: <code>{s['errors']}</code>\n"
        f"Duplicates dropped: <code>{s['duplicate']}</code> · dead chats skipped: <code>{s['skipped_dead_chat']}</code> "
        f"(<code>{len(_AUTONAME_DEAD_CHATS)}</code> currently marked)\n"
        f"Monitor userbot: {userbot_note}\n"
        f"Secondary bot (bot2): {bot2_note}\n"
        f"🚧 Gate — catch_bot msgs isolated: <code>{_BOTGATE_STATS['catchbot_isolated']}</code> · "
        f"other bots skipped: <code>{_BOTGATE_STATS['other_bots_skipped']}</code> · "
        f"unresolved (passed): <code>{_BOTGATE_STATS['unresolved_passed_through']}</code>\n\n"
        f"<i>Counters reset on restart. bot1 only sees catch_bot's spawns where Bot-to-Bot mode is on, "
        f"bot1 is admin and Group Privacy is off.</i>",
        parse_mode='html'
    )

def register_userbot_handlers(client):
    # 💾 /save — see its own comment further down (near the toggle command) for the full
    # writeup. Registered here (not as a plain @bot1.on decorator) because it needs to run on
    # monitor_userbot specifically, which doesn't exist yet at module-load time — this function
    # only runs once monitor_userbot has actually connected.
    client.add_event_handler(passive_catchbot_check_capture, events.NewMessage(from_users=CATCH_BOT_ID))
    # ⚡ auto name reveal — see AUTO NAME REVEAL block above. Replies still go out from bot1, never this account.
    client.add_event_handler(autoname_catchbot_spawn_handler, events.NewMessage(incoming=True, func=_autoname_event_filter))

# ---- The monitor userbot itself — a REAL Telegram account (not a bot token), logged in via
# a StringSession the owner supplies with /xbotsetsession. Stays None until that happens, or
# until load_and_start_monitor_userbot() finds a previously-saved session at boot. ----
monitor_userbot: Optional[TelegramClient] = None

# ==========================================
# 🧵 USERBOT WORKER POOL — extra real-account userbots (StringSessions) that share the heavy
# sweeps instead of everything running on monitor_userbot alone:
#   • /syncfromcatch (+ /syncfromcatch_parallel [n])  — the .check sweep over catch_bot; every
#     account in the pool takes ids from ONE shared queue, so N accounts ≈ N× faster.
#   • /xbotresync + /xbotimportall — channel-history walks.
#
# HOW TO ADD ACCOUNTS (any of these; they all end up in the same pool):
#   1. /xbotaddworker <StringSession> [label]   — DM only. Several accounts at once: one per
#      line. Validated, saved to Mongo (`sync_workers`), live immediately. The message with the
#      session strings is deleted right after.
#   2. WORKER_SESSIONS env var — sessions separated by newline / comma / space. Nothing is
#      written to Mongo, which is the safer place to keep them if the database was ever exposed.
#   3. the legacy powerranger_col / _col2 / _col3 collections ({"session":..., "name":...}).
# Manage: /xbotworkers (list) · /xbotworkers check (can each one really post in the storage
# group + reach catch_bot?) · /xbotremoveworker <n|label> · /xbotloadworkers (reload all).
#
# SYNC PACING: each account is paced individually at CATCHBOT_SYNC_DELAY_SECONDS — the same
# per-account rate a single-account /syncfromcatch already uses — and a cooldown reply from
# catch_bot backs THAT account off (see CATCHBOT_SYNC_COOLDOWN_HINTS) while the others carry on.
# ==========================================
POWER_RANGER_COLLECTIONS = ["powerranger_col", "powerranger_col2", "powerranger_col3"]
SYNC_WORKERS_COLLECTION = "sync_workers"          # written by /xbotaddworker; _id = telegram user id
worker_pool_clients: List[Tuple[TelegramClient, str]] = []
worker_pool_meta: Dict[str, dict] = {}            # label -> {"user_id", "source", "col"}
_worker_pool_load_lock = asyncio.Lock()
_worker_pool_loaded = False                       # flips True once the first load attempt finished

async def _connect_worker_session(session_str: str):
    """Connects one StringSession and returns (client, me). NEVER uses client.start(): on a dead
    session start() falls back to asking for a phone number on stdin, which hangs a server."""
    client = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
    try:
        await asyncio.wait_for(client.connect(), timeout=30)
        if not await client.is_user_authorized():
            raise RuntimeError("session not authorized (revoked, expired or not a user session)")
        me = await client.get_me()
        if getattr(me, "bot", False):
            raise RuntimeError("that is a bot-token session — .check needs a real user account")
        return client, me
    except BaseException:
        try:
            await client.disconnect()
        except Exception:
            pass
        raise

def _worker_env_sessions() -> List[Tuple[str, str]]:
    raw = os.environ.get("WORKER_SESSIONS", "") or ""
    toks = [t for t in re.split(r"[\s,;]+", raw.strip()) if len(t) >= 40]
    return [(t, f"env{i + 1}") for i, t in enumerate(toks)]

async def load_worker_pool():
    """Connects every saved session (powerranger collections + sync_workers + WORKER_SESSIONS
    env) concurrently and keeps the ones that log in in `worker_pool_clients`. Safe to call again
    (/xbotloadworkers): it disconnects and rebuilds the pool instead of stacking duplicates, and
    the same Telegram account found twice is only kept once.

    Document schema (unchanged): {"session": "<StringSession>", "name": "<label>"}."""
    global worker_pool_clients, _worker_pool_loaded
    SESSION_FIELD = "session"
    NAME_FIELD = "name"
    async with _worker_pool_load_lock:
        try:
            for old_client, _label in worker_pool_clients:
                try:
                    await old_client.disconnect()
                except Exception:
                    pass
            sources = []   # (session_str, label, source, collection)
            for col_name in POWER_RANGER_COLLECTIONS + [SYNC_WORKERS_COLLECTION]:
                try:
                    async for doc in db[col_name].find({}):
                        session_str = doc.get(SESSION_FIELD)
                        if session_str:
                            sources.append((session_str, doc.get(NAME_FIELD) or str(doc.get("_id")), col_name, col_name))
                except Exception as e:
                    print(f"⚠️ [worker pool] couldn't read {col_name}: {type(e).__name__}")
            for tok, label in _worker_env_sessions():
                sources.append((tok, label, "env", None))

            sem = asyncio.Semaphore(8)
            async def _one(src_row):
                async with sem:
                    return await _connect_worker_session(src_row[0])
            results = await asyncio.gather(*[_one(s) for s in sources], return_exceptions=True)

            loaded: List[Tuple[TelegramClient, str]] = []
            meta: Dict[str, dict] = {}
            seen_ids = set()
            for (session_str, label, source, col), res in zip(sources, results):
                if isinstance(res, BaseException):
                    print(f"❌ [worker pool] {source}/{label}: {type(res).__name__}: {str(res)[:120]}")
                    continue
                client, me = res
                if me.id in seen_ids:
                    print(f"ℹ️ [worker pool] {source}/{label}: same account as another worker — skipped.")
                    try:
                        await client.disconnect()
                    except Exception:
                        pass
                    continue
                seen_ids.add(me.id)
                full = f"{label} (@{me.username or me.id})"
                loaded.append((client, full))
                meta[full] = {"user_id": me.id, "source": source, "col": col}
                print(f"✅ [worker pool] Loaded {source}/{label} as @{me.username or me.id}")
            worker_pool_clients = loaded
            worker_pool_meta.clear()
            worker_pool_meta.update(meta)
            print(f"🚀 [worker pool] {len(worker_pool_clients)} worker(s) ready for /syncfromcatch, /xbotresync + /xbotimportall.")
        finally:
            _worker_pool_loaded = True

def _get_history_workers() -> List[Tuple[TelegramClient, str]]:
    """Which accounts /xbotresync + /xbotimportall should split channel history across: the
    loaded pool if there is one, otherwise just monitor_userbot alone (today's behavior)."""
    if worker_pool_clients:
        return worker_pool_clients
    if monitor_userbot and monitor_userbot.is_connected():
        return [(monitor_userbot, "monitor_userbot")]
    return []

def _partition_round_robin(items: list, n: int) -> List[list]:
    """Splits items into n buckets round-robin (some buckets may be empty if n > len(items))."""
    buckets: List[list] = [[] for _ in range(n)]
    for i, item in enumerate(items):
        buckets[i % n].append(item)
    return buckets

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

        # 🔁 Resume an interrupted /syncfromcatch run the same way — if the bot restarted
        # mid-sweep, pick up right after the last id it confirmed, instead of leaving
        # SYNC_IN_PROGRESS's on-disk "active" flag stuck True forever with nothing running.
        sync_state = await bot_settings_col.find_one({"_id": "catchbot_sync_state"})
        if sync_state and sync_state.get("active"):
            resume_from = max(CATCHBOT_SYNC_MIN_ID, sync_state.get("last_checked_id", 0) + 1)  # no max-side clamp — sync is open-ended now
            print(f"🔁 [xbot monitor] Resuming interrupted /syncfromcatch from id {resume_from}...")
            asyncio.create_task(_run_catchbot_sync(resume_from, status_chat_id=OWNER_ID, status_msg_id=None))
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

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotloadworkers$', 'bot1')))
async def xbot_load_workers_command(event):
    """(Re)loads the powerranger_col / _col2 / _col3 sessions into worker_pool_clients. Run
    this once after deploying (or any time you add/remove a session in those collections) —
    /xbotresync and /xbotimportall pick up whatever's loaded here automatically."""
    if event.sender_id != OWNER_ID:
        return
    status = await event.reply("⏳ Loading worker pool from powerranger_col / _col2 / _col3...")
    await load_worker_pool()
    if worker_pool_clients:
        names = "\n".join(f"  • {label}" for _client, label in worker_pool_clients)
        await status.edit(f"✅ Loaded {len(worker_pool_clients)} worker(s):\n{names}")
    else:
        await status.edit(
            "⚠️ No workers loaded (collections empty, or every saved session failed to log in "
            "— check the logs). /syncfromcatch, /xbotresync and /xbotimportall will keep using "
            "monitor_userbot alone. Add accounts with /xbotaddworker <session>."
        )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotaddworker\s+([\s\S]+)$', 'bot1')))
async def xbot_add_worker_command(event):
    """/xbotaddworker <StringSession> [label] — one account per line, so a whole batch can be
    pasted at once. DM only; the message (it carries login secrets) is deleted immediately."""
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM only — it carries login session strings.")
    rows = []
    for ln in event.pattern_match.group(1).splitlines():
        ln = ln.strip()
        if not ln:
            continue
        parts = ln.split(None, 1)
        rows.append((parts[0], parts[1].strip() if len(parts) > 1 else ""))
    try:
        await event.delete()
    except Exception:
        await event.reply("⚠️ Couldn't delete your message — please delete it yourself, it contains session strings.")
    if not rows:
        return await bot1.send_message(event.chat_id, "❌ No session found in that message.")
    status = await bot1.send_message(event.chat_id, f"⏳ Checking {len(rows)} session(s)...")

    async def _try(session_str):
        if len(session_str) < 40:
            raise RuntimeError("that doesn't look like a String Session")
        return await _connect_worker_session(session_str)
    results = await asyncio.gather(*[_try(s) for s, _l in rows], return_exceptions=True)

    lines, added = [], 0
    async with _worker_pool_load_lock:
        known_ids = {m["user_id"] for m in worker_pool_meta.values()}
        try:
            if monitor_userbot and monitor_userbot.is_connected():
                known_ids.add((await monitor_userbot.get_me()).id)
        except Exception:
            pass
        for i, ((session_str, label), res) in enumerate(zip(rows, results), 1):
            if isinstance(res, BaseException):
                lines.append(f"❌ #{i}: {escape_html(str(res)[:100] or type(res).__name__)}")
                continue
            client, me = res
            if me.id in known_ids:
                try:
                    await client.disconnect()
                except Exception:
                    pass
                lines.append(f"↩️ #{i}: @{escape_html(me.username or str(me.id))} is already in the pool")
                continue
            label = label or f"worker{len(worker_pool_clients) + 1}"
            full = f"{label} (@{me.username or me.id})"
            try:
                await db[SYNC_WORKERS_COLLECTION].update_one(
                    {"_id": me.id},
                    {"$set": {"session": session_str, "name": label, "added_at": time.time()}},
                    upsert=True)
            except Exception as e:
                lines.append(f"⚠️ #{i}: connected but couldn't save to Mongo ({type(e).__name__}) — works until restart")
            known_ids.add(me.id)
            worker_pool_clients.append((client, full))
            worker_pool_meta[full] = {"user_id": me.id, "source": SYNC_WORKERS_COLLECTION, "col": SYNC_WORKERS_COLLECTION}
            added += 1
            lines.append(f"✅ #{i}: {escape_html(full)}")
    await status.edit(
        f"👷 <b>Added {added}/{len(rows)}</b> — pool now has <code>{len(worker_pool_clients)}</code> worker(s)\n"
        + "\n".join(lines)
        + "\n\n<i>Run</i> <code>/xbotworkers check</code> <i>to confirm each one can post in the storage group "
          "and reach catch_bot, then</i> <code>/syncfromcatch</code>.",
        parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotworkers(?:\s+(check))?(?:@\w+)?$', 'bot1')))
async def xbot_workers_command(event):
    if event.sender_id != OWNER_ID:
        return
    do_check = bool(event.pattern_match.group(1))
    entries = []
    if monitor_userbot and monitor_userbot.is_connected():
        entries.append((monitor_userbot, "monitor_userbot", "monitor"))
    for client, label in worker_pool_clients:
        entries.append((client, label, (worker_pool_meta.get(label) or {}).get("source", "?")))
    if not entries:
        return await event.reply("📭 No userbots loaded. Add some with <code>/xbotaddworker &lt;session&gt;</code>.", parse_mode='html')
    status = await event.reply(f"⏳ {'Checking' if do_check else 'Listing'} {len(entries)} account(s)...")
    reasons = [None] * len(entries)
    if do_check:
        res = await asyncio.gather(*[_sync_worker_preflight(c) for c, _l, _s in entries], return_exceptions=True)
        reasons = [None if r is None else (r if isinstance(r, str) else type(r).__name__) for r in res]
    out, ok = [], 0
    for n, ((client, label, source), why) in enumerate(zip(entries, reasons), 1):
        if do_check:
            mark = "✅ ready" if why is None else f"❌ {escape_html(why)}"
            ok += why is None
        else:
            mark = "🟢 connected" if client.is_connected() else "🔴 disconnected"
        out.append(f"<b>{n}.</b> {escape_html(label)} · <i>{escape_html(source)}</i> · {mark}")
    head = f"👷 <b>Userbots</b> ({len(entries)})" + (f" — <code>{ok}</code> ready" if do_check else "")
    await status.edit(head + "\n" + "\n".join(out), parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotremoveworker\s+(.+)$', 'bot1')))
async def xbot_remove_worker_command(event):
    """/xbotremoveworker <number from /xbotworkers | part of the label>"""
    if event.sender_id != OWNER_ID:
        return
    key = event.pattern_match.group(1).strip()
    async with _worker_pool_load_lock:
        target = None
        if key.isdigit():
            n = int(key)
            offset = 1 if (monitor_userbot and monitor_userbot.is_connected()) else 0
            if n - 1 - offset >= 0 and n - 1 - offset < len(worker_pool_clients):
                target = worker_pool_clients[n - 1 - offset]
        if target is None:
            hits = [w for w in worker_pool_clients if key.lower() in w[1].lower()]
            if len(hits) == 1:
                target = hits[0]
            elif len(hits) > 1:
                return await event.reply("❌ More than one match — use the number from /xbotworkers.")
        if target is None:
            return await event.reply("❌ No such worker (the monitor userbot is managed with /xbotsetsession).")
        client, label = target
        meta = worker_pool_meta.pop(label, {})
        worker_pool_clients[:] = [w for w in worker_pool_clients if w[1] != label]
        try:
            await client.disconnect()
        except Exception:
            pass
        note = ""
        if meta.get("col") == SYNC_WORKERS_COLLECTION:
            try:
                await db[SYNC_WORKERS_COLLECTION].delete_one({"_id": meta.get("user_id")})
            except Exception as e:
                note = f"\n⚠️ couldn't delete it from Mongo: {type(e).__name__}"
        elif meta.get("source") == "env":
            note = "\nℹ️ It came from WORKER_SESSIONS — remove it there too or it returns on restart."
        elif meta.get("col"):
            note = f"\nℹ️ It came from <code>{escape_html(meta['col'])}</code> — delete it there too or it returns on /xbotloadworkers."
    await event.reply(f"🗑️ Removed <b>{escape_html(label)}</b>. Pool: <code>{len(worker_pool_clients)}</code> worker(s).{note}", parse_mode='html')

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
    """Walks every channel in chat_ids' full history and auto-imports 'added new Character'
    posts. Channels are split across _get_history_workers() and walked CONCURRENTLY — with one
    worker (monitor_userbot alone) this behaves exactly like before, just possibly with a
    different channel order; with a loaded pool, each worker takes its own slice of channels.

    Checkpointing is per-channel now (state["progress"][str(chat_id)] = last message id seen),
    instead of the old single "current_chat_id" pointer — that's what lets several channels be
    in flight at once and still resume every one of them correctly after a restart.
    """
    global _bulk_import_active, _bulk_import_cancel_requested
    if _bulk_import_active:
        return  # a run is already in progress (e.g. resumed at startup) — never overlap two
    workers = _get_history_workers()
    if not workers:
        msg = "❌ Monitor userbot isn't connected and no worker pool is loaded. Use /xbotsetsession or /xbotloadworkers first."
        if status_chat_id:
            await bot1.send_message(status_chat_id, msg)
        return
    _bulk_import_active = True
    _bulk_import_cancel_requested = False

    state = await bot_settings_col.find_one({"_id": "xbot_bulk_import_state"}) or {}
    progress: Dict[str, int] = dict(state.get("progress") or {})
    if not progress and state.get("current_chat_id") and state.get("last_processed_msg_id"):
        # 🩹 one-time migration from the old single-channel-pointer checkpoint format
        progress[str(state["current_chat_id"])] = state["last_processed_msg_id"]
    counts = {
        "checked": state.get("checked", 0), "imported": state.get("imported", 0),
        "skipped_duplicate": state.get("skipped_duplicate", 0),
        "skipped_no_media": state.get("skipped_no_media", 0),
        "skipped_bad_rarity": state.get("skipped_bad_rarity", 0),
        "errors": state.get("errors", 0)
    }
    await bot_settings_col.update_one(
        {"_id": "xbot_bulk_import_state"},
        {"$set": {"active": True, "chat_ids": chat_ids, "started_at": state.get("started_at", time.time()),
                   "progress": progress, **counts}},
        upsert=True
    )
    status_state = {"last_edit_ts": 0.0}

    async def report_progress():
        # Time-throttled (not count-throttled) since several workers now increment
        # counts["checked"] concurrently — this keeps edit_message calls to ~1 every 3s no
        # matter how many workers are running, instead of firing once per worker per 25 msgs.
        if not (status_chat_id and status_msg_id):
            return
        now = time.time()
        if now - status_state["last_edit_ts"] < 3:
            return
        status_state["last_edit_ts"] = now
        try:
            await bot1.edit_message(
                status_chat_id, status_msg_id,
                f"⏳ <b>Bulk import running…</b> ({len(workers)} worker(s))\n"
                f"{_bulk_import_counts_lines(counts)}",
                parse_mode='html'
            )
        except Exception:
            pass

    async def worker_task(worker_client, worker_label, my_chat_ids):
        for chat_id in my_chat_ids:
            if _bulk_import_cancel_requested:
                return
            source_bot = monitored_chat_map.get(chat_id, "unknown")
            resume_id = progress.get(str(chat_id))
            kwargs = {"reverse": True}  # oldest first — same reasoning as /xbotresync
            if resume_id:
                kwargs["min_id"] = resume_id
            try:
                async for msg in worker_client.iter_messages(chat_id, **kwargs):
                    if _bulk_import_cancel_requested:
                        return
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
                    progress[str(chat_id)] = msg.id
                    await bot_settings_col.update_one(
                        {"_id": "xbot_bulk_import_state"},
                        {"$set": {f"progress.{chat_id}": msg.id, **counts}}
                    )
                    await report_progress()
                    await asyncio.sleep(BULK_IMPORT_DELAY_SECONDS)
            except Exception as e:
                await report_system_error("_run_bulk_import", f"worker {worker_label} on chat {chat_id}: {e}")

    try:
        buckets = _partition_round_robin(chat_ids, len(workers))
        tasks = [
            worker_task(client, label, bucket)
            for (client, label), bucket in zip(workers, buckets) if bucket
        ]
        await asyncio.gather(*tasks)
    except Exception as e:
        await report_system_error("_run_bulk_import", str(e))
    finally:
        was_cancelled = _bulk_import_cancel_requested
        _bulk_import_active = False
        await bot_settings_col.update_one({"_id": "xbot_bulk_import_state"}, {"$set": {"active": False, **counts}})
    if was_cancelled:
        summary = (
            f"🛑 <b>Bulk import stopped</b> (checkpoint saved per-channel — /xbotimportall will resume from here)\n"
            f"{_bulk_import_counts_lines(counts)}"
        )
    else:
        summary = (
            f"✅ <b>Bulk import complete!</b> ({len(workers)} worker(s))\n"
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
    workers = _get_history_workers()
    if not workers:
        return await event.reply("❌ Monitor userbot isn't connected and no worker pool is loaded. Use /xbotsetsession or /xbotloadworkers first.")
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
                   "progress": {}, "checked": 0, "imported": 0, "skipped_duplicate": 0, "errors": 0,
                   "started_at": time.time()}},
        upsert=True
    )
    status_msg = await event.reply(
        f"⏳ <b>Starting bulk import</b> across {len(chat_ids)} channel(s) with {len(workers)} worker(s)...\n"
        f"Paced at {BULK_IMPORT_DELAY_SECONDS}s/message per worker — this is expected to take a while "
        f"for a large history. If the bot restarts for any reason, it'll pick back up right where "
        f"each channel left off automatically.",
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
    progress = state.get("progress") or {}
    total_chats = len(state.get("chat_ids") or [])
    await event.reply(
        f"📦 <b>Bulk Import Status</b>\n"
        f"Status: {running}\n"
        f"👷 Workers: {len(_get_history_workers())}\n"
        f"{_bulk_import_counts_lines(state)}\n"
        f"📍 Channels with progress: {len(progress)}/{total_chats}",
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

# 🩹 NEW (per owner request — "background tasks piling up made the bot slow, need a way to
# stop /xbotresync"): same shape as SYNC_IN_PROGRESS / _catchbot_sync_cancel_requested above
# for /syncfromcatch. /xbotresync had neither: no guard against starting a second overlapping
# run, and nothing checked inside its loop to ever stop early once started — a resync over a
# large, busy channel's full history could run for a very long time with no way to interrupt
# it short of restarting the whole bot process.
XBOT_RESYNC_IN_PROGRESS = False
_xbot_resync_cancel_requested = False

async def _xbot_resync_worker(worker_client, worker_label, my_chat_ids, shared, status):
    """One worker's share of an /xbotresync run: walks each of my_chat_ids' full history and
    re-indexes it, incrementing the run-wide `shared` counters as it goes. Several of these run
    concurrently (one per worker), each on its own disjoint slice of channels, so status-edit
    calls are time-throttled here (shared["last_edit_ts"]) rather than count-throttled — that
    keeps edit_message calls to about 1 every 3s total no matter how many workers are running."""
    for chat_id in my_chat_ids:
        if _xbot_resync_cancel_requested:
            return
        source_bot = monitored_chat_map.get(chat_id, "unknown")
        try:
            await xbot_hashes_col.delete_many({"chat_id": chat_id})
            # reverse=True: oldest first — matters when a character's been renamed more than
            # once, so the LAST rename processed is the actually-current name.
            async for msg in worker_client.iter_messages(chat_id, reverse=True):
                if _xbot_resync_cancel_requested:
                    return
                shared["checked"] += 1
                now = time.time()
                if now - shared["last_edit_ts"] >= 3:
                    shared["last_edit_ts"] = now
                    try:
                        await status.edit(
                            f"⏳ Resyncing with {shared['num_workers']} worker(s)...\n"
                            f"📨 Checked: {shared['checked']}\n✅ Updated: {shared['updated']}",
                            parse_mode='html'
                        )
                    except Exception:
                        pass
                caption = msg.raw_text or ""
                # 🩹 FIX: same gap as /xbotscan — rename/event/rarity/image-update posts were
                # invisible here before. Same no-auto-import-during-bulk-replay reasoning too.
                if await _maybe_sync_catchbot_character_change(msg, chat_id, caption):
                    shared["updated"] += 1
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
                    shared["updated"] += 1
                await asyncio.sleep(0.1)
        except Exception as e:
            print(f"xbot resync error for {chat_id} (worker {worker_label}): {e}")

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotresync(?:\s+(-?\d+))?$', 'bot1')))
async def xbot_resync_channel_command(event):
    global XBOT_RESYNC_IN_PROGRESS, _xbot_resync_cancel_requested
    if event.sender_id != OWNER_ID:
        return
    if not event.is_private:
        return await event.reply("❌ Use this in DM.")
    workers = _get_history_workers()
    if not workers:
        return await event.reply("❌ Monitor userbot isn't connected and no worker pool is loaded. Use /xbotsetsession or /xbotloadworkers first.")
    if XBOT_RESYNC_IN_PROGRESS:
        return await event.reply("⚠️ An /xbotresync is already running. Use /xbotresynccancel to stop it first.")
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
        status = await event.reply(
            f"⏳ Resetting all {len(chat_ids_to_scan)} channels with {len(workers)} worker(s)... "
            f"(/xbotresynccancel to stop)"
        )
    XBOT_RESYNC_IN_PROGRESS = True
    _xbot_resync_cancel_requested = False
    shared = {"checked": 0, "updated": 0, "last_edit_ts": 0.0, "num_workers": len(workers)}
    try:
        buckets = _partition_round_robin(chat_ids_to_scan, len(workers))
        tasks = [
            _xbot_resync_worker(client, label, bucket, shared, status)
            for (client, label), bucket in zip(workers, buckets) if bucket
        ]
        await asyncio.gather(*tasks)
        if _xbot_resync_cancel_requested:
            await status.edit(f"🛑 <b>Cancelled.</b>\n📨 Checked: {shared['checked']}\n🔄 Re-indexed: {shared['updated']}", parse_mode='html')
        else:
            await status.edit(
                f"✅ <b>Resync Complete!</b> ({len(workers)} worker(s))\n"
                f"📨 Checked: {shared['checked']}\n🔄 Re-indexed: {shared['updated']}",
                parse_mode='html'
            )
    finally:
        XBOT_RESYNC_IN_PROGRESS = False
        _xbot_resync_cancel_requested = False

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]xbotresynccancel(?:@\w+)?$', 'bot1')))
async def xbot_resync_cancel_command(event):
    global _xbot_resync_cancel_requested
    if event.sender_id != OWNER_ID:
        return
    if not XBOT_RESYNC_IN_PROGRESS:
        return await event.reply("📭 No /xbotresync run is currently in progress.")
    _xbot_resync_cancel_requested = True
    await event.reply("🛑 Marked for stop — it'll wrap up its current message/channel and stop shortly.")

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
    text += f"\n👷 Worker pool: {len(worker_pool_clients)} loaded (/xbotloadworkers to (re)load)"
    await event.reply(text, parse_mode='html')


# ==========================================
# 💰 CCM CURRENCY SYSTEM — commands
# ==========================================
# /setvalue (owner-only) sets Rarity 2-9's [min,max] worth IN GRAMS in one shot, then walks
# straight into the SUPREME (Rarity 1) per-event picker below. /balance and /exchange are the
# player-facing side (/daily no longer pays). See _get_gram_tier_values / _get_gram_event_values
# near CNFT_RARITY_INFO for the actual pricing data these all read and write.
# ==========================================
_SETVALUE_LINE_RE = re.compile(r'(?mi)^\s*([2-9])\s+(\d{1,9})\s*g?\s+(\d{1,9})\s*g?\s*$')
_SETVALUE_GRAM_VALUE_RE = re.compile(r'(?i)^\s*(\d{1,9})\s*g?\s*$')

async def _list_supreme_events():
    """Distinct event names among stored SUPREME (Rarity 1) characters — "General" included,
    same fallback /addchar and release_spawn already use for an uncategorized character."""
    raw_events = await characters_base_col.distinct("event", {"rarity_tier": "SUPREME"})
    return sorted({(e or "General") for e in raw_events})

def _ccm_event_picker_buttons(event_names, configured):
    # 🩹 FIX (owner report — tapping a SUPREME event button did nothing at all): callback_data
    # used to be f"ccmsetevent_{name}" — the raw event name, verbatim. Telegram callback_data
    # is capped at 64 BYTES total, and a longer name (easy to hit with Burmese script, which
    # runs ~3 bytes/character) could silently break the button. A plain numeric index side-steps
    # that entirely — same safe, all-digits style every OTHER working callback in this file
    # already uses (see triv_ near trigger_trivia_spawn), never embedding free-form text.
    # (Callback names keep the old "ccmsetevent_" prefix on purpose — they're internal ids only.)
    rows, row = [], []
    for i, name in enumerate(event_names):
        mark = "✅ " if name in configured else ""
        row.append(Button.inline(f"{mark}{name}", data=f"ccmsetevent_{i}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([Button.inline("✅ Done", data="ccmsetevent_done")])
    return rows

async def _send_ccm_event_picker(event):
    """Shows every SUPREME event as a tappable button — tapping one prompts the owner to
    reply with that event's worth IN GRAMS (see ccm_event_picker_pick / ccm_event_value_reply)."""
    event_names = await _list_supreme_events()
    if not event_names:
        await event.reply(
            "🪞 <b>SUPREME (Rarity 1)</b> character ဘယ်ဟာမှ database ထဲမှာ မတွေ့ရသေးပါ — "
            "SUPREME character တစ်ခုခု ထည့်ပြီးမှ ပြန်ကြိုးစားပါ။",
            parse_mode='html'
        )
        return
    configured = await _get_gram_event_values()
    text = (
        f"🪞 <b>SUPREME (Rarity 1) — Event အလိုက် Worth ({GRAM_EMOJI} gram)</b>\n\n"
        f"Event တစ်ခုချင်းစီအတွက် SUPREME card တစ်ကတ်ရဲ့ တန်ဖိုးကို <b>gram နဲ့ပဲ</b> သတ်မှတ်ပါ "
        f"(1 g = {MMK_PER_GRAM} MMK)။ မသတ်မှတ်ရသေးတဲ့ event ကတော့ default "
        f"{DEFAULT_SUPREME_GRAM_RANGE[0]:,}–{DEFAULT_SUPREME_GRAM_RANGE[1]:,} g နဲ့ပြပါတယ်။\n"
        "Event ကို နှိပ်ပြီး Value ကို ↩️ Reply ပို့ပါ — ✅ ပါပြီဆိုရင် အရင်သတ်မှတ်ပြီးသားပါ။"
    )
    await event.reply(text, parse_mode='html', buttons=_ccm_event_picker_buttons(event_names, configured))

# 📋 Sample ladder shown in /setvalue's help — derived from the owner's anchor "Divine = 500–700 g
# (= 500–700 MMK)" scaled by each tier's relative weight in _RARITY_VALUE_MAP, rounded to tidy numbers.
_SETVALUE_SAMPLE_LADDER = (
    "2 1000 1400\n3 700 1000\n4 500 700\n5 350 500\n6 200 300\n7 140 200\n8 85 120\n9 45 60"
)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]setvalue(?:@\w+)?(?:\s+([\s\S]*))?$', 'bot1')))
async def setvalue_cmd(event):
    if event.sender_id != OWNER_ID: return
    # The value table can be typed straight after /setvalue, OR pasted as its own message that
    # the owner then replies to with a bare "/setvalue" — whichever is more convenient in the
    # moment. Either way, one line per tier: "<Rarity No. 2-9> <Min g> <Max g>" — GRAMS only.
    raw = (event.pattern_match.group(1) or "").strip()
    if not raw and event.is_reply:
        replied = await event.get_reply_message()
        raw = (replied.text or "").strip() if replied else ""

    matches = _SETVALUE_LINE_RE.findall(raw) if raw else []
    if not matches:
        stored = await _get_gram_tier_values()
        rate_line = f"💱 <code>1 g = {MMK_PER_GRAM} MMK = {CCM_PER_GRAM} ccm</code>"
        lines = []
        for n in sorted((k for k in RARITY_NUM_MAP if k != "1"), key=int):
            v = stored.get(n)
            if v:
                lo, hi, tag = int(v["min"]), int(v["max"]), ""
            else:
                lo, hi = DEFAULT_GRAM_TIER_VALUES[n]
                tag = " <i>(default)</i>"
            lines.append(f"<code>{n}</code> {RARITY_NUM_MAP[n]['name']} — <code>{lo:,}–{hi:,}</code> g{tag}")
        return await event.reply(
            f"📋 <b>လက်ရှိ Rarity Worth ({GRAM_EMOJI} gram):</b>\n<blockquote>{chr(10).join(lines)}</blockquote>\n{rate_line}\n\n"
            "<b>ပြောင်းချင်ရင်:</b> line တစ်ကြောင်းစီ <code>[Rarity No.] [Min g] [Max g]</code> — "
            "<b>gram နဲ့ပဲ</b> ထည့်ပါ (ccm နဲ့ မရပါ)။ <code>/setvalue</code> နောက်မှာ တန်းရိုက်ပါ၊ "
            "ဒါမှမဟုတ် table ပါတဲ့ message ကို Reply ပြန်ပြီး <code>/setvalue</code> ရိုက်ပါ:\n\n"
            f"<pre>{_SETVALUE_SAMPLE_LADDER}</pre>\n"
            "<i>(<b>default</b> လို့ပြတာတွေက မသတ်မှတ်ရသေးလို့ ဒီ default ladder ကို သုံးနေတာပါ — "
            "Divine (4) = 500–700 g = 500–700 MMK)</i>",
            parse_mode='html'
        )

    updates = {}
    for num, mn, mx in matches:
        mn, mx = int(mn), int(mx)
        if mx < mn:
            mn, mx = mx, mn
        updates[num] = {"min": mn, "max": mx}
    await bot_settings_col.update_one(
        {"_id": "gram_tier_values"},
        {"$set": {f"values.{num}": rng for num, rng in updates.items()}},
        upsert=True
    )
    lines = [
        f"<code>{n}</code> {RARITY_NUM_MAP[n]['name']} — <code>{v['min']:,}–{v['max']:,}</code> g"
        for n, v in sorted(updates.items(), key=lambda kv: int(kv[0]))
    ]
    await event.reply(
        f"✅ <b>{len(updates)} Rarity tier(s) Worth သတ်မှတ်ပြီးပါပြီ ({GRAM_EMOJI} gram):</b>\n"
        f"<blockquote>{chr(10).join(lines)}</blockquote>",
        parse_mode='html'
    )
    # 🪞 Rarity 1 (SUPREME) doesn't take a flat range — walk straight into its per-event picker.
    await _send_ccm_event_picker(event)

@bot1.on(events.CallbackQuery(pattern=r'^ccmsetevent_done$'))
async def ccm_event_picker_done(event):
    if event.sender_id != OWNER_ID: return await event.answer()
    try:
        await event.edit("✅ <b>SUPREME event worth (gram) ပြီးပါပြီ။</b>", parse_mode='html', buttons=None)
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^ccmsetevent_(\d+)$'))
async def ccm_event_picker_pick(event):
    if event.sender_id != OWNER_ID: return await event.answer()
    try:
        idx = int(event.pattern_match.group(1))
        event_names = await _list_supreme_events()
        if idx < 0 or idx >= len(event_names):
            return await event.answer("⚠️ Event list ပြောင်းသွားပါပြီ — /setvalue ကို ပြန်ခေါ်ပါ။", alert=True)
        event_name = event_names[idx]
        current = (await _get_gram_event_values()).get(event_name)
        hint = f" (လက်ရှိ: <code>{int(current):,}</code> g)" if current is not None else ""
        text = (
            f"🪞 <b>Event:</b> {escape_html(event_name)}{hint}\n\n"
            f"↩️ <b>Reply to this message</b> with this event's worth in <b>grams</b> (e.g. <code>1500</code>)."
        )
        sent = await event.reply(text, parse_mode='html')
        pending_ccm_event_prompt_ids[sent.id] = event_name
        await event.answer()
    except Exception as e:
        # 🩹 This is exactly what was silent before the index-based fix above — any failure
        # here now at least surfaces as a visible alert instead of a tap that does nothing.
        print(f"ccm_event_picker_pick error: {e}")
        try:
            await event.answer(f"❌ Error: {e}", alert=True)
        except Exception:
            pass

@bot1.on(events.NewMessage(incoming=True))
async def ccm_event_value_reply(event):
    if event.sender_id != OWNER_ID: return
    if not event.is_reply: return
    if event.reply_to_msg_id not in pending_ccm_event_prompt_ids: return
    event_name = pending_ccm_event_prompt_ids.pop(event.reply_to_msg_id)
    m = _SETVALUE_GRAM_VALUE_RE.match(event.text or "")
    if not m:
        pending_ccm_event_prompt_ids[event.reply_to_msg_id] = event_name  # invalid — keep waiting
        await event.reply("❌ gram ဂဏန်း (positive number) ပဲ ပို့ပါ — ↩️ ဒီ Reply ကိုပဲ ပြန် Reply လုပ်ပါ။", parse_mode='html')
        return
    value = int(m.group(1))
    await _set_gram_event_value(event_name, value)
    await event.reply(f"✅ <b>{escape_html(event_name)}</b> ➜ <code>{value:,}</code> g ({GRAM_EMOJI}) သတ်မှတ်ပြီးပါပြီ။", parse_mode='html')
    await _send_ccm_event_picker(event)  # re-show with the ✅ updated, so the owner can keep going or tap Done

def _wallet_text(plain_name, ccm, gram, unlimited_gram=False):
    title_text = escape_html(f"{plain_name}'s Wallet")
    gram_text = "♾️ Unlimited" if unlimited_gram else f"<code>{gram:,}</code> g"
    return (
        f"💰 <b>{title_text}</b>\n\n"
        f"💰 <b>ccm:</b> <code>{ccm:,}</code>\n"
        f"{GRAM_EMOJI} <b>gram:</b> {gram_text}\n\n"
        f"💱 <code>{CCM_PER_GRAM} ccm = 1 g</code>"
    )

def _wallet_buttons(user_id):
    return [[Button.inline("💱 Exchange", data=f"wal_exch_{user_id}")]]

def _exchange_panel_text(ccm, gram):
    max_g = ccm // CCM_PER_GRAM
    if max_g >= 1:
        tail = (f"➡️ <b>ဒီအချိန် လဲလို့ရတာ:</b> <code>{max_g:,}</code> g "
                f"(<code>{max_g * CCM_PER_GRAM:,}</code> ccm)\n\n👇 လဲချင်တဲ့ gram ကို ရွေးပါ")
    else:
        tail = (f"➡️ <b>ဒီအချိန် လဲလို့ရတာ:</b> <code>0</code> g\n"
                f"<i>1 g လဲဖို့ အနည်းဆုံး {CCM_PER_GRAM} ccm လိုပါတယ် — Trivia၊ /daily နဲ့ catch ကနေ ccm ရယူပါ။</i>")
    return (
        f"💱 <b>Exchange</b> — <code>{CCM_PER_GRAM} ccm = 1 g</code> {GRAM_EMOJI}\n\n"
        f"💰 ccm: <code>{ccm:,}</code>\n"
        f"{GRAM_EMOJI} gram: <code>{gram:,}</code> g\n"
        f"{tail}"
    )

def _exchange_panel_buttons(user_id, ccm):
    max_g = ccm // CCM_PER_GRAM
    rows, row = [], []
    for g in (1, 5, 10, 50, 100):
        if g < max_g:   # max_g itself is covered by the "All" button below
            row.append(Button.inline(f"{g} g", data=f"wal_pick_{user_id}_{g}"))
            if len(row) == 3:
                rows.append(row)
                row = []
    if row:
        rows.append(row)
    if max_g >= 1:
        rows.append([Button.inline(f"All · {max_g:,} g", data=f"wal_pick_{user_id}_{max_g}")])
    rows.append([Button.inline("⬅️ Back", data=f"wal_back_{user_id}")])
    return rows

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]balance(?:@\w+)?$', 'bot1')))
async def ccm_balance_cmd(event):
    user_id = event.sender_id
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    user_doc = await users_catcher_col.find_one({"user_id": user_id}) or {}
    await event.reply(
        _wallet_text(plain_name, int(user_doc.get("ccm_balance", 0)), int(user_doc.get("gram_balance", 0)),
                     unlimited_gram=has_unlimited_gram(user_id)),
        parse_mode='html', buttons=_wallet_buttons(user_id)
    )

@bot1.on(events.CallbackQuery(pattern=r'^wal_(exch|pick|back)_(\d+)(?:_(\d+))?$'))
async def wallet_callback_handler(event):
    """The buttons under /balance: Exchange -> panel (shows ccm + how many grams are exchangeable
    + amount buttons) -> pick an amount -> confirm (exch_confirm_* below) -> done."""
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    owner_id = int(event.pattern_match.group(2))
    picked = event.pattern_match.group(3)
    if event.sender_id != owner_id:
        return await event.answer("သင့်ရဲ့ button မဟုတ်ပါ။", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)
    try:
        doc = await users_catcher_col.find_one({"user_id": owner_id}) or {}
        ccm = int(doc.get("ccm_balance", 0))
        gram = int(doc.get("gram_balance", 0))
        max_g = ccm // CCM_PER_GRAM
        try:
            if action == "back":
                name = await get_plain_name(event, owner_id)
                await event.edit(_wallet_text(name, ccm, gram, unlimited_gram=has_unlimited_gram(owner_id)),
                                 parse_mode='html', buttons=_wallet_buttons(owner_id))
            elif action == "exch":
                _EXCHANGE_CONSUMED.discard((event.chat_id, event.message_id))  # a fresh exchange round on this message
                await event.edit(_exchange_panel_text(ccm, gram), parse_mode='html',
                                 buttons=_exchange_panel_buttons(owner_id, ccm))
            else:  # pick
                grams = int(picked or 0)
                cost = grams * CCM_PER_GRAM
                if grams < 1 or grams > EXCHANGE_MAX_GRAMS_PER_TX or cost > ccm:
                    await event.edit(_exchange_panel_text(ccm, gram), parse_mode='html',
                                     buttons=_exchange_panel_buttons(owner_id, ccm))
                    return await event.answer("ccm မလောက်တော့ပါ — ပမာဏကို ပြန်ရွေးပါ။", alert=True)
                await event.edit(
                    f"💱 <b>လဲလှယ်မလား?</b>\n\n"
                    f"💰 <code>{cost:,}</code> ccm  ➜  {GRAM_EMOJI} <code>{grams:,}</code> g\n\n"
                    f"💰 ccm ရှိတာ: <code>{ccm:,}</code> · လဲပြီးရင် ကျန်မယ့်: <code>{ccm - cost:,}</code>",
                    parse_mode='html',
                    buttons=[[
                        Button.inline("✅ Confirm", data=f"exch_confirm_{owner_id}_{grams}"),
                        Button.inline("❌ Cancel", data=f"wal_exch_{owner_id}")
                    ]]
                )
        except errors.MessageNotModifiedError:
            pass
        await event.answer()
    except Exception as e:
        await report_system_error("wallet_callback_handler", f"{e}\nData: {event.data}")
        try:
            await event.answer("Hmm, something didn't work.", alert=True)
        except Exception:
            pass

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]daily(?:@\w+)?$', 'bot1')))
async def ccm_daily_cmd(event):
    """/daily — once per 24h, a random DAILY_MIN_MMK..DAILY_MAX_MMK worth of ccm. The claim is a
    compare-and-set on last_daily inside ONE Mongo update, so two simultaneous /daily messages
    can never both pay out (the payout is worth real MMK, so a double-claim race isn't acceptable)."""
    user_id = event.sender_id
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    user_doc = await users_catcher_col.find_one({"user_id": user_id}) or {}
    now = time.time()
    last_daily = user_doc.get("last_daily", 0) or 0
    streak = user_doc.get("daily_streak", 0) or 0

    def _cooldown_reply(last):
        rem_time = max(1, int(DAILY_COOLDOWN_SECONDS - (time.time() - last)))
        return (f"⏳ {mention} <b>ယနေ့အတွက် ယူပြီးသားပါ။</b> နောက်တစ်ကြိမ် "
                f"<code>{str(timedelta(seconds=rem_time))}</code> အတွင်း ပြန်ယူလို့ရပါမယ်။")

    if now - last_daily < DAILY_COOLDOWN_SECONDS:
        return await event.reply(_cooldown_reply(last_daily), parse_mode='html')
    if now - last_daily > DAILY_STREAK_RESET_SECONDS:
        streak = 0
    new_streak = streak + 1
    lo, hi = daily_ccm_range()
    reward = random.randint(lo, hi)
    # compare-and-set: only succeeds if last_daily is still exactly what we just read
    cas_filter = {"user_id": user_id, "last_daily": last_daily} if last_daily else {"user_id": user_id, "last_daily": {"$in": [0, None]}}
    claimed = await users_catcher_col.find_one_and_update(
        cas_filter,
        {"$inc": {"ccm_balance": reward},
         "$set": {"last_daily": now, "daily_streak": new_streak, "fullname": plain_name}},
        return_document=ReturnDocument.AFTER
    )
    if claimed is None:  # a concurrent /daily got there first
        return await event.reply(f"⏳ {mention} <b>ယနေ့အတွက် ယူပြီးသားပါ။</b>", parse_mode='html')
    grams_eq = reward / CCM_PER_GRAM
    mmk_eq = grams_eq * MMK_PER_GRAM
    await event.reply(
        f"🎁 {mention} <b>Daily Bonus ရပါပြီ! <code>+{reward:,} 💰 ccm</code></b>\n"
        f"≈ {GRAM_EMOJI} <code>{grams_eq:,.1f}</code> g · <code>{mmk_eq:,.0f}</code> MMK\n"
        f"🔥 <b>{new_streak} ရက်ဆက်တိုက်</b>\n\n"
        f"💱 /exchange နဲ့ gram ပြောင်းလို့ရပါတယ်။",
        parse_mode='html'
    )

# ==========================================
# 💱 /exchange — ccm → gram (per owner request: 200 ccm = 1 g)
# ==========================================
# /exchange <grams|all> asks for confirmation, then converts in ONE atomic Mongo update: the
# `ccm_balance >= cost` check and the two $inc's (ccm down, gram up) happen together, so there is
# no window where ccm is taken but grams aren't granted (or the reverse), and two concurrent taps
# can't both succeed on one balance. Each completed exchange is also logged to exchange_history —
# grams are real-money-valued (1 g = 1 MMK), so there should be an audit trail.
# One-way on purpose: grams can't be turned back into ccm (that would let bought/granted grams
# flow back into the ccm economy).
EXCHANGE_COOLDOWN_SECONDS = 3
EXCHANGE_MAX_GRAMS_PER_TX = 1_000_000
exchange_history_col = db["exchange_history"]
_EXCHANGE_CONSUMED = set()  # (chat_id, msg_id) of confirm prompts already used — a button can never pay out twice

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]exchange(?:@\w+)?(?:\s+(all|\d{1,9}))?$', 'bot1')))
async def exchange_cmd(event):
    user_id = event.sender_id
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    is_cd, remaining = await is_on_cooldown(user_id, "exchange", EXCHANGE_COOLDOWN_SECONDS)
    if is_cd:
        return await event.reply(f"⏳ {remaining}s စောင့်ပါ။", parse_mode='html')
    doc = await users_catcher_col.find_one({"user_id": user_id}) or {}
    ccm = int(doc.get("ccm_balance", 0))
    gram = int(doc.get("gram_balance", 0))
    max_g = ccm // CCM_PER_GRAM
    arg = event.pattern_match.group(1)
    if not arg:
        return await event.reply(
            _exchange_panel_text(ccm, gram)
            + "\n\n<i>Command နဲ့လဲချင်ရင်:</i> <code>/exchange [gram]</code> / <code>/exchange all</code>",
            parse_mode='html', buttons=_exchange_panel_buttons(user_id, ccm)
        )
    grams = max_g if arg.lower() == "all" else int(arg)
    if grams < 1:
        return await event.reply(
            f"❌ ccm မလောက်သေးပါ — 1 g လဲဖို့ အနည်းဆုံး <code>{CCM_PER_GRAM}</code> ccm လိုပါတယ် "
            f"(လက်ရှိ <code>{ccm:,}</code> ccm)။ ccm ကို Trivia ဖြေပြီး ရယူပါ။",
            parse_mode='html'
        )
    if grams > EXCHANGE_MAX_GRAMS_PER_TX:
        return await event.reply(f"❌ တစ်ကြိမ်ကို အများဆုံး <code>{EXCHANGE_MAX_GRAMS_PER_TX:,}</code> g ပဲ လဲလို့ရပါတယ်။", parse_mode='html')
    cost = grams * CCM_PER_GRAM
    if ccm < cost:
        return await event.reply(
            f"❌ ccm မလောက်ပါ — <code>{grams:,}</code> g အတွက် <code>{cost:,}</code> ccm လိုပါတယ်၊ "
            f"သင့်မှာ <code>{ccm:,}</code> ccm ပဲရှိပါတယ် (အများဆုံး <code>{max_g:,}</code> g)။",
            parse_mode='html'
        )
    await event.reply(
        f"💱 <b>လဲလှယ်မလား?</b>\n\n"
        f"💰 <code>{cost:,}</code> ccm  ➜  {GRAM_EMOJI} <code>{grams:,}</code> g",
        parse_mode='html',
        buttons=[[
            Button.inline("✅ Confirm", data=f"exch_confirm_{user_id}_{grams}"),
            Button.inline("❌ Cancel", data=f"exch_cancel_{user_id}_{grams}")
        ]]
    )

@bot1.on(events.CallbackQuery(pattern=r'^exch_(confirm|cancel)_(\d+)_(\d+)$'))
async def exchange_callback_handler(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    owner_id = int(event.pattern_match.group(2))
    grams = int(event.pattern_match.group(3))
    if event.sender_id != owner_id:
        return await event.answer("သင့်ရဲ့ button မဟုတ်ပါ။", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)

    if action == "cancel":
        try:
            await event.edit("❎ လဲလှယ်မှု ပယ်ဖျက်လိုက်ပါပြီ။", buttons=None)
        except Exception:
            pass
        return await event.answer("Cancelled", alert=False)

    token = (event.chat_id, event.message_id)
    if token in _EXCHANGE_CONSUMED:
        return await event.answer("ဒီ လဲလှယ်မှုကို လုပ်ပြီးသားပါ။", alert=True)
    _EXCHANGE_CONSUMED.add(token)
    if len(_EXCHANGE_CONSUMED) > 5000:
        _EXCHANGE_CONSUMED.clear()
        _EXCHANGE_CONSUMED.add(token)
    if grams < 1 or grams > EXCHANGE_MAX_GRAMS_PER_TX:
        return await event.answer("❌ Invalid amount.", alert=True)

    cost = grams * CCM_PER_GRAM
    try:
        updated = await users_catcher_col.find_one_and_update(
            {"user_id": owner_id, "ccm_balance": {"$gte": cost}},
            {"$inc": {"ccm_balance": -cost, "gram_balance": grams}},
            return_document=ReturnDocument.AFTER
        )
        if updated is None:
            _EXCHANGE_CONSUMED.discard(token)  # nothing was charged — let them retry after earning more
            try:
                await event.edit("❌ ccm မလောက်တော့ပါ။", buttons=None)
            except Exception:
                pass
            return await event.answer("Not enough ccm.", alert=True)
        try:
            await exchange_history_col.insert_one({
                "user_id": owner_id, "grams": grams, "ccm_spent": cost, "rate": CCM_PER_GRAM, "ts": time.time()
            })
        except Exception as e:
            print(f"⚠️ exchange_history insert failed (exchange itself succeeded): {type(e).__name__}: {e}")
        await event.edit(
            f"✅ <b>လဲလှယ်ပြီးပါပြီ!</b>\n\n"
            f"💰 −<code>{cost:,}</code> ccm  ➜  {GRAM_EMOJI} +<code>{grams:,}</code> g\n\n"
            f"💰 ccm: <code>{int(updated.get('ccm_balance', 0)):,}</code>\n"
            f"{GRAM_EMOJI} gram: <code>{int(updated.get('gram_balance', 0)):,}</code> g",
            parse_mode='html', buttons=[[Button.inline("💱 Exchange more", data=f"wal_exch_{owner_id}")]]
        )
        await event.answer("Done~", alert=False)
    except Exception as e:
        await report_system_error("exchange_callback_handler", f"{e}\nData: {event.data}")
        try:
            await event.answer("Hmm, something didn't work.", alert=True)
        except Exception:
            pass

# ==========================================
# 🎁 /giftccm — player-to-player ccm transfer (per owner request: the economy needs to
# actually support giving/receiving ccm for a future card marketplace to work on top of it).
# Same confirm/cancel button UX as the card /gift command above, for a consistent feel; the
# actual transfer goes through try_deduct_ccm (see the CURRENCY SYSTEM block) so a race between
# two simultaneous spends — this and, say, a trivia loss landing at the same moment — can never
# double-spend the same ccm.
# ==========================================
GIFTCCM_MIN_AMOUNT = 1
GIFTCCM_COOLDOWN_SECONDS = 5  # just enough to stop accidental double-submits/spam, not a real rate limit

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftccm(?:@\w+)?\s+(\d+)$', 'bot1')))
async def gift_ccm_handler(event):
    sender_id = event.sender_id
    if not event.is_reply:
        return await event.reply(
            "Reply to who you want to send ccm to first, okay?~\nThen just type <code>/giftccm [amount]</code>.",
            parse_mode='html'
        )
    is_cd, remaining = await is_on_cooldown(sender_id, "giftccm", GIFTCCM_COOLDOWN_SECONDS)
    if is_cd:
        return await event.reply(f"Whoa, slow down~ give it {remaining:.0f}s.", parse_mode='html')

    replied = await event.get_reply_message()
    if not replied or not replied.sender_id:
        return await event.reply("Hmm, I can't find them.", parse_mode='html')
    receiver_id = replied.sender_id
    if receiver_id == sender_id:
        return await event.reply("That's you, silly. Someone else~", parse_mode='html')
    try:
        receiver_sender = await replied.get_sender()
        if getattr(receiver_sender, 'bot', False):
            return await event.reply("Bots don't take ccm, sweetheart.", parse_mode='html')
    except Exception:
        pass  # can't verify — fall through rather than block a legitimate gift over a lookup hiccup

    amount = int(event.pattern_match.group(1))
    if amount < GIFTCCM_MIN_AMOUNT:
        return await event.reply(f"That's a bit too little. Minimum {GIFTCCM_MIN_AMOUNT} ccm~", parse_mode='html')

    sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
    sender_balance = (sender_doc or {}).get("ccm_balance", 0)
    if sender_balance < amount:
        return await event.reply(
            f"Hmm, you don't have enough for that. You've got {sender_balance:,}~",
            parse_mode='html'
        )

    receiver_mention = await get_html_mention(event, receiver_id)
    # 🎀 Reze voice confirm design
    confirm_text = f"Sending {amount:,} ccm to {receiver_mention}?~"
    buttons = [[
        Button.inline("✅ Yeah", data=f"giftccm_confirm_{sender_id}_{receiver_id}_{amount}"),
        Button.inline("❌ Nope", data=f"giftccm_cancel_{sender_id}_{receiver_id}_{amount}")
    ]]
    await event.reply(confirm_text, buttons=buttons, parse_mode='html')

@bot1.on(events.CallbackQuery(pattern=r'^giftccm_(confirm|cancel)_(\d+)_(\d+)_(\d+)$'))
async def gift_ccm_callback_handler(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    amount = int(event.pattern_match.group(4))
    if event.sender_id != sender_id:
        return await event.answer("That's not yours to tap, sweetheart~", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)

    if action == "cancel":
        try:
            await event.edit("Okay, keeping it with you then~", buttons=None)
            await event.answer("Cancelled~", alert=True)
        except Exception as e:
            await report_system_error("gift_ccm_callback_handler (cancel)", f"{e}\nData: {event.data}")
            try:
                await event.answer("Hmm, something didn't work.", alert=True)
            except Exception:
                pass
        return

    # confirm — try_deduct_ccm is the atomic, race-safe part: it only takes effect if the
    # sender STILL has enough RIGHT NOW, never trusting the balance shown when the button was
    # first sent (which could be stale by the time it's tapped).
    try:
        if not await try_deduct_ccm(sender_id, amount):
            await event.edit("Hmm, you don't have enough for that now.", parse_mode='html', buttons=None)
            await event.answer("Not enough ccm~", alert=True)
            return
        await users_catcher_col.update_one(
            {"user_id": receiver_id},
            {"$inc": {"ccm_balance": amount}},
            upsert=True
        )
        receiver_mention = await get_html_mention(event, receiver_id)
        await event.edit(
            f"{amount:,} ccm, off to {receiver_mention}. Don't be a stranger~",
            parse_mode='html',
            buttons=None
        )
        await event.answer("Sent~", alert=True)
    except Exception as e:
        await report_system_error("gift_ccm_callback_handler (confirm)", f"{e}\nData: {event.data}")
        try:
            await event.answer("Hmm, something didn't work.", alert=True)
        except Exception:
            pass

# ==========================================
# 🪙 /giftgram — player-to-player gram transfer (per owner request: so one player can pay another
# in grams, e.g. for a card). Same reply + ✅/❌ confirm UX as /giftccm. The payment is the atomic
# try_deduct_gram; if crediting the receiver fails AFTER the deduction the sender is refunded, and
# every completed transfer is logged to gram_transfers (grams are real-money-valued, so keep a trail).
# ==========================================
GIFTGRAM_MIN_AMOUNT = 1
GIFTGRAM_MAX_AMOUNT = 1_000_000
GIFTGRAM_COOLDOWN_SECONDS = 5
gram_transfers_col = db["gram_transfers"]
_GIFTGRAM_CONSUMED = set()   # (chat_id, msg_id) of confirm prompts already used — one prompt can never pay twice

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]giftgram(?:@\w+)?\s+(\d{1,9})$', 'bot1')))
async def gift_gram_handler(event):
    sender_id = event.sender_id
    if not event.is_reply:
        return await event.reply(
            f"{GRAM_EMOJI} လွှဲချင်တဲ့သူကို <b>Reply</b> ပြန်ပြီး <code>/giftgram [gram]</code> လို့ရိုက်ပါ။",
            parse_mode='html')
    is_cd, remaining = await is_on_cooldown(sender_id, "giftgram", GIFTGRAM_COOLDOWN_SECONDS)
    if is_cd:
        return await event.reply(f"⏳ {remaining:.0f}s စောင့်ပါ။", parse_mode='html')
    replied = await event.get_reply_message()
    if not replied or not replied.sender_id:
        return await event.reply("❌ လက်ခံမယ့်သူကို မတွေ့ပါ။", parse_mode='html')
    receiver_id = replied.sender_id
    if receiver_id == sender_id:
        return await event.reply("❌ ကိုယ့်ကိုယ်ကို လွှဲလို့မရပါ။", parse_mode='html')
    try:
        receiver_sender = await replied.get_sender()
        if getattr(receiver_sender, 'bot', False):
            return await event.reply("❌ Bot ကို gram လွှဲလို့မရပါ။", parse_mode='html')
    except Exception:
        pass  # can't verify — don't block a legitimate transfer over a lookup hiccup
    amount = int(event.pattern_match.group(1))
    if amount < GIFTGRAM_MIN_AMOUNT:
        return await event.reply(f"❌ အနည်းဆုံး {GIFTGRAM_MIN_AMOUNT} g ပါ။", parse_mode='html')
    if amount > GIFTGRAM_MAX_AMOUNT:
        return await event.reply(f"❌ တစ်ကြိမ်ကို အများဆုံး {GIFTGRAM_MAX_AMOUNT:,} g ပါ။", parse_mode='html')
    unlimited = has_unlimited_gram(sender_id)
    if not unlimited:
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id}) or {}
        balance = int(sender_doc.get("gram_balance", 0))
        if balance < amount:
            return await event.reply(
                f"❌ gram မလောက်ပါ — သင့်မှာ <code>{balance:,}</code> g ပဲရှိပါတယ်။ /balance မှာ ccm ကို /exchange နဲ့ gram ပြောင်းလို့ရပါတယ်။",
                parse_mode='html')
    receiver_mention = await get_html_mention(event, receiver_id)
    await event.reply(
        f"{GRAM_EMOJI} <b>{receiver_mention}</b> ဆီ <code>{amount:,}</code> g လွှဲမလား?\n"
        + ("♾️ <i>Owner — gram အကန့်အသတ်မရှိပါ (သင့်ဆီကနေ မနှုတ်ပါ)။</i>\n" if unlimited else "")
        + f"<i>လွှဲပြီးရင် ပြန်မရနိုင်ပါ (သူ့ဆီ ရောက်သွားမှာပါ)။</i>",
        parse_mode='html',
        buttons=[[Button.inline("✅ Confirm", data=f"giftgram_confirm_{sender_id}_{receiver_id}_{amount}"),
                  Button.inline("❌ Cancel", data=f"giftgram_cancel_{sender_id}_{receiver_id}_{amount}")]])

@bot1.on(events.CallbackQuery(pattern=r'^giftgram_(confirm|cancel)_(\d+)_(\d+)_(\d+)$'))
async def gift_gram_callback_handler(event):
    action = event.pattern_match.group(1)
    if isinstance(action, bytes):
        action = action.decode('utf-8')
    sender_id = int(event.pattern_match.group(2))
    receiver_id = int(event.pattern_match.group(3))
    amount = int(event.pattern_match.group(4))
    if event.sender_id != sender_id:
        return await event.answer("သင့်ရဲ့ button မဟုတ်ပါ။", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)
    if action == "cancel":
        try:
            await event.edit("❎ ပယ်ဖျက်လိုက်ပါပြီ။", buttons=None)
            await event.answer("Cancelled", alert=False)
        except Exception as e:
            await report_system_error("gift_gram_callback_handler (cancel)", f"{e}\nData: {event.data}")
        return
    token = (event.chat_id, event.message_id)
    if token in _GIFTGRAM_CONSUMED:
        return await event.answer("ဒီ လွှဲမှုကို လုပ်ပြီးသားပါ။", alert=True)
    _GIFTGRAM_CONSUMED.add(token)
    if len(_GIFTGRAM_CONSUMED) > 5000:
        _GIFTGRAM_CONSUMED.clear()
        _GIFTGRAM_CONSUMED.add(token)
    if amount < GIFTGRAM_MIN_AMOUNT or amount > GIFTGRAM_MAX_AMOUNT or receiver_id == sender_id:
        return await event.answer("❌ Invalid transfer.", alert=True)
    try:
        if not await try_deduct_gram(sender_id, amount):
            _GIFTGRAM_CONSUMED.discard(token)  # nothing was charged — allow a retry
            await event.edit("❌ gram မလောက်တော့ပါ။", buttons=None)
            return await event.answer("Not enough gram.", alert=True)
        try:
            await users_catcher_col.update_one({"user_id": receiver_id}, {"$inc": {"gram_balance": amount}}, upsert=True)
        except Exception:
            # the receiver couldn't be credited — give the sender their grams back, then surface the error
            await refund_gram(sender_id, amount)
            raise
        try:
            await gram_transfers_col.insert_one({"from": sender_id, "to": receiver_id, "grams": amount, "ts": time.time(),
                                                 "minted": has_unlimited_gram(sender_id)})
        except Exception as e:
            print(f"⚠️ gram_transfers log failed (transfer itself succeeded): {type(e).__name__}: {e}")
        receiver_mention = await get_html_mention(event, receiver_id)
        if has_unlimited_gram(sender_id):
            left_text = "♾️ Unlimited"
        else:
            left_text = f"<code>{int(((await users_catcher_col.find_one({'user_id': sender_id})) or {}).get('gram_balance', 0)):,}</code> g"
        await event.edit(
            f"✅ {GRAM_EMOJI} <code>{amount:,}</code> g ကို {receiver_mention} ဆီ ပို့ပြီးပါပြီ။\n"
            f"သင့်ဆီ ကျန်တာ: {left_text}",
            parse_mode='html', buttons=None)
        await event.answer("Sent", alert=False)
    except Exception as e:
        await report_system_error("gift_gram_callback_handler (confirm)", f"{e}\nData: {event.data}")
        try:
            await event.answer("Hmm, something didn't work.", alert=True)
        except Exception:
            pass


# ---- CATCH LOGIC (with daily limit and spawn_count increment on success) ----
DAILY_CATCH_LIMIT = 22  # flat cap for everyone — single source of truth, used by both the
# limit check in catch_handler and the /today "who hit the limit first" ranking below.

rare_catch_log_col = db["rare_catch_log"]

async def notify_owner_rare_catch(tier, char_id, char_name, user_id, fullname, chat_id, msg_id=None):
    """DM the OWNER who just caught a SUPREME / CATAPHRACT card (per owner request: so they can see who got
    the valuable ones): card + id + event, its worth in grams, the catcher (mention · full name · user id),
    the chat (title · id), how many of its catch limit are used, and a link to the catch message when one can
    be built. Never raises — a failed DM only prints a warning."""
    try:
        mention = f'<a href="tg://user?id={user_id}">{escape_html(fullname or str(user_id))}</a>'
        doc = await characters_base_col.find_one({"char_id": char_id}, {"event": 1, "spawn_count": 1, "spawn_limit": 1}) or {}
        event_name = doc.get("event")
        worth = await _card_worth_grams(tier, event_name)
        title = link = None
        try:
            ent = await bot1.get_entity(chat_id)
            title = getattr(ent, "title", None) or " ".join(x for x in (getattr(ent, "first_name", None), getattr(ent, "last_name", None)) if x) or None
            uname = getattr(ent, "username", None)
            if uname:
                link = f"https://t.me/{uname}/{msg_id}" if msg_id else f"https://t.me/{uname}"
        except Exception:
            pass
        if link is None and msg_id and str(chat_id).startswith("-100"):
            link = f"https://t.me/c/{str(chat_id)[4:]}/{msg_id}"
        lines = [f"🏆 <b>{tier} ᴄᴀᴜɢʜᴛ!</b>",
                 f"🎴 <b>{escape_html(char_name or char_id)}</b> · <code>{display_char_id(char_id)}</code>"
                 + (f" · {escape_html(event_name)}" if event_name else "")]
        if worth:
            lo, hi = worth
            lines.append(f"{GRAM_EMOJI} ᴡᴏʀᴛʜ: <code>{lo:,}</code> g" if lo == hi else f"{GRAM_EMOJI} ᴡᴏʀᴛʜ: <code>{lo:,}–{hi:,}</code> g")
        lines += [f"👤 {mention} · {escape_html(fullname or '')}",
                  f"🆔 ᴜsᴇʀ: <code>{user_id}</code>",
                  f"💬 ᴄʜᴀᴛ: " + (f"<b>{escape_html(title)}</b> · " if title else "") + f"<code>{chat_id}</code>"]
        limit, count = doc.get("spawn_limit", 0) or 0, doc.get("spawn_count", 0) or 0
        if limit > 0:
            lines.append(f"📦 ᴄᴀᴜɢʜᴛ: <code>{count}/{limit}</code>")
        if link:
            lines.append(f'🔗 <a href="{link}">Open the catch message</a>')
        await bot1.send_message(OWNER_ID, "\n".join(lines), parse_mode='html', link_preview=False)
    except Exception as e:
        print(f"⚠️ notify_owner_rare_catch failed: {type(e).__name__}: {e}")

async def perform_catch(chat_id, user_id, spawn_data, event, reply_to_msg=None, is_callback=False, temp_msg_id=None):
    mention = await get_html_mention(event, user_id)
    plain_name = await get_plain_name(event, user_id)
    await ensure_user_registered(user_id, plain_name)
    try:
        # 💰 A successful catch pays a SMALL flat ccm amount (CATCH_CCM_MIN..CATCH_CCM_MAX — see the
        # CURRENCY SYSTEM block near CNFT_RARITY_INFO). It rides in the same atomic $inc as the
        # catch counters, so there's no extra DB round trip.
        ccm_reward = random.randint(CATCH_CCM_MIN, CATCH_CCM_MAX) if CATCH_CCM_MAX > 0 else 0
        inc_fields = {
            "total_caught": 1,
            f"group_catches.{str(chat_id)}": 1,
            "daily_catches": 1
        }
        if ccm_reward > 0:
            inc_fields["ccm_balance"] = ccm_reward
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
                "$inc": inc_fields,
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

        # 🩹 CHANGED (per owner request): new catch-announcement layout. The ID is in <code> so tapping it
        # copies it (handy for /check <id>, /sell <id>, /gift ...).
        success_msg = (
            f"Ohh my Goodness, {mention} fucked {escape_html(character_name)}\n"
            f"{rarity_emoji} ʀᴀʀɪᴛʏ: {rarity_display}  | ID - <code>{display_char_id(spawn_data['char_id'])}</code>\n"
            f"{cat_display}\n"
            + (f"💰 <b>+{ccm_reward:,} ccm</b> earned!\n" if ccm_reward > 0 else "")
            + "👒 ᴄʜᴇᴄᴋ ʏᴏᴜʀ /harem!"
        )
        # 🏆 Supreme / Cataphract only ever come from the owner's /fspawn. Who caught one is NOT shown in the
        # group — the OWNER gets a private DM (see notify_owner_rare_catch, sent after the catch message is
        # delivered) and the catch is kept in rare_catch_log.
        if rarity_tier in NEVER_SPAWN_TIERS:
            try:
                await rare_catch_log_col.insert_one({"user_id": user_id, "fullname": plain_name, "chat_id": chat_id,
                                                     "char_id": spawn_data['char_id'], "name": character_name,
                                                     "tier": rarity_tier, "ts": time.time()})
            except Exception as _e:
                print(f"⚠️ rare_catch_log insert failed: {type(_e).__name__}: {_e}")

        # 🩹 CHANGED (per owner request): harem + profile buttons removed — a single 🛒 Buy &
        # Sell button opens the market menu instead (see market_menu_from_catch_callback).
        success_buttons = [[
            Button.inline("🛒 Buy & Sell", data=f"mkt_menu_{user_id}")
        ]]
        # 🎁 Under Buy & Sell: a URL button ANYONE can tap — opens bot2's DM, /start pays free gram
        # (see TAKE GRAM FREE near CNFT_RARITY_INFO). Not shown if bot2 isn't running.
        _free_gram_link = free_gram_url()
        if _free_gram_link:
            success_buttons.append([Button.url(FREE_GRAM_BUTTON_LABEL, _free_gram_link)])

        if chat_id in active_group_spawns: 
            del active_group_spawns[chat_id]
        if chat_id in spawn_locks: 
            del spawn_locks[chat_id]

        final_msg_id = temp_msg_id
        if is_callback:
            _sent = await bot1.send_message(chat_id, success_msg, reply_to=reply_to_msg or event.message_id, parse_mode='html', buttons=success_buttons)
            final_msg_id = getattr(_sent, "id", None)
        elif temp_msg_id:
            try:
                await bot1.edit_message(chat_id, temp_msg_id, success_msg, parse_mode='html', buttons=success_buttons)
            except errors.MessageNotModifiedError:
                pass
            except Exception:
                _sent = await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
                final_msg_id = getattr(_sent, "id", None)
        else:
            _sent = await event.reply(success_msg, parse_mode='html', buttons=success_buttons)
            final_msg_id = getattr(_sent, "id", None)
        if rarity_tier in NEVER_SPAWN_TIERS:   # 🏆 tell the owner (in the background — never holds up or breaks the catch)
            _t = asyncio.create_task(notify_owner_rare_catch(
                rarity_tier, spawn_data['char_id'], character_name, user_id, plain_name, chat_id, final_msg_id))
            _BOTGATE_BG_TASKS.add(_t)
            _t.add_done_callback(lambda t: (_BOTGATE_BG_TASKS.discard(t), t.cancelled() or t.exception()))
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

# 🎯 CATCH_RACE_JUDGE_WINDOW — owner report (repeated — "the first person to actually type
# /fuck [name] doesn't get it, someone who typed it later does"): the previous fix (claim the
# spawn atomically under spawn_locks[chat_id], with no `await` between arriving in
# catch_handler and reaching that lock) was necessary but NOT sufficient. It assumed asyncio
# task-scheduling order faithfully mirrors real message-send order — but it doesn't have to:
# under real load, a later-sent /fuck can still get its handler task scheduled to run (and
# reach the lock) before an earlier one's, for reasons outside this bot's control. Ported from
# main_pyန.py, where this was already diagnosed and fixed the same way (see its own
# CATCH_RACE_JUDGE_WINDOW comment).
#
# So winning no longer depends on task-scheduling order AT ALL. Every valid /fuck (or /catch,
# /morgan) attempt for a spawn is buffered for CATCH_RACE_JUDGE_WINDOW seconds, and the winner
# is picked by comparing event.id — the message ID Telegram itself assigns, strictly
# increasing per chat, authoritative and independent of any bot-side processing jitter. Real
# trade-off: EVERY catch (including an uncontested solo one) now waits out this window before
# the catch even begins, in exchange for a fairness guarantee that no longer depends on
# framework/scheduler internals. See catch_handler for the buffering + judging logic.
CATCH_RACE_JUDGE_WINDOW = 0.6

def _catch_user_blocked(user_id):
    """Sync + in-memory. True while the user is spam-muted or gbanned (gban shares user_mute_until)."""
    if user_id in user_mute_until and time.time() < user_mute_until[user_id]:
        return True
    return bool(is_gbanned(user_id)[0])

# 🩹 (per owner request) A spam-muted player's /fuck used to be ignored in total silence, so they thought the bot
# was broken. They now get ONE short notice saying how long is left (and the clock time it ends). Throttled per
# person so mashing /fuck can't turn the notice itself into spam, and it deletes itself after a while.
CATCH_MUTE_NOTICE_COOLDOWN = 15   # seconds — at most one notice per muted person per window
CATCH_MUTE_NOTICE_TTL = 30        # seconds until the notice deletes itself
_catch_mute_notice_last = {}      # user_id -> ts

def _fmt_mute_left(seconds):
    """Pure. 372 -> '6m 12s', 45 -> '45s', 4000 -> '1h 06m' (rounded up, never shows 0)."""
    seconds = max(1, int(seconds) + (0 if float(seconds).is_integer() else 1))
    h, rem = divmod(seconds, 3600)
    m, sec = divmod(rem, 60)
    if h:
        return f"{h}h {m:02d}m"
    if m:
        return f"{m}m {sec:02d}s"
    return f"{sec}s"

async def _send_catch_block_notice(event, user_id):
    """Tells a racer WHY their /fuck was ignored: spam-muted -> time left + end clock time; gbanned -> the
    normal ban text (with its duration). Sent as a plain message, NOT a reply — a muted player's command is
    already deleted by spam_detection_and_mute, and replying to a deleted message fails. Never raises."""
    try:
        now = time.time()
        banned, rec = is_gbanned(user_id)
        if banned:
            if now - _gban_notice_last_sent.get(user_id, 0) < GBAN_NOTICE_COOLDOWN:
                return
            _gban_notice_last_sent[user_id] = now
            await bot1.send_message(event.chat_id, build_gban_blocked_text(rec), parse_mode='html')
            return
        until = user_mute_until.get(user_id, 0)
        if now >= until:
            return
        if now - _catch_mute_notice_last.get(user_id, 0) < CATCH_MUTE_NOTICE_COOLDOWN:
            return
        _catch_mute_notice_last[user_id] = now   # set BEFORE any await — concurrent /fuck messages must not double-send
        if len(_catch_mute_notice_last) > 5000:
            for k in [k for k, ts in _catch_mute_notice_last.items() if now - ts > 300]:
                _catch_mute_notice_last.pop(k, None)
        mention = await get_html_mention(event, user_id)
        end_clock = datetime.fromtimestamp(until, TZ).strftime("%H:%M")
        msg = await bot1.send_message(
            event.chat_id,
            bq(f"⏳ {mention}, /fuck is paused for you right now — it unlocks in "
               f"<code>{_fmt_mute_left(until - now)}</code> (≈ {end_clock})."),
            parse_mode='html')
        asyncio.create_task(_delete_after_delay(bot1, event.chat_id, msg.id, delay=CATCH_MUTE_NOTICE_TTL))
    except Exception as _e:
        print(f"⚠️ catch block notice failed for {user_id}: {type(_e).__name__}: {_e}")

async def _catch_eligibility(event, user_id):
    """Can this racer actually take the spawn right now? Returns (status, notice_text):
         ("ok", None)       — free to catch
         ("blocked", None)  — spam-muted / gbanned: skipped (the judge sends them _send_catch_block_notice)
         ("capped", text)   — hit the daily limit: skipped, with the 'come back tomorrow' text to send them
    Never claims or changes the spawn — catch_handler's judge walks the racers in message-ID order and
    uses this to find the first one who really can."""
    if _catch_user_blocked(user_id):
        return "blocked", None
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
        if user_doc.get("daily_catches", 0) >= DAILY_CATCH_LIMIT:
            mention = await get_html_mention(event, user_id)
            return "capped", (
                f"<b>…</b> {mention}, you've had enough of me for today — {DAILY_CATCH_LIMIT} is your limit. "
                f"come back tomorrow 🤍"
            )
    return "ok", None

CATCH_USAGE_TEXT = (
    "📌 <b>Usage:</b> <code>/fuck [Character Name]</code>\n"
    "<i>◈ say my name exactly, or whisper /who and I'll tell you… "
    "or just tap the button.</i>"
)

# 🩹 CHANGED (per owner request): /obtain renamed to /fuck for the bot's cute-anime-wifey
# tone. /obtain (and the .obtain dot-form) still work as a legacy alias, and /collect is
# still retired (a different, unrelated bot in the same groups uses that name — see below).
# /morgan stays as its own separate fun alias, unrelated to this rename.
# 🩹 CHANGED (per owner request): /catch is now a real, live alias too — not just text shown
# in reveal messages. /catch and /fuck claim the exact same spawn the exact same way, so both
# copy-buttons the bot shows (see who_reveal_handler / _identify_media_and_reply) actually work.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:morgan|fuck|catch)(?:@\w+)?\s+(.*)$', 'bot1')))
async def catch_handler(event):
    if event.is_private: return
    user_id = event.sender_id
    chat_id = event.chat_id
    # Check spam mute — GLOBALLY, across every group.
    # History: this used to be total silence (owner: "no repeated 'you're muted' reply on every retry").
    # Players then thought the bot was broken, so (per owner request) they now get ONE short notice with the
    # time left — throttled per person (CATCH_MUTE_NOTICE_COOLDOWN) so retries can't repeat it.
    if user_id in user_mute_until and time.time() < user_mute_until[user_id]:
        await _send_catch_block_notice(event, user_id)
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
    
    # See CATCH_REQUIRED_SUFFIX comment near normalize_name for why this check exists and why
    # it normally MUST reuse the exact same rejection text as a genuinely wrong guess.
    # 🩹 CHANGED (explicit owner request, 2026-09 — risk acknowledged): players were pasting
    # what a RIVAL name-reveal bot gave them (a bare first-name "hint", or a "full name" with a
    # trailing bracket flourish like "[♥]") and getting confused when the same-looking guess
    # failed here. This carves out exactly those two shapes — and ONLY when the guess is
    # otherwise a correct name for the character actually spawned right now — to explain why,
    # instead of the generic message. ⚠️ Tradeoff (flagged to and accepted by the owner): this
    # is a more specific signal than "wrong guess", so a rival-bot operator who notices it could
    # in principle compare against THIS bot's own /who output (which does carry the suffix) and
    # infer CATCH_REQUIRED_SUFFIX — the ambiguity the ANTI-SNIPE, PART 3 design above existed to
    # prevent. Revert to the single generic message below if that starts happening in practice.
    if not catch_name.endswith(CATCH_REQUIRED_SUFFIX):
        no_flourish = re.sub(r'\s*\[[^\]]*\]\s*$', '', catch_name).strip()  # drop a trailing "[...]" like "[♥]"
        target_norm = normalize_name(spawn_data["name"])
        target_first_word = target_norm.split(" ", 1)[0] if target_norm else ""
        guess_norm = normalize_name(no_flourish)
        if guess_norm and (guess_norm == target_norm or guess_norm == target_first_word):
            return await event.reply(
                "heyy, မင်းရေးတာ မမှားပေမယ့် ကဒ်မရနေတဲ့ အကြောင်းက တခြား name ဖော် bot ကို "
                "သုံးလို့ပါ။ ယူမယ်ဆို နောက် ကဒ်ကျလာချိန်မှာ တိုက်ရိုက် /w လို့ စာထောက်ပြီး "
                "ပေးတဲ့ နာမည်ကို ယူပြီး ကောက်ပါ။ အဆင်ပြေပါစေ 🤍",
                parse_mode='html'
            )
        return await event.reply(f"❌ <b>…that's not my name. whisper /who and try again.</b>", parse_mode='html')
    name_guess = catch_name[:-len(CATCH_REQUIRED_SUFFIX)]
    if normalize_name(name_guess) != normalize_name(spawn_data["name"]):
        return await event.reply(f"❌ <b>…that's not my name. whisper /who and try again.</b>", parse_mode='html')

    # 🎯 Buffer this valid attempt and judge the whole race by real Telegram message-ID order
    # once the window closes — see CATCH_RACE_JUDGE_WINDOW's docstring above for why. Every
    # racer's task lands here; only the FIRST one to arrive (task-scheduling order doesn't
    # matter for THIS part — it's just "who gets stuck holding the judging job", not who wins)
    # actually runs the code below the `if`. Everyone else just adds themselves to the buffer
    # and returns — the judge replies to them (win or lose) on their behalf once it decides.
    existing_buf = catch_race_buffer.get(chat_id)
    if existing_buf is not None:
        existing_buf.append((event, user_id))
        return
    buf = [(event, user_id)]
    catch_race_buffer[chat_id] = buf
    try:
        await asyncio.sleep(CATCH_RACE_JUDGE_WINDOW)
    finally:
        # try/finally so a stuck buffer entry (which would silently swallow every future
        # /fuck in this chat — see the `if existing_buf is not None` check above) can never
        # survive an unexpected error here.
        candidates = catch_race_buffer.pop(chat_id, buf)

    # Racers are ranked by real Telegram message ID = whoever actually sent /fuck first, full stop —
    # independent of network jitter, DB round trips, or asyncio scheduling on the bot's side.
    candidates.sort(key=lambda c: c[0].id)

    # 🔒 Claim the spawn atomically — check-and-set with no await in between, under the per-chat lock —
    # for the WHOLE judging below, so a late /fuck arriving while we sort out the racers can't grab it.
    # claimed_by stays None until we know who really gets it.
    async with spawn_locks[chat_id]:
        spawn_data = active_group_spawns.get(chat_id)
        if not spawn_data or spawn_data.get("claimed"):
            for loser_event, _loser_uid in candidates:
                asyncio.create_task(_reply_already_caught(loser_event, spawn_data))
            return
        spawn_data["claimed"] = True
        spawn_data["claimed_by"] = None

    # 🩹 FIX (owner report — "when the FIRST racer is at their limit / spam-muted / banned, everybody behind
    # them is ignored and the bot goes silent; only a later /fuck [name] works"): the old code judged ONLY
    # candidates[0]. If that person couldn't catch, the spawn was handed back and the rest of the racers —
    # who had typed the right name in time — were dropped without a single reply. Now the judge walks the
    # racers in message-ID order and the FIRST one who can actually catch wins:
    #   • daily limit reached → told "come back tomorrow", skipped
    #   • spam-muted / gbanned (incl. someone muted or banned DURING the judge window) → skipped, told how long is left
    #   • everyone else behind them still gets their real chance (and the normal "too late" if they lose)
    # Only if NOBODY can catch is the spawn released so a later /fuck still works.
    winner_idx = None
    try:
        status_by_uid = {}   # one DB check per person, even if they typed /fuck twice
        for idx, (cand_event, cand_uid) in enumerate(candidates):
            if cand_uid in status_by_uid:
                continue   # their earlier message already decided it (and, if capped, already notified)
            try:
                status, notice = await _catch_eligibility(cand_event, cand_uid)
            except Exception as _e:
                print(f"⚠️ catch eligibility check failed for {cand_uid}: {type(_e).__name__}: {_e}")
                status, notice = "error", None
            status_by_uid[cand_uid] = status
            if status == "ok":
                winner_idx = idx
                break
            if status == "blocked":
                # muted/banned (e.g. became so during the judge window) — skipped, but told why + when it ends
                asyncio.create_task(_send_catch_block_notice(cand_event, cand_uid))
            elif notice:
                async def _send_notice(ev=cand_event, text=notice):
                    try:
                        await ev.reply(text, parse_mode='html')
                    except Exception:
                        pass
                asyncio.create_task(_send_notice())
    except BaseException:
        spawn_data["claimed"] = False
        spawn_data["claimed_by"] = None
        raise

    if winner_idx is None:
        # nobody could take it — give the spawn back instead of wasting it
        async with spawn_locks[chat_id]:
            if active_group_spawns.get(chat_id) is spawn_data and spawn_data.get("claimed_by") is None:
                spawn_data["claimed"] = False
        return

    winner_event, user_id = candidates[winner_idx]
    spawn_data["claimed_by"] = user_id
    # Racers who typed it AFTER the winner lose this race (muted/banned ones stay silent).
    losers = []
    for _c in candidates[winner_idx + 1:]:
        if _c[1] == user_id:
            continue
        if _catch_user_blocked(_c[1]):
            asyncio.create_task(_send_catch_block_notice(_c[0], _c[1]))   # muted/banned: why + when, not "too late"
        else:
            losers.append(_c)

    # Tell everyone who lost this specific race exactly who beat them — fired once the
    # winner's own catch flow has actually finished below (see the try block around
    # perform_catch further down), not here, so "too late" never lands in the group before
    # the winner's own success message has gone out.
    event = winner_event  # everything below acts on behalf of the judged winner

    # 🔒 Limited rarity (Supreme/Cataphract): catching (/fuck) is deliberately NEVER blocked by the
    # per-user cap — a rare 4th copy won by actually catching it is accepted (per owner request).
    # The cap only stops copies arriving from other players: /gift and market bids.

    # 🐛→🦋 catching animation: one message, edited in place frame-by-frame — no extra
    # replies sent, and perform_catch() below edits this same message into the final result
    # (instead of deleting it and sending a new one).
    # 🩹 CHANGED (per owner request): this used to be event.reply("💫") — a REPLY to the
    # racer's own /fuck message, which meant onlookers could see (via the reply preview)
    # who was in the running before the result was ever revealed. Sent as a plain message now,
    # so nobody knows who's even attempting it until the final edit reveals the winner.
    temp_msg = await bot1.send_message(chat_id, "💫")
    await asyncio.sleep(0.6)
    try:
        await temp_msg.edit("🌈")
    except errors.MessageNotModifiedError:
        pass
    await asyncio.sleep(0.4)
    # 🩹 FIX (ported from main_pyန.py, same owner report there — "sometimes only the 2 emoji
    # show, no success message"): perform_catch's OWN internal try/except only starts after
    # its get_html_mention/get_plain_name/ensure_user_registered calls, so a hiccup in any of
    # those (flood-wait, transient network error) used to propagate straight out of this call
    # with nothing here to catch it — leaving the animation message stuck forever, the spawn
    # stuck claimed=True with no winner ever announced, and the win silently lost. This
    # try/except is the last-resort net around that.
    try:
        await perform_catch(chat_id, user_id, spawn_data, event, reply_to_msg=event.id, is_callback=False, temp_msg_id=temp_msg.id)
        # Losers only get told "too late" AFTER the winner's own success message has actually
        # landed — fired off concurrently from here so it doesn't block anything further.
        for loser_event, _loser_uid in losers:
            asyncio.create_task(_reply_already_caught(loser_event, spawn_data))
    except Exception as e:
        if chat_id in active_group_spawns:
            del active_group_spawns[chat_id]
        if chat_id in spawn_locks:
            del spawn_locks[chat_id]
        error_msg = f"❌ <b>Catch Logic Fault:</b> {escape_html(str(e))}"
        try:
            await bot1.edit_message(chat_id, temp_msg.id, error_msg, parse_mode='html')
        except Exception:
            await event.reply(error_msg, parse_mode='html')

async def _reply_already_caught(event, spawn_data):
    """Short, English, tells whoever lost the race exactly who beat them — replaces the old
    generic 'Already caught!' which left everyone guessing."""
    winner_id = (spawn_data or {}).get("claimed_by")
    if winner_id:
        mention = await get_html_mention(event, winner_id)
        text = (
            f"⟡ ᴛᴏᴏ ʟᴀᴛᴇ — ɪ'ᴠᴇ ᴀʟʀᴇᴀᴅʏ ʙᴇᴇɴ ꜰᴜᴄᴋᴇᴅ.\n"
            f"🪼╰─ ʙʏ {mention} ─╯🪼"
        )
    else:
        text = "❌ <b>…someone already claimed me.</b>"
    return await event.reply(text, parse_mode='html')
# ---- 🤖 AUTOMATIC refillcatch (owner report — "I have to run /refillcatch by hand all the time") ----
# spawn_count only ever moves +1 per real catch (perform_catch), but copies also enter and leave
# harems other ways — gifts, market wins, /delchar + pruning, merges, self-heal cleanup — so it
# drifts away from what's really in players' vaults, and "Caught globally" plus every CatchLimit
# check drift with it. /refillcatch fixed that, but only when the owner remembered to run it.
# Now the SAME recount runs on its own in the background (refillcatch_auto_loop, started from
# start_system) and only writes characters whose count is actually wrong.
REFILLCATCH_AUTO_INTERVAL_SECONDS = 900  # 15 min — change here to run it more/less often

async def _real_catch_counts():
    """{char_id: number of copies actually sitting in players' harems}."""
    pipeline = [
        {"$project": {"harem.char_id": 1}},
        {"$unwind": "$harem"},
        {"$group": {"_id": "$harem.char_id", "count": {"$sum": 1}}},
    ]
    results = await users_catcher_col.aggregate(pipeline, allowDiskUse=True).to_list(length=None)
    return {r["_id"]: r["count"] for r in results if r.get("_id")}

async def recompute_spawn_counts(hard_invalidate=True):
    """Recounts every character's spawn_count from real vault data. Writes only the ones that
    differ, and each write is compare-and-set on the value that was read — if a real catch bumped
    the counter in the meantime that one is simply skipped and fixed on the next pass, never
    clobbered with a stale number. Returns (corrected, total_checked)."""
    counts = await _real_catch_counts()
    docs = await characters_base_col.find({}, {"char_id": 1, "spawn_count": 1}).to_list(length=None)
    ops = []
    for d in docs:
        cid = d.get("char_id")
        if not cid:
            continue
        real = counts.get(cid, 0)
        if "spawn_count" in d:
            if d["spawn_count"] == real:
                continue
            flt = {"char_id": cid, "spawn_count": d["spawn_count"]}
        else:
            flt = {"char_id": cid, "spawn_count": {"$exists": False}}
        ops.append(UpdateOne(flt, {"$set": {"spawn_count": real}}))
    if ops:
        await characters_base_col.bulk_write(ops, ordered=False)
        await invalidate_character_caches(hard=hard_invalidate)
    return len(ops), len(docs)

async def refillcatch_auto_loop():
    await asyncio.sleep(90)  # let boot (indexes, roster preload) settle first
    while True:
        try:
            corrected, total = await recompute_spawn_counts(hard_invalidate=False)
            if corrected:
                print(f"🔁 [auto refillcatch] corrected {corrected}/{total} characters' catch counts.")
        except Exception as e:
            print(f"⚠️ refillcatch_auto_loop error: {type(e).__name__}: {e}")
        await asyncio.sleep(REFILLCATCH_AUTO_INTERVAL_SECONDS)

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
        corrected, total = await recompute_spawn_counts()
        await status_msg.edit(
            f"✅ <b>Full Resync Complete!</b>\n"
            f"🔁 <code>{total}</code> characters checked, <code>{corrected}</code> corrected — Global Catch counts now match players' real vaults.\n"
            f"🤖 ဒါကို bot က <code>{REFILLCATCH_AUTO_INTERVAL_SECONDS // 60}</code> မိနစ်တစ်ခါ အလိုအလျောက် လုပ်ပေးနေပါပြီ၊ manual မလိုတော့ပါဘူး။",
            parse_mode='html'
        )

# ==========================================
# 🎯 HMODE – RARITY FILTER + 🎪 EVENT FILTER
# ==========================================
# Two-step picker (per owner request): /hmode's rarity grid is step 1, unchanged in shape.
# Tapping a rarity now walks into step 2 — an event picker for that specific rarity, 2 buttons
# per row, 5 rows (10 events) per page, with Previous/Next navigation, a "Skip Event" option
# (sets rarity_filter only, clearing event_filter — the original single-step behavior), and a
# Back button to return to the rarity grid. Every button here uses a plain numeric index in its
# callback_data, never the raw event name — same lesson as /setvalue's event picker (see its
# own comment near ccmsetevent_pick): Telegram's callback_data caps at 64 bytes, easy to blow
# past with a longer name (Burmese script runs ~3 bytes/character), and an index sidesteps that
# entirely regardless of name length or script.
HMODE_EVENTS_PER_PAGE = 10  # 2/row × 5 rows, per owner spec

async def _list_events_for_tier(tier_name):
    """Distinct event names among characters of one rarity tier — 'General' included, same
    fallback used everywhere else this bot tags an uncategorized character."""
    raw_events = await characters_base_col.distinct("event", {"rarity_tier": tier_name})
    return sorted({(e or "General") for e in raw_events})

async def _render_hmode_rarity_grid(user_id):
    """(text, buttons) for /hmode's step-1 rarity grid — shared by the /hmode command itself
    and hevent_back_callback (the picker's Back button), so both stay in sync automatically."""
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    current_filter = user_doc.get("rarity_filter") if user_doc else None
    buttons, row = [], []
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
    text = (
        f"◈ <b>who do you want to see in /harem?</b>\n"
        f"Current: {current_filter if current_filter else 'None (Show All)'}\n\n"
        f"…tap a rarity to filter, or clear to see everyone\n"
        f"<i>🔐 Only you can use these buttons.</i>"
    )
    return text, buttons

async def _render_hmode_event_picker(tier_num, user_id, page=0):
    """(text, buttons) for /hmode's step-2 event picker, for the rarity tier_num points at."""
    rarity_data = RARITY_NUM_MAP[tier_num]
    tier_name = rarity_data["name"]
    tier = RARITY_TIERS[int(tier_num) - 1]
    event_names = await _list_events_for_tier(tier)

    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    current_rarity = user_doc.get("rarity_filter") if user_doc else None
    current_event = user_doc.get("event_filter") if (user_doc and current_rarity == tier_name) else None

    if not event_names:
        text = (
            f"◈ <b>{tier_name}</b>\n\n"
            f"No events found for this rarity yet — tap Skip to filter by rarity only."
        )
        buttons = [
            [Button.inline("⏭ Skip Event", data=f"hevent_skip_{tier_num}_{user_id}")],
            [Button.inline("🔙 Back", data=f"hevent_back_{user_id}")]
        ]
        return text, buttons

    total_pages = max(1, (len(event_names) + HMODE_EVENTS_PER_PAGE - 1) // HMODE_EVENTS_PER_PAGE)
    page = max(0, min(page, total_pages - 1))
    start = page * HMODE_EVENTS_PER_PAGE
    page_events = event_names[start:start + HMODE_EVENTS_PER_PAGE]

    rows, row = [], []
    for i, name in enumerate(page_events):
        global_idx = start + i
        mark = "✅ " if name == current_event else ""
        row.append(Button.inline(f"{mark}{name}", data=f"hevent_pick_{tier_num}_{global_idx}_{user_id}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)

    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Previous", data=f"hevent_page_{tier_num}_{page - 1}_{user_id}"))
    if start + HMODE_EVENTS_PER_PAGE < len(event_names):
        nav_row.append(Button.inline("Next ▶", data=f"hevent_page_{tier_num}_{page + 1}_{user_id}"))
    if nav_row:
        rows.append(nav_row)
    rows.append([Button.inline("⏭ Skip Event", data=f"hevent_skip_{tier_num}_{user_id}")])
    rows.append([Button.inline("🔙 Back", data=f"hevent_back_{user_id}")])

    text = (
        f"◈ <b>{tier_name} — pick an Event</b> (page {page + 1}/{total_pages})\n"
        f"Current: {current_event if current_event else 'All events'}\n\n"
        f"…tap an event to filter to just that, or Skip for every {tier_name} card\n"
        f"<i>🔐 Only you can use these buttons.</i>"
    )
    return text, rows

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]hmode(?:@\w+)?$', 'bot1')))
async def set_rarity_filter_handler(event):
    text, buttons = await _render_hmode_rarity_grid(event.sender_id)
    await event.reply(text, buttons=buttons, parse_mode='html')

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
            {"$set": {"rarity_filter": None, "event_filter": None}},
            upsert=True
        )
        await event.answer("…filter cleared. I'll show you everyone~")
        await event.edit("✅ Filter cleared. Use /harem to see everyone again.", buttons=None)
        return
    # 🎪 Rarity picked — walk into the event picker (per owner request) instead of setting the
    # filter immediately, so they can optionally narrow further to one specific event.
    tier_num = action
    if not RARITY_NUM_MAP.get(tier_num):
        return await event.answer("❌ Invalid rarity.")
    text, buttons = await _render_hmode_event_picker(tier_num, user_id, page=0)
    await event.edit(text, buttons=buttons, parse_mode='html')
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^hevent_pick_(\d+)_(\d+)_(\d+)$'))
async def hevent_pick_callback(event):
    tier_num = event.pattern_match.group(1)
    # 🩹 FIX (owner report — Event picker always said "Invalid rarity"): a CallbackQuery
    # pattern matches the raw callback bytes, so group(1) comes back as bytes (b"1") here,
    # not str "1" — RARITY_NUM_MAP is keyed by str, so the .get(tier_num) below always
    # missed. rarity_filter_callback (just above) and show_rarity_gallery_nav already
    # decode for this exact reason; this handler (and hevent_skip_callback/
    # hevent_page_callback right below) had been missed when /hmode's event picker was added.
    if isinstance(tier_num, bytes):
        tier_num = tier_num.decode('utf-8')
    global_idx = int(event.pattern_match.group(2))
    owner_user_id = int(event.pattern_match.group(3))
    if event.sender_id != owner_user_id:
        return await event.answer("⚠️ ဒါက သင့်ရဲ့ Filter မဟုတ်ပါ။ /hmode ကို ကိုယ်တိုင်နှိပ်ပါ။", alert=True)
    rarity_data = RARITY_NUM_MAP.get(tier_num)
    if not rarity_data:
        return await event.answer("❌ Invalid rarity.", alert=True)
    tier = RARITY_TIERS[int(tier_num) - 1]
    event_names = await _list_events_for_tier(tier)
    if global_idx < 0 or global_idx >= len(event_names):
        return await event.answer("⚠️ Event list ပြောင်းသွားပါပြီ — /hmode ကို ပြန်ခေါ်ပါ။", alert=True)
    event_name = event_names[global_idx]
    await users_catcher_col.update_one(
        {"user_id": owner_user_id},
        {"$set": {"rarity_filter": rarity_data["name"], "event_filter": event_name}},
        upsert=True
    )
    await event.answer(f"…now showing {rarity_data['name']} — {event_name}")
    await event.edit(
        f"✅ Filter set to {rarity_data['name']} — {event_name}. Use /harem to see them.",
        buttons=None
    )

@bot1.on(events.CallbackQuery(pattern=r'^hevent_skip_(\d+)_(\d+)$'))
async def hevent_skip_callback(event):
    tier_num = event.pattern_match.group(1)
    if isinstance(tier_num, bytes):  # 🩹 see hevent_pick_callback above
        tier_num = tier_num.decode('utf-8')
    owner_user_id = int(event.pattern_match.group(2))
    if event.sender_id != owner_user_id:
        return await event.answer("⚠️ ဒါက သင့်ရဲ့ Filter မဟုတ်ပါ။ /hmode ကို ကိုယ်တိုင်နှိပ်ပါ။", alert=True)
    rarity_data = RARITY_NUM_MAP.get(tier_num)
    if not rarity_data:
        return await event.answer("❌ Invalid rarity.", alert=True)
    await users_catcher_col.update_one(
        {"user_id": owner_user_id},
        {"$set": {"rarity_filter": rarity_data["name"], "event_filter": None}},
        upsert=True
    )
    await event.answer(f"…now showing {rarity_data['name']} first")
    await event.edit(f"✅ Filter set to {rarity_data['name']}. Use /harem to see them.", buttons=None)

@bot1.on(events.CallbackQuery(pattern=r'^hevent_page_(\d+)_(\d+)_(\d+)$'))
async def hevent_page_callback(event):
    tier_num = event.pattern_match.group(1)
    if isinstance(tier_num, bytes):  # 🩹 see hevent_pick_callback above
        tier_num = tier_num.decode('utf-8')
    page = int(event.pattern_match.group(2))
    owner_user_id = int(event.pattern_match.group(3))
    if event.sender_id != owner_user_id:
        return await event.answer("⚠️ ဒါက သင့်ရဲ့ Filter မဟုတ်ပါ။ /hmode ကို ကိုယ်တိုင်နှိပ်ပါ။", alert=True)
    if not RARITY_NUM_MAP.get(tier_num):
        return await event.answer("❌ Invalid rarity.", alert=True)
    text, buttons = await _render_hmode_event_picker(tier_num, owner_user_id, page=page)
    try:
        await event.edit(text, buttons=buttons, parse_mode='html')
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^hevent_back_(\d+)$'))
async def hevent_back_callback(event):
    owner_user_id = int(event.pattern_match.group(1))
    if event.sender_id != owner_user_id:
        return await event.answer("⚠️ ဒါက သင့်ရဲ့ Filter မဟုတ်ပါ။ /hmode ကို ကိုယ်တိုင်နှိပ်ပါ။", alert=True)
    text, buttons = await _render_hmode_rarity_grid(owner_user_id)
    try:
        await event.edit(text, buttons=buttons, parse_mode='html')
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

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
        "<i>Example:</i> <code>/fav 1234</code>\n\n"
        f"💠 Or set up to {MAX_FAV_CARDS} at once with plain numeric IDs, space-separated:\n"
        "<i>Example:</i> <code>/fav 1234 4567</code>\n\n"
        "◈ pick your favorite(s) to show off on <code>/harem</code> — browse them with the ◀ ▶ buttons there.",
        parse_mode='html'
    )

# ---- /fav with inline confirmation (single card) OR direct multi-set (2+ numeric IDs) ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]fav(?:@\w+)?\s+(.+)$', 'bot1')))
async def set_favorite_card(event):
    user_id = event.sender_id
    raw_args = event.pattern_match.group(1).strip()
    tokens = raw_args.split()
    is_unlimited = user_id == OWNER_ID or user_id in added_owner_ids

    # ==========================================
    # 💠 Multi-favourite path (per owner request): 2+ space-separated tokens. Deliberately
    # numeric-IDs-only (no confirm dance — a list of up to MAX_FAV_CARDS doesn't fit the
    # single-card Yes/No confirm UI, and callback_data has a hard ~64-byte cap that a list of
    # full char_ids would blow past anyway). REPLACES the whole favourites list (matches how a
    # single /fav already replaced the one favourite it had).
    # ==========================================
    if len(tokens) > 1:
        if len(tokens) > MAX_FAV_CARDS:
            return await event.reply(
                f"❌ <b>…up to {MAX_FAV_CARDS} favourites at a time — you gave {len(tokens)}.</b>",
                parse_mode='html'
            )
        if not all(re.fullmatch(r'\d+', t) for t in tokens):
            return await event.reply(
                "❌ <b>…for multiple favourites, IDs must be plain numbers, space-separated.</b>\n"
                "<i>Example:</i> <code>/fav 1234 4567</code>",
                parse_mode='html'
            )
        # De-dup while preserving order — typing the same id twice shouldn't cost 2 of the 10 slots.
        seen, ordered_tokens = set(), []
        for t in tokens:
            if t not in seen:
                seen.add(t)
                ordered_tokens.append(t)
        char_id_inputs = [normalize_char_id_input(t) for t in ordered_tokens]

        found_cards = await characters_base_col.find(
            {"char_id": {"$regex": "^(" + "|".join(re.escape(c) for c in char_id_inputs) + ")$", "$options": "i"}}
        ).to_list(length=None)
        found_by_upper = {c["char_id"].upper(): c for c in found_cards}

        if is_unlimited:
            owned_upper = set(found_by_upper.keys())  # 👑 unlimited vault — everything that exists counts as owned
        else:
            user_doc = await users_catcher_col.find_one({"user_id": user_id})
            user_harem = user_doc.get("harem", []) if user_doc else []
            owned_upper = {(x.get("char_id") or "").upper() for x in user_harem if isinstance(x, dict)}

        valid_ids, skipped = [], []
        for input_id in char_id_inputs:
            card = found_by_upper.get(input_id.upper())
            if not card:
                skipped.append((display_char_id(input_id), "not found"))
            elif card["char_id"].upper() not in owned_upper:
                skipped.append((display_char_id(card["char_id"]), "not yours"))
            elif card["char_id"] not in valid_ids:
                valid_ids.append(card["char_id"])

        # 🩹 "တကယ်ရှိမှ ပြနော်" — only IDs actually owned (or unlimited-vault) ever make it into
        # fav_cards; anything else is reported back as skipped, never silently added.
        if not valid_ids:
            return await event.reply(
                "❌ <b>…none of those are actually yours (or don't exist).</b> Catch/gift them first.",
                parse_mode='html'
            )

        await users_catcher_col.update_one(
            {"user_id": user_id},
            {"$set": {"fav_cards": valid_ids}, "$unset": {"fav_card": ""}},
            upsert=True
        )

        lines = [f"✅ <b>Favourites updated</b> ({len(valid_ids)}/{MAX_FAV_CARDS}):"]
        for cid in valid_ids:
            c = found_by_upper[cid.upper()]
            lines.append(f"⭐ <code>{display_char_id(cid)}</code> — {escape_html(c.get('name', 'Unknown'))}")
        if skipped:
            lines.append("")
            lines.append("⚠️ <b>Skipped:</b>")
            for label, reason in skipped:
                lines.append(f"• <code>{escape_html(str(label))}</code> ({reason})")
        lines.append("\n◈ Browse them with the ◀ ▶ buttons on <code>/harem</code>.")
        return await event.reply("\n".join(lines), parse_mode='html')

    # ==========================================
    # Single-card path — unchanged from before (confirm buttons + photo preview).
    # ==========================================
    raw_input = tokens[0]
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
    
    if is_unlimited:
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
        f"⟡ <b>FAVORITE SELECTION</b> ⟡\n\n"
        f"🪽 <b>{card['name']}</b>\n"
        f"⌁ <code>{display_char_id(actual_char_id)}</code>\n"
        f"◆ {card.get('rarity', 'Unknown')}\n"
        f"{artist_line(card)}\n\n"
        f"╰─━━━━━━━─╯\n"
        f"ᴍᴀʀᴋ ᴛʜɪs ᴄʜᴀʀᴀᴄᴛᴇʀ ᴀs ᴀ ғᴀᴠᴏʀɪᴛᴇ\n"
        f"ᴀɴᴅ ᴋᴇᴇᴘ ɪᴛ ɪɴ ʏᴏᴜʀ /ʜᴀʀᴇᴍ."
    )
    buttons = [
        [
            Button.inline("⟡ ʏᴇᴘ", data=f"fav_confirm_{user_id}_{actual_char_id}"),
            Button.inline("⟡ ɴᴏᴘᴇ", data=f"fav_cancel_{user_id}_{actual_char_id}")
        ]
    ]

    async def _send_fav_confirm(media):
        return await event.reply(confirm_text, file=media, buttons=buttons, parse_mode='html')

    # 🩹 FIX: this used to be a plain text-only event.reply — the character's photo never
    # showed up on the /fav confirmation, unlike every other confirm-style prompt in the bot
    # (/gift, /check, etc. all attach the card's media). Same pattern as _send_gift_confirm:
    # fall back to text-only if the media genuinely can't be fetched, so the confirm buttons
    # always reach the user either way.
    try:
        sent = await send_with_char_media(card["char_id"], card["storage_msg_id"], _send_fav_confirm)
        if sent is None:
            await event.reply(confirm_text, buttons=buttons, parse_mode='html')
    except Exception as e:
        print(f"Fav media error: {e}")
        await event.reply(confirm_text, buttons=buttons, parse_mode='html')

# ---- Helper functions for harem ----
async def remove_one_harem_copy(user_id, char_id, status, unbound_only=False):
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
    # unbound_only=True (gift / sell): never pick a copy that was gifted by an owner-mode person
    match = {"char_id": char_id, "status": status}
    if unbound_only:
        match["bound"] = {"$ne": True}
    await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": match}},
        {"$unset": {"harem.$": 1}}
    )
    await users_catcher_col.update_one({"user_id": user_id}, {"$pull": {"harem": None}})

async def clear_stale_favorite(user_id, char_id, remaining_harem):
    """Call this right after removing char_id from user_id's harem (gift / sell-and-bought /
    trade / scrap). If that was their LAST copy — and it was sitting in their favourites,
    legacy 'fav_card' or the new 'fav_cards' list, either way — drop it from both so /harem and
    /profile stop showing a card they no longer own."""
    still_owns_it = any(isinstance(it, dict) and it.get("char_id") == char_id for it in remaining_harem)
    if still_owns_it:
        return
    await users_catcher_col.update_one(
        {"user_id": user_id, "fav_card": char_id},
        {"$unset": {"fav_card": ""}}
    )
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$pull": {"fav_cards": char_id}}
    )

CARD_RANK_CACHE_TTL = 600  # 10 minutes — ranks don't need to be perfectly real-time, a bit of staleness is fine
_CARD_RANK_CACHE = {}  # char_id -> (owners_list, cached_at)

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
    1. Each card's top-10 ownership leaderboard is cached in-memory (CARD_RANK_CACHE_TTL).
       This cache is *shared across every user* — a popular card's leaderboard is the
       same list no matter whose /harem is asking, so cache hit rate is high.
    2. Whatever isn't cached gets resolved in ONE aggregation call covering every
       missing char_id at once (relies on the harem.char_id index), instead of the
       old approach of one full aggregation per card."""
    if not char_ids:
        return {}
    ranks = {}
    missing = []
    now = time.time()
    for cid in char_ids:
        cached = _CARD_RANK_CACHE.get(cid)
        if cached and (now - cached[1]) < CARD_RANK_CACHE_TTL:
            ranks[cid] = _rank_from_owners(cached[0], user_id)
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
        _CARD_RANK_CACHE[cid] = (owners, time.time())
    # Cards nobody owns yet never show up in the aggregation output — cache an empty
    # list for those too, otherwise they'd re-trigger the aggregation on every call.
    for cid in missing:
        if cid not in found_ids:
            ranks[cid] = None
            _CARD_RANK_CACHE[cid] = ([], time.time())
    return ranks

# ==========================================
# 🕒 HAREM ORDER — NEWEST FIRST (per owner request)
# ==========================================
#   • normal player: the card you got most recently is first (a char's newest copy counts, so a
#     fresh gift/catch of a card you already had moves it back to the top). Cards with no
#     caught_date (very old / imported entries) go last.
#   • owner / added-owner "unlimited vault": the cards most recently ADDED to the bot come first —
#     i.e. what /syncfromcatch just imported (it stamps created_at on every NEW card; re-syncing an
#     existing card leaves created_at alone, so an update doesn't push it to the top). Cards that
#     predate created_at come after those, newest storage message first.
def harem_recency_key(card, last_caught, unlimited_vault):
    """Sort key — ascending order == newest first."""
    if unlimited_vault:
        ca = card.get("created_at")
        has = isinstance(ca, (int, float)) and not isinstance(ca, bool)
        return (0 if has else 1, -(ca if has else 0), -int(card.get("storage_msg_id") or 0))
    return (0, -(last_caught.get(card.get("char_id"), 0) or 0), 0)

def order_harem_cards(cards, last_caught, unlimited_vault, weight_fn):
    """Newest first. Ties (same moment / no date) keep the old order: rarity (high first), then name."""
    base = sorted(cards, key=lambda x: (-weight_fn(x.get("rarity", "")), (x.get("name") or "").lower()))
    return sorted(base, key=lambda x: harem_recency_key(x, last_caught, unlimited_vault))

def split_into_category_runs(ordered_cards):
    """[(category, [cards...])...] — consecutive cards of the same anime share one run (one header)."""
    runs = []
    for card in ordered_cards:
        cat = card.get("category") or "Unknown Series"
        if runs and runs[-1][0] == cat:
            runs[-1][1].append(card)
        else:
            runs.append((cat, [card]))
    return runs

async def send_paginated_harem(client, chat_id, user_id, page=1, edit_msg_id=None, viewer_id=None, fav_idx=0):
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
    # Projected — this function only ever reads harem/rarity_filter/event_filter/fav_card(s)
    # off the user doc, no need to pull wallet_balance, cooldowns, msg_history, etc. too.
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"harem": 1, "rarity_filter": 1, "event_filter": 1, "fav_card": 1, "fav_cards": 1, "_id": 0}) or {}
    raw_harem = user_doc.get("harem", [])
    raw_owned_id_set = {item.get("char_id") for item in raw_harem if isinstance(item, dict) and item.get("char_id")}
    rarity_filter = user_doc.get("rarity_filter")
    # 🎪 event_filter (per owner request) — a further narrowing WITHIN rarity_filter, picked
    # from /hmode's event picker. Harem entries only ever store char_id/rarity/caught_date (see
    # perform_catch) — the event tag lives on the CHARACTER doc, not the catch record — so
    # applying this filter means joining against character data by char_id, unlike rarity_filter
    # which harem entries already carry directly.
    event_filter = user_doc.get("event_filter")

    if is_unlimited_vault:
        all_chars = await get_all_characters_cached()  # already invalidated on /addchar etc.
        if rarity_filter:
            all_chars = [c for c in all_chars if classify_rarity(c.get("rarity")) == classify_rarity(rarity_filter)]
        if event_filter:
            all_chars = [c for c in all_chars if (c.get("event") or "General") == event_filter]
        if not all_chars:
            msg = (f"⚔️ <b>…nobody matches that, quietly.</b>\nUse <code>/hmode</code> to change or clear it."
                   if (rarity_filter or event_filter) else "<b>No characters exist yet — add some with /addchar.</b>")
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
            roster_by_id = _get_roster_index(await get_all_characters_cached())["by_id"] if event_filter else {}
            for item in raw_harem:
                if isinstance(item, dict) and classify_rarity(item.get("rarity")) == classify_rarity(rarity_filter):
                    if event_filter:
                        # (was: a dict comprehension over the WHOLE roster rebuilt on every /harem view)
                        roster_char = roster_by_id.get(item.get("char_id"))
                        char_event = (roster_char.get("event") or "General") if roster_char else None
                        if char_event != event_filter:
                            continue
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
    CATEGORY_SEP = "༺━━━━༻"  # defined here too (not just inside the cache-miss branch below) so the render step further down can always use it, even on a cache hit
    # ⚡ PERFORMANCE: the unlimited vault (OWNER_ID / added_owner_ids) is IDENTICAL for every
    # such viewer at a given rarity filter — always literally the whole roster, nothing
    # personal. Building `groups`/`pages` below (sort every character, chunk into
    # PAGE_CHAR_BUDGET-sized pages) is pure CPU work with zero per-viewer input, so redoing
    # it on every single /harem call AND every Next/Previous tap was pure waste once the
    # roster gets large. Cache the FINISHED pages, keyed only by the active rarity filter,
    # and skip straight to page-selection on a hit. invalidate_character_caches() clears
    # this immediately on any real roster change; UNLIMITED_VAULT_PAGES_CACHE_TTL is just a
    # safety net.
    cache_key = rarity_filter or "__all__"
    now_ts = time.time()
    _cached_pages_entry = _unlimited_vault_pages_cache.get(cache_key) if is_unlimited_vault else None
    if _cached_pages_entry and now_ts < _cached_pages_entry[2]:
        pages, page_char_ids_per_page = _cached_pages_entry[0], _cached_pages_entry[1]
    else:
        # ⚡ PERFORMANCE FIX: the unlimited vault already fetched every character it needs as
        # `all_chars` above (get_all_characters_cached(), rarity-filtered) — `owned_ids` IS just
        # `all_chars`'s char_ids. Re-querying characters_base_col here for the exact same rows
        # was a completely redundant full round-trip on every cache-miss (any time
        # /addchar/editchar/delchar just ran, or the 10-min safety TTL lapsed) — real cost for
        # a roster in the thousands, and the actual "1 minute+" delay the owner reported likely
        # traces straight back to this. Regular (non-unlimited) users skip this branch entirely
        # and keep the original targeted query below — their harem is small and genuinely
        # different data.
        db_chars = all_chars if is_unlimited_vault else await characters_base_col.find({"char_id": {"$in": owned_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "event": 1, "_id": 0}).to_list(length=None)
        category_totals = await get_category_totals_cached()
        def get_rarity_weight(rarity_str):
            return rarity_rank_value(rarity_str)
        from collections import defaultdict
        by_category = defaultdict(list)
        for card in db_chars:
            by_category[card.get("category") or "Unknown Series"].append(card)
        # 🎨 UI REDESIGN (matches catch_bot's own /harem layout): cards are grouped back under a
        # per-category header — "🗽 <Anime> (<owned>/<total>)" then a dashed divider — with every
        # owned card underneath as its own single "<id> | <rarity emoji> | <name> [<event>] (xN)"
        # line. Groups are packed onto pages greedily; if a category's remaining cards don't fit
        # on the current page, its header is simply repeated at the top of the next page so every
        # page still reads correctly standalone.
        CATEGORY_SEP = "༺━━━━༻"
        groups = []  # [(cat, owned_in_cat, total_in_cat, [(char_id, card_line), ...]), ...]
        # 🕒 NEWEST FIRST (see HAREM ORDER above). The old layout listed every anime A→Z; now cards
        # are ordered by recency and a category header is printed for each consecutive run of the
        # same anime — "(owned/total)" still counts the WHOLE category, not just the run.
        owned_per_cat = {c: len(v) for c, v in by_category.items()}
        last_caught = {}
        if not is_unlimited_vault:
            for _it in filtered_harem:
                if isinstance(_it, dict) and _it.get("char_id"):
                    _ts = _it.get("caught_date") or 0
                    if _ts > last_caught.get(_it["char_id"], 0):
                        last_caught[_it["char_id"]] = _ts
        ordered_cards = order_harem_cards(db_chars, last_caught, is_unlimited_vault, get_rarity_weight)
        for cat, run_cards in split_into_category_runs(ordered_cards):
            owned_in_cat = owned_per_cat.get(cat, len(run_cards))
            total_in_cat = category_totals.get(cat, owned_in_cat)
            cat_lines = []
            for card in run_cards:
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
                display_name = name_with_event_tag(card['name'], card.get("event"))
                card_line = (
                    f"<code>{display_char_id(cid)}</code> | {rarity_emoji} | "
                    f"{escape_html(display_name)} ({status_str})"
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
            header_len = utf16_len(f"🗽 {cat} ({owned_in_cat}/{total_in_cat})\n{CATEGORY_SEP}") + 1
            idx = 0
            while idx < len(cat_lines):
                fresh_on_page = (not current_page) or (current_page[-1][0] != cat)
                if fresh_on_page and current_page and (current_len + header_len) >= PAGE_CHAR_BUDGET:
                    _flush_page()
                    fresh_on_page = True
                this_header_len = header_len if fresh_on_page else 0
                remaining_budget = PAGE_CHAR_BUDGET - current_len - this_header_len
                # 🩹 FIX (real bug — "everything shows as one giant unbroken block instead of
                # splitting across pages", reported for large vaults like the owner's unlimited
                # one): the check above only flushes when a NEW category is starting on an
                # already-full page. Once we were mid-category (fresh_on_page False) and the
                # page had already filled up, remaining_budget went zero/negative but nothing
                # here ever flushed for THAT — the inner packing loop's "always let at least one
                # line through" fallback (chunk starts empty every pass, so its own overflow
                # check never fires on the first line) just kept forcing one more line onto the
                # SAME page, forever, for as long as this one category still had lines left. A
                # single category deep enough (trivial for the owner's vault, which is the
                # entire roster) would swallow its whole remaining cast onto one page and never
                # roll over. If the page already has content and there's genuinely no room left,
                # flush now, before packing anything else — the `continue` re-enters this same
                # while loop with an empty page, so fresh_on_page recomputes True and this
                # category's header correctly reprints on the new page.
                if current_page and remaining_budget <= 0:
                    _flush_page()
                    continue
                chunk_start_idx = idx
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
                is_continuation = chunk_start_idx > 0  # some of this category's lines already landed on an earlier page
                current_page.append((cat, owned_in_cat, total_in_cat, chunk, is_continuation))
                current_page_ids.extend(cid for cid, _ in chunk)
                current_len += this_header_len + chunk_len
            current_len += 1  # blank spacer line after this category's block
        _flush_page()
        if is_unlimited_vault:
            _unlimited_vault_pages_cache[cache_key] = (pages, page_char_ids_per_page, now_ts + UNLIMITED_VAULT_PAGES_CACHE_TTL)
    total_pages = len(pages) or 1
    if page < 1: page = 1
    if page > total_pages: page = total_pages
    page_groups = pages[page - 1] if pages else []
    # Only now do we know exactly which cards are visible on this page — look up ranks for
    # just those instead of the whole vault.
    page_char_ids = page_char_ids_per_page[page - 1] if page_char_ids_per_page else []
    ranks_map = await get_user_ranks_for_cards(viewer_id, page_char_ids)
    # 🩹 FIX (per owner report): a single category was getting its "☘️ <Anime> (owned/total)"
    # header re-printed multiple times — even mid-page, not just across a Next/Previous page
    # turn. The chunking loop above already splits ONE category into several (cat, chunk)
    # entries in `page_groups` whenever it doesn't fit one pass of PAGE_CHAR_BUDGET (each later
    # entry correctly costs 0 toward the budget for its header — see `this_header_len` above,
    # `fresh_on_page` is already False for those), but this render step used to print a header
    # for every entry regardless, so the SAME anime's header showed up back-to-back for no
    # reason — and since that extra text was never counted against PAGE_CHAR_BUDGET in the
    # first place, it could quietly push a page's real length past what the budget accounted
    # for, right up to the 1024-char caption ceiling — which is exactly what was occasionally
    # knocking the fav-card photo off the message (see `can_attach_photo` below). Only print
    # the header when this entry's category actually differs from the one before it — whether
    # "before it" means the previous entry on this same page, or (for a page's first entry)
    # the last category shown on the previous page. Applies the same regardless of whether an
    # /hmode rarity filter is active — this is purely about how entries got chunked above.
    prev_page_last_cat = pages[page - 2][-1][0] if page > 1 and pages[page - 2] else None
    page_lines = []
    prev_cat = prev_page_last_cat
    n_groups = len(page_groups)
    for gi, (cat, owned_in_cat, total_in_cat, chunk, is_continuation) in enumerate(page_groups):
        if cat != prev_cat:
            contd_label = " (cont'd)" if is_continuation else ""
            page_lines.append(f"🗽 {escape_html(cat)} (<code>{owned_in_cat}/{total_in_cat}</code>){contd_label}")
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
        next_cat = page_groups[gi + 1][0] if gi + 1 < n_groups else None
        if cat != next_cat:
            page_lines.append("")  # blank spacer only once a category's block truly ends
        prev_cat = cat
    try:
        sender_ent = await client.get_entity(user_id)
        first = getattr(sender_ent, 'first_name', '') or ''
        last = getattr(sender_ent, 'last_name', '') or ''
        fullname = f"{first} {last}".strip() or getattr(sender_ent, 'username', '') or "Hunter"
    except: fullname = "Hunter"
    mention = f"<a href='tg://user?id={user_id}'><b>{escape_html(fullname)}</b></a>"
    output_text = f"{mention}'s {small_caps('Recent Characters')} - {small_caps('Page')}: <code>{page}/{total_pages}</code>\n"
    if rarity_filter:
        event_suffix = f" — {escape_html(event_filter)}" if event_filter else ""
        output_text += f" <b>🦚Filter:</b> {rarity_filter}{event_suffix}\n"
    output_text += "\n"
    for l in page_lines:
        output_text += l + "\n"
    output_text += "\n"
    if is_unlimited_vault:
        output_text += f"⟡ ᴘʀᴇᴍɪᴜᴍ ᴏᴡɴᴇʀ ᴍᴏᴅᴇ ⟡"
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
    # 🩹 FIX (per owner report): dropped the separate "Clean Filter"/"Change Filter" buttons
    # entirely — down to exactly two rows now: Previous/Next on top, a single switch_inline
    # "Characters" button below. /hmode still exists as a plain command for anyone who wants
    # to change or clear their filter; it's just no longer a button on every vault page.
    # 💠 Multi-favourite (per owner request): up to MAX_FAV_CARDS, ordered, browsed with their
    # own ◀ ▶ buttons independent of which text page (Previous/Next above) is showing. Stale
    # entries — cards the player no longer owns even a single copy of — are pruned here rather
    # than just skipped, so they don't keep coming back on every /harem call. Skipped for the
    # unlimited vault: every card is always "owned" there, so a favourite never goes stale.
    fav_ids_raw = get_fav_card_list(user_doc)
    if is_unlimited_vault:
        valid_favs = fav_ids_raw
    else:
        valid_favs = [cid for cid in fav_ids_raw if cid in raw_owned_id_set]
        if len(valid_favs) != len(fav_ids_raw):
            if valid_favs:
                await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"fav_cards": valid_favs}})
            else:
                await users_catcher_col.update_one({"user_id": user_id}, {"$unset": {"fav_cards": "", "fav_card": ""}})
    fav_idx = (fav_idx % len(valid_favs)) if valid_favs else 0

    nav_buttons = []
    if page > 1:
        nav_buttons.append(Button.inline("⟪⟪⟪", data=f"harem2_{page-1}_{fav_idx}_{user_id}_{viewer_id}"))
    if page < total_pages:
        nav_buttons.append(Button.inline("⟫⟫⟫", data=f"harem2_{page+1}_{fav_idx}_{user_id}_{viewer_id}"))
    if nav_buttons:
        buttons.append(nav_buttons)
    if len(valid_favs) > 1:
        prev_idx = (fav_idx - 1) % len(valid_favs)
        next_idx = (fav_idx + 1) % len(valid_favs)
        buttons.append([
            Button.inline("◀", data=f"favnav_{page}_{prev_idx}_{user_id}_{viewer_id}"),
            Button.inline(f"⭐ {fav_idx + 1}/{len(valid_favs)}", data=f"favnav_{page}_{fav_idx}_{user_id}_{viewer_id}"),
            Button.inline("▶", data=f"favnav_{page}_{next_idx}_{user_id}_{viewer_id}")
        ])
    buttons.append([Button.switch_inline(f"Characters ⛩ ({total_cards})", query=f"harem.{user_id}", same_peer=True)])
    # 💥 Real Fuck (per owner request): owner-mode viewers see EVERY character in the vault above, so
    # their own real catches (the harem array) get a separate inline gallery — "collected.<id>".
    if is_unlimited_vault and is_own_vault:
        real_count = sum(1 for item in raw_harem if isinstance(item, dict) and item.get("char_id"))
        buttons.append([Button.switch_inline(f"💥 Real Fuck ({real_count})", query=f"collected.{user_id}", same_peer=True)])
    # 🛒 Market shortcuts (per owner request — "make it easy to list for auction / buy-sell
    # from harem"): only shown on a real, own vault — selling doesn't apply to the unlimited
    # OWNER_ID/added-owner view above, since there's no actual harem-array copy there to move
    # into "market" status.
    if is_own_vault and not is_unlimited_vault:
        buttons.append([
            Button.inline("🛒 Sell a Character", data=f"mkt_sellpick_0_{user_id}"),
            Button.inline("🛍 Market", data=f"mkt_menu_{user_id}")
        ])
    if not buttons:
        buttons = None
    fav_media = None
    target_display_id = valid_favs[fav_idx] if valid_favs else None
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

    async def _send_fresh_harem_message():
        """Sends a brand-new vault message, with the cover photo re-attached whenever
        possible. Used both for a first-time /harem AND to recover from a failed
        edit_message below — a single shared path so a caption hiccup on page 12 can't
        permanently strand the vault on a photo-less text message for the rest of that
        pagination session."""
        if can_attach_photo:
            async def _send_harem_photo(media):
                return await client.send_message(chat_id, output_text, file=media, parse_mode='html', buttons=buttons)
            sent = await send_with_char_media(target_display_id, fav_card_data["storage_msg_id"], _send_harem_photo)
            if sent is not None:
                return
        await client.send_message(chat_id, output_text, parse_mode='html', buttons=buttons)

    try:
        if edit_msg_id:
            try:
                await client.edit_message(chat_id, edit_msg_id, output_text, parse_mode='html', buttons=buttons)
            except errors.MessageNotModifiedError:
                pass
            except Exception:
                # 🩹 FIX (real bug — reported: a too-long caption made the vault's photo vanish
                # for good). This used to fall back to a bare send_message with no file=, so the
                # very first time edit_message failed for ANY reason (a caption that slipped
                # past Telegram's real limit despite the PAGE_CHAR_BUDGET guarantee above, a
                # message deleted out from under it, a transient API hiccup — doesn't matter
                # which), the photo was gone for good: every later Next/Previous kept editing
                # that same now-photo-less message. Recovering through _send_fresh_harem_message
                # — the SAME "send fresh, with photo if possible" path a brand-new /harem uses —
                # means the cover photo is back on the very next page instead of never again.
                try:
                    await client.delete_messages(chat_id, edit_msg_id)
                except Exception:
                    pass
                await _send_fresh_harem_message()
        else:
            await _send_fresh_harem_message()
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
    # 🎪 event_filter (per owner request) — UNLIKE rarity_filter above, picking a specific
    # event via /hmode's event picker (see hevent_pick_callback near set_rarity_filter_handler)
    # IS a hard filter, applied further down: only cards matching BOTH filter_tier and
    # event_filter are shown. Deliberately different from the rarity-only philosophy just
    # explained — a whole paginated event picker exists specifically so someone can drill into
    # "just my Halloween 2026 SUPREME cards", so respecting that as a real filter (not just a
    # sort nudge) is the point, not a surprise.
    event_filter = user_doc.get("event_filter") if user_doc else None
    # 👑 Same unlimited-vault rule as /harem itself (see send_paginated_harem) — every
    # character that exists counts as owned, one copy each, computed live so /addchar never
    # needs a sync step. force_real_harem (the "collected." entry point) opts back into the
    # owner's REAL harem array, for viewing their actual personal catches.
    is_unlimited_vault = (target_user_id == OWNER_ID or target_user_id in added_owner_ids) and not force_real_harem

    latest_caught = {}  # char_id -> most recent caught_date, for hmode's newest-first sort
    # below. Only meaningful for a REAL harem (catch history exists); the unlimited vault has
    # no such history, so this just stays empty there and that sort key is a no-op for it.

    if is_unlimited_vault:
        all_chars = await get_all_characters_cached()  # already invalidated on /addchar etc.
        if not all_chars:
            return await event.answer([], cache_time=0, switch_pm="❌ No characters found.", switch_pm_param="start")
        harem_counts = {c["char_id"]: 1 for c in all_chars}
        owned_ids = list(harem_counts.keys())
        total_cards = len(owned_ids)
        # 🩹 PERF FIX (owner report — added-owners' harem inline gallery showing NOTHING at all):
        # all_chars above is already the FULL character roster with every field this function
        # needs (name/category/rarity/storage_msg_id/artist/event) — owned_ids for an unlimited
        # vault is, by construction, every char_id that exists. The characters_base_col query
        # that used to run unconditionally right after this if/else was therefore re-fetching
        # that exact same ~7000-document collection AGAIN from Mongo, over the network, on every
        # single inline keystroke/scroll — on top of the cache hit that had already just handed
        # us the same data. With the roster in the thousands, that redundant round trip was very
        # plausibly enough to blow past Telegram's ~10s inline-query response deadline, which
        # looks exactly like "nothing shows up" client-side (a silent timeout, not an error).
        db_chars = all_chars
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
            cdate = item.get("caught_date") or 0
            if cdate > latest_caught.get(cid, 0):
                latest_caught[cid] = cdate
        owned_ids = list(harem_counts.keys())
        total_cards = len(raw_harem)
        db_chars = await characters_base_col.find({"char_id": {"$in": owned_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "storage_msg_id": 1, "artist": 1, "event": 1, "_id": 0}).to_list(length=None)
    if filter_tier and event_filter:
        db_chars = [
            x for x in db_chars
            if classify_rarity(x.get("rarity", "")) == filter_tier and (x.get("event") or "General") == event_filter
        ]
        if not db_chars:
            return await event.answer(
                [], cache_time=0,
                switch_pm=f"…no {filter_tier} cards from '{event_filter}' yet", switch_pm_param="start"
            )
    # Filter-matching cards sort first (priority, not exclusion — see filter_tier note above);
    # within THAT matching group specifically, newest-caught first (per owner request — hmode
    # should surface your most recent pulls of that rarity, not bury them alphabetically) —
    # falls back to 0 (a no-op tie) for non-matching cards and for the unlimited vault, so
    # neither of those groups' ordering changes at all. Same anime kept together within each
    # remaining tier, same as before.
    # 🕒 NEWEST FIRST (per owner request — see HAREM ORDER above send_paginated_harem): within the
    # filter-matching group and within the rest, the most recently obtained card comes first
    # (unlimited vault: the most recently ADDED, e.g. just synced from catch_bot).
    db_chars = sorted(db_chars, key=lambda x: (
        0 if (filter_tier and classify_rarity(x.get("rarity", "")) == filter_tier) else 1,
        harem_recency_key(x, latest_caught, is_unlimited_vault),
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
            display_name = name_with_event_tag(card['name'], card.get("event"))
            cat_name = card.get("category") or "Unknown Series"
            owned_in_cat = cat_owned_counts.get(cat_name, 1)
            total_in_cat = category_totals.get(cat_name, owned_in_cat)
            # 🎪 Full event name (e.g. "💞Valentine💞") shown at the very bottom of the caption,
            # separated by two blank lines — same "General means no event" rule as /check's own
            # event_block, just applied here too since this caption never showed it (only the
            # compact [emoji] tag folded into display_name above).
            event_val = card.get("event")
            event_footer = (
                f"\n\n\n{escape_html(event_val)}"
                if event_val and str(event_val).strip().lower() != "general" else ""
            )
            caption = (
                f"🧃OᴡO! ᴄʜᴇᴄᴋ ᴏᴜᴛ {escape_html(owner_name)} sᴀɴ ᴄʜᴀʀᴀᴄᴛᴇʀ!\n\n"
                f"{escape_html(cat_name)} ({owned_in_cat}/{total_in_cat})\n"
                f"{display_char_id(cid)}: {escape_html(display_name)}{qty_note}\n"
                f"{rarity_emoji} {RARITY_LABEL_STYLED}: {rarity_plain}"
                f"{event_footer}"
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
    mode_note = " · 👑 Unlimited Vault" if is_unlimited_vault else (" · 💥 Real Fuck" if force_real_harem else "")
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

# ---- "cnft." inline query: browse/search /addspecial's CNFT cards from ANY chat (e.g. the
# promo group behind the spawn message's "💠 Buy CNFT Cards" button), so people can actually
# see what exists and who holds what before buying/selling — these never organically spawn, so
# this inline gallery is the only place most players will ever lay eyes on one. ----
async def handle_cnft_inline_query(event, query_text):
    builder = event.builder
    search = query_text.split(".", 1)[1].strip().lower() if "." in query_text else ""
    all_chars = await get_all_characters_cached()
    cnft_chars = [c for c in all_chars if classify_rarity(c.get("rarity", "")) in CNFT_TIERS]
    if search:
        cnft_chars = [
            c for c in cnft_chars
            if search in str(c.get("char_id", "")).lower()
            or search in str(c.get("name", "")).lower()
            or search in str(c.get("category", "")).lower()
        ]
    # Newest drops first (created_at is set by addspecial_ingest_handler at insert time).
    cnft_chars.sort(key=lambda c: c.get("created_at", 0), reverse=True)
    page_chars = cnft_chars[:50]
    try:
        media_by_cid = await get_char_display_media_batch(bot1, page_chars)
    except Exception as e:
        print(f"CNFT inline gallery batch fetch error: {e}")
        media_by_cid = {}
    # One query for every holder on this page instead of one find_one() per card. Collects
    # ALL holders per card now (a list, not a single winner) — CNFT is no longer one-of-one,
    # so several different people can legitimately hold the same card at once.
    holder_by_cid = {}
    page_cids = [c["char_id"] for c in page_chars]
    if page_cids:
        async for holder_doc in users_catcher_col.find(
            {"harem.char_id": {"$in": page_cids}}, {"user_id": 1, "harem.char_id": 1}
        ):
            held_here = {h.get("char_id") for h in holder_doc.get("harem", []) if isinstance(h, dict)}
            for cid in held_here & set(page_cids):
                holder_by_cid.setdefault(cid, []).append(holder_doc["user_id"])
    results = []
    for card in page_chars:
        cid = card["char_id"]
        storage_media = media_by_cid.get(cid)
        if not storage_media:
            continue
        try:
            holders = holder_by_cid.get(cid) or []
            status_line = f"👥 <b>Owned by:</b> {len(holders)}" if holders else "🆓 <b>Unclaimed</b>"
            caption = (
                f"💠 <b>{escape_html(card['name'])}</b>\n"
                f"🆔 <code>{display_char_id(cid)}</code>\n"
                f"🫧 <b>Anime:</b> {escape_html(card.get('category', ''))}\n"
                f"🏷️ <b>Rarity:</b> {card.get('rarity', '')}\n"
                f"{status_line}\n"
                f"💬 <a href=\"{escape_html(CNFT_PROMO_GROUP_URL)}\">Buy / trade here</a>"
            )
            results.append(_inline_media_result(builder, storage_media, cid, card['name'], caption))
        except Exception as e:
            print(f"CNFT inline gallery error for {cid}: {e}")
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
    elif query_text.startswith("cnft."):
        await handle_cnft_inline_query(event, query_text)
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
        f"📦 <b>Owned:</b> <code>{count} copies</code>\n\n"
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
    # ==========================================
    # 🎠 Multi-favourite (per owner request): "harem2" is Previous/Next on the TEXT page,
    # carrying the currently-shown favourite photo's index along so it doesn't reset to the
    # first favourite every time you flip a page. "favnav" is the ◀ ⭐ ▶ row that cycles WHICH
    # favourite photo is shown, independent of the text page. Both just re-render the same
    # view with different (page, fav_idx) — kept as a separate prefix from the older "harem"
    # branch above (3 parts, no fav_idx) so already-sent messages with the old button layout
    # keep working exactly as before.
    # ==========================================
    elif action_type in ("harem2", "favnav"):
        page = int(data_parts[1])
        fav_idx = int(data_parts[2])
        target_user_id = int(data_parts[3])
        viewer_id = event.sender_id
        await send_paginated_harem(bot1, event.chat_id, target_user_id, page=page, fav_idx=fav_idx, edit_msg_id=event.message_id, viewer_id=viewer_id)
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
                return await event.answer("❌ …not yours anymore.", alert=True)
            await users_catcher_col.update_one(
                {"user_id": target_user_id},
                {"$set": {"fav_cards": [card["char_id"]]}, "$unset": {"fav_card": ""}}
            )
            await event.answer("🤍your favorite now~")
            try:
                await event.edit(
                    f"🍬 <b>{escape_html(card['name'])}</b> (<code>{display_char_id(card['char_id'])}</code>) ကို "
                    f"favourite အဖြစ် သတ်မှတ်လိုက်ပြီ! ✨ /harem မှာ ဒီကတ်ပေါ်လာမယ်။",
                    parse_mode='html', buttons=None
                )
            except Exception:
                pass
            return
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
    raw_harem = user_doc.get("harem", []) if user_doc else []
    fav_ids_raw = get_fav_card_list(user_doc) if user_doc else []
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
    valid_fav_ids = [cid for cid in fav_ids_raw if cid in unique_ids]
    if len(valid_fav_ids) != len(fav_ids_raw):
        # Owner no longer has any copy of one or more of these — clear the stale favourite(s).
        if valid_fav_ids:
            await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"fav_cards": valid_fav_ids}})
        else:
            await users_catcher_col.update_one({"user_id": user_id}, {"$unset": {"fav_cards": "", "fav_card": ""}})
    if valid_fav_ids:
        fav_docs = await characters_base_col.find({"char_id": {"$in": valid_fav_ids}}).to_list(length=None)
        fav_names_by_id = {d["char_id"]: d.get("name", d["char_id"]) for d in fav_docs}
        SHOWN = 3
        shown = [f"{escape_html(fav_names_by_id.get(cid, cid))} (<code>{display_char_id(cid)}</code>)" for cid in valid_fav_ids[:SHOWN]]
        more = f" +{len(valid_fav_ids) - SHOWN} more" if len(valid_fav_ids) > SHOWN else ""
        label = small_caps("Favourite") if len(valid_fav_ids) == 1 else small_caps("Favourites")
        fav_line = f"├─➩ ⭐ {label}: {', '.join(shown)}{more}\n"

    pct = (unique_owned / base_total * 100) if base_total else 0
    level, level_progress, level_span = get_experience_level(total_caught)

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
        f"├─➩ 🎁 {small_caps('Gifted')}: <code>{total_gifted}</code>\n"
        f"├─➩ 🎀 {small_caps('Received')}: <code>{total_gift_received}</code>\n"
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

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]profile(?:@\w+)?$', 'bot1')))
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

# ==========================================
# 🔍 CHECK CHARACTER — styled to look IDENTICAL to catch_bot's own '.check <id>' DM reply
# (see parse_catchbot_check's docstring for a real example this is modeled on — built from the
# two actual replies the owner supplied). Deliberately NOT identical in a couple of ways because
# we genuinely don't have the same data catch_bot does, or no longer show a currency value at all:
#   • No Value/currency line — the currency system has been removed from this bot entirely.
#   • "Caught globally" counts catches on THIS bot only (character['spawn_count'], incremented
#     in perform_catch) — completely separate from catch_bot's own tally for the same
#     character, even after /syncfromcatch. A freshly-synced character legitimately starts at 0
#     here regardless of what catch_bot shows.
# Also dropped vs. the old version: the artist line and the spawn_limit/"X left" line — catch_bot's
# own '.check' doesn't show either, and matching it exactly means not showing them either.
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
    
    # ✅ spawn_count က catch အရေအတွက်ကိုပြတယ် — catch_bot ရဲ့ "caught globally" line အတွက်
    catch_count = character.get("spawn_count", 0)
    
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
    for u in top_hunters:
        uname = escape_html(clean_display_name(u.get("fullname"), fallback=f"Agent {u['user_id']}"))
        # ✅ Mention ပါစေ — tg://user deep link works off the stored user_id alone (no extra
        # get_entity round-trip needed), so tapping a name opens that collector's account.
        mention = f"<a href='tg://user?id={u['user_id']}'>{uname}</a>"
        leaderboard_str += f"➥ {mention} x{u['count']}\n"
    
    rarity_tier = classify_rarity(character.get("rarity", ""))
    rarity_emoji = RARITY_EMOJI.get(rarity_tier, RARITY_DEFAULT_EMOJI)
    rarity_plain = rarity_tier.capitalize() if rarity_tier else "Unknown"
    event_tag = character.get("event")
    event_block = f"\n\n{event_tag}" if event_tag and event_tag != "General" else ""

    # 🪙 Worth line (per owner request) — the card's configured worth IN GRAMS from /setvalue (a
    # range for Rarity 2-9, a single value per event for SUPREME), never a random roll. Omitted
    # entirely if the owner hasn't priced that tier/event yet — "hide, don't show a fake 0".
    ccm_value_line = ""
    _worth = await _card_worth_grams(rarity_tier, character.get("event"))
    if _worth:
        ccm_value_line = format_worth_line(*_worth) + "\n\n"

    info_text = (
        f"OwO! Check out this character!\n\n"
        f"{escape_html(character['category'])}\n"
        f"{display_char_id(character['char_id'])}: {escape_html(character['name'])}\n"
        f"({rarity_emoji} {RARITY_LABEL_STYLED}: {rarity_plain})"
        f"{event_block}\n\n"
        f"{ccm_value_line}"
        f"🌎 {catchstyle_caps('caught globally')}: {catch_count} {catchstyle_caps('times')}\n\n"
        f"🎖️ {catchstyle_caps('top 10 catchers of this character')}!\n"
        f"{leaderboard_str if leaderboard_str else '➥ No collectors yet.'}"
    )

    async def _send_check(media):
        return await event.reply(info_text, parse_mode='html', file=media)

    sent = await send_with_char_media(character["char_id"], character["storage_msg_id"], _send_check)
    if sent is None:
        await event.reply(info_text, parse_mode='html')
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
# 🔗 OWNER-MODE GIFT RULES (per owner request)
# ==========================================
#   • BOUND CARDS: a card an owner-mode person (OWNER_ID or an /addowner grantee) gifts arrives in
#     the receiver's harem with "bound": True. The receiver can NOT re-gift it and can NOT list it on
#     the market (see classify_copies / is_bound_entry; remove_one_harem_copy and
#     set_one_harem_copy_status take unbound_only=True so they can never pick a bound copy).
#     Copies the receiver caught or bought themselves are unaffected, even of the same card.
#     Only gifts made AFTER this change are bound — existing harem entries carry no flag.
#   • PAID SUPREME / CATAPHRACT GIFTS: an owner-mode person gifting a Supreme or Cataphract card to
#     somebody must pay the card's /setvalue worth in grams (the top of its range; Supreme = its
#     event's value) — the gift prompt asks with a "💳 Pay N g & Gift" button. The grams go to
#     OWNER_ID. OWNER_ID itself is exempt unless LIMITED_GIFT_FEE_OWNER_EXEMPT is set to False.
OWNER_GIFT_BOUND = True
LIMITED_GIFT_FEE_OWNER_EXEMPT = True   # False = OWNER_ID pays too
LIMITED_GIFT_FEE_TO_OWNER = True       # False = the fee is simply burned

def is_owner_mode(user_id):
    return user_id == OWNER_ID or user_id in added_owner_ids

def is_bound_entry(entry):
    return isinstance(entry, dict) and entry.get("bound") is True

def classify_copies(harem, char_id):
    """(first copy that may be gifted, number of copies that are bound). A listed (market) copy never counts."""
    tradable, bound = None, 0
    for x in (harem or []):
        if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") != "market":
            if is_bound_entry(x):
                bound += 1
            elif tradable is None:
                tradable = x
    return tradable, bound

def gifted_harem_entry(char_id, rarity, sender_id):
    """The harem entry a gift receiver gets — bound when the sender is an owner-mode person."""
    entry = {"char_id": char_id, "caught_date": time.time(), "rarity": rarity, "status": "vault"}
    if OWNER_GIFT_BOUND and is_owner_mode(sender_id):
        entry["bound"] = True
        entry["gifted_by"] = sender_id
    return entry

def limited_gift_fee_applies(sender_id, tier):
    if not (is_owner_mode(sender_id) and is_limited_tier(tier)):
        return False
    return not (sender_id == OWNER_ID and LIMITED_GIFT_FEE_OWNER_EXEMPT)

async def limited_gift_price(tier, event_name):
    """Grams an owner-mode gifter pays: the TOP of the card's /setvalue worth range (Supreme: its event's value)."""
    worth = await _card_worth_grams(tier, event_name)
    return int(worth[1]) if worth else 0

# ==========================================
# 🎁 GIFT (fixed)
# ==========================================
ADDED_OWNER_GIFT_LIMIT_PER_CARD = 3  # /addowner grantees: like OWNER_ID, can gift ANY
# character with no real catch needed — max N times per card, tracked per (user, char_id).
# card can be gifted before it's exhausted — see gift_asset_handler/gift_callback_handler.

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]gift(?:@\w+)?\s+(.+)$', 'bot1')))
async def gift_asset_handler(event):
    if not event.is_reply:
        return await event.reply("Hey — reply to whoever you want to send her to first, okay?", parse_mode='html')

    char_id = normalize_char_id_input(event.pattern_match.group(1))
    sender_id = event.sender_id
    reply_msg = await event.get_reply_message()
    receiver_id = reply_msg.sender_id

    if sender_id == receiver_id:
        return await event.reply("Ah, that's you, silly. Pick someone else~", parse_mode='html')

    char_data = await characters_base_col.find_one({"char_id": char_id})
    if not char_data:
        return await event.reply("Hmm, I can't find that one.", parse_mode='html')

    # 💠 CHANGED (per owner request): CNFT used to be enforced as one-of-one — a card already
    # held by someone got called out and transferred away on re-gift. That's removed now: CNFT
    # behaves exactly like any other card for gifting purposes (the SAME ownership check right
    # below already covers it — OWNER_ID/added_owner_ids gift from an unlimited vault, anyone
    # else needs it in their own harem). The only thing that still makes CNFT different from a
    # regular card is that it's spawnable=False (never a random spawn — /addspecial or
    # checksync are the only ways one enters circulation). See CNFT_TIERS' comment near its
    # definition, updated to match.

    # Ownership check
    if sender_id == OWNER_ID:
        pass  # 👑 Unlimited vault
    elif sender_id in added_owner_ids:
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        gift_count_used = ((sender_doc or {}).get("added_owner_gift_count") or {}).get(char_id, 0)
        if gift_count_used >= ADDED_OWNER_GIFT_LIMIT_PER_CARD:
            return await event.reply(
                f"You've already sent her the max {ADDED_OWNER_GIFT_LIMIT_PER_CARD} times. That's enough, yeah?",
                parse_mode='html'
            )
    else:
        sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
        sender_harem = sender_doc.get("harem", []) if sender_doc else []
        char_item, _bound_n = classify_copies(sender_harem, char_id)
        if not char_item:
            if _bound_n:
                return await event.reply(
                    "🔒 ဒီကတ်ကို Owner ဆီက gift ရထားတာမို့ တခြားသူကို ပြန်ပေးလို့မရပါ။", parse_mode='html')
            return await event.reply(f"Hey, she's not yours to give away~", parse_mode='html')

    # 🔒 Limited rarity: the receiver may hold at most LIMITED_PER_USER_CAP copies of this card.
    _rdoc = await users_catcher_col.find_one({"user_id": receiver_id}, {"harem": 1})
    if not can_receive_limited((_rdoc or {}).get("harem"), char_id, _doc_tier(char_data)):
        return await event.reply(
            f"🔒 သူ့မှာ ဒီကတ်ကို {LIMITED_PER_USER_CAP} ကတ် ရှိပြီးသားမို့ ထပ်ပေးလို့မရပါ။ "
            f"(Supreme / Cataphract ကို gift နဲ့ {LIMITED_PER_USER_CAP} ကတ်ထက်ပိုမပေးနိုင်ပါ)",
            parse_mode='html')

    r_mention = await get_html_mention(event, receiver_id)

    # 💳 Owner-mode person gifting a Supreme / Cataphract card: the card's /setvalue worth (in grams)
    # has to be paid first — asked right here, with a pay button instead of the plain "Yeah".
    _gift_tier = _doc_tier(char_data)
    fee_price = 0
    yes_label = "✅ Yeah"
    fee_text = ""
    if limited_gift_fee_applies(sender_id, _gift_tier):
        fee_price = await limited_gift_price(_gift_tier, char_data.get("event"))
    if fee_price > 0:
        _worth = await _card_worth_grams(_gift_tier, char_data.get("event"))
        _sdoc = await users_catcher_col.find_one({"user_id": sender_id}, {"gram_balance": 1}) or {}
        _bal = int(_sdoc.get("gram_balance", 0))
        if _bal < fee_price:
            return await event.reply(
                f"💳 <b>{escape_html(char_data['name'])}</b> က {RARITY_DISPLAY_NAME.get(_gift_tier, _gift_tier)} ကတ်မို့ "
                f"gift လုပ်ဖို့ setvalue <code>{fee_price:,}</code> g ပေးရပါမယ်။\n"
                f"သင့်မှာ <code>{_bal:,}</code> g ပဲရှိပါတယ် — /exchange နဲ့ ccm ကို gram ပြောင်းပါ။",
                parse_mode='html')
        yes_label = f"💳 Pay {fee_price:,} g & Gift"
        fee_text = (
            f"\n\n{format_worth_line(*_worth) if _worth else ''}\n"
            f"💳 Gift လုပ်ဖို့ <b>{fee_price:,} g</b> ပေးရပါမယ် (သင့်မှာ <code>{_bal:,}</code> g)။"
        )
    owner_note = "\n🔗 <i>Owner gift — လက်ခံသူက ဒီကတ်ကို ရောင်းလို့/ပြန်ပေးလို့ မရပါ။</i>" if (OWNER_GIFT_BOUND and is_owner_mode(sender_id)) else ""

    # 🎀 Reze voice confirm design
    confirm_text = (
        f"Sending {escape_html(char_data['name'])} to {r_mention}? Just say the word~"
        f"{fee_text}{owner_note}"
    )

    # ✅ မှန်ကန်တဲ့ Button Data
    buttons = [
        [
            Button.inline(yes_label, data=f"gift_confirm_{sender_id}_{receiver_id}_{char_id}"),
            Button.inline("❌ Nope", data=f"gift_cancel_{sender_id}_{receiver_id}_{char_id}")
        ]
    ]

    async def _send_gift_confirm(media):
        return await event.reply(confirm_text, file=media, buttons=buttons, parse_mode='html')

    # 🩹 FIX ("caption cut off" bug — same class as /harem's "Message was too long" crash and
    # /profile's caption fix): a message sent WITH a photo has its text bound by Telegram's
    # 1024-UTF-16-unit CAPTION limit, not the normal 4096-char message limit. A long character
    # name/category, or an unusually long recipient display name inside r_mention, can push
    # confirm_text past that and get the caption cut off (or rejected) by Telegram. Checking
    # first with utf16_len (plain len() undercounts emoji/astral characters — see utf16_len's
    # own docstring) and skipping straight to the photo-less reply when it won't safely fit
    # avoids ever risking that, instead of only reacting to it after the fact.
    CAPTION_SAFE_LIMIT = 1024
    # ✅ Media ပြဿနာရှိရင်တောင် Button ပါတဲ့ Message ပို့ပေးမယ်
    try:
        if utf16_len(confirm_text) <= CAPTION_SAFE_LIMIT:
            sent = await send_with_char_media(char_data["char_id"], char_data["storage_msg_id"], _send_gift_confirm)
            if sent is None:
                await event.reply(confirm_text, buttons=buttons, parse_mode='html')
        else:
            await event.reply(confirm_text, buttons=buttons, parse_mode='html')
    except Exception as e:
        print(f"Gift media error: {e}")
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
        return await event.answer("That's not yours to tap, sweetheart~", alert=True)
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)

    if action == "cancel":
        # 🩹 FIX (per owner report): owner/added-owner .gift confirms were leaving the button
        # spinning forever with no reply at all — Telethon does NOT auto-answer a callback
        # when the handler raises, so any unhandled exception here (a slow/failed Mongo call,
        # or event.edit choking on an unexpected '<'/'>' in a rarity/name field under
        # parse_mode='html') skipped event.answer() entirely. Wrapping in try/except ensures
        # the spinner always closes and the error gets reported either way.
        try:
            await event.edit("Ah, changed your mind? No worries.\nKeeping her with you then~", parse_mode='html', buttons=None)
            await event.answer("Cancelled~", alert=True)
        except Exception as e:
            await report_system_error("gift_callback_handler (cancel)", f"{e}\nData: {event.data}")
            try:
                await event.answer("Hmm, something didn't work.", alert=True)
            except Exception:
                pass
        return

    # confirm — see the FIX note above the cancel branch; same reasoning applies here, and
    # this is the path the owner-mode report was actually about.
    # 💳 fee_state: grams taken for a Supreme/Cataphract owner-mode gift. Refunded by the `finally`
    # at the end of this handler if the gift didn't actually reach the receiver (any early return or error).
    fee_state = {"paid": 0, "committed": False}
    try:
        # 🔒 Limited rarity: re-check at tap time (the receiver may have gotten one meanwhile),
        # BEFORE anything is taken from the sender.
        _cdoc = await characters_base_col.find_one({"char_id": char_id}, {"rarity": 1, "rarity_tier": 1, "event": 1})
        if _cdoc:
            _rdoc = await users_catcher_col.find_one({"user_id": receiver_id}, {"harem": 1})
            if not can_receive_limited((_rdoc or {}).get("harem"), char_id, _doc_tier(_cdoc)):
                await event.edit(f"🔒 သူ့မှာ ဒီကတ်ကို {LIMITED_PER_USER_CAP} ကတ် ရှိပြီးသားမို့ ထပ်ပေးလို့မရပါ။", parse_mode='html', buttons=None)
                return await event.answer("Receiver is at the card limit.", alert=True)
        # 💳 Owner-mode Supreme/Cataphract gift: pay the card's setvalue first (atomic; refunded in `finally` on failure)
        if _cdoc and limited_gift_fee_applies(sender_id, _doc_tier(_cdoc)):
            _price = await limited_gift_price(_doc_tier(_cdoc), _cdoc.get("event"))
            if _price > 0:
                if not await try_deduct_gram(sender_id, _price):
                    await event.edit(f"❌ gram မလောက်ပါ — gift လုပ်ဖို့ <code>{_price:,}</code> g လိုပါတယ်။", parse_mode='html', buttons=None)
                    return await event.answer("Not enough gram.", alert=True)
                fee_state["paid"] = _price
        if sender_id == OWNER_ID:
            # 👑 Unlimited vault: nothing to remove — this card stays available for every future
            # gift too. Rarity comes straight from the character record instead of a harem item
            # (the owner may never have actually caught this one for real). Gift stats are still
            # tracked for visibility, they just don't touch the owner's real harem array.
            char_data = await characters_base_col.find_one({"char_id": char_id})
            if not char_data:
                await event.edit("Ah — she's not there anymore.", parse_mode='html', buttons=None)
                await event.answer("Can't find her~", alert=True)
                return
            char_rarity = char_data.get("rarity", "Unknown")
            gift_tier = classify_rarity(char_rarity)
            # 💠 CHANGED (per owner request): CNFT is no longer one-of-one — it's never removed
            # from a "prior holder" anymore, same as any other card the owner gifts from the
            # unlimited vault.
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
                await event.edit("Ah — she's not there anymore.", parse_mode='html', buttons=None)
                await event.answer("Can't find her~", alert=True)
                return
            sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
            gift_count_used = ((sender_doc or {}).get("added_owner_gift_count") or {}).get(char_id, 0)
            if gift_count_used >= ADDED_OWNER_GIFT_LIMIT_PER_CARD:
                await event.edit(
                    f"You've already sent her the max {ADDED_OWNER_GIFT_LIMIT_PER_CARD} times. That's enough, yeah?",
                    parse_mode='html',
                    buttons=None
                )
                await event.answer("That's enough for now~", alert=True)
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
            char_item, _bound_n = classify_copies(sender_harem, char_id)
            if not char_item:
                await event.edit(
                    "🔒 ဒီကတ်ကို Owner ဆီက gift ရထားတာမို့ ပြန်ပေးလို့မရပါ။" if _bound_n else "Ah — she's not there anymore.",
                    parse_mode='html', buttons=None)
                await event.answer("Can't find her~", alert=True)
                return
            # 🩹 FIX: atomic $pull-based removal (see remove_one_harem_copy) instead of the old
            # find_one → sender_harem.remove() → $set the whole array back — same lost-update
            # race risk as marketplace/trade/sell fixed earlier.
            char_rarity = char_item.get("rarity", "Unknown")
            gift_tier = char_item.get("rarity_tier") or classify_rarity(char_rarity)
            await remove_one_harem_copy(sender_id, char_id, char_item.get("status", "vault"), unbound_only=True)
            await users_catcher_col.update_one(
                {"user_id": sender_id},
                {"$inc": {"total_gifted": 1, f"gifted_by_rarity.{gift_tier}": 1}}
            )
            sender_doc_after = await users_catcher_col.find_one({"user_id": sender_id}, {"harem": 1})
            await clear_stale_favorite(sender_id, char_id, (sender_doc_after or {}).get("harem", []))

        r_plain_name = await get_plain_name(event, receiver_id)
        await users_catcher_col.update_one(
            {"user_id": receiver_id},
            {
                "$push": {"harem": gifted_harem_entry(char_id, char_rarity, sender_id)},
                "$inc": {"total_caught": 1, "total_gift_received": 1},
                "$set": {"fullname": r_plain_name}
            },
            upsert=True
        )
        fee_state["committed"] = True   # the card is in the receiver's harem — the fee stays paid
        if fee_state["paid"]:
            try:
                if LIMITED_GIFT_FEE_TO_OWNER and sender_id != OWNER_ID:
                    await users_catcher_col.update_one({"user_id": OWNER_ID}, {"$inc": {"gram_balance": fee_state["paid"]}}, upsert=True)
                await gram_transfers_col.insert_one({"from": sender_id, "to": OWNER_ID if LIMITED_GIFT_FEE_TO_OWNER else None,
                                                     "grams": fee_state["paid"], "reason": "limited_gift", "char_id": char_id,
                                                     "receiver": receiver_id, "ts": time.time()})
            except Exception as e:
                await report_system_error("gift fee credit/log", f"{e} (sender {sender_id} paid {fee_state['paid']} g for {char_id})")
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

        # 🎨 A designed confirmation where the gift happened.
        char_doc = await characters_base_col.find_one({"char_id": char_id})
        char_name_display = escape_html(char_doc.get("name", "?")) if char_doc else char_id

        # 🎀 Reze voice success design
        success_text = f"{char_name_display} is theirs now. Take care of her, yeah?~"
        if fee_state["paid"]:
            success_text += f"\n💳 −{fee_state['paid']:,} g"
        # 🩹 Kept the caption-length guard below even though this shorter line will practically
        # never hit the 1024-UTF-16-unit media-caption cap on its own — see the FIX note there
        # for why a media message's edit text is capped lower than a normal message's 4096.
        CAPTION_SAFE_LIMIT = 1024
        if utf16_len(success_text) <= CAPTION_SAFE_LIMIT:
            await event.edit(success_text, parse_mode='html', buttons=None)
        else:
            try:
                await event.edit("Sent~ (details below ⬇️)", parse_mode='html', buttons=None)
            except Exception:
                pass
            await event.respond(success_text, parse_mode='html')
        await event.answer("Sent~", alert=True)
        # 🩹 CHANGED (per owner request): a DM to the receiver used to be sent here too — removed,
        # the in-chat confirmation above is enough now.
    except Exception as e:
        # ❌ See the FIX note above: this is what actually closes the spinner and tells the
        # owner + the user something broke, instead of the tap just going nowhere.
        await report_system_error("gift_callback_handler (confirm)", f"{e}\nData: {event.data}")
        try:
            await event.edit(
                "Hmm, something didn't work. Try again in a sec?",
                parse_mode='html',
                buttons=None
            )
            await event.answer("Hmm, something didn't work.", alert=True)
        except Exception:
            pass
    finally:
        if fee_state["paid"] and not fee_state["committed"]:
            try:   # the gift didn't go through — give the grams back
                await refund_gram(sender_id, fee_state["paid"])
            except Exception as _e:
                await report_system_error("gift fee REFUND FAILED", f"sender {sender_id} is owed {fee_state['paid']} g: {_e}")

# ==========================================
# 🔗 /bindgifts — make OLD owner-mode gifts bound too (per owner request)
# ==========================================
# Gifts made before the bound rule existed carry no "bound" flag. This walks gift_history (every
# /gift logs sender, receiver, char_id and a timestamp) for gifts sent by the owner, the current
# /addowner grantees and any user ids you add to the command (e.g. someone you already ran
# /removeowner on), and flags the matching card in the receiver's harem as bound: it then can't be
# sold or re-gifted — exactly like a new owner gift. A history row is matched to the receiver's
# harem entry for that card that was created within BIND_MATCH_TOLERANCE_SECONDS of the gift, has no
# chat_id (it wasn't caught) and isn't bound yet. Gifts the receiver no longer holds (re-gifted, sold,
# removed) are simply reported as "gone". /bindgifts shows a preview first; the ✅ button applies it.
# Safe to run again any time — already-bound cards are skipped.
BIND_MATCH_TOLERANCE_SECONDS = 120

def plan_gift_bindings(history_rows, harem_by_user, tolerance=BIND_MATCH_TOLERANCE_SECONDS):
    """Pure. Returns (bindings, stats): bindings = [(receiver_id, char_id, caught_date, sender_id)]."""
    stats = {"rows": 0, "matched": 0, "already_bound": 0, "gone": 0, "by_sender": {}, "by_receiver": {}}
    bindings, used = [], set()
    for row in sorted(history_rows, key=lambda r: r.get("timestamp") or 0):
        rid, cid, ts, sid = row.get("receiver_id"), row.get("char_id"), row.get("timestamp"), row.get("sender_id")
        if not (rid and cid and isinstance(ts, (int, float))):
            continue
        stats["rows"] += 1
        best, best_gap, bound_near = None, None, False
        for e in (harem_by_user.get(rid) or []):
            if not (isinstance(e, dict) and e.get("char_id") == cid and e.get("chat_id") is None):
                continue
            cd = e.get("caught_date")
            if not isinstance(cd, (int, float)) or abs(cd - ts) > tolerance:
                continue
            if is_bound_entry(e):
                bound_near = True
            elif (rid, id(e)) not in used and (best is None or abs(cd - ts) < best_gap):
                best, best_gap = e, abs(cd - ts)
        if best is not None:
            used.add((rid, id(best)))
            bindings.append((rid, cid, best["caught_date"], sid))
            stats["matched"] += 1
            stats["by_sender"][sid] = stats["by_sender"].get(sid, 0) + 1
            stats["by_receiver"][rid] = stats["by_receiver"].get(rid, 0) + 1
        elif bound_near:
            stats["already_bound"] += 1
        else:
            stats["gone"] += 1
    return bindings, stats

def _bindgifts_senders(extra_ids):
    return sorted({OWNER_ID, *added_owner_ids, *extra_ids})

async def _compute_gift_bindings(senders):
    rows = await gift_history_col.find(
        {"sender_id": {"$in": senders}}, {"sender_id": 1, "receiver_id": 1, "char_id": 1, "timestamp": 1}
    ).to_list(length=None)
    receivers = sorted({r["receiver_id"] for r in rows if r.get("receiver_id")})
    harem_by_user = {}
    for i in range(0, len(receivers), 200):
        async for d in users_catcher_col.find({"user_id": {"$in": receivers[i:i + 200]}}, {"user_id": 1, "harem": 1}):
            harem_by_user[d["user_id"]] = d.get("harem") or []
    return plan_gift_bindings(rows, harem_by_user)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]bindgifts(?:@\w+)?((?:\s+\d{5,15}){0,3})$', 'bot1')))
async def bindgifts_command(event):
    """/bindgifts [extra sender ids]  — preview; the button applies it."""
    if event.sender_id != OWNER_ID:
        return
    extra = [int(x) for x in event.pattern_match.group(1).split()]
    senders = _bindgifts_senders(extra)
    bindings, st = await _compute_gift_bindings(senders)
    lines = [
        "🔗 <b>Bind old owner gifts</b>",
        f"• senders checked: <code>{len(senders)}</code> (owner + added owners" + (f" + {len(extra)} id(s) you gave" if extra else "") + ")",
        f"• gifts in history: <code>{st['rows']}</code>",
        f"• <b>to bind now: <code>{st['matched']}</code></b> card(s) at <code>{len(st['by_receiver'])}</code> user(s)",
        f"• already bound: <code>{st['already_bound']}</code> · no longer held (re-gifted / sold / removed): <code>{st['gone']}</code>",
    ]
    if st["by_sender"]:
        lines.append("• by sender: " + ", ".join(f"<code>{s}</code> ×{n}" for s, n in sorted(st["by_sender"].items(), key=lambda x: -x[1])[:6]))
    if not bindings:
        return await event.reply("\n".join(lines) + "\n\n✅ Nothing to bind.", parse_mode='html')
    data = "bindgifts_go" + "".join(f"_{i}" for i in extra)
    await event.reply("\n".join(lines) + "\n\n<i>Bound cards can't be sold or re-gifted by their holder.</i>",
                      parse_mode='html', buttons=[[Button.inline(f"✅ Bind {st['matched']} cards", data=data),
                                                   Button.inline("❌ Cancel", data="bindgifts_skip")]])

@bot1.on(events.CallbackQuery(pattern=r'^bindgifts_(go|skip)(?:_\d+)*$'))
async def bindgifts_callback(event):
    if event.sender_id != OWNER_ID:
        return await event.answer("Owner only.", alert=True)
    raw = event.data.decode("utf-8") if isinstance(event.data, bytes) else str(event.data)
    parts = raw.split("_")
    if not claim_single_tap(event):
        return await event.answer("One sec~", alert=False)
    if parts[1] == "skip":
        await event.edit("❎ Nothing changed.", buttons=None)
        return await event.answer("OK")
    await event.answer("Working…")
    try:
        extra = [int(x) for x in parts[2:]]
        bindings, st = await _compute_gift_bindings(_bindgifts_senders(extra))   # recomputed fresh at tap time
        done = skipped = 0
        for rid, cid, cd, sid in bindings:
            res = await users_catcher_col.update_one(
                {"user_id": rid, "harem": {"$elemMatch": {"char_id": cid, "caught_date": cd,
                                                          "bound": {"$ne": True}, "chat_id": {"$exists": False}}}},
                {"$set": {"harem.$.bound": True, "harem.$.gifted_by": sid}})
            if res.modified_count:
                done += 1
            else:
                skipped += 1
        await event.edit(f"✅ <b>Bound {done} card(s)</b> from old owner gifts"
                         + (f" · {skipped} changed meanwhile (run /bindgifts again)" if skipped else "") + ".",
                         parse_mode='html', buttons=None)
    except Exception as e:
        await report_system_error("bindgifts_callback", str(e))
        await event.edit(f"❌ Failed: <code>{escape_html(str(e)[:200])}</code>", parse_mode='html', buttons=None)

# ==========================================
# 🛒 PVP MARKET — player-to-player character auctions, built on the SAME atomic primitives
# /gift and /giftccm already use (try_deduct_ccm, remove_one_harem_copy) so it doesn't repeat
# the lost-update race the OLD marketplace/trade system had (see remove_one_harem_copy's own
# docstring — that fix was written specifically because of bugs in the marketplace this
# replaces). "market" is also the SAME harem-item status /gift and /fuck-checks already know
# to skip — nothing about those needs to change for a listed card to be untouchable elsewhere.
#
# Escrow model (why): a bidder's ccm is deducted the MOMENT their bid becomes the new highest
# — not held-but-spendable, not charged only at the end. Being outbid refunds it immediately.
# This is the standard auction pattern (eBay etc.) and, more importantly here, it's what stops
# "bid huge, then spend the ccm elsewhere before the auction ends" from being a viable way to
# win an auction for free — a real risk with a charge-at-settlement design.
#
# 💰 Sale fee (per owner request): MARKET_FEE_PERCENT of every sold auction's final price goes
# straight to OWNER_ID's ccm balance — not burned. See _settle_market_listing.
#
# 🚦 Separate group-membership gate (per owner request): using ANY part of the market requires
# being a member of MARKET_FORCE_SUB_CHAT_ID — checked independently of, and in addition to,
# the site-wide FORCE_SUB_CHAT_ID gate above (a different group). Since that gate only covers
# slash-commands matched by raw text, and half of the market's surface is inline buttons,
# _market_require_group_member() is called explicitly at the top of every command AND every
# callback handler below, rather than being added to FORCE_SUB_GATED_COMMANDS.
# ⚠️ SETUP REQUIRED: bot1 must already be a member of that group for get_permissions() to be
# able to check anyone else's membership there — same real-world requirement the existing
# FORCE_SUB_CHAT_ID gate already has.
#
# Assumptions / tunable constants below (duration, fee %, bid increments, listing cap) are a
# first pass — easy single-line edits, not load-bearing architecture.
# ==========================================
MARKET_LISTING_DURATION_SECONDS = 24 * 3600  # how long a new listing stays open
MARKET_MIN_STARTING_PRICE = 50               # floor for /sell's starting price
MARKET_FEE_PERCENT = 10                      # 💰 taken off the final price, credited to OWNER_ID
MARKET_MAX_ACTIVE_LISTINGS_PER_USER = 5      # per seller, at once — keeps one person from flooding the board
MARKET_EXPIRY_CHECK_INTERVAL = 30            # seconds between market_auction_expiry_scheduler sweeps
MARKET_BROWSE_PAGE_SIZE = 5
MARKET_BID_CONVERSATION_TIMEOUT = 120
MARKET_FORCE_SUB_INVITE_LINK = "https://t.me/+QdhGvV5-rOs4NGY9"  # shown on the "Join" button only
MARKET_FORCE_SUB_CHAT_ID = -1003967256441  # 🚦 the actual group checked for membership — given directly by the owner

# 💰 Minimum ccm a new bid must clear over the current one — scales with rarity (per owner
# request: "the higher the rarity, the bigger the required bid jump should be"), instead of a
# single flat number for every character. Falls back to MARKET_DEFAULT_BID_INCREMENT for any
# tier not listed here (OTHER, or a future tier added to RARITY_TIERS later).
MARKET_BID_INCREMENT_BY_TIER = {
    "COMMON": 50, "UNCOMMON": 75, "RARE": 100, "LEGENDARY": 150, "MYSTICAL": 250,
    "DIVINE": 400, "CROSSVERSE": 600, "CATAPHRACT": 900, "SUPREME": 1500,
    "CNFT A": 250, "CNFT S": 400, "CNFT SS": 600,
}
MARKET_DEFAULT_BID_INCREMENT = 50

market_listings_col = db["market_listings"]  # one doc per auction — see market_auction_expiry_scheduler for the status lifecycle
market_history_col = db["market_history"]    # completed-sale log, same shape/spirit as gift_history_col

def _market_time_left(ends_at):
    secs = max(0, int(ends_at - time.time()))
    if secs <= 0: return "ending…"
    if secs < 60: return f"{secs}s"
    if secs < 3600: return f"{secs // 60}m"
    if secs < 86400: return f"{secs // 3600}h {(secs % 3600) // 60}m"
    return f"{secs // 86400}d {(secs % 86400) // 3600}h"

def _market_bid_increment(rarity_tier):
    return MARKET_BID_INCREMENT_BY_TIER.get(rarity_tier, MARKET_DEFAULT_BID_INCREMENT)

def _market_min_next_bid(listing):
    tier = listing.get("rarity_tier") or classify_rarity(listing.get("rarity"))
    increment = _market_bid_increment(tier)
    if listing.get("current_bid", 0) > 0:
        return listing["current_bid"] + increment
    return listing["starting_price"]

async def _market_mention_for(user_id):
    """Clickable tg://user?id= mention built straight from stored profile data — for
    background-scheduler notifications (sold/outbid DMs) where there's no live message event
    to derive a mention from the way get_html_mention does. Same clean_display_name +
    tg://user?id= shape render_trivia_leaderboard_page already uses, for the same reason."""
    doc = await users_catcher_col.find_one({"user_id": user_id}, {"fullname": 1})
    uname = escape_html(clean_display_name((doc or {}).get("fullname"), fallback=f"Agent {user_id}"))
    return f"<a href='tg://user?id={user_id}'>{uname}</a>"

async def is_market_force_sub_member(user_id):
    """🩹 Same fix as is_force_sub_member above — only a confirmed UserNotParticipantError
    counts as not-a-member; any other error fails open instead of wrongly caching a real
    member as blocked."""
    now = time.time()
    cached = market_force_sub_membership_cache.get(user_id)
    if cached and now < cached[1]:
        return cached[0]
    try:
        perms = await bot1.get_permissions(MARKET_FORCE_SUB_CHAT_ID, user_id)
        is_member = perms is not None
    except errors.UserNotParticipantError:
        is_member = False
    except Exception as e:
        print(f"⚠️ is_market_force_sub_member: couldn't verify {user_id}, failing open ({e})")
        return cached[0] if cached else True
    market_force_sub_membership_cache[user_id] = (is_member, now + FORCE_SUB_MEMBERSHIP_TTL)
    return is_member

async def _market_require_group_member(event) -> bool:
    """Gate for every Buy & Sell entry point. True = allowed to proceed. False = the
    join-prompt has already been sent (an alert for a callback tap, since alerts can't hold
    buttons, plus a real message with a Join button either way) — call sites just `return`."""
    user_id = event.sender_id
    if user_id == OWNER_ID:
        return True
    if await is_market_force_sub_member(user_id):
        return True
    text = (
        "🛒 <b>Join our market group first!</b>\n"
        "You need to be a member there to buy or sell in the market.\n"
        "Tap below to join, then try again."
    )
    buttons = [[Button.url("Join Market Group", MARKET_FORCE_SUB_INVITE_LINK)]]
    if isinstance(event, events.CallbackQuery.Event):
        try:
            await event.answer("🚫 Join the market group first!", alert=True)
        except Exception:
            pass
        try:
            await event.respond(text, parse_mode='html', buttons=buttons)
        except Exception:
            pass
    else:
        try:
            await event.reply(text, parse_mode='html', buttons=buttons)
        except Exception:
            pass
    return False

async def set_one_harem_copy_status(user_id, char_id, from_status, to_status, unbound_only=False):
    """Atomically flips exactly ONE harem copy matching (char_id, from_status) to to_status —
    same positional-$ pattern as remove_one_harem_copy (find the one matching array slot,
    change just that slot), so this carries the exact same atomicity guarantee: no
    find-modify-write-the-whole-array round trip, nothing else touching this user's harem in
    the gap can get silently overwritten. Returns True if a copy was actually flipped, False
    if none matched (already sold/gifted/moved by something else — call sites treat that as
    "this listing/action no longer applies", not as an error to retry)."""
    match = {"char_id": char_id, "status": from_status}
    if unbound_only:
        match["bound"] = {"$ne": True}
    result = await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": match}},
        {"$set": {"harem.$.status": to_status}}
    )
    return result.modified_count > 0

async def _market_listing_card_text(listing, char_data=None):
    char_data = char_data or await characters_base_col.find_one({"char_id": listing["char_id"]})
    name = escape_html(char_data["name"]) if char_data else listing.get("char_id", "?")
    rarity_display = strip_rarity_number(listing.get("rarity", "Unknown"))
    tier = listing.get("rarity_tier") or classify_rarity(listing.get("rarity"))
    emoji = RARITY_EMOJI.get(tier, RARITY_DEFAULT_EMOJI)
    seller_mention = await _market_mention_for(listing['seller_id'])
    bid_line = (
        f"💰 <b>Current bid:</b> <code>{listing['current_bid']:,}</code> ccm"
        if listing.get("current_bid", 0) > 0
        else f"💰 <b>Starting price:</b> <code>{listing['starting_price']:,}</code> ccm"
    )
    return (
        f"🛒 <b>{name}</b> | 🐧 {display_char_id(listing['char_id'])}\n"
        f"{emoji} {RARITY_LABEL_STYLED}: {rarity_display}\n"
        f"{bid_line}\n"
        f"⏱ <b>Ends in:</b> {_market_time_left(listing['ends_at'])}\n"
        f"📤 <b>Seller:</b> {seller_mention}"
    )

# ---- Market menu — reached via the 🛒 Buy & Sell button under a successful /fuck, or /market ----
async def _send_market_menu(event, user_id, edit=False):
    active_count = await market_listings_col.count_documents({"seller_id": user_id, "status": "active"})
    text = (
        f"🛒 <b>The Market</b>\n\n"
        f"Auction your characters for 💰 ccm, or bid on what others are selling.\n"
        f"<i>Your active listings: {active_count}/{MARKET_MAX_ACTIVE_LISTINGS_PER_USER}</i>\n\n"
        f"➕ <b>To sell:</b> <code>/sell [id] [starting price]</code>"
    )
    buttons = [
        [Button.inline("📋 Browse Auctions", data="mkt_page_0")],
        [Button.inline("💰 My Listings", data="mkt_mine_0")],
        [Button.switch_inline("📦 my harem", query=f"harem.{user_id}", same_peer=True)],
    ]
    if edit:
        try:
            await event.edit(text, parse_mode='html', buttons=buttons)
            return
        except errors.MessageNotModifiedError:
            return
    await event.reply(text, parse_mode='html', buttons=buttons)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]market(?:@\w+)?$', 'bot1')))
async def market_menu_command(event):
    if not await _market_require_group_member(event):
        return
    await _send_market_menu(event, event.sender_id)

@bot1.on(events.CallbackQuery(pattern=r'^mkt_menu_(\d+)$'))
async def market_menu_from_catch_callback(event):
    """The 🛒 Buy & Sell button under a fresh catch. 🩹 CHANGED (per owner request): ANYONE in the group can tap
    it, not just the catcher — it opens the market menu for WHOEVER tapped (their own listings / harem), so the
    number in the callback data (the catcher's id) is no longer checked; it's only kept so old buttons and the
    /harem 🛍 Market button keep working."""
    if not await _market_require_group_member(event):
        return
    await event.answer()
    await _send_market_menu(event, event.sender_id)

@bot1.on(events.CallbackQuery(pattern=r'^mkt_menu$'))
async def market_menu_back_callback(event):
    if not await _market_require_group_member(event):
        return
    await event.answer()
    await _send_market_menu(event, event.sender_id, edit=True)

# ---- Browse active auctions, paginated ----
async def _render_market_browse_page(page):
    total = await market_listings_col.count_documents({"status": "active"})
    listings = await market_listings_col.find({"status": "active"}).sort("ends_at", 1) \
        .skip(page * MARKET_BROWSE_PAGE_SIZE).limit(MARKET_BROWSE_PAGE_SIZE).to_list(length=MARKET_BROWSE_PAGE_SIZE)
    if not listings:
        text = "📋 <b>Active Auctions</b>\n\n😶 <i>Nothing listed right now — be the first with /sell!</i>" if page == 0 \
            else "<i>No more listings.</i>"
        buttons = [[Button.inline("🔙 Back", data="mkt_menu")]]
        return text, buttons
    lines = [f"📋 <b>Active Auctions</b> ({total} total)\n"]
    rows = []
    for listing in listings:
        char_data = await characters_base_col.find_one({"char_id": listing["char_id"]}, {"name": 1})
        name = char_data["name"] if char_data else listing["char_id"]
        price = listing["current_bid"] if listing.get("current_bid", 0) > 0 else listing["starting_price"]
        label = f"{name} — {price:,}💰 ({_market_time_left(listing['ends_at'])})"
        rows.append([Button.inline(label[:60], data=f"mkt_view_{listing['_id']}")])
    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Previous", data=f"mkt_page_{page - 1}"))
    if (page + 1) * MARKET_BROWSE_PAGE_SIZE < total:
        nav_row.append(Button.inline("Next ▶", data=f"mkt_page_{page + 1}"))
    buttons = rows + ([nav_row] if nav_row else []) + [[Button.inline("🔙 Back", data="mkt_menu")]]
    return "\n".join(lines), buttons

@bot1.on(events.CallbackQuery(pattern=r'^mkt_page_(\d+)$'))
async def market_browse_page_callback(event):
    if not await _market_require_group_member(event):
        return
    page = int(event.pattern_match.group(1))
    text, buttons = await _render_market_browse_page(page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

# ---- Listing detail + bid entry point ----
async def _render_market_detail(listing_id, viewer_id):
    try:
        listing = await market_listings_col.find_one({"_id": ObjectId(listing_id)})
    except Exception:
        listing = None
    if not listing or listing.get("status") != "active":
        return "❌ <b>This listing is no longer active.</b>", [[Button.inline("🔙 Back", data="mkt_page_0")]]
    text = await _market_listing_card_text(listing)
    buttons = []
    if listing["seller_id"] == viewer_id:
        if listing.get("current_bid", 0) == 0:
            buttons.append([Button.inline("❌ Cancel Listing", data=f"mkt_cancel_{listing['_id']}")])
        else:
            text += "\n\n<i>You can't cancel — someone's already bid.</i>"
    else:
        min_next = _market_min_next_bid(listing)
        buttons.append([Button.inline(f"💰 Bid (min {min_next:,})", data=f"mkt_bid_{listing['_id']}")])
    buttons.append([Button.inline("🔙 Back", data="mkt_page_0")])
    return text, buttons

@bot1.on(events.CallbackQuery(pattern=r'^mkt_view_([a-fA-F0-9]{24})$'))
async def market_view_listing_callback(event):
    if not await _market_require_group_member(event):
        return
    listing_id = event.pattern_match.group(1)
    if isinstance(listing_id, bytes):
        listing_id = listing_id.decode('utf-8')
    text, buttons = await _render_market_detail(listing_id, event.sender_id)
    try:
        listing = await market_listings_col.find_one({"_id": ObjectId(listing_id)})
        if listing:
            char_data = await characters_base_col.find_one({"char_id": listing["char_id"]})
            if char_data:
                async def _send_detail(media):
                    return await event.respond(text, file=media, parse_mode='html', buttons=buttons)
                sent = await send_with_char_media(char_data["char_id"], char_data["storage_msg_id"], _send_detail)
                if sent is not None:
                    await event.answer()
                    return
    except Exception as e:
        print(f"market_view_listing_callback media error: {e}")
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
    except errors.MessageNotModifiedError:
        pass
    await event.answer()

# ---- Cancel a listing (seller only, only before any bid) ----
@bot1.on(events.CallbackQuery(pattern=r'^mkt_cancel_([a-fA-F0-9]{24})$'))
async def market_cancel_listing_callback(event):
    if not await _market_require_group_member(event):
        return
    listing_id = event.pattern_match.group(1)
    if isinstance(listing_id, bytes):
        listing_id = listing_id.decode('utf-8')
    if not claim_single_tap(event):
        return await event.answer("⏳ Processing...", alert=False)
    try:
        listing = await market_listings_col.find_one_and_update(
            {"_id": ObjectId(listing_id), "seller_id": event.sender_id, "status": "active", "current_bid": 0},
            {"$set": {"status": "cancelled"}}
        )
        if not listing:
            await event.answer("❌ Can't cancel this — it may already have a bid.", alert=True)
            return
        await set_one_harem_copy_status(event.sender_id, listing["char_id"], "market", "vault")
        await event.edit("🗑️ <b>Listing cancelled.</b> The card is back in your harem.", parse_mode='html', buttons=None)
        await event.answer("Cancelled.")
    except Exception as e:
        await report_system_error("market_cancel_listing_callback", f"{e}\nData: {event.data}")
        await event.answer("❌ Something went wrong!", alert=True)

# ---- Place a bid — conversation-based amount entry ----
@bot1.on(events.CallbackQuery(pattern=r'^mkt_bid_([a-fA-F0-9]{24})$'))
async def market_bid_start_callback(event):
    if not await _market_require_group_member(event):
        return
    listing_id = event.pattern_match.group(1)
    if isinstance(listing_id, bytes):
        listing_id = listing_id.decode('utf-8')
    bidder_id = event.sender_id
    try:
        listing = await market_listings_col.find_one({"_id": ObjectId(listing_id)})
    except Exception:
        listing = None
    if not listing or listing.get("status") != "active":
        return await event.answer("❌ This listing is no longer active.", alert=True)
    if listing["seller_id"] == bidder_id:
        return await event.answer("❌ You can't bid on your own listing.", alert=True)
    # 🔒 Limited rarity: a bidder already at the per-user cap can't win (and so can't bid on) another copy.
    _bdoc = await users_catcher_col.find_one({"user_id": bidder_id}, {"harem": 1})
    if not can_receive_limited((_bdoc or {}).get("harem"), listing["char_id"], listing.get("rarity_tier") or classify_rarity(listing.get("rarity"))):
        return await event.answer(f"🔒 You already hold {LIMITED_PER_USER_CAP} copies of this card (the limit).", alert=True)
    min_next = _market_min_next_bid(listing)
    # 🩹 FIX: same peer-collision risk as market_sellpick_choose_callback (see
    # market_dm_conversation_locks' comment in BotState) — a user bidding on two listings back
    # to back, or bidding while a sell-price prompt is already open with them, would otherwise
    # hit "Cannot open exclusive conversation in a chat that already has one open conversation".
    # Locks are shared across both flows since Telethon keys conversations by peer, not by which
    # feature opened them.
    lock = market_dm_conversation_locks[bidder_id]
    if lock.locked():
        return await event.answer("⏳ You already have a prompt open with me — reply to it (or /cancel it) first.", alert=True)
    await event.answer()
    async with lock:
        try:
            async with bot1.conversation(bidder_id, timeout=MARKET_BID_CONVERSATION_TIMEOUT) as conv:
                await conv.send_message(
                    f"💰 <b>Place your bid</b>\nMinimum: <code>{min_next:,}</code> ccm\n\n"
                    f"Reply with a number, or /cancel.",
                    parse_mode='html'
                )
                resp = await conv.get_response()
                raw = (resp.raw_text or "").strip()
                if raw.lower() == "/cancel":
                    return await conv.send_message("❌ Cancelled.")
                if not raw.isdigit():
                    return await conv.send_message("❌ That's not a number. Run the bid button again to retry.")
                amount = int(raw)
                await _market_place_bid(conv, listing_id, bidder_id, amount)
        except asyncio.TimeoutError:
            try:
                await bot1.send_message(bidder_id, "⌛ <b>Bid timed out.</b> Tap the bid button again to retry.", parse_mode='html')
            except Exception:
                pass
        except errors.PeerIdInvalidError:
            # 🩹 FIX: same "bots cannot start conversations" case as the sell flow — the bidder
            # has never opened a PM with the bot, so it can't send them the first message.
            try:
                start_hint = f"@{BOT1_USERNAME}" if BOT1_USERNAME else "me"
                await event.respond(
                    f"⚠️ <b>I can't message you privately yet.</b>\n"
                    f"Please start a private chat with {start_hint} (send it /start), then tap "
                    f"the bid button again.",
                    parse_mode='html'
                )
            except Exception:
                pass
        except ValueError as e:
            if "exclusive conversation" in str(e).lower():
                try:
                    await event.respond("⏳ You already have a prompt open with me — reply to it first.", parse_mode='html')
                except Exception:
                    pass
            else:
                await report_system_error("market_bid_start_callback", f"{e}")
        except Exception as e:
            await report_system_error("market_bid_start_callback", f"{e}")

async def _market_place_bid(conv, listing_id, bidder_id, amount):
    """The actual escrowed bid. Order matters for correctness:
    1. Re-check the listing is still active + amount still clears the CURRENT min (cheap read,
       just to reject an obviously-stale bid before touching anyone's ccm).
    2. Deduct the bidder's ccm FIRST (try_deduct_ccm — atomic, fails clean if they can't
       afford it — nothing else has happened yet if this fails).
    3. Atomically try to claim the listing's current_bid/current_bidder_id — the Mongo filter
       itself re-checks status=="active" AND current_bid < amount, so if someone else's bid
       won this exact race in the meantime, this update matches nothing and fails.
       - Fails → refund the ccm just deducted in step 2 (nobody's money is lost, this bidder
         just didn't win the race) and tell them the new current price.
       - Succeeds → refund whoever was PREVIOUSLY winning (if anyone) — their escrow is
         released now that they've been outbid.
    No two of these steps can leave money floating unaccounted for: every deduction has an
    unconditional refund path if the thing it was for doesn't end up happening."""
    try:
        listing = await market_listings_col.find_one({"_id": ObjectId(listing_id)})
    except Exception:
        listing = None
    if not listing or listing.get("status") != "active":
        return await conv.send_message("❌ This listing is no longer active.")
    if amount < _market_min_next_bid(listing):
        return await conv.send_message(f"❌ Too low — minimum is <code>{_market_min_next_bid(listing):,}</code> ccm.", parse_mode='html')
    _bdoc = await users_catcher_col.find_one({"user_id": bidder_id}, {"harem": 1})
    if not can_receive_limited((_bdoc or {}).get("harem"), listing["char_id"], listing.get("rarity_tier") or classify_rarity(listing.get("rarity"))):
        return await conv.send_message(f"🔒 You already hold {LIMITED_PER_USER_CAP} copies of this card (the limit) — bid not placed.")

    if not await try_deduct_ccm(bidder_id, amount):
        return await conv.send_message("❌ You don't have enough ccm for that bid.")

    updated = await market_listings_col.find_one_and_update(
        {"_id": ObjectId(listing_id), "status": "active", "current_bid": {"$lt": amount}},
        {"$set": {"current_bid": amount, "current_bidder_id": bidder_id}},
        return_document=ReturnDocument.AFTER
    )
    if not updated:
        # Someone else's bid won the race (or the listing ended) between our read above and
        # this atomic claim — give the ccm straight back, nothing else to undo.
        await users_catcher_col.update_one({"user_id": bidder_id}, {"$inc": {"ccm_balance": amount}})
        fresh = await market_listings_col.find_one({"_id": ObjectId(listing_id)})
        current = fresh.get("current_bid", 0) if fresh else 0
        return await conv.send_message(
            f"❌ Too slow — the bid is already at <code>{current:,}</code> ccm. Your ccm hasn't been touched."
            if fresh and fresh.get("status") == "active" else "❌ This listing just ended.",
            parse_mode='html'
        )

    # (the $set above overwrote current_bidder_id with the NEW bidder — whoever held the
    # previous highest bid, if anyone, is exactly what `listing` still shows, since that's
    # the read from BEFORE this update.)
    prev_bidder_id = listing.get("current_bidder_id")
    prev_amount = listing.get("current_bid", 0)
    if prev_bidder_id and prev_amount > 0:
        await users_catcher_col.update_one({"user_id": prev_bidder_id}, {"$inc": {"ccm_balance": prev_amount}})
        new_bidder_mention = await _market_mention_for(bidder_id)
        try:
            await bot1.send_message(
                prev_bidder_id,
                f"📢 <b>You've been outbid!</b> {new_bidder_mention} bid <code>{amount:,}</code> ccm on "
                f"<code>{display_char_id(listing['char_id'])}</code> — your <code>{prev_amount:,}</code> ccm is back in your balance.",
                parse_mode='html'
            )
        except Exception:
            pass
    await conv.send_message(
        f"✅ <b>Bid placed!</b> <code>{amount:,}</code> ccm is now held in escrow for this auction.\n"
        f"⏱ Ends in {_market_time_left(updated['ends_at'])}.",
        parse_mode='html'
    )

# ---- My Listings ----
async def _render_market_mine_page(user_id, page):
    total = await market_listings_col.count_documents({"seller_id": user_id})
    docs = await market_listings_col.find({"seller_id": user_id}).sort("created_at", -1) \
        .skip(page * MARKET_BROWSE_PAGE_SIZE).limit(MARKET_BROWSE_PAGE_SIZE).to_list(length=MARKET_BROWSE_PAGE_SIZE)
    if not docs:
        text = "💰 <b>My Listings</b>\n\n😶 <i>Nothing listed yet — try /sell.</i>" if page == 0 else "<i>No more.</i>"
        return text, [[Button.inline("🔙 Back", data="mkt_menu")]]
    status_emoji = {"active": "🟢", "sold": "✅", "expired_unsold": "⚪", "cancelled": "🗑️"}
    lines = ["💰 <b>My Listings</b>\n"]
    for d in docs:
        char_data = await characters_base_col.find_one({"char_id": d["char_id"]}, {"name": 1})
        name = char_data["name"] if char_data else d["char_id"]
        emoji = status_emoji.get(d["status"], "•")
        price = d["current_bid"] if d.get("current_bid", 0) > 0 else d["starting_price"]
        lines.append(f"{emoji} <b>{escape_html(name)}</b> — {price:,}💰 ({d['status']})")
    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Previous", data=f"mkt_mine_{page - 1}"))
    if (page + 1) * MARKET_BROWSE_PAGE_SIZE < total:
        nav_row.append(Button.inline("Next ▶", data=f"mkt_mine_{page + 1}"))
    buttons = ([nav_row] if nav_row else []) + [[Button.inline("🔙 Back", data="mkt_menu")]]
    return "\n".join(lines), buttons

@bot1.on(events.CallbackQuery(pattern=r'^mkt_mine_(\d+)$'))
async def market_mine_page_callback(event):
    if not await _market_require_group_member(event):
        return
    page = int(event.pattern_match.group(1))
    text, buttons = await _render_market_mine_page(event.sender_id, page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

# ---- Shared by /sell AND the 🛒 Sell button under /harem below — validates ownership/limits
# and shows the same confirm/cancel prompt either way. `send(text, buttons)` lets each call
# site decide HOW to deliver it (event.reply for a plain command, conv.send_message from
# inside a bot1.conversation() for the button-driven picker). ----
async def _market_offer_listing_confirm(send, seller_id, char_id, price):
    if price < MARKET_MIN_STARTING_PRICE:
        return await send(f"❌ <b>Minimum starting price is {MARKET_MIN_STARTING_PRICE:,} ccm.</b>", None)

    active_count = await market_listings_col.count_documents({"seller_id": seller_id, "status": "active"})
    if active_count >= MARKET_MAX_ACTIVE_LISTINGS_PER_USER:
        return await send(
            f"❌ <b>You already have {MARKET_MAX_ACTIVE_LISTINGS_PER_USER} active listings</b> — that's the max at once. "
            f"Check /market → My Listings.", None
        )

    char_data = await characters_base_col.find_one({"char_id": char_id})
    if not char_data:
        return await send("❌ <b>…I don't know anyone with that ID.</b>", None)

    seller_doc = await users_catcher_col.find_one({"user_id": seller_id})
    seller_harem = (seller_doc or {}).get("harem", [])
    char_item = next((x for x in seller_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") == "vault" and not is_bound_entry(x)), None)
    if not char_item:
        if any(isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") == "vault" and is_bound_entry(x) for x in seller_harem):
            return await send("🔒 <b>Owner ဆီက gift ရထားတဲ့ ကတ်မို့ ရောင်းလို့မရပါ။</b>", None)
        return await send("❌ <b>…she's not yours to sell</b> (or she's already listed/otherwise unavailable).", None)

    confirm_text = (
        f"🛒 <b>List for auction?</b>\n\n"
        f"╭ ᴄʜᴀʀᴀᴄᴛᴇʀ\n╰➤ {escape_html(char_data['name'])}\n\n"
        f"╭ sᴛᴀʀᴛɪɴɢ ᴘʀɪᴄᴇ\n╰➤ {price:,} ccm\n\n"
        f"⏱ Runs for {MARKET_LISTING_DURATION_SECONDS // 3600}h once listed. "
        f"A {MARKET_FEE_PERCENT}% fee is taken from the final sale.\n"
        f"<i>The card leaves your harem the moment you confirm, and only comes back if nobody bids.</i>"
    )
    buttons = [[
        Button.inline("✅ List it", data=f"mkt_sell_confirm_{seller_id}_{char_id}_{price}"),
        Button.inline("…not yet", data=f"mkt_sell_cancel_{seller_id}")
    ]]
    await send(confirm_text, buttons)

# ---- /sell [id] [starting price] ----
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]sell(?:@\w+)?\s+(\S+)\s+(\d+)$', 'bot1')))
async def market_sell_command(event):
    if not await _market_require_group_member(event):
        return
    seller_id = event.sender_id
    char_id = normalize_char_id_input(event.pattern_match.group(1))
    price = int(event.pattern_match.group(2))

    async def send(text, buttons):
        await event.reply(text, buttons=buttons, parse_mode='html')
    await _market_offer_listing_confirm(send, seller_id, char_id, price)

# ---- 🛒 Sell a Character button (under /harem) — pick from your own sellable cards instead
# of having to know/type a char_id. Reuses _market_offer_listing_confirm for the actual
# confirm step once a price is given, so behavior is identical to /sell either way. ----
async def _render_market_sellpick_page(user_id, page):
    user_doc = await users_catcher_col.find_one({"user_id": user_id}, {"harem": 1})
    raw_harem = (user_doc or {}).get("harem", [])
    counts = {}
    for item in raw_harem:
        if isinstance(item, dict) and item.get("char_id") and item.get("status") == "vault" and not is_bound_entry(item):
            counts[item["char_id"]] = counts.get(item["char_id"], 0) + 1
    if not counts:
        return ("🛒 <b>Nothing to sell</b> — every copy you own is already listed, gifted to you by an owner (those can't be sold), or your harem's empty.",
                [[Button.inline("🔙 Back", data="mkt_menu")]])
    char_ids = sorted(counts.keys())
    char_docs = await characters_base_col.find({"char_id": {"$in": char_ids}}, {"char_id": 1, "name": 1}).to_list(length=None)
    name_by_id = {c["char_id"]: c["name"] for c in char_docs}
    total = len(char_ids)
    page_ids = char_ids[page * MARKET_BROWSE_PAGE_SIZE:(page + 1) * MARKET_BROWSE_PAGE_SIZE]
    rows = [
        [Button.inline(f"{name_by_id.get(cid, cid)} (x{counts[cid]})"[:60], data=f"mkt_sellpick_go_{cid}_{user_id}")]
        for cid in page_ids
    ]
    nav_row = []
    if page > 0:
        nav_row.append(Button.inline("◀ Previous", data=f"mkt_sellpick_{page - 1}_{user_id}"))
    if (page + 1) * MARKET_BROWSE_PAGE_SIZE < total:
        nav_row.append(Button.inline("Next ▶", data=f"mkt_sellpick_{page + 1}_{user_id}"))
    buttons = rows + ([nav_row] if nav_row else []) + [[Button.inline("🔙 Back", data="mkt_menu")]]
    return f"🛒 <b>Pick a character to sell</b> ({total} sellable)", buttons

@bot1.on(events.CallbackQuery(pattern=r'^mkt_sellpick_(\d+)_(\d+)$'))
async def market_sellpick_page_callback(event):
    page = int(event.pattern_match.group(1))
    owner_uid = int(event.pattern_match.group(2))
    if event.sender_id != owner_uid:
        return await event.answer("❌ Not for you.", alert=True)
    if not await _market_require_group_member(event):
        return
    text, buttons = await _render_market_sellpick_page(owner_uid, page)
    try:
        await event.edit(text, parse_mode='html', buttons=buttons)
        await event.answer()
    except errors.MessageNotModifiedError:
        await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^mkt_sellpick_go_([a-zA-Z0-9_]+)_(\d+)$'))
async def market_sellpick_choose_callback(event):
    char_id_raw = event.pattern_match.group(1)
    char_id = (char_id_raw.decode('utf-8') if isinstance(char_id_raw, bytes) else char_id_raw).upper()
    owner_uid = int(event.pattern_match.group(2))
    if event.sender_id != owner_uid:
        return await event.answer("❌ Not for you.", alert=True)
    if not await _market_require_group_member(event):
        return
    # 🩹 FIX: debounce exact double-taps on this same row (Telegram clients sometimes fire a
    # callback twice, and a user's own fast double-tap lands before the first one is answered).
    if not claim_single_tap(event):
        return await event.answer("⏳ Processing...", alert=False)
    # 🩹 FIX: bail out fast (with a normal alert, not a crash) if this user already has a
    # sell/bid conversation open — see market_dm_conversation_locks' comment in BotState for
    # why two of these for the same user_id can't coexist.
    lock = market_dm_conversation_locks[owner_uid]
    if lock.locked():
        return await event.answer("⏳ You already have a sell prompt open — reply to it (or /cancel it) first.", alert=True)
    await event.answer()
    char_data = await characters_base_col.find_one({"char_id": char_id})
    char_name = escape_html(char_data["name"]) if char_data else char_id
    async with lock:
        try:
            async with bot1.conversation(owner_uid, timeout=MARKET_BID_CONVERSATION_TIMEOUT) as conv:
                await conv.send_message(
                    f"🛒 <b>Selling {char_name}</b>\nWhat starting price (in ccm)? Minimum {MARKET_MIN_STARTING_PRICE:,}.\n\n"
                    f"Reply with a number, or /cancel.",
                    parse_mode='html'
                )
                resp = await conv.get_response()
                raw = (resp.raw_text or "").strip()
                if raw.lower() == "/cancel":
                    return await conv.send_message("❌ Cancelled.")
                if not raw.isdigit():
                    return await conv.send_message("❌ That's not a number. Tap the sell button again to retry.")
                price = int(raw)

                async def send(text, buttons):
                    await conv.send_message(text, buttons=buttons, parse_mode='html')
                await _market_offer_listing_confirm(send, owner_uid, char_id, price)
        except asyncio.TimeoutError:
            try:
                await bot1.send_message(owner_uid, "⌛ <b>Timed out.</b> Tap the sell button again to retry.", parse_mode='html')
            except Exception:
                pass
        except errors.PeerIdInvalidError:
            # 🩹 FIX: this is the "invalid Peer... bots cannot start conversations" error. It's
            # not a system fault — Telegram refuses to let a bot send the FIRST private message
            # to a user who has never opened a PM with it (or who blocked it). Tell the user
            # what to do instead of paging the owner every time it happens.
            try:
                start_hint = f"@{BOT1_USERNAME}" if BOT1_USERNAME else "me"
                await event.respond(
                    f"⚠️ <b>I can't message you privately yet.</b>\n"
                    f"Please start a private chat with {start_hint} (send it /start), then tap "
                    f"the sell button again.",
                    parse_mode='html'
                )
            except Exception:
                pass
        except ValueError as e:
            if "exclusive conversation" in str(e).lower():
                # 🩹 FIX: belt-and-suspenders for the same "already open" race the lock above
                # guards against — should be effectively unreachable now, but if it ever does
                # fire (e.g. a lock key mismatch from a future edit), fail soft instead of
                # spamming the owner's error channel.
                try:
                    await event.respond("⏳ You already have a prompt open with me — reply to it first.", parse_mode='html')
                except Exception:
                    pass
            else:
                await report_system_error("market_sellpick_choose_callback", f"{e}")
        except Exception as e:
            await report_system_error("market_sellpick_choose_callback", f"{e}")

@bot1.on(events.CallbackQuery(pattern=r'^mkt_sell_cancel_(\d+)$'))
async def market_sell_cancel_callback(event):
    seller_id = int(event.pattern_match.group(1))
    if event.sender_id != seller_id:
        return await event.answer("❌ Not for you.", alert=True)
    await event.edit("…changed your mind. Nothing was listed.", buttons=None)
    await event.answer()

@bot1.on(events.CallbackQuery(pattern=r'^mkt_sell_confirm_(\d+)_([a-zA-Z0-9_]+)_(\d+)$'))
async def market_sell_confirm_callback(event):
    seller_id = int(event.pattern_match.group(1))
    char_id_raw = event.pattern_match.group(2)
    char_id = (char_id_raw.decode('utf-8') if isinstance(char_id_raw, bytes) else char_id_raw).upper()
    price = int(event.pattern_match.group(3))
    if event.sender_id != seller_id:
        return await event.answer("❌ Not for you.", alert=True)
    if not await _market_require_group_member(event):
        return
    if not claim_single_tap(event):
        return await event.answer("⏳ Processing...", alert=False)
    try:
        seller_doc = await users_catcher_col.find_one({"user_id": seller_id})
        seller_harem = (seller_doc or {}).get("harem", [])
        char_item = next((x for x in seller_harem if isinstance(x, dict) and x.get("char_id") == char_id and x.get("status") == "vault" and not is_bound_entry(x)), None)
        if not char_item:
            await event.edit("❌ <b>…she's already gone.</b> Nothing was listed.", parse_mode='html', buttons=None)
            await event.answer("Card not found.", alert=True)
            return
        flipped = await set_one_harem_copy_status(seller_id, char_id, "vault", "market", unbound_only=True)
        if not flipped:
            await event.edit("❌ <b>…she's already gone.</b> Nothing was listed.", parse_mode='html', buttons=None)
            await event.answer("Card not found.", alert=True)
            return
        now = time.time()
        listing_doc = {
            "seller_id": seller_id, "char_id": char_id,
            "rarity": char_item.get("rarity", "Unknown"),
            "rarity_tier": char_item.get("rarity_tier") or classify_rarity(char_item.get("rarity")),
            "starting_price": price, "current_bid": 0, "current_bidder_id": None,
            "created_at": now, "ends_at": now + MARKET_LISTING_DURATION_SECONDS,
            "status": "active",
        }
        result = await market_listings_col.insert_one(listing_doc)
        char_data = await characters_base_col.find_one({"char_id": char_id})
        char_name = escape_html(char_data["name"]) if char_data else char_id
        await event.edit(
            f"✅ <b>Listed!</b>\n\n{char_name} is up for auction at <code>{price:,}</code> ccm starting price.\n"
            f"⏱ Ends in {MARKET_LISTING_DURATION_SECONDS // 3600}h. Check /market → My Listings for updates.",
            parse_mode='html', buttons=None
        )
        await event.answer("Listed!")
    except Exception as e:
        await report_system_error("market_sell_confirm_callback", f"{e}\nData: {event.data}")
        try:
            await event.answer("❌ Something went wrong!", alert=True)
        except Exception:
            pass

# ---- Auction expiry — settles every ended listing: pays the seller (minus the ccm-sink fee),
# hands the winner the card, or returns an unsold card to the seller's vault. ----
async def _settle_market_listing(listing):
    listing_id = listing["_id"]
    winner_id = listing.get("current_bidder_id")
    final_bid = listing.get("current_bid", 0)
    char_id = listing["char_id"]
    seller_id = listing["seller_id"]
    if winner_id and final_bid > 0:
        moved = await remove_one_harem_copy(seller_id, char_id, "market")
        await users_catcher_col.update_one(
            {"user_id": winner_id},
            {
                "$push": {"harem": {"char_id": char_id, "caught_date": time.time(), "rarity": listing.get("rarity", "Unknown"), "status": "vault"}},
                "$inc": {"total_caught": 1}
            },
            upsert=True
        )
        fee = round(final_bid * MARKET_FEE_PERCENT / 100)
        proceeds = final_bid - fee
        await users_catcher_col.update_one({"user_id": seller_id}, {"$inc": {"ccm_balance": proceeds}}, upsert=True)
        if fee > 0:
            await users_catcher_col.update_one({"user_id": OWNER_ID}, {"$inc": {"ccm_balance": fee}}, upsert=True)
        seller_doc_after = await users_catcher_col.find_one({"user_id": seller_id}, {"harem": 1})
        await clear_stale_favorite(seller_id, char_id, (seller_doc_after or {}).get("harem", []))
        await market_listings_col.update_one({"_id": listing_id}, {"$set": {"status": "sold"}})
        try:
            await market_history_col.insert_one({
                "listing_id": str(listing_id), "seller_id": seller_id, "buyer_id": winner_id,
                "char_id": char_id, "final_price": final_bid, "fee": fee, "timestamp": time.time()
            })
        except Exception as e:
            print(f"market_history log error: {e}")
        char_data = await characters_base_col.find_one({"char_id": char_id})
        char_name = escape_html(char_data["name"]) if char_data else char_id
        seller_mention = await _market_mention_for(seller_id)
        winner_mention = await _market_mention_for(winner_id)
        for uid, text in (
            (seller_id, f"✅ <b>Your listing sold!</b>\n{char_name} went to {winner_mention} for <code>{final_bid:,}</code> ccm — "
                        f"<code>{proceeds:,}</code> ccm credited ({fee:,} fee)."),
            (winner_id, f"🎉 <b>You won the auction!</b>\n{char_name} (from {seller_mention}) is now in your /harem."),
        ):
            try:
                await bot1.send_message(uid, text, parse_mode='html')
            except Exception:
                pass
    else:
        await set_one_harem_copy_status(seller_id, char_id, "market", "vault")
        await market_listings_col.update_one({"_id": listing_id}, {"$set": {"status": "expired_unsold"}})
        char_data = await characters_base_col.find_one({"char_id": char_id})
        char_name = escape_html(char_data["name"]) if char_data else char_id
        try:
            await bot1.send_message(seller_id, f"⏱ <b>No bids.</b> {char_name} is back in your harem.", parse_mode='html')
        except Exception:
            pass

async def market_auction_expiry_scheduler():
    """Sweeps ended listings every MARKET_EXPIRY_CHECK_INTERVAL seconds for the life of the
    process. Each settlement is independent — one failing (a bad char_id, a Telegram DM
    hiccup) never blocks the rest of the sweep or crashes the loop."""
    while True:
        await asyncio.sleep(MARKET_EXPIRY_CHECK_INTERVAL)
        try:
            ended = await market_listings_col.find({"status": "active", "ends_at": {"$lte": time.time()}}).to_list(length=None)
            for listing in ended:
                try:
                    await _settle_market_listing(listing)
                except Exception as e:
                    await report_system_error("market_auction_expiry_scheduler (settle)", f"listing {listing.get('_id')}: {e}")
        except Exception as e:
            print(f"market_auction_expiry_scheduler sweep error: {e}")

# ==========================================
# 👑 /addowner — reply to a user's message to grant them the SAME unlimited-vault privilege
# OWNER_ID has: every character counts as "owned" for browsing (/harem, the inline gallery),
# for /fav, AND for /gift — no real /collect catch needed for any of them. The one difference
# from OWNER_ID: gifting is capped at ADDED_OWNER_GIFT_LIMIT_PER_CARD times per card (OWNER_ID
# has no cap at all). See gift_asset_handler/gift_callback_handler for where that's enforced.
# (/gift and the 🛒 Market above are the only transfer paths in the bot — nothing extra to
# restrict here for either of them; an added owner uses both exactly like anyone else.)
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
        f"ဒါပေမဲ့ ကဒ်တစ်ခုစီကို <b>{ADDED_OWNER_GIFT_LIMIT_PER_CARD} ကြိမ်ထိပဲ</b> ပေးလို့ရပါမယ်။\n"
        f"🔗 Gift လုပ်တဲ့ကတ်ကို လက်ခံသူက ရောင်း/ပြန်ပေး မရပါ။ 💳 Supreme / Cataphract ကို gift လုပ်ရင် "
        f"setvalue (gram) ပေးရပါမယ်။",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]removeowner(?:\s+(\d{5,15}))?$', 'bot1')))
async def remove_owner_command(event):
    """/removeowner <user_id>  — or reply to the user's message with /removeowner (both work)."""
    if event.sender_id != OWNER_ID:
        return
    arg = event.pattern_match.group(1)
    if arg:
        target_id = int(arg)
    elif event.is_reply:
        replied = await event.get_reply_message()
        target_id = replied.sender_id
    else:
        return await event.reply(
            "❌ <b>Usage:</b> <code>/removeowner [user_id]</code> — or reply to the user's message with /removeowner.\n"
            "<i>/listowners shows every added owner with their id.</i>", parse_mode='html')
    if target_id not in added_owner_ids:
        return await event.reply(f"❌ <code>{target_id}</code> isn't an added owner. (/listowners)", parse_mode='html')
    await added_owners_col.delete_one({"user_id": target_id})
    added_owner_ids.discard(target_id)
    try:
        mention = await get_html_mention(event, target_id)
    except Exception:
        mention = f"<code>{target_id}</code>"   # account not resolvable (left / deleted) — the id is enough
    await event.reply(f"✅ Removed added-owner status from {mention} (<code>{target_id}</code>).", parse_mode='html')

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
# 📤 /adduploader — OWNER ONLY. Reply to a user's message to let them use /addchar (add new
# characters, optionally with their own chosen ID). Nothing else: no vault, no gifting bypass and
# no other owner command — those stay OWNER_ID / /addowner only.
# ==========================================
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]adduploader$', 'bot1')))
async def add_uploader_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_reply:
        return await event.reply("❌ <b>Reply to the user's message with /adduploader.</b>", parse_mode='html')
    replied = await event.get_reply_message()
    target_id = replied.sender_id
    if not target_id:
        return await event.reply("❌ Can't tell who sent that message (anonymous/channel post).")
    if target_id == OWNER_ID:
        return await event.reply("❌ That's already you.")
    if getattr(await replied.get_sender(), 'bot', False):
        return await event.reply("❌ Can't add a bot as an uploader.")
    mention = await get_html_mention(event, target_id)
    if target_id in uploader_ids:
        return await event.reply(f"❌ {mention} is already an uploader.", parse_mode='html')
    await uploaders_col.update_one(
        {"user_id": target_id},
        {"$set": {"added_by": OWNER_ID, "added_at": time.time()}},
        upsert=True
    )
    uploader_ids.add(target_id)
    await event.reply(
        f"📤 <b>Added Uploader:</b> {mention}\n"
        f"ဒီ user က <code>/addchar</code> ကို သုံးနိုင်ပါပြီ (media ကို reply ပြီး "
        f"<code>/addchar Name | Category | Rarity | Event | CatchLimit | ID</code>)။\n"
        f"တခြား owner command တွေ မသုံးနိုင်ပါ။",
        parse_mode='html'
    )

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:removeuploader|deluploader)(?:\s+(\d{5,15}))?$', 'bot1')))
async def remove_uploader_command(event):
    """/removeuploader <user_id>  — or reply to the user's message with /removeuploader."""
    if event.sender_id != OWNER_ID:
        return
    arg = event.pattern_match.group(1)
    if arg:
        target_id = int(arg)
    elif event.is_reply:
        replied = await event.get_reply_message()
        target_id = replied.sender_id
    else:
        return await event.reply(
            "❌ <b>Usage:</b> <code>/removeuploader [user_id]</code> — or reply to the user's message with /removeuploader.\n"
            "<i>/listuploaders shows every uploader with their id.</i>", parse_mode='html')
    if target_id not in uploader_ids:
        return await event.reply(f"❌ <code>{target_id}</code> isn't an uploader. (/listuploaders)", parse_mode='html')
    await uploaders_col.delete_one({"user_id": target_id})
    uploader_ids.discard(target_id)
    try:
        mention = await get_html_mention(event, target_id)
    except Exception:
        mention = f"<code>{target_id}</code>"
    await event.reply(f"✅ Removed uploader status from {mention} (<code>{target_id}</code>).", parse_mode='html')

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]listuploaders$', 'bot1')))
async def list_uploaders_command(event):
    if event.sender_id != OWNER_ID:
        return
    if not uploader_ids:
        return await event.reply("📭 No uploaders yet — use /adduploader (as a reply) to add one.")
    lines = []
    for uid in uploader_ids:
        try:
            mention = await get_html_mention(event, uid)
        except Exception:
            mention = f"<code>{uid}</code>"
        lines.append(f"• {mention} (<code>{uid}</code>)")
    await event.reply("📤 <b>Uploaders:</b>\n" + "\n".join(lines), parse_mode='html')

# ==========================================
# 🚫 GBAN COMMANDS — /gban, /ungban, /gunban (Owner-only)
# ==========================================
# The actual enforcement (is_gbanned / gban_block_gate / gban_block_gate_callback) lives right
# after bot1's creation near the top of the file, registered before every other handler so a
# banned user's commands/taps never reach anything else — see that section for the full
# reasoning. This section is just the owner-facing tooling that WRITES to
# gbanned_until/gban_col: the /gban 2-step wizard (reason -> duration), /ungban + its /gunban
# alias (owner request), and the boot-time reloader that makes a "perm" ban survive a restart.
#
# ⚠️ CONFISCATION NOTE: the spec this was built from also calls for sweeping the target's VLT
# balance and Star balance to the owner on ban. This bot's internal currency system (any
# VLT/Star wallet field on users_catcher_col) was fully removed a while back — see the
# "currency system... has been removed" comments near _RARITY_VALUE_MAP and the retired join
# reward, and note none of GUARD_GAME_COMMANDS' games (/slot, /dice, /mines, etc.) are actually
# registered anywhere anymore either. There is simply nothing left to confiscate there, so
# gban_apply() below only clears the target's harem (cards). If a VLT/Star wallet ever gets
# added back to the schema, extend gban_apply() to zero it out and $inc it onto OWNER_ID here.
def parse_gban_duration(raw: str):
    """'30m' / '24h' / '7d' / '2w' / 'perm' / 'permanent' -> (expiry_seconds_or_inf, label).
    Returns (None, None) if the text doesn't parse as a valid duration."""
    raw = (raw or "").strip().lower()
    if raw in ("perm", "permanent"):
        return float('inf'), "Permanent"
    m = re.match(r'^(\d+)\s*(m|h|d|w)$', raw)
    if not m:
        return None, None
    amount = int(m.group(1))
    if amount <= 0:
        return None, None
    unit = m.group(2)
    seconds_per_unit = {"m": 60, "h": 3600, "d": 86400, "w": 604800}[unit]
    unit_label = {"m": "minute", "h": "hour", "d": "day", "w": "week"}[unit]
    label = f"{amount} {unit_label}{'s' if amount != 1 else ''}"
    return amount * seconds_per_unit, label


async def gban_apply(event, target_id: int, target_name: str, reason: str, expiry: float, duration_label: str):
    """Bans target_id bot-wide: clears their harem (see the confiscation note above the
    section header — no VLT/Star fields exist on this bot to sweep), records the ban
    in-memory (gbanned_until + user_mute_until, for the two enforcement gates) and durably in
    gban_col (restart-safe via load_active_gbans_cache)."""
    now = time.time()

    target_doc = await users_catcher_col.find_one_and_update(
        {"user_id": target_id},
        {"$set": {"harem": []}}
    )
    confiscated_cards = len((target_doc or {}).get("harem") or [])

    gbanned_until[target_id] = {"expiry": expiry, "reason": reason, "duration_label": duration_label}
    user_mute_until[target_id] = expiry  # also blocks /fuck /catch /who via the shared spam-mute check

    await gban_col.insert_one({
        "user_id": target_id,
        "target_name": target_name,
        "reason": reason,
        "duration_label": duration_label,
        "banned_by": OWNER_ID,
        "banned_at": now,
        "expires_at": None if expiry == float('inf') else expiry,
        "active": True,
    })

    await event.reply(
        f"✅ <b>GBAN APPLIED</b>\n\n"
        f"🎯 <b>Target:</b> <a href='tg://user?id={target_id}'>{escape_html(target_name)}</a> (<code>{target_id}</code>)\n"
        f"📝 <b>Reason:</b> {escape_html(reason)}\n"
        f"⏳ <b>Duration:</b> {escape_html(duration_label)}\n"
        f"🎴 <b>Cards confiscated:</b> <code>{confiscated_cards}</code>\n\n"
        f"🌐 Blocked bot-wide — every group and DM.",
        parse_mode='html'
    )


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]gban(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def gban_command(event):
    if event.sender_id != OWNER_ID:
        return
    target_id = None
    if event.is_reply:
        replied = await event.get_reply_message()
        if replied and replied.sender_id:
            target_id = replied.sender_id
    if target_id is None:
        arg = event.pattern_match.group(1)
        if arg and arg.isdigit():
            target_id = int(arg)
    if target_id is None:
        return await event.reply(
            "❌ <b>Usage:</b> <code>/gban [user_id]</code> or reply to the user's message with <code>/gban</code>.",
            parse_mode='html'
        )
    if target_id == OWNER_ID:
        return await event.reply("🚫 The owner can't be gbanned.", parse_mode='html')
    if target_id in bot_ids:
        return await event.reply("🚫 Can't gban a bot.", parse_mode='html')

    already_banned, rec = is_gbanned(target_id)
    if already_banned:
        return await event.reply(
            f"⚠️ <code>{target_id}</code> is already gbanned.\n"
            f"📝 <b>Reason:</b> {escape_html(rec.get('reason', 'No reason given'))}\n"
            f"⏳ <b>Duration:</b> {escape_html(str(rec.get('duration_label', 'Permanent')))}",
            parse_mode='html'
        )

    target_name = await get_plain_name(event, target_id)
    text = (
        f"🚫 <b>GBAN — Step 1/2</b>\n\n"
        f"🎯 <b>Target:</b> <a href='tg://user?id={target_id}'>{escape_html(target_name)}</a> (<code>{target_id}</code>)\n\n"
        f"↩️ <b>Reply to this message</b> with the ban reason."
    )
    sent = await event.reply(text, parse_mode='html')
    pending_gban_prompt_ids[sent.id] = {"step": "reason", "target_id": target_id, "target_name": target_name}


@bot1.on(events.NewMessage(incoming=True))
async def gban_wizard_reply(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_reply:
        return
    if event.reply_to_msg_id not in pending_gban_prompt_ids:
        return
    state = pending_gban_prompt_ids.pop(event.reply_to_msg_id)
    raw = (event.text or "").strip()
    if not raw:
        pending_gban_prompt_ids[event.reply_to_msg_id] = state  # empty reply doesn't count — put the state back
        return

    if state["step"] == "reason":
        text = (
            f"🚫 <b>GBAN — Step 2/2</b>\n\n"
            f"🎯 <b>Target:</b> <a href='tg://user?id={state['target_id']}'>{escape_html(state['target_name'])}</a>\n"
            f"📝 <b>Reason:</b> {escape_html(raw)}\n\n"
            f"↩️ <b>Reply to this message</b> with a duration:\n"
            f"<code>30m</code> · <code>24h</code> · <code>7d</code> · <code>2w</code> · <code>perm</code>"
        )
        sent = await event.reply(text, parse_mode='html')
        pending_gban_prompt_ids[sent.id] = {**state, "step": "duration", "reason": raw}
        return

    if state["step"] == "duration":
        expiry, duration_label = parse_gban_duration(raw)
        if expiry is None:
            sent = await event.reply(
                "❌ <b>Invalid duration.</b> Use <code>30m</code>, <code>24h</code>, <code>7d</code>, "
                "<code>2w</code>, or <code>perm</code>.\n\n↩️ <b>Reply to this message</b> with a valid duration.",
                parse_mode='html'
            )
            pending_gban_prompt_ids[sent.id] = state
            return
        await gban_apply(event, state["target_id"], state["target_name"], state["reason"], expiry, duration_label)


@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.](?:ungban|gunban)(?:@\w+)?(?:\s+(\S+))?$', 'bot1')))
async def ungban_handler(event):
    # 🩹 /gunban is an alias for /ungban (owner request).
    if event.sender_id != OWNER_ID:
        return
    target_id = None
    if event.is_reply:
        replied = await event.get_reply_message()
        if replied and replied.sender_id:
            target_id = replied.sender_id
    if target_id is None:
        arg = event.pattern_match.group(1)
        if arg and arg.isdigit():
            target_id = int(arg)
    if target_id is None:
        return await event.reply(
            "❌ <b>Usage:</b> <code>/ungban [user_id]</code> or reply to the user's message with <code>/ungban</code>.",
            parse_mode='html'
        )

    was_banned, _ = is_gbanned(target_id)
    gbanned_until.pop(target_id, None)
    user_mute_until.pop(target_id, None)
    result = await gban_col.update_many(
        {"user_id": target_id, "active": True},
        {"$set": {"active": False, "lifted_at": time.time()}}
    )
    if not was_banned and result.modified_count == 0:
        return await event.reply(f"ℹ️ <code>{target_id}</code> isn't currently gbanned.", parse_mode='html')
    await event.reply(f"✅ <b>GBAN lifted</b> for <code>{target_id}</code>.", parse_mode='html')


async def load_active_gbans_cache():
    """Bot restart -> gbanned_until/user_mute_until (in-memory) are empty again. Reload every
    still-active, not-yet-expired ban from gban_col so a 'perm' gban doesn't silently lift
    itself just because the process restarted. Called from run_bot1_forever(), right after
    load_added_owners_cache()."""
    try:
        now = time.time()
        active = await gban_col.find({"active": True}).to_list(length=None)
        loaded = 0
        for ban in active:
            expires_at = ban.get("expires_at")
            if expires_at and expires_at <= now:
                continue  # already expired — left inactive-in-spirit; is_gbanned()/ungban will square away the DB flag later
            uid = ban["user_id"]
            expiry = expires_at if expires_at else float('inf')
            gbanned_until[uid] = {
                "expiry": expiry,
                "reason": ban.get("reason", "No reason given"),
                "duration_label": ban.get("duration_label", "Permanent"),
            }
            user_mute_until[uid] = expiry
            loaded += 1
        if loaded:
            print(f"🚫 GBAN: restored {loaded} active global ban(s) from DB.")
    except Exception as e:
        print(f"load_active_gbans_cache error: {e}")

# ==========================================
# 👑 TOPSPAWN — top-tier drop event toggle (owner-only)
# ==========================================
# Writes/reads the SAME _cached_top_tier_enabled flag get_effective_rarity_weights() (near
# DEFAULT_RARITY_WEIGHTS, far above) reads on every spawn — see that section for the actual
# weights and the reasoning. ON = CROSSVERSE / DIVINE / MYSTICAL / LEGENDARY drop on equal
# footing (TOP_TIER_EVENT_WEIGHT_ON), SUPREME / CATAPHRACT only get a small bump. This command
# is just the on/off switch plus a live readout of what that means for the current roster.
_TOPSPAWN_EVENT_TIERS = ("CROSSVERSE", "DIVINE", "MYSTICAL", "LEGENDARY")

async def _topspawn_live_readout():
    """(percent lines, warning lines) for the tiers /topspawn cares about, computed with the
    exact same eligibility filter + tier weights trigger_dynamic_spawn uses. A tier with no
    eligible card can never spawn whatever its weight is — that is called out, not hidden.
    Never raises: the toggle itself must not fail because a preview couldn't be built."""
    try:
        eligible = get_spawn_eligible_characters(await get_all_characters_cached())
        counts = {}
        for c in eligible:
            tier = c.get("rarity_tier") or classify_rarity(c.get("rarity", ""))
            counts[tier] = counts.get(tier, 0) + 1
        weights = get_effective_rarity_weights()
        weight_of = lambda t: weights.get(t, UNKNOWN_TIER_WEIGHT)
        total = sum(weight_of(t) for t in counts)
        lines, warnings = [], []
        for t in RARITY_TIERS:
            if t not in _TOPSPAWN_EVENT_TIERS and t not in ("SUPREME", "CATAPHRACT"):
                continue
            n = counts.get(t, 0)
            pct = (weight_of(t) / total * 100) if (total > 0 and n) else 0.0
            lines.append(f"{t:<11} {pct:6.2f}%  ({n} cards)")
            if n == 0 and t in _TOPSPAWN_EVENT_TIERS:
                warnings.append(t)
        return lines, warnings
    except Exception as e:
        print(f"⚠️ _topspawn_live_readout failed: {type(e).__name__}: {e}")
        return [], []

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]topspawn(?:@\w+)?(?:\s+(on|off))?$', 'bot1')))
async def toggle_top_tier_spawn(event):
    global _cached_top_tier_enabled
    if event.sender_id != OWNER_ID: return
    arg = (event.pattern_match.group(1) or "").lower()
    if not arg:
        status = "🟢 ON" if _cached_top_tier_enabled else "🔴 OFF"
        _w = get_effective_rarity_weights()
        return await event.reply(
            f"👑 <b>TOP-TIER SPAWN</b>\n\n"
            f"Status: {status}\n"
            f"Current weights: SUPREME <code>{_w['SUPREME']}</code> · CATAPHRACT <code>{_w['CATAPHRACT']}</code> · "
            f"CROSSVERSE <code>{_w['CROSSVERSE']}</code> · DIVINE <code>{_w['DIVINE']}</code> · "
            f"MYSTICAL <code>{_w['MYSTICAL']}</code> · LEGENDARY <code>{_w['LEGENDARY']}</code>\n\n"
            f"📖 <b>Usage:</b> <code>/topspawn on</code> or <code>/topspawn off</code>\n"
            f"<i>/spawnrates shows the live percentages.</i>",
            parse_mode='html'
        )
    new_state = (arg == "on")
    _cached_top_tier_enabled = new_state
    await bot_settings_col.update_one(
        {"_id": "top_tier_spawn_enabled"},
        {"$set": {"enabled": new_state}},
        upsert=True
    )
    lines, warnings = await _topspawn_live_readout()
    readout = f"\n\n<pre>{escape_html(chr(10).join(lines))}</pre>" if lines else ""
    warn = ""
    if warnings:
        warn = (f"\n⚠️ <b>{', '.join(warnings)}</b> — eligible card မရှိသေးလို့ (မရှိ၊ ဒါမှမဟုတ် CatchLimit ပြည့်နေ) "
                f"weight ဘယ်လောက်ပေးပေး မကျနိုင်ပါဘူး။")
    if new_state:
        text = (
            f"👑 <b>TOP-TIER SPAWN: ON</b>\n\n"
            f"CROSSVERSE · DIVINE · MYSTICAL · LEGENDARY အားလုံး weight "
            f"<code>{TOP_TIER_EVENT_WEIGHT_ON['CROSSVERSE']}</code> (အညီအမျှ) ဖြစ်သွားပါပြီ။ "
            f"SUPREME / CATAPHRACT ကတော့ ဘယ်တော့မှ အလိုလို မကျပါဘူး (owner /fspawn သာ)။"
            f"{readout}{warn}\n"
            f"Run <code>/topspawn off</code> any time to go back to the normal rates."
        )
    else:
        _w = get_effective_rarity_weights()
        text = (
            f"👑 <b>TOP-TIER SPAWN: OFF</b>\n\n"
            f"Normal rates ပြန်ရောက်ပါပြီ — DIVINE <code>{_w['DIVINE']}</code> · MYSTICAL <code>{_w['MYSTICAL']}</code> · "
            f"LEGENDARY <code>{_w['LEGENDARY']}</code> · CROSSVERSE <code>{_w['CROSSVERSE']}</code> "
            f"(/spawnpattern ပါ pattern အတိုင်း)။ SUPREME / CATAPHRACT က /fspawn နဲ့ပဲ ကျပါတယ်။"
            f"{readout}"
        )
    await event.reply(text, parse_mode='html')

# ==========================================
# 🎲 /spawnpattern — view / change the rarity spawn pattern (owner-only; see RARITY SPAWN PATTERN above)
# ==========================================
_SPAWNPATTERN_ALIASES = {
    "COMMON": "COMMON", "COM": "COMMON", "UNCOMMON": "UNCOMMON", "UNC": "UNCOMMON", "RARE": "RARE",
    "LEGENDARY": "LEGENDARY", "LEG": "LEGENDARY", "MYSTICAL": "MYSTICAL", "MYST": "MYSTICAL", "MYS": "MYSTICAL",
    "DIVINE": "DIVINE", "DIV": "DIVINE", "CROSSVERSE": "CROSSVERSE", "CROSS": "CROSSVERSE", "CV": "CROSSVERSE",
}

def parse_spawnpattern_args(text):
    """Pure. 'COMMON 20 DIVINE=6 …' → ({tier: n}, [error strings])."""
    updates, errors_ = {}, []
    for word, num in re.findall(r'([A-Za-z]+)\s*[=:]?\s*(\d{1,4})', text or ""):
        w = word.upper()
        if w in ("SUPREME", "SUP", "CATAPHRACT", "CATA"):
            errors_.append(f"{w}: never spawns on its own — use /fspawn sup | cata | <id>")
        elif w in _SPAWNPATTERN_ALIASES:
            updates[_SPAWNPATTERN_ALIASES[w]] = int(num)
        else:
            errors_.append(f"{w}: unknown tier")
    return updates, errors_

def spawnpattern_table(pattern):
    total = sum(pattern.values()) or 1
    lines = [f"{t:<11} {pattern.get(t, 0):>4}  {pattern.get(t, 0) / total * 100:5.1f}%" for t in
             ("COMMON", "UNCOMMON", "RARE", "LEGENDARY", "MYSTICAL", "DIVINE", "CROSSVERSE")]
    lines.append(f"{'CATAPHRACT':<11} {'—':>4}  never (owner /fspawn)")
    lines.append(f"{'SUPREME':<11} {'—':>4}  never (owner /fspawn)")
    return "\n".join(lines)

@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]spawnpattern(?:@\w+)?(?:\s+([\s\S]+))?$', 'bot1')))
async def spawnpattern_command(event):
    global _cached_spawn_pattern
    if event.sender_id != OWNER_ID:
        return
    arg = (event.pattern_match.group(1) or "").strip()
    if arg.lower() == "reset":
        _cached_spawn_pattern = None
        _spawn_decks.clear()
        await bot_settings_col.delete_one({"_id": "spawn_pattern"})
        return await event.reply("♻️ Spawn pattern reset to the default.\n\n<pre>" + spawnpattern_table(get_spawn_pattern()) + "</pre>", parse_mode='html')
    if arg:
        updates, errs = parse_spawnpattern_args(arg)
        if errs:
            return await event.reply("❌ " + "\n❌ ".join(escape_html(e) for e in errs), parse_mode='html')
        if not updates:
            return await event.reply("❌ Nothing understood. Example: <code>/spawnpattern COMMON 20 MYSTICAL 12 DIVINE 6 CROSSVERSE 2</code>", parse_mode='html')
        new_pattern = {**get_spawn_pattern(), **updates}
        cleaned = clean_spawn_pattern(new_pattern)
        if not cleaned:
            return await event.reply("❌ At least one tier must have a count above 0.")
        _cached_spawn_pattern = cleaned
        _spawn_decks.clear()   # every chat starts a fresh deck from the new pattern
        await bot_settings_col.update_one({"_id": "spawn_pattern"}, {"$set": {"counts": cleaned}}, upsert=True)
    pattern = get_spawn_pattern()
    total = sum(pattern.values())
    status = "ON" if _cached_top_tier_enabled else "OFF"
    await event.reply(
        f"🎲 <b>Spawn pattern</b> — out of every <code>{total}</code> spawns in a chat:\n\n<pre>{spawnpattern_table(pattern)}</pre>\n"
        f"<i>Each chat shuffles this into a deck, so these counts are exact, not luck. /topspawn {status} · "
        f"/spawnweight level {_cached_spawnweight_level} apply on top of it.</i>\n\n"
        f"<b>Change:</b> <code>/spawnpattern COMMON 20 UNCOMMON 20 RARE 20 LEGENDARY 20 MYSTICAL 12 DIVINE 6 CROSSVERSE 2</code> "
        f"(only the tiers you list change) · <code>/spawnpattern reset</code>",
        parse_mode='html')

# ==========================================
# 🎲 SPAWNRATES — live per-tier spawn percentages (owner-only)
# ==========================================
# Uses the exact same eligibility filter, tier weights and tier-first picking as
# trigger_dynamic_spawn, so what it prints is what chats actually get. Added 2026-09 alongside
# the per-tier weighting change so "make SUPREME/CATAPHRACT rarer" can be checked immediately.
@bot1.on(events.NewMessage(pattern=own_pattern(r'^[/.]spawnrates(?:@\w+)?$', 'bot1')))
async def show_spawn_rates(event):
    if event.sender_id != OWNER_ID: return
    characters_list = await get_all_characters_cached()
    eligible = get_spawn_eligible_characters(characters_list)
    if not eligible:
        return await event.reply("⚠️ No eligible characters right now.", parse_mode='html')
    tier_weights = get_effective_rarity_weights()
    counts = {}
    for c in eligible:
        tier = c.get("rarity_tier") or classify_rarity(c.get("rarity", ""))
        counts[tier] = counts.get(tier, 0) + 1
    weight_of = lambda t: tier_weights.get(t, UNKNOWN_TIER_WEIGHT)
    total_weight = sum(weight_of(t) for t in counts)
    ordered = [t for t in RARITY_TIERS if t in counts] + [t for t in counts if t not in RARITY_TIERS]
    lines = []
    for t in ordered:
        pct = (weight_of(t) / total_weight * 100) if total_weight > 0 else 0
        lines.append(f"{t:<11} {pct:6.2f}%  ({counts[t]} cards)")
    status = "ON" if _cached_top_tier_enabled else "OFF"
    await event.reply(
        f"🎲 <b>Spawn rates</b> — per spawn, per tier\n"
        f"<i>/topspawn {status} · /spawnweight level {_cached_spawnweight_level} · {len(eligible)} eligible cards · "
        f"pattern deck of {sum(spawn_deck_counts({t: weight_of(t) for t in counts}).values())} spawns per chat (/spawnpattern)</i>\n\n"
        f"<pre>{escape_html(chr(10).join(lines))}</pre>",
        parse_mode='html'
    )

# ==========================================
# 🗑️ HAITIME / RESETSTATS / GIFTALL / STEALTH
# ==========================================
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
                if current_time - data.get("spawn_time", 0) > GHOST_SPAWN_STALE_SECONDS:
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
            # Same belt-and-suspenders reasoning for pending_trivia_quiz / trivia_quiz_timeout_watcher.
            expired_trivia = [
                cid for cid, quiz in pending_trivia_quiz.items()
                if current_time - quiz.get("quiz_time", 0) > TRIVIA_TIMEOUT_SECONDS + 60
            ]
            for cid in expired_trivia:
                if cid in pending_trivia_quiz: del pending_trivia_quiz[cid]
        except Exception as e:
            logging.error(f"Cleaner Error: {e}")
        await asyncio.sleep(GHOST_SPAWN_POLL_SECONDS)
async def run_bot1_forever():
    global BOT1_USERNAME
    while True:
        try:
            print("🚀 Connecting Main Bot (bot1)...")
            print(f"🔧 {telethon_env_info()}")
            await bot1.start(bot_token=MAIN_BOT_TOKEN)
            me_main = await bot1.get_me()
            print(f"✅ Main Bot connected as @{me_main.username}")
            if BOT1_READY is not None:
                BOT1_READY.set()  # releases _startup_media_identity_warm — it must not touch Telegram before this point
            if me_main.username: BOT1_USERNAME = me_main.username.lower()
            if me_main.id not in bot_ids: bot_ids.append(me_main.id)
            await load_rarity_weight_cache()
            await load_trivia_settings_cache()
            await load_channel_work_cache()
            await load_added_owners_cache()
            await load_uploaders_cache()
            asyncio.create_task(load_active_gbans_cache())  # 🩹 non-blocking — see _create_indexes_background's docstring above for why a Mongo round-trip must never sit in this critical path; a stuck/slow gban_col query would otherwise delay ghost_spawn_cleaner/group_counter_flush_loop below it
            await load_group_spawn_counters_cache()
            asyncio.create_task(ghost_spawn_cleaner())
            asyncio.create_task(market_auction_expiry_scheduler())
            asyncio.create_task(group_counter_flush_loop())
            print("📅 Background tasks started.")
            await bot1.run_until_disconnected()
        except Exception as system_fault:
            print(f"⚠️ Main Bot disconnected: {system_fault}")
            print("⏳ Restarting Main Bot in 30 seconds...")
            await asyncio.sleep(30)


async def run_bot2_forever():
    """Secondary (spawn-reveal-only) bot. Returns immediately when SECONDARY_BOT_TOKEN is unset."""
    global BOT2_USERNAME
    if bot2 is None:
        print("ℹ️ SECONDARY_BOT_TOKEN not set — bot2 disabled (single-bot mode).")
        return
    while True:
        try:
            print("🚀 Connecting Secondary Bot (bot2)...")
            await bot2.start(bot_token=SECONDARY_BOT_TOKEN)
            me2 = await bot2.get_me()
            if me2.username: BOT2_USERNAME = me2.username.lower()
            if me2.id not in bot_ids: bot_ids.append(me2.id)
            print(f"✅ Secondary Bot connected as @{me2.username}")
            await bot2.run_until_disconnected()
        except Exception as e:
            if type(e).__name__ in ("AccessTokenInvalidError", "AccessTokenExpiredError"):
                print("❌ SECONDARY_BOT_TOKEN was rejected by Telegram — bot2 stays off until the token is fixed and the app restarted.")
                return
            print(f"⚠️ Secondary Bot disconnected: {str(e).replace(SECONDARY_BOT_TOKEN, '***')}")
            print("⏳ Restarting Secondary Bot in 30 seconds...")
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
    await load_catchbot_sync_range_cache()  # 🩹 must load BEFORE the task below, which may
    # immediately resume an interrupted /syncfromcatch run and needs the right min/max already
    # in place for that resume's clamping to be correct.
    await load_autoname_setting()  # ⚡ persisted /autoname on|off
    verify_botgate_is_first()      # 🚧 startup self-check for the bot-sender gate
    asyncio.create_task(load_and_start_monitor_userbot())
    asyncio.create_task(load_worker_pool())
    global BOT1_READY
    BOT1_READY = asyncio.Event()
    asyncio.create_task(_startup_media_identity_warm())
    asyncio.create_task(limit_policy_loop())  # 🔒 Supreme/Cataphract catch limit + per-user cap — see LIMITED RARITIES block
    asyncio.create_task(refillcatch_auto_loop())  # 🤖 keeps spawn_count in step with real vaults — see REFILLCATCH_AUTO_INTERVAL_SECONDS
    await asyncio.gather(run_bot1_forever(), run_bot2_forever())

if __name__ == "__main__":
    try:
        asyncio.run(start_system())
    except (KeyboardInterrupt, SystemExit):
        print("Bot System Shutting Down.")
        
