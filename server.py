"""
Card Market — Telegram Mini App backend.

This is a SEPARATE process from the bot's main.py, sharing the same MongoDB database. It
implements the Buy / Sell / Bid (24h auction) / Scrap marketplace the bot itself doesn't have
UI for anymore — main.py's /trade, /buy, /sell, /market commands were removed at some point in
the past, leaving only a couple of compatible remnants behind (the harem item "market" status
value, and the remove_one_harem_copy/clear_stale_favorite helpers). This backend picks up that
same "market" status convention so the bot's existing /harem display (which already shows
"normal" vs "market" counts per card) reflects listings created here with no changes needed on
the bot side beyond adding a button that opens this Mini App.

WHY A SEPARATE PROCESS: a Telegram Web App is a real web page Telegram's client loads in its
own browser — it needs an HTTPS URL to load from and a JSON API to call, neither of which a
Telethon bot process provides on its own. This runs alongside main.py (same server, same
database), not instead of it.

ENVIRONMENT VARIABLES REQUIRED (same MONGO_URI / MAIN_BOT_TOKEN as main.py — copy the same
values, don't create new ones):
  MONGO_URI       - same MongoDB connection string main.py uses
  MAIN_BOT_TOKEN  - same bot token main.py uses (needed to verify Telegram's initData signature,
                    AND to fetch card images from the storage channel via Telethon)
  APP_ID          - same Telegram API id main.py uses (for the Telethon client below)
  APP_HASH        - same Telegram API hash main.py uses
  STORAGE_CHANNEL - the chat id character images are stored in (same value as main.py's
                    SPECIFIC_CONTROL_GROUP — see main.py's STORAGE_CHANNEL constant)

See README.md in this folder for how to actually deploy and wire this up to the bot.
"""
import os
import time
import hmac
import hashlib
import json
import asyncio
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager

from fastapi import FastAPI, Header, HTTPException, Request
from fastapi.responses import Response, FileResponse
from fastapi.staticfiles import StaticFiles
from fastapi.middleware.cors import CORSMiddleware
from motor.motor_asyncio import AsyncIOMotorClient
from telethon import TelegramClient
from telethon.errors import RPCError

# ==========================================
# ⚙️ CONFIG — copy the exact same values main.py uses for these, so both processes see the
# same database and can verify/act on the same Telegram account.
# ==========================================
def _require_env(name):
    value = os.environ.get(name)
    if not value:
        raise RuntimeError(f"❌ Missing required environment variable: {name}.")
    return value

MONGO_URI = _require_env("MONGO_URI")
MAIN_BOT_TOKEN = _require_env("MAIN_BOT_TOKEN")
APP_ID = int(_require_env("APP_ID"))
APP_HASH = _require_env("APP_HASH")
STORAGE_CHANNEL = int(_require_env("STORAGE_CHANNEL"))

client_mongo = AsyncIOMotorClient(MONGO_URI, maxPoolSize=10)
db = client_mongo["telegram_bot"]  # same DB name main.py uses — do not change

users_catcher_col = db["users_catcher_data"]      # same collection main.py uses
characters_base_col = db["characters_base_data"]  # same collection main.py uses
bot_settings_col = db["bot_settings"]             # same collection main.py uses (reads ccm_tier_values / ccm_event_values that /setvalue writes)
market_listings_col = db["market_listings"]       # NEW — this backend owns this collection

# A second, lightweight Telethon session, logged in as the SAME bot, used only to fetch card
# images out of the storage channel (see /api/character-image/{char_id} below). This is a
# separate client/session file from main.py's own bot1 — both can be logged in as the same bot
# account simultaneously without conflict (Telegram allows multiple active bot sessions).
telethon_client = TelegramClient("market_webapp_session", APP_ID, APP_HASH)

# ==========================================
# 🎯 RARITY — minimal standalone copy of main.py's rarity tier logic. Kept in sync by hand:
# if you edit RARITY_TIERS/RARITY_EMOJI in main.py, mirror the change here too.
# ==========================================
RARITY_TIERS = ["SUPREME", "CATAPHRACT", "CROSSVERSE", "DIVINE", "MYSTICAL", "LEGENDARY", "RARE", "UNCOMMON", "COMMON"]
RARITY_EMOJI = {
    "SUPREME": "🎞", "CATAPHRACT": "🛡", "CROSSVERSE": "🌌", "DIVINE": "✨",
    "MYSTICAL": "🔮", "LEGENDARY": "🏆", "RARE": "💎", "UNCOMMON": "🍀", "COMMON": "⚪️",
}
RARITY_TIER_TO_NUM = {tier: str(i + 1) for i, tier in enumerate(RARITY_TIERS)}

def classify_rarity(rarity_str):
    if not rarity_str:
        return None
    for tier in RARITY_TIERS:
        if tier in rarity_str.upper():
            return tier
    return None

async def get_ccm_tier_values():
    doc = await bot_settings_col.find_one({"_id": "ccm_tier_values"})
    return (doc or {}).get("values", {})

async def get_ccm_event_values():
    doc = await bot_settings_col.find_one({"_id": "ccm_event_values"})
    return {e["event"]: e["value"] for e in (doc or {}).get("events", []) if e.get("event")}

SCRAP_VALUE_FRACTION = 4  # scrap pays 1/4 of the tier's normal configured value, per owner spec
SCRAPPABLE_TIER_NUMS = {"5", "6", "7", "8", "9"}  # MYSTICAL through COMMON only

async def compute_scrap_value(rarity_str):
    """Scrap payout for one card. Returns (allowed, value):
      - allowed=False for SUPREME/CATAPHRACT/CROSSVERSE/DIVINE (tiers 1-4) — these are meant to
        stay in circulation (traded/kept), not burned, so scrapping them is rejected outright
        rather than just paying 0.
      - allowed=True for MYSTICAL through COMMON (tiers 5-9), paying 1/4 of that tier's normal
        configured [min,max] range (the same table /setvalue's bulk command manages for catch
        rewards) — never the SUPREME event-price table, since SUPREME can't reach this branch
        at all.
    """
    tier = classify_rarity(rarity_str)
    num = RARITY_TIER_TO_NUM.get(tier)
    if not num or num not in SCRAPPABLE_TIER_NUMS:
        return False, 0
    rng = (await get_ccm_tier_values()).get(num)
    if not rng:
        return True, 0
    lo, hi = int(rng.get("min", 0)), int(rng.get("max", 0))
    if hi < lo:
        lo, hi = hi, lo
    import random
    full_value = random.randint(lo, hi) if hi > 0 else 0
    return True, full_value // SCRAP_VALUE_FRACTION

def is_scrappable(rarity_str):
    tier = classify_rarity(rarity_str)
    num = RARITY_TIER_TO_NUM.get(tier)
    return bool(num and num in SCRAPPABLE_TIER_NUMS)

async def try_deduct_ccm(user_id, amount):
    """Same atomic, race-safe debit as main.py's try_deduct_ccm — only succeeds if user_id
    currently has enough. Duplicated here (not imported) since this is a separate process; if
    you change main.py's version, mirror the change here too."""
    result = await users_catcher_col.find_one_and_update(
        {"user_id": user_id, "ccm_balance": {"$gte": amount}},
        {"$inc": {"ccm_balance": -amount}}
    )
    return result is not None

async def mark_one_harem_copy(user_id, char_id, from_status, to_status):
    """Atomically flips exactly ONE harem entry matching (char_id, from_status) to to_status —
    e.g. "vault" -> "market" when listing, or "market" -> "vault" when cancelling/expiring
    unsold. Same positional-$ technique as main.py's remove_one_harem_copy, for the same
    reason: only one array element should ever be touched, even if the owner has several
    copies of the same char_id."""
    result = await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": {"char_id": char_id, "status": from_status}}},
        {"$set": {"harem.$.status": to_status}}
    )
    return result.modified_count > 0

async def remove_one_harem_copy(user_id, char_id, status):
    """Same as main.py's own helper of this name — duplicated here since this is a separate
    process. Used when a sold/scrapped card needs to actually leave the seller's harem array
    (rather than just changing its status)."""
    await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": {"char_id": char_id, "status": status}}},
        {"$unset": {"harem.$": 1}}
    )
    await users_catcher_col.update_one({"user_id": user_id}, {"$pull": {"harem": None}})

async def add_harem_copy(user_id, char_id, rarity):
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$push": {"harem": {"char_id": char_id, "caught_date": time.time(), "rarity": rarity, "status": "vault"}}},
        upsert=True
    )

# ==========================================
# 🔐 TELEGRAM WEB APP AUTH — verifies Telegram's initData signature so a request can be
# trusted to really be from the Telegram user it claims, not something forged by opening the
# same URL in a normal browser. See: https://core.telegram.org/bots/webapps#validating-data
# ==========================================
AUTH_MAX_AGE_SECONDS = 86400  # reject initData older than this (replay-window, not a session length)

def verify_init_data(init_data: str):
    """Returns the authenticated user dict {id, first_name, username, ...} or raises
    HTTPException(401) if the signature doesn't check out or it's too old."""
    if not init_data:
        raise HTTPException(401, "Missing Telegram auth data.")
    try:
        parsed = dict(parse_qsl(init_data, strict_parsing=True))
    except ValueError:
        raise HTTPException(401, "Malformed auth data.")
    received_hash = parsed.pop("hash", None)
    if not received_hash:
        raise HTTPException(401, "Missing auth signature.")
    data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
    secret_key = hmac.new(b"WebAppData", MAIN_BOT_TOKEN.encode(), hashlib.sha256).digest()
    computed_hash = hmac.new(secret_key, data_check_string.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(computed_hash, received_hash):
        raise HTTPException(401, "Invalid auth signature.")
    auth_date = int(parsed.get("auth_date", 0))
    if time.time() - auth_date > AUTH_MAX_AGE_SECONDS:
        raise HTTPException(401, "Auth data expired — reopen the app from the bot.")
    try:
        user = json.loads(parsed.get("user", "{}"))
    except json.JSONDecodeError:
        raise HTTPException(401, "Malformed user data.")
    if not user.get("id"):
        raise HTTPException(401, "No user in auth data.")
    return user

async def get_authed_user(x_telegram_init_data: str = Header(default="")):
    """FastAPI dependency — every endpoint below that needs to know WHO is calling takes this
    as a parameter, e.g. `user = Depends(get_authed_user)`."""
    return verify_init_data(x_telegram_init_data)

# ==========================================
# ⏰ AUCTION SETTLEMENT — background task, runs continuously in this process. An auction
# that's past its expires_at gets settled the next time this loop wakes up (checked every 30s,
# not instantly on the second it expires — a short delay here is harmless and far simpler than
# scheduling exact-time callbacks per-auction).
# ==========================================
async def auction_settlement_loop():
    while True:
        try:
            now = time.time()
            expired = await market_listings_col.find({
                "type": "auction", "status": "active", "expires_at": {"$lte": now}
            }).to_list(length=None)
            for listing in expired:
                seller_id = listing["seller_id"]
                char_id = listing["char_id"]
                rarity = listing.get("rarity")
                winner_id = listing.get("current_bidder_id")
                winning_bid = listing.get("current_bid")
                if winner_id and winning_bid:
                    # Someone won — card to them, escrowed ccm to the seller (the winner's ccm
                    # was already deducted/escrowed at bid time, see /api/market/bid below, so
                    # this is a payout, not a fresh charge).
                    await remove_one_harem_copy(seller_id, char_id, "market")
                    await add_harem_copy(winner_id, char_id, rarity)
                    await users_catcher_col.update_one(
                        {"user_id": seller_id}, {"$inc": {"ccm_balance": winning_bid}}, upsert=True
                    )
                    await market_listings_col.update_one(
                        {"_id": listing["_id"]}, {"$set": {"status": "sold", "settled_at": now}}
                    )
                else:
                    # No bids — card just goes back to the seller's vault, nothing to pay out.
                    await mark_one_harem_copy(seller_id, char_id, "market", "vault")
                    await market_listings_col.update_one(
                        {"_id": listing["_id"]}, {"$set": {"status": "expired", "settled_at": now}}
                    )
        except Exception as e:
            print(f"auction_settlement_loop error: {e}")
        await asyncio.sleep(30)

@asynccontextmanager
async def lifespan(app: FastAPI):
    await telethon_client.start(bot_token=MAIN_BOT_TOKEN)
    await market_listings_col.create_index("status")
    await market_listings_col.create_index([("type", 1), ("status", 1), ("expires_at", 1)])
    await market_listings_col.create_index("seller_id")
    await market_listings_col.create_index("current_bidder_id")
    settlement_task = asyncio.create_task(auction_settlement_loop())
    yield
    settlement_task.cancel()
    await telethon_client.disconnect()

app = FastAPI(lifespan=lifespan)
app.add_middleware(
    CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"],
)  # Telegram's in-app browser is picky about this even though the page and API share an origin
   # in normal deployment — harmless to leave open since every write endpoint below is still
   # gated by verify_init_data regardless of where the request came from.

# ==========================================
# 🖼️ CARD IMAGE PROXY — a browser <img> tag can't fetch a Telegram file directly (there's no
# public URL for it), so this endpoint fetches the character's stored photo/video via Telethon
# and streams the bytes back with a normal image content-type. Cached in memory after the
# first fetch per char_id, since character art never changes after /addchar.
# ==========================================
_image_cache = {}  # char_id -> (bytes, content_type)

@app.get("/api/character-image/{char_id}")
async def character_image(char_id: str):
    if char_id in _image_cache:
        data, content_type = _image_cache[char_id]
        return Response(content=data, media_type=content_type)
    char = await characters_base_col.find_one({"char_id": char_id})
    if not char or not char.get("storage_msg_id"):
        raise HTTPException(404, "No image for this character.")
    try:
        msg = await telethon_client.get_messages(STORAGE_CHANNEL, ids=char["storage_msg_id"])
        if not msg or not (msg.photo or msg.video):
            raise HTTPException(404, "Stored message has no image/video.")
        data = await msg.download_media(file=bytes)
        content_type = "video/mp4" if msg.video else "image/jpeg"
        _image_cache[char_id] = (data, content_type)
        return Response(content=data, media_type=content_type)
    except RPCError as e:
        raise HTTPException(502, f"Couldn't fetch image from Telegram: {e}")

# ==========================================
# 👤 ME — balance + basic identity
# ==========================================
@app.get("/api/me")
async def api_me(user=None, x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    user_id = user["id"]
    doc = await users_catcher_col.find_one({"user_id": user_id})
    return {
        "user_id": user_id,
        "name": user.get("first_name", "Hunter"),
        "ccm_balance": (doc or {}).get("ccm_balance", 0),
    }

# ==========================================
# 🎴 MY CARDS — vault-status (available, not currently listed) cards, grouped by char_id
# ==========================================
@app.get("/api/my-cards")
async def api_my_cards(x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    doc = await users_catcher_col.find_one({"user_id": user["id"]})
    harem = (doc or {}).get("harem", [])
    counts = {}
    for item in harem:
        if isinstance(item, dict) and item.get("status", "vault") == "vault" and item.get("char_id"):
            cid = item["char_id"]
            counts[cid] = counts.get(cid, 0) + 1
    if not counts:
        return {"cards": []}
    chars = await characters_base_col.find(
        {"char_id": {"$in": list(counts.keys())}},
        {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "event": 1, "_id": 0}
    ).to_list(length=None)
    return {"cards": [
        {**c, "quantity": counts[c["char_id"]], "rarity_tier": classify_rarity(c.get("rarity")),
         "scrappable": is_scrappable(c.get("rarity"))}
        for c in chars
    ]}

# ==========================================
# 🏪 MARKET — browse active listings
# ==========================================
@app.get("/api/market")
async def api_market():
    listings = await market_listings_col.find({"status": "active"}).sort("created_at", -1).to_list(length=500)
    char_ids = list({l["char_id"] for l in listings})
    chars = {
        c["char_id"]: c for c in await characters_base_col.find(
            {"char_id": {"$in": char_ids}}, {"char_id": 1, "name": 1, "category": 1, "rarity": 1, "_id": 0}
        ).to_list(length=None)
    }
    now = time.time()
    out = []
    for l in listings:
        c = chars.get(l["char_id"], {})
        out.append({
            "listing_id": str(l["_id"]),
            "char_id": l["char_id"],
            "name": c.get("name", "?"),
            "category": c.get("category", "?"),
            "rarity_tier": classify_rarity(c.get("rarity")),
            "seller_id": l["seller_id"],
            "type": l["type"],
            "price": l.get("price"),
            "current_bid": l.get("current_bid"),
            "bid_count": len(l.get("bids", [])),
            "seconds_left": max(0, int(l["expires_at"] - now)) if l.get("expires_at") else None,
        })
    return {"listings": out}

# ==========================================
# 📤 LIST — put one vault-status copy up for sale or auction
# ==========================================
@app.post("/api/market/list")
async def api_market_list(payload: dict, x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    user_id = user["id"]
    char_id = payload.get("char_id")
    listing_type = payload.get("type")  # "buy_now" | "auction"
    price = payload.get("price")
    if listing_type not in ("buy_now", "auction"):
        raise HTTPException(400, "type must be buy_now or auction.")
    if not isinstance(price, int) or price < 1:
        raise HTTPException(400, "price must be a positive whole number.")

    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = (doc or {}).get("harem", [])
    item = next((it for it in harem if isinstance(it, dict) and it.get("char_id") == char_id and it.get("status", "vault") == "vault"), None)
    if not item:
        raise HTTPException(400, "You don't have a spare copy of that card to list.")

    if not await mark_one_harem_copy(user_id, char_id, "vault", "market"):
        raise HTTPException(409, "Couldn't reserve that card — try again.")

    now = time.time()
    listing = {
        "seller_id": user_id,
        "char_id": char_id,
        "rarity": item.get("rarity"),
        "type": listing_type,
        "price": price,
        "current_bid": price if listing_type == "auction" else None,
        "current_bidder_id": None,
        "bids": [],
        "created_at": now,
        "expires_at": (now + 86400) if listing_type == "auction" else None,  # 24h, fixed, per owner spec
        "status": "active",
    }
    result = await market_listings_col.insert_one(listing)
    return {"listing_id": str(result.inserted_id)}

# ==========================================
# 💸 BUY NOW
# ==========================================
@app.post("/api/market/buy")
async def api_market_buy(payload: dict, x_telegram_init_data: str = Header(default="")):
    from bson import ObjectId
    user = verify_init_data(x_telegram_init_data)
    buyer_id = user["id"]
    listing = await market_listings_col.find_one({"_id": ObjectId(payload.get("listing_id")), "status": "active", "type": "buy_now"})
    if not listing:
        raise HTTPException(404, "Listing not found or no longer available.")
    if listing["seller_id"] == buyer_id:
        raise HTTPException(400, "You can't buy your own listing.")

    claimed = await market_listings_col.find_one_and_update(
        {"_id": listing["_id"], "status": "active"}, {"$set": {"status": "sold_pending"}}
    )
    if not claimed:
        raise HTTPException(409, "Someone else just bought this.")

    if not await try_deduct_ccm(buyer_id, listing["price"]):
        await market_listings_col.update_one({"_id": listing["_id"]}, {"$set": {"status": "active"}})
        raise HTTPException(402, "Not enough ccm.")

    await remove_one_harem_copy(listing["seller_id"], listing["char_id"], "market")
    await add_harem_copy(buyer_id, listing["char_id"], listing.get("rarity"))
    await users_catcher_col.update_one(
        {"user_id": listing["seller_id"]}, {"$inc": {"ccm_balance": listing["price"]}}, upsert=True
    )
    await market_listings_col.update_one({"_id": listing["_id"]}, {"$set": {"status": "sold", "settled_at": time.time()}})
    return {"ok": True}

# ==========================================
# 🔨 BID — raises the current auction price; outbid bidders are refunded automatically
# ==========================================
@app.post("/api/market/bid")
async def api_market_bid(payload: dict, x_telegram_init_data: str = Header(default="")):
    from bson import ObjectId
    user = verify_init_data(x_telegram_init_data)
    bidder_id = user["id"]
    amount = payload.get("amount")
    listing = await market_listings_col.find_one({"_id": ObjectId(payload.get("listing_id")), "status": "active", "type": "auction"})
    if not listing:
        raise HTTPException(404, "Auction not found or already ended.")
    if listing["seller_id"] == bidder_id:
        raise HTTPException(400, "You can't bid on your own auction.")
    if listing.get("expires_at", 0) <= time.time():
        raise HTTPException(400, "This auction just ended.")
    min_next_bid = listing["current_bid"] + 1 if listing.get("current_bidder_id") else listing["current_bid"]
    if not isinstance(amount, int) or amount < min_next_bid:
        raise HTTPException(400, f"Bid must be at least {min_next_bid:,} ccm.")

    # 💰 ESCROW: the new bidder's ccm is reserved NOW (atomic, race-safe) — not just at auction
    # end — so nobody can bid beyond what they actually have, across any number of auctions at
    # once. The PREVIOUS highest bidder (if any) gets their own escrowed amount refunded here,
    # having just been outbid.
    if not await try_deduct_ccm(bidder_id, amount):
        raise HTTPException(402, "Not enough ccm for that bid.")

    updated = await market_listings_col.find_one_and_update(
        {"_id": listing["_id"], "status": "active", "current_bid": listing["current_bid"]},
        {
            "$set": {"current_bid": amount, "current_bidder_id": bidder_id},
            "$push": {"bids": {"bidder_id": bidder_id, "amount": amount, "time": time.time()}},
        }
    )
    if not updated:
        # Someone else's bid landed in the same instant — refund this bid, tell them to retry.
        await users_catcher_col.update_one({"user_id": bidder_id}, {"$inc": {"ccm_balance": amount}})
        raise HTTPException(409, "Someone just outbid you — refresh and try again.")

    prev_bidder = listing.get("current_bidder_id")
    prev_amount = listing.get("current_bid")
    if prev_bidder and prev_amount:
        await users_catcher_col.update_one({"user_id": prev_bidder}, {"$inc": {"ccm_balance": prev_amount}}, upsert=True)
    return {"ok": True}

# ==========================================
# 🚫 CANCEL — seller pulls their own active listing back
# ==========================================
@app.post("/api/market/cancel")
async def api_market_cancel(payload: dict, x_telegram_init_data: str = Header(default="")):
    from bson import ObjectId
    user = verify_init_data(x_telegram_init_data)
    listing = await market_listings_col.find_one({"_id": ObjectId(payload.get("listing_id")), "status": "active"})
    if not listing:
        raise HTTPException(404, "Listing not found.")
    if listing["seller_id"] != user["id"]:
        raise HTTPException(403, "That's not your listing.")
    if listing["type"] == "auction" and listing.get("current_bidder_id"):
        raise HTTPException(400, "Can't cancel — this auction already has a bid.")
    await mark_one_harem_copy(listing["seller_id"], listing["char_id"], "market", "vault")
    await market_listings_col.update_one({"_id": listing["_id"]}, {"$set": {"status": "cancelled"}})
    return {"ok": True}

# ==========================================
# 🔥 SCRAP — burn one vault-status copy for ccm, no listing involved
# ==========================================
@app.post("/api/market/scrap")
async def api_market_scrap(payload: dict, x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    user_id = user["id"]
    char_id = payload.get("char_id")
    doc = await users_catcher_col.find_one({"user_id": user_id})
    harem = (doc or {}).get("harem", [])
    item = next((it for it in harem if isinstance(it, dict) and it.get("char_id") == char_id and it.get("status", "vault") == "vault"), None)
    if not item:
        raise HTTPException(400, "You don't have a spare copy of that card to scrap.")
    allowed, value = await compute_scrap_value(item.get("rarity"))
    if not allowed:
        raise HTTPException(400, "This rarity is too valuable to scrap — Divine and above can only be sold or auctioned.")
    if not await remove_one_harem_copy_if_exists(user_id, char_id):
        raise HTTPException(409, "Couldn't scrap that card — try again.")
    if value > 0:
        await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"ccm_balance": value}})
    return {"ccm_earned": value}

async def remove_one_harem_copy_if_exists(user_id, char_id):
    result = await users_catcher_col.update_one(
        {"user_id": user_id, "harem": {"$elemMatch": {"char_id": char_id, "status": "vault"}}},
        {"$unset": {"harem.$": 1}}
    )
    if result.modified_count:
        await users_catcher_col.update_one({"user_id": user_id}, {"$pull": {"harem": None}})
    return result.modified_count > 0

# ==========================================
# 📋 MY LISTINGS / MY BIDS
# ==========================================
@app.get("/api/my-listings")
async def api_my_listings(x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    listings = await market_listings_col.find({"seller_id": user["id"], "status": "active"}).to_list(length=None)
    return {"listings": [{**l, "_id": str(l["_id"])} for l in listings]}

@app.get("/api/my-bids")
async def api_my_bids(x_telegram_init_data: str = Header(default="")):
    user = verify_init_data(x_telegram_init_data)
    listings = await market_listings_col.find({"status": "active", "current_bidder_id": user["id"]}).to_list(length=None)
    return {"listings": [{**l, "_id": str(l["_id"])} for l in listings]}

# ==========================================
# 📁 STATIC FILES — the Mini App page itself
# ==========================================
app.mount("/static", StaticFiles(directory=os.path.join(os.path.dirname(__file__), "static")), name="static")

@app.get("/")
async def index():
    return FileResponse(os.path.join(os.path.dirname(__file__), "static", "index.html"))
