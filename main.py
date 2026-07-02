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
from telethon import TelegramClient, events, errors, functions, Button
from telethon.sessions import StringSession
from motor.motor_asyncio import AsyncIOMotorClient
from pymongo import ReturnDocument
from deep_translator import GoogleTranslator

load_dotenv()

# ==========================================
# ⚙️ CONFIGURATION (from environment)
# ==========================================
MONGO_URI = os.getenv("MONGO_URI")
APP_ID = int(os.getenv("APP_ID"))
APP_HASH = os.getenv("APP_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
OWNER_ID = int(os.getenv("OWNER_ID"))
SPECIFIC_GROUP = int(os.getenv("SPECIFIC_GROUP"))
SPAWN_BOT_ID = int(os.getenv("SPAWN_BOT_ID", 6157455819))
HINT_BOT_ID = int(os.getenv("HINT_BOT_ID", 8506436817))
WAIFU_CHAT_ID = int(os.getenv("WAIFU_CHAT_ID", -1003834579058))

# Global states
spawn_tracker = {}
last_spawn_chat_id = None
HINT_REGEX = re.compile(r"(/catch\s+[^\n]+)")
is_catch_stopped = False
is_active = False
SYMBOLS = ["🍒", "🍋", "🔔", "💎", "7️⃣"]

# MongoDB
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]

tomboy_col = db["tomboy_col"]
reply_save_col = db["reply_save_col"]
tomgaygp_col = db["tomgaygp_col"]
users_catcher_col = db["users_catcher_data"]
characters_base_col = db["characters_base_data"]
groups_config_col = db["groups_catcher_config"]
groups_col = db["active_groups"]
banned_users_col = db["banned_users"]
groups_counters_col = db["groups_msg_counters"]
spawn_disabled_col = db["spawn_disabled_chats"]   # new collection for spawn toggle

# Event loop
loop = asyncio.new_event_loop()
asyncio.set_event_loop(loop)

# Telegram clients
bot = TelegramClient('official_bot_session', APP_ID, APP_HASH, loop=loop)
userbot = None

STORAGE_CHANNEL = SPECIFIC_GROUP

# ==========================================
# 🔧 HELPERS (with tagline)
# ==========================================
TAGLINE = "\n\nAlso try this @Imjustkidding_bot"

def bq(text):
    return f"<blockquote><b>{text}</b></blockquote>"

async def reply_tag(event, text, **kwargs):
    if TAGLINE not in text:
        text += TAGLINE
    await event.reply(text, **kwargs)

async def send_tag(client, chat_id, text, **kwargs):
    if TAGLINE not in text:
        text += TAGLINE
    while True:
        try:
            return await client.send_message(chat_id, text, **kwargs)
        except errors.FloodWaitError as e:
            await asyncio.sleep(e.seconds)
        except Exception as e:
            logging.error(f"send_tag error: {e}")
            raise

async def edit_tag(client, entity, message, text, **kwargs):
    if TAGLINE not in text:
        text += TAGLINE
    while True:
        try:
            return await client.edit_message(entity, message, text, **kwargs)
        except errors.FloodWaitError as e:
            await asyncio.sleep(e.seconds)
        except errors.MessageNotModifiedError:
            return
        except Exception as e:
            logging.error(f"edit_tag error: {e}")
            raise

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
                "rarity_counts": {"Bear":0, "Rainbow":0, "Crossverse":0, "Trident":0, "Koinobori":0, "Medium":0, "Lower":0}
            }
        },
        upsert=True
    )

# ---------- wallet ----------
async def get_balance(user_id):
    doc = await users_catcher_col.find_one({"user_id": user_id})
    if not doc:
        await users_catcher_col.insert_one({"user_id": user_id, "wallet_balance": 0, "total_caught": 0, "harem": []})
        return 0
    return doc.get("wallet_balance", 0)

async def set_balance(user_id, amount):
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"wallet_balance": amount}}, upsert=True)

async def add_balance(user_id, amount):
    await users_catcher_col.update_one({"user_id": user_id}, {"$inc": {"wallet_balance": amount}}, upsert=True)

# ---------- rarity ----------
RARITY_TIERS = [
    {"name":"Bear","emoji":"🧸","value":1000},
    {"name":"Rainbow","emoji":"🌈","value":800},
    {"name":"Crossverse","emoji":"⚡️","value":600},
    {"name":"Trident","emoji":"🔱","value":400},
    {"name":"Koinobori","emoji":"🎏","value":200},
    {"name":"Medium","emoji":"💛","value":100},
    {"name":"Lower","emoji":"💜","value":50}
]
RARITY_EMOJI = {t["name"]: t["emoji"] for t in RARITY_TIERS}
RARITY_ORDER = {t["name"]: idx for idx, t in enumerate(RARITY_TIERS)}

def classify_rarity(rarity_str):
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
# 🌍 DUMMY HTTP SERVER
# ==========================================
async def handle_render_health_check(reader, writer):
    await reader.read(100)
    response = "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nOK"
    writer.write(response.encode('utf-8'))
    await writer.drain()
    writer.close()

async def start_dummy_web_server():
    port = int(os.environ.get("PORT", 10000))
    try:
        server = await asyncio.start_server(handle_render_health_check, '0.0.0.0', port)
        print(f"🌍 Dummy HTTP Server started on port {port} for Render Health Check!")
        async with server:
            await server.serve_forever()
    except Exception as e:
        print(f"❌ Failed to start Dummy Web Server: {e}")

# ==========================================
# 🎯 USERBOT SNIPER (unchanged)
# ==========================================
async def delete_catch_message_delayed(client, chat_id, msg_id):
    try:
        await asyncio.sleep(1)
        await client.delete_messages(chat_id, msg_id)
    except Exception:
        pass

async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker, is_catch_stopped
    if is_catch_stopped:
        return
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in event.text:
            if event.chat_id in [-1001947407820, -1003067509608]:
                return
            if any(emoji in event.text for emoji in ["🔵", "🟣", "🟡", "🟠", "💮"]):
                return
            orig_chat_id = event.chat_id
            last_spawn_chat_id = orig_chat_id
            try:
                fwd_msg = await event.message.forward_to(WAIFU_CHAT_ID)
                reply_msg = await fwd_msg.reply("/waifu")
                spawn_tracker[fwd_msg.id] = orig_chat_id
                spawn_tracker[reply_msg.id] = orig_chat_id
                if len(spawn_tracker) > 100:
                    spawn_tracker.pop(next(iter(spawn_tracker)))
            except Exception:
                pass

async def hint_solver_handler(event):
    global last_spawn_chat_id, spawn_tracker, is_catch_stopped
    if is_catch_stopped:
        return
    if event.chat_id == WAIFU_CHAT_ID and event.sender_id == HINT_BOT_ID and event.text:
        match = HINT_REGEX.search(event.text)
        if match:
            catch_command = match.group(1).strip(" `\n\r")
            target_group = last_spawn_chat_id
            if event.reply_to_msg_id and event.reply_to_msg_id in spawn_tracker:
                target_group = spawn_tracker[event.reply_to_msg_id]
            if target_group:
                if target_group in [-1001947407820, -1003067509608]:
                    return
                try:
                    delay_time = random.uniform(0.5, 0.6)
                    async with event.client.action(target_group, 'typing'):
                        await asyncio.sleep(delay_time)
                    sent_msg = await event.client.send_message(target_group, catch_command)
                    asyncio.create_task(delete_catch_message_delayed(event.client, target_group, sent_msg.id))
                except Exception:
                    pass

async def catch_success_forwarder_handler(event):
    global is_catch_stopped
    if is_catch_stopped:
        return
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!" in event.text and event.message.mentioned:
            try:
                await event.message.forward_to(SPECIFIC_GROUP)
            except Exception:
                pass

async def mass_broadcast_handler(event):
    if event.text and event.text.strip() == '/ပို့' and event.is_reply:
        if event.chat_id == 'me' or event.chat_id == SPECIFIC_GROUP:
            target_msg = await event.get_reply_message()
            await event.delete()
            status_msg = await event.client.send_message(event.chat_id, "🔄 **Mass Broadcast လုပ်ငန်းစဉ် စတင်နေပါပြီ...**")
            success_count = 0
            fail_count = 0
            dialogs = await event.client.get_dialogs()
            for dialog in dialogs:
                if dialog.is_group:
                    if dialog.id == event.chat_id:
                        continue
                    try:
                        await event.client.send_message(dialog.id, target_msg)
                        success_count += 1
                        await asyncio.sleep(random.uniform(2.5, 4.5))
                    except errors.FloodWaitError as e:
                        print(f"⚠️ FloodWait {e.seconds}s")
                        await asyncio.sleep(e.seconds)
                        try:
                            await event.client.send_message(dialog.id, target_msg)
                            success_count += 1
                        except Exception:
                            fail_count += 1
                    except Exception:
                        fail_count += 1
            report_text = (
                f"📊 **Broadcast လုပ်ငန်းစဉ် ပြီးဆုံးပါပြီ Chief!**\n\n"
                f"✅ ပို့ဆောင်မှု အောင်မြင်သော Group: `{success_count}` ခု\n"
                f"❌ စာဖျက်ခံရ/ပို့မရသော Group: `{fail_count}` ခု\n"
                f"📈 စုစုပေါင်း အောင်မြင်မှုအရေအတွက်: `{success_count}` ခု ရှိနေပါသည်။"
            )
            await status_msg.edit(report_text)

# ==========================================
# ⚡ SYSTEM 1: AUTO-TEXT CALCULATOR
# ==========================================
@bot.on(events.NewMessage)
async def auto_text_calculator(event):
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
            reply_text = f"`{text} = {result}`\n\n📣 For support - @Rashxdl"
            await reply_tag(event, reply_text)
        except Exception:
            pass

# ==========================================
# ⚡ SYSTEM 2: INTERACTIVE CALCULATOR
# ==========================================
def calc_keyboard(user_id):
    return [
        [Button.inline("C", f"C_{user_id}"), Button.inline("⌫", f"back_{user_id}"), Button.inline("(", f"(_{user_id}"), Button.inline(")", f")_{user_id}")],
        [Button.inline("7", f"7_{user_id}"), Button.inline("8", f"8_{user_id}"), Button.inline("9", f"9_{user_id}"), Button.inline("÷", f"/_{user_id}")],
        [Button.inline("4", f"4_{user_id}"), Button.inline("5", f"5_{user_id}"), Button.inline("6", f"6_{user_id}"), Button.inline("×", f"*_{user_id}")],
        [Button.inline("1", f"1_{user_id}"), Button.inline("2", f"2_{user_id}"), Button.inline("3", f"3_{user_id}"), Button.inline("-", f"-_{user_id}")],
        [Button.inline("0", f"0_{user_id}"), Button.inline(".", f"._{user_id}"), Button.inline("=", f"=_{user_id}"), Button.inline("+", f"+_{user_id}")]
    ]

@bot.on(events.NewMessage(pattern=r'(?i)^/calc'))
async def start_calc(event):
    user_id = event.sender_id
    user = await event.get_sender()
    first_name = user.first_name if user else "User"
    text = (
        f"📱 **INTERACTIVE CALCULATOR**\n"
        f"👤 **Owner:** [{first_name}](tg://user?id={user_id})\n"
    )
    if event.is_private:
        text += f"💼 For business - @Rashxdl\n💡 Use \" + - * / \"\n"
    text += f"🔢 **Expression:** `0`\n\n📣 For support - @Rashxdl"
    await event.respond(text + TAGLINE, buttons=calc_keyboard(user_id))

@bot.on(events.CallbackQuery)
async def global_callback_handler(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    msg = await event.get_message()
    if "_" in data:
        action, allowed_user_id = data.split("_", 1)
        try:
            allowed_user_id = int(allowed_user_id)
        except ValueError:
            return
    else:
        action = data
        allowed_user_id = None

    if allowed_user_id and event.sender_id != allowed_user_id:
        await event.answer("⚠️ ဒီ Calculator က တခြားသူ ဖွင့်ထားတာမို့လို့ မင်းနှိပ်လို့မရပါဘူးခင်ဗျာ။", alert=True)
        return

    match = re.search(r'`([^`]*)`', msg.text)
    if match:
        current_expr = match.group(1).strip()
    else:
        current_expr = "0"
    if current_expr == "0":
        current_expr = ""

    if action == "C":
        new_expr = "0"
    elif action == "back":
        new_expr = current_expr[:-1] if len(current_expr) > 0 else "0"
        if not new_expr:
            new_expr = "0"
    elif action == "=":
        if "=" in current_expr or "Error" in current_expr:
            await event.answer()
            return
        try:
            math_expr = current_expr.replace("÷", "/").replace("×", "*")
            if any(char not in "0123456789+-*/(). " for char in math_expr):
                raise ValueError()
            result = eval(math_expr, {"__builtins__": None}, {})
            new_expr = f"{current_expr} = {result}"
        except Exception:
            new_expr = "Error"
    else:
        if "Error" in current_expr or "=" in current_expr:
            if action in ["+", "-", "/", "*"]:
                try:
                    current_expr = current_expr.split("=")[1].strip()
                except:
                    current_expr = ""
            else:
                current_expr = ""
        new_expr = current_expr + action

    display_expr = new_expr.replace("/", "÷").replace("*", "×")
    if not display_expr:
        display_expr = "0"

    try:
        lines = msg.text.split("\n")
        owner_line = [l for l in lines if "Owner:" in l][0]
    except Exception:
        owner_line = "👤 **Owner:** User"

    new_text = (
        f"📱 **INTERACTIVE CALCULATOR**\n"
        f"{owner_line}\n"
    )
    if event.is_private:
        new_text += f"💼 For business - @Rashxdl\n💡 Use \" + - * / \"\n"
    new_text += f"🔢 **Expression:** `{display_expr}`\n\n📣 For support - @Rashxdl"
    if not new_text.endswith(TAGLINE):
        new_text += TAGLINE

    if msg.text != new_text:
        try:
            await event.edit(new_text, buttons=calc_keyboard(allowed_user_id))
        except Exception:
            pass
    await event.answer()

# ==========================================
# ⚡ SYSTEM 3: TRANSLATION
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^/tr(.*)'))
async def translate_to_english(event):
    text_to_translate = event.pattern_match.group(1).strip()
    if not text_to_translate and event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg and reply_msg.text:
            text_to_translate = reply_msg.text
    if not text_to_translate:
        await reply_tag(event, "❌ **အသုံးပြုပုံ:**\n1. `/tr မင်္ဂလာပါ` (စာတိုက်ရိုက်ရိုက်ပြီး ပြန်ခြင်း)\n2. တခြားသူစာကို Reply ပြန်ပြီး `/tr` ဟု ရိုက်ခြင်း")
        return
    try:
        translated_text = GoogleTranslator(source='auto', target='en').translate(text_to_translate)
        reply_text = f"🔤 **Translated to English:**\n\n`{translated_text}`\n\n📣 For support - @Rashxdl"
        await reply_tag(event, reply_text)
    except Exception as e:
        logging.error(f"Translation Error: {e}")
        await reply_tag(event, "⚠️ ဘာသာပြန်ရတာ အဆင်မပြေဖြစ်သွားပါတယ်။ ခဏနေမှ ပြန်ကြိုးစားကြည့်ပါ။")

# ==========================================
# 🎰 SLOT GAME
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^/balance'))
async def balance_handler(event):
    user_id = event.sender_id
    bal = await get_balance(user_id)
    await reply_tag(event, f"💰 **Balance:** {bal:,} MMK")

@bot.on(events.NewMessage(pattern=r'(?i)^/slot(?:\s+(\d+))?'))
async def slot_handler(event):
    args = event.pattern_match.group(1)
    if not args:
        await reply_tag(event, "🎰 **Usage:** `/slot <amount>`")
        return
    try:
        bet = int(args.strip())
    except ValueError:
        await reply_tag(event, "❌ **Invalid amount.**")
        return
    user_id = event.sender_id
    balance = await get_balance(user_id)
    if bet <= 0:
        return
    if balance < bet:
        await reply_tag(event, "❌ **Not enough balance.**")
        return
    await add_balance(user_id, -bet)
    status_msg = await event.reply("🎰 **[ 🔄 | 🔄 | 🔄 ]**\n\n*Reels are spinning...* 🎰")
    for _ in range(3):
        await asyncio.sleep(0.5)
        fake_reels = [random.choice(SYMBOLS) for _ in range(3)]
        try:
            await status_msg.edit(f"🎰 **[ {' | '.join(fake_reels)} ]**\n\n*Spinning...* 🔄")
        except Exception:
            pass
    reels = [random.choice(SYMBOLS) for _ in range(3)]
    payout = 0
    if reels == ["7️⃣", "7️⃣", "7️⃣"]:
        payout = bet * 5
    elif reels[0] == reels[1] == reels[2]:
        payout = bet * 2
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]:
        payout = bet * 1.5
    if payout > 0:
        await add_balance(user_id, payout)
    win_status = f"🎉 **Win:** +{payout:,} MMK" if payout > 0 else "😭 **You Lost!**"
    final_text = (
        f"🎰 **[ {' | '.join(reels)} ]**\n\n"
        f"💵 **Bet:** {bet:,} MMK\n"
        f"{win_status}\n"
        f"💰 **Balance:** {await get_balance(user_id):,} MMK"
    )
    try:
        await status_msg.edit(final_text + TAGLINE)
    except Exception:
        await reply_tag(event, final_text)

# ==========================================
# 🎁 DAILY REWARD
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^[./]daily(?:@\w+)?$'))
async def daily_reward_handler(event):
    user_id = event.sender_id
    current_time = time.time()
    doc = await users_catcher_col.find_one({"user_id": user_id})
    last_daily = doc.get("last_daily", 0) if doc else 0
    balance = doc.get("wallet_balance", 0) if doc else 0
    cooldown = 86400
    elapsed_time = current_time - last_daily
    if elapsed_time < cooldown:
        remaining_time = cooldown - elapsed_time
        hours = int(remaining_time // 3600)
        minutes = int((remaining_time % 3600) // 60)
        seconds = int(remaining_time % 60)
        await reply_tag(event,
            f"❌ **Daily Reward ကို ရယူပြီးသား ဖြစ်နေပါတယ်!**\n\n"
            f"⏳ နောက်တစ်ကြိမ် ထပ်မံရယူနိုင်ရန် စောင့်ဆိုင်းရန်အချိန် -\n"
            f"👉 `{hours:02d} နာရီ {minutes:02d} မိနစ် {seconds:02d} စက္ကန့်` ကျန်ပါသေးသည်။"
        )
        return
    new_balance = balance + 50000
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$set": {"wallet_balance": new_balance, "last_daily": current_time}},
        upsert=True
    )
    await reply_tag(event,
        f"🎉 **Daily Reward အောင်မြင်စွာ ရယူပြီးပါပြီ!**\n\n"
        f"🎁 ယနေ့အတွက် ဆုကြေး: `50,000` MMK\n"
        f"💰 သင့်ရဲ့ လက်ရှိ စုစုပေါင်းကျန်ငွေ: `{new_balance:,}` MMK"
    )

# ==========================================
# 👑 OWNER BALANCE COMMANDS
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^/deposit(?:\s+(\d+)\s+(\d+))?'))
async def deposit_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1) or not match.group(2):
        await reply_tag(event, "⚠️ **Usage:** `/deposit <user_id> <amount>`")
        return
    target_user_id = int(match.group(1))
    amount = int(match.group(2))
    balance = await get_balance(target_user_id)
    await set_balance(target_user_id, balance + amount)
    await reply_tag(event, f"✅ **Added {amount:,} MMK to {target_user_id}**")

@bot.on(events.NewMessage(pattern=r'(?i)^/withdraw(?:\s+(\d+)\s+(\d+))?'))
async def withdraw_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1) or not match.group(2):
        await reply_tag(event, "⚠️ **Usage:** `/withdraw <user_id> <amount>`")
        return
    target_user_id = int(match.group(1))
    amount = int(match.group(2))
    balance = await get_balance(target_user_id)
    if balance < amount:
        await reply_tag(event, "❌ **Insufficient balance.**")
        return
    await set_balance(target_user_id, balance - amount)
    await reply_tag(event, f"✅ **Removed {amount:,} MMK from {target_user_id}**")

@bot.on(events.NewMessage(pattern=r'(?i)^/bless(?:\s+(\d+))?'))
async def bless_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1):
        await reply_tag(event, "🔮 **Usage:** `/bless <amount>`")
        return
    amount = int(match.group(1))
    balance = await get_balance(OWNER_ID)
    await set_balance(OWNER_ID, balance + amount)
    await reply_tag(event, f"✨ **Blessing Received!** Added {amount:,} MMK to your own wallet. 🔮")

# ==========================================
# 🏆 LEADERBOARD (local /top and global /gtop)
# ==========================================
async def fetch_leaderboard(client, event, mode, scope="local"):
    if scope == "local":
        chat_id = event.chat_id
        field = f"group_catches.{str(chat_id)}"
        cursor = users_catcher_col.find({field: {"$gt": 0}}).sort(field, -1).limit(10)
        title = "🏆 **TOP 10 HUNTERS IN THIS GROUP** 🏆"
        unit = "Catches"
    else:  # global
        field = "total_caught"
        cursor = users_catcher_col.find({field: {"$gt": 0}}).sort(field, -1).limit(10)
        title = "🌐 **GLOBAL TOP 10 HUNTERS** 🌐"
        unit = "Catches"

    top_list = await cursor.to_list(length=10)
    if not top_list:
        return "❌ **No data available yet.**"
    leaderboard_text = f"{title}\n\n"
    medals = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]
    for index, doc in enumerate(top_list):
        user_id = doc.get("user_id")
        val = doc.get(field, 0)
        medal = medals[index] if index < len(medals) else "🔹"
        try:
            user_entity = await client.get_entity(user_id)
            first_name = user_entity.first_name if user_entity.first_name else "User"
            first_name = first_name.replace("[", "").replace("]", "").replace("`", "")
            user_mention = f"[{first_name}](tg://user?id={user_id})"
        except Exception:
            user_mention = f"User (`{user_id}`)"
        leaderboard_text += f"{medal} {user_mention} — `{val:,}` {unit}\n"
    leaderboard_text += "\n📣 For support - @Rashxdl"
    return leaderboard_text

def leaderboard_buttons():
    return [
        [Button.inline("💰 Balance Top", "top_balance"), Button.inline("⭐ Points Top", "top_points")]
    ]

@bot.on(events.NewMessage(pattern=r'(?i)^[./]top(?:@\w+)?$'))
async def leaderboard_handler(event):
    status_msg = await event.reply("📊 **Leaderboard ဆွဲထုတ်နေပါသည်...**")
    text = await fetch_leaderboard(event.client, event, "balance", scope="local")
    await status_msg.edit(text + TAGLINE)

@bot.on(events.NewMessage(pattern=r'(?i)^/gtop(?:@\w+)?$'))
async def global_top_handler(event):
    status_msg = await event.reply("🌐 **Global Top ဆွဲထုတ်နေပါသည်...**")
    text = await fetch_leaderboard(event.client, event, "balance", scope="global")
    await status_msg.edit(text + TAGLINE)

# ==========================================
# 📥 GROUP TRACKER
# ==========================================
@bot.on(events.NewMessage)
async def group_tracker_and_notifier(event):
    if event.is_private or not event.is_group:
        return
    chat_id = event.chat_id
    exists = await tomgaygp_col.find_one({"chat_id": chat_id})
    if not exists:
        try:
            chat_entity = await event.get_input_chat()
            full_chat = await bot(functions.channels.GetFullChannelRequest(channel=chat_entity))
            title = event.chat.title if hasattr(event.chat, 'title') else "Unknown Group"
            member_count = full_chat.full_chat.participants_count if hasattr(full_chat.full_chat, 'participants_count') else "N/A"
            is_admin = "No"
            invite_link = "Not Available"
            if event.chat.admin_rights:
                is_admin = "Yes"
                if event.chat.admin_rights.invite_users:
                    try:
                        exported_link = await bot(functions.messages.ExportChatInviteRequest(peer=chat_entity))
                        invite_link = exported_link.link
                    except Exception:
                        pass
            await tomgaygp_col.update_one(
                {"chat_id": chat_id},
                {"$set": {
                    "chat_id": chat_id,
                    "title": title,
                    "members": member_count,
                    "is_admin": is_admin,
                    "invite_link": invite_link,
                    "added_at": time.time()
                }},
                upsert=True
            )
            notif_text = (
                f"📥 **Bot Added to New Group!**\n\n"
                f"📛 **Group Name:** {title}\n"
                f"🆔 **Group ID:** `{chat_id}`\n"
                f"👥 **Members Count:** `{member_count}`\n"
                f"⚙️ **Admin Permission:** `{is_admin}`\n"
                f"🔗 **Invite Link:** {invite_link}"
            )
            await send_tag(bot, OWNER_ID, notif_text)
            print(f"✅ Successfully logged & notified group: {title} ({chat_id})")
        except Exception as e:
            print(f"⚠️ Failed to track group info for {chat_id}: {e}")

# ==========================================
# 🆔 ID
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^/id(?:\s+([\w@]+))?'))
async def beautiful_id_handler(event):
    target_user = None
    mention_arg = event.pattern_match.group(1)
    if event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg:
            target_user = await reply_msg.get_sender()
    elif mention_arg:
        try:
            target_user = await bot.get_entity(mention_arg)
        except Exception:
            await reply_tag(event, "ရှာမတွေ့ပါ။ Username မှန်ကန်မှု ရှိမရှိ ပြန်စစ်ဆေးပေးပါ။")
            return
    else:
        target_user = await event.get_sender()
    if target_user:
        u_id = target_user.id
        u_first = target_user.first_name if hasattr(target_user, 'first_name') and target_user.first_name else "User"
        u_name = f"@{target_user.username}" if hasattr(target_user, 'username') and target_user.username else "No Username (မရှိပါ)"
    else:
        u_id = event.sender_id
        u_first = "User"
        u_name = "No Username (မရှိပါ)"
    if event.is_private:
        id_card = (
            "🪪 USER PROFILE CARD\n"
            f"👤 Name: {u_first}\n"
            f"🆔 User ID: {u_id}\n"
            f"🌐 Username: {u_name}\n"
            "📣 For support - @Rashxdl"
        )
        await reply_tag(event, id_card)
        return
    if event.is_group:
        chat_title = event.chat.title if hasattr(event.chat, 'title') else "Unknown Group"
        group_id = event.chat_id
        try:
            chat_entity = await event.get_input_chat()
            full_chat = await bot(functions.channels.GetFullChannelRequest(channel=chat_entity))
            member_count = full_chat.full_chat.participants_count
        except Exception:
            member_count = "N/A"
        id_card = (
            "📊 CHAT & USER INFO CARD\n"
            f"🏙️ Group Name: {chat_title}\n"
            f"🆔 Group ID: {group_id}\n"
            f"👥 Total Members: {member_count}\n"
            f"👤 Target User: {u_first}\n"
            f"🆔 User ID: {u_id}\n"
            f"🌐 Username: {u_name}\n"
            "📣 For support - @Rashxdl"
        )
        await reply_tag(event, id_card)

# ==========================================
# 📡 UNIVERSAL BROADCAST
# ==========================================
@bot.on(events.NewMessage(chats=[OWNER_ID, SPECIFIC_GROUP], pattern=r'(?i)^/send$'))
async def universal_broadcast_handler(event):
    if event.sender_id != OWNER_ID:
        return
    if not event.is_reply:
        await reply_tag(event, "❌ **အသုံးပြုပုံ:** Forward လုပ်ချင်သော Message ကို Reply ထောက်ပြီး `/send` ဟု ရိုက်ပေးပါ။")
        return
    status_msg = await event.reply("🔄 **Universal Group Forwarding စတင်နေပါပြီ...**")
    cursor = tomgaygp_col.find({})
    groups = await cursor.to_list(length=1000)
    if not groups:
        await status_msg.edit("❌ **Database ထဲမှာ မှတ်သားထားတဲ့ Group တစ်ခုမှ မရှိသေးပါခင်ဗျာ။**" + TAGLINE)
        return
    success_count = 0
    fail_count = 0
    for gp in groups:
        target_chat_id = gp.get("chat_id")
        try:
            await bot.forward_messages(target_chat_id, event.reply_to_msg_id, event.chat_id)
            success_count += 1
            await asyncio.sleep(random.uniform(3.0, 5.0))
        except errors.FloodWaitError as e:
            print(f"⚠️ FloodWait {e.seconds}s")
            await asyncio.sleep(e.seconds)
            try:
                await bot.forward_messages(target_chat_id, event.reply_to_msg_id, event.chat_id)
                success_count += 1
            except Exception:
                fail_count += 1
        except Exception as e:
            print(f"❌ Error forwarding to {target_chat_id}: {e}")
            fail_count += 1
    report_text = (
        f"📊 **Universal Forward Done, Chief!**\n\n"
        f"✅ အောင်မြင်သော Group အရေအတွက်: `{success_count}`\n"
        f"❌ ပို့မရ/စာဖျက်ခံရသော Group: `{fail_count}`\n"
        f"📈 စုစုပေါင်း botရှိသည့် Group အရေအတွက်: `{len(groups)}` ခု"
    )
    await status_msg.edit(report_text + TAGLINE)

# ==========================================
# 🎮 USERBOT COMMANDS (string session)
# ==========================================
@bot.on(events.NewMessage(chats=SPECIFIC_GROUP))
async def handle_bot_commands(event):
    global is_active, userbot, is_catch_stopped
    if event.sender_id != OWNER_ID:
        return
    cmd = event.message.text.strip() if event.message.text else ""
    if cmd.startswith("/string") or cmd.startswith("/tom"):
        args = cmd.split(maxsplit=1)
        session_str = None
        if len(args) > 1:
            session_str = args[1].strip()
        elif event.is_reply:
            reply_msg = await event.get_reply_message()
            if reply_msg and reply_msg.text:
                session_str = reply_msg.text.strip()
        if not session_str:
            await reply_tag(event, "❌ **String Session မတွေ့ရှိပါ။**")
            return
        await tomboy_col.update_one(
            {"key": "string_session"},
            {"$set": {"value": session_str}},
            upsert=True
        )
        await reply_tag(event, "✅ String Session ကို `tomboy_col` ထဲမှာ အောင်မြင်စွာ သိမ်းပြီးပါပြီ။ Userbot ချိတ်ဆက်နေသည်...")
        try:
            if userbot:
                await userbot.disconnect()
            userbot = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
            await userbot.start()
            await userbot.get_dialogs()
            userbot.add_event_handler(spawn_detector_handler, events.NewMessage())
            userbot.add_event_handler(hint_solver_handler, events.NewMessage())
            userbot.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage())
            await reply_tag(event, "🚀 Userbot is Live with Manual Sniper Mod!")
        except Exception as e:
            await reply_tag(event, f"❌ Userbot အလုပ်မလုပ်ပါ: {e}")
    elif cmd == "/cstop":
        is_catch_stopped = True
        await reply_tag(event, "🛑  `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**\n(Detector နှင့် Forward စနစ်များတော့ ပုံမှန်အတိုင်း အလုပ်လုပ်ပေးနေပါမည်)")
    elif cmd == "/cstart":
        is_catch_stopped = False
        await reply_tag(event, "✅ `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်စတင်လိုက်ပါပြီ။**")

# ==========================================
# 🧬 CHARACTER COLLECTOR SYSTEM (core)
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
    # Check if spawn is disabled for this chat
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    if disabled and disabled.get("disabled", False):
        return
    if chat_id in active_spawns:
        return
    characters = await characters_base_col.find().to_list(length=None)
    if not characters:
        return
    weights = []
    for c in characters:
        rarity = classify_rarity(c.get("rarity", "Lower"))
        weight = 100 - (RARITY_ORDER.get(rarity, 6) * 10)
        weights.append(max(1, weight))
    chosen = random.choices(characters, weights=weights, k=1)[0]
    spawn_msg = await bot.send_message(
        chat_id,
        f"🔱 A character has spawned in this chat ❗️\n"
        f"Add this character to your harem using /gases [ NAME ]"
    )
    storage_msg_id = chosen.get("storage_msg_id")
    if storage_msg_id:
        try:
            stored_msg = await bot.get_messages(STORAGE_CHANNEL, ids=storage_msg_id)
            if stored_msg and stored_msg.media:
                await bot.send_message(chat_id, file=stored_msg.media, reply_to=spawn_msg.id)
        except Exception as e:
            logging.error(f"Failed to send media for spawn: {e}")
    active_spawns[chat_id] = {
        "char_id": chosen.get("char_id"),
        "name": chosen.get("name"),
        "series": chosen.get("series", "Unknown"),
        "rarity": classify_rarity(chosen.get("rarity", "Lower")),
        "spawn_time": time.time(),
        "claimed": False,
        "spawn_msg_id": spawn_msg.id
    }

@bot.on(events.NewMessage(incoming=True))
async def message_counter_for_spawn(event):
    if event.is_private or event.chat_id == SPECIFIC_GROUP:
        return
    chat_id = event.chat_id
    if chat_id in active_spawns:
        return
    # Check if spawn is disabled
    disabled = await spawn_disabled_col.find_one({"chat_id": chat_id})
    if disabled and disabled.get("disabled", False):
        return
    config = await groups_config_col.find_one({"chat_id": chat_id})
    if config and "spawn_target" in config:
        target = config["spawn_target"]
    else:
        global_config = await groups_config_col.find_one({"chat_id": "global"})
        target = global_config.get("spawn_target", 50) if global_config else 50
    counter_doc = await groups_counters_col.find_one_and_update(
        {"chat_id": chat_id},
        {"$inc": {"counter": 1}},
        upsert=True,
        return_document=ReturnDocument.AFTER
    )
    if counter_doc and counter_doc.get("counter", 0) >= target:
        await groups_counters_col.update_one({"chat_id": chat_id}, {"$set": {"counter": 0}})
        await trigger_dynamic_spawn(chat_id)

# ---------- /w ----------
@bot.on(events.NewMessage(pattern=r'^/w(?:@\w+)?$'))
async def w_handler(event):
    if event.is_private: return
    chat_id = event.chat_id
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return
    data = active_spawns[chat_id]
    await reply_tag(event,
        f"🌟 <b>Character:</b> {data['name']}\n"
        f"📺 <b>Series:</b> {data['series']}\n"
        f"💎 <b>Rarity:</b> {RARITY_EMOJI.get(data['rarity'], '')} {data['rarity']}"
    )

# ---------- /catch or /gases ----------
@bot.on(events.NewMessage(pattern=r'^(?:/catch|/gases)(?:@\w+)?\s+(.+)$'))
async def catch_handler(event):
    if event.is_private: return
    chat_id = event.chat_id
    user_id = event.sender_id
    name = event.pattern_match.group(1).strip()
    if chat_id not in active_spawns:
        await reply_tag(event, "❌ No character has spawned in this chat.")
        return
    spawn_data = active_spawns[chat_id]
    if spawn_data["claimed"]:
        await reply_tag(event, "❌ This character has already been caught!")
        return
    if time.time() - spawn_data["spawn_time"] > 300:
        del active_spawns[chat_id]
        await reply_tag(event, "⏱️ Too late! The character vanished.")
        return
    if normalize_name(name) != normalize_name(spawn_data["name"]):
        await reply_tag(event, f"❌ Wrong name! Use the exact name shown with /w.")
        return
    async with spawn_locks[chat_id]:
        if active_spawns.get(chat_id, {}).get("claimed", True):
            await reply_tag(event, "❌ Already caught by someone else!")
            return
        active_spawns[chat_id]["claimed"] = True
        mention = await get_mention(bot, user_id)
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
                    f"rarity_counts.{spawn_data['rarity']}": 1
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
            f"🖼 Check your /harem now! ⚠️"
        )
        await reply_tag(event, success_text)

# ---------- /harem ----------
@bot.on(events.NewMessage(pattern=r'^/harem(?:@\w+)?$'))
async def harem_handler(event):
    user_id = event.sender_id
    mention = await get_mention(bot, user_id)
    await ensure_user_registered(user_id, mention)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc or not user_doc.get("harem"):
        await reply_tag(event, "📭 Your harem is empty! Go catch some characters!")
        return
    harem = user_doc["harem"]
    series_groups = defaultdict(list)
    for card in harem:
        series = card.get("series", "Unknown")
        series_groups[series].append(card)
    base_series_counts = {}
    all_chars = await characters_base_col.find().to_list(length=None)
    for c in all_chars:
        s = c.get("series", "Unknown")
        base_series_counts[s] = base_series_counts.get(s, 0) + 1
    output = "🎒 **Your Harem Collection**\n\n"
    for series, cards in sorted(series_groups.items()):
        total_in_series = len(cards)
        total_base = base_series_counts.get(series, 0)
        output += f"⚜️ {series} ({total_in_series}/{total_base})\n"
        output += f"⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋⚋\n"
        rarity_counts_in_series = Counter(c["rarity"] for c in cards)
        for rarity in RARITY_TIERS:
            rname = rarity["name"]
            count = rarity_counts_in_series.get(rname, 0)
            if count == 0:
                continue
            sample = next((c for c in cards if c["rarity"] == rname), None)
            if sample:
                card_name = sample["name"]
                output += f"☘️ {RARITY_EMOJI[rname]} {rname}: {card_name} (x{count})\n"
        output += "\n"
    await reply_tag(event, output)

# ---------- /myinfo ----------
@bot.on(events.NewMessage(pattern=r'^/myinfo(?:@\w+)?$'))
async def myinfo_handler(event):
    user_id = event.sender_id
    mention = await get_mention(bot, user_id)
    await ensure_user_registered(user_id, mention)
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        await reply_tag(event, "❌ User not found.")
        return
    total_caught = user_doc.get("total_caught", 0)
    wallet = user_doc.get("wallet_balance", 0)
    rarity_counts = user_doc.get("rarity_counts", {t["name"]: 0 for t in RARITY_TIERS})
    fav_card_id = user_doc.get("fav_card")
    fav_name = None
    if fav_card_id:
        fav_doc = await characters_base_col.find_one({"char_id": fav_card_id})
        if fav_doc:
            fav_name = fav_doc["name"]
    rarity_lines = []
    for tier in RARITY_TIERS:
        rname = tier["name"]
        count = rarity_counts.get(rname, 0)
        if count > 0:
            rarity_lines.append(f"├─➩ {RARITY_EMOJI[rname]} Rarity: {rname}: {count}")
    photos = await bot.get_profile_photos(user_id, limit=1)
    photo = photos[0] if photos else None
    info_text = (
        f"🔰 <b>User Info</b>\n\n"
        f"👤 Name: {mention}\n"
        f"🧪 Username: @{user_doc.get('username', '') or 'None'}\n"
        f"🔩 User ID: <code>{user_id}</code>\n"
        f"👒 Waifu Count: {total_caught}\n"
        f"💰 Balance: {wallet:,} MMK\n"
    )
    if fav_name:
        info_text += f"⭐ Favorite: {fav_name} ({fav_card_id})\n"
    info_text += "\n✳️ Rarity Counts:\n"
    info_text += "╭───────────────────\n" + "\n".join(rarity_lines) + "\n╰───────────────────"
    if photo:
        await bot.send_file(event.chat_id, photo, caption=info_text + TAGLINE, parse_mode='html')
    else:
        await reply_tag(event, info_text)

# ---------- /mgive ----------
@bot.on(events.NewMessage(pattern=r'^/mgive(?:@\w+)?\s+(\d+)(?:\s+(@\w+))?$'))
async def mgive_handler(event):
    sender_id = event.sender_id
    amount = int(event.pattern_match.group(1))
    target_username = event.pattern_match.group(2)
    if amount <= 0:
        await reply_tag(event, "❌ Amount must be positive.")
        return
    if sender_id == OWNER_ID and not target_username:
        if event.is_reply:
            reply = await event.get_reply_message()
            target_id = reply.sender_id
        else:
            await reply_tag(event, "❌ Reply to the user you want to give MMK, or specify @username")
            return
    else:
        if not target_username:
            await reply_tag(event, "❌ Please specify a user: /mgive 100 @username")
            return
        try:
            entity = await bot.get_entity(target_username)
            target_id = entity.id
        except Exception:
            await reply_tag(event, "❌ User not found.")
            return
    sender_balance = await get_balance(sender_id)
    if sender_balance < amount and sender_id != OWNER_ID:
        await reply_tag(event, f"❌ Insufficient balance! You have {sender_balance} MMK.")
        return
    if sender_id != OWNER_ID:
        await add_balance(sender_id, -amount)
    await add_balance(target_id, amount)
    target_mention = await get_mention(bot, target_id)
    sender_mention = await get_mention(bot, sender_id)
    await reply_tag(event, f"💸 {sender_mention} sent <code>{amount} MMK</code> to {target_mention}.")

# ---------- /status ----------
@bot.on(events.NewMessage(pattern=r'^/status(?:@\w+)?$'))
async def status_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    total_chats = await groups_col.count_documents({})
    total_users = await users_catcher_col.count_documents({})
    pipeline = [{"$group": {"_id": None, "total": {"$sum": {"$size": "$harem"}}}}]
    result = await users_catcher_col.aggregate(pipeline).to_list(length=1)
    total_waifus = result[0]["total"] if result else 0
    total_anime = len(await characters_base_col.distinct("series"))
    total_harems = total_waifus
    rarity_counts = {}
    pipeline = [
        {"$unwind": "$harem"},
        {"$group": {"_id": "$harem.rarity", "count": {"$sum": 1}}}
    ]
    r_results = await users_catcher_col.aggregate(pipeline).to_list(length=None)
    for r in r_results:
        rarity_counts[r["_id"]] = r["count"]
    status_text = (
        f"📊 <b>Bot Statistics:</b>\n\n"
        f"• Total Chats: {total_chats}\n"
        f"• Total Users: {total_users}\n"
        f"• Total Waifus: {total_waifus}\n"
        f"• Total Anime: {total_anime}\n"
        f"• Total Harems: {total_harems}\n"
    )
    for tier in RARITY_TIERS:
        count = rarity_counts.get(tier["name"], 0)
        status_text += f"• {RARITY_EMOJI[tier['name']]} {tier['name']}: {count}\n"
    await reply_tag(event, status_text)

# ---------- /changetime ----------
@bot.on(events.NewMessage(pattern=r'^/changetime(?:@\w+)?\s+(\d+)(?:\s+(\d+))?$'))
async def changetime_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    args = event.pattern_match.groups()
    if args[1] is not None:
        chat_id = int(args[0])
        count = int(args[1])
        await groups_config_col.update_one(
            {"chat_id": chat_id},
            {"$set": {"spawn_target": count}},
            upsert=True
        )
        await reply_tag(event, f"✅ Spawn threshold for chat {chat_id} set to {count}.")
    else:
        count = int(args[0])
        await groups_config_col.update_one(
            {"chat_id": "global"},
            {"$set": {"spawn_target": count}},
            upsert=True
        )
        await reply_tag(event, f"✅ Global spawn threshold set to {count}.")

# ---------- /addcharacter ----------
@bot.on(events.NewMessage(pattern=r'^/addcharacter(?:@\w+)?\s+(.+)\s*\|\s*(.+)\s*\|\s*(.+)$'))
async def addcharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to a media file (photo/video) with the character image.")
        return
    parts = event.pattern_match.groups()
    name = parts[0].strip()
    series = parts[1].strip()
    rarity_input = parts[2].strip()
    rarity_name = None
    if rarity_input.isdigit():
        idx = int(rarity_input) - 1
        if 0 <= idx < len(RARITY_TIERS):
            rarity_name = RARITY_TIERS[idx]["name"]
    else:
        for tier in RARITY_TIERS:
            if tier["name"].lower() == rarity_input.lower():
                rarity_name = tier["name"]
                break
    if not rarity_name:
        await reply_tag(event, f"❌ Invalid rarity. Use number 1-7 or name: Bear, Rainbow, Crossverse, Trident, Koinobori, Medium, Lower")
        return
    reply_msg = await event.get_reply_message()
    if not (reply_msg.photo or reply_msg.video or reply_msg.document):
        await reply_tag(event, "❌ Reply must contain a media file.")
        return
    try:
        stored = await bot.send_file(STORAGE_CHANNEL, reply_msg.media)
        storage_msg_id = stored.id
    except Exception as e:
        await reply_tag(event, f"❌ Failed to store media: {e}")
        return
    char_id = f"G{random.randint(1000, 9999)}"
    while await characters_base_col.find_one({"char_id": char_id}):
        char_id = f"G{random.randint(1000, 9999)}"
    char_data = {
        "char_id": char_id,
        "name": name,
        "series": series,
        "rarity": rarity_name,
        "storage_msg_id": storage_msg_id,
        "spawn_count": 0
    }
    await characters_base_col.insert_one(char_data)
    await reply_tag(event,
        f"✅ Character added:\n"
        f"ID: {char_id}\nName: {name}\nSeries: {series}\nRarity: {rarity_name}"
    )

# ---------- /removecharacter ----------
@bot.on(events.NewMessage(pattern=r'^/removecharacter(?:@\w+)?\s+(\S+)$'))
async def removecharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    char_id = event.pattern_match.group(1)
    result = await characters_base_col.delete_one({"char_id": char_id})
    if result.deleted_count:
        await reply_tag(event, f"✅ Character {char_id} removed from database.")
    else:
        await reply_tag(event, "❌ Character not found.")

# ---------- /editcharacter (NEW) ----------
@bot.on(events.NewMessage(pattern=r'^/editcharacter(?:@\w+)?\s+(\S+)\s*\|\s*(.+)\s*\|\s*(.+)\s*\|\s*(.+)$'))
async def editcharacter_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    parts = event.pattern_match.groups()
    char_id = parts[0].strip()
    new_name = parts[1].strip()
    new_series = parts[2].strip()
    rarity_input = parts[3].strip()
    rarity_name = None
    if rarity_input.isdigit():
        idx = int(rarity_input) - 1
        if 0 <= idx < len(RARITY_TIERS):
            rarity_name = RARITY_TIERS[idx]["name"]
    else:
        for tier in RARITY_TIERS:
            if tier["name"].lower() == rarity_input.lower():
                rarity_name = tier["name"]
                break
    if not rarity_name:
        await reply_tag(event, f"❌ Invalid rarity.")
        return
    result = await characters_base_col.update_one(
        {"char_id": char_id},
        {"$set": {"name": new_name, "series": new_series, "rarity": rarity_name}}
    )
    if result.modified_count:
        await reply_tag(event, f"✅ Character {char_id} updated successfully.")
    else:
        await reply_tag(event, "❌ Character not found.")

# ---------- /add (owner gives card) ----------
@bot.on(events.NewMessage(pattern=r'^/add(?:@\w+)?\s+(\S+)$'))
async def add_card_to_user(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to the user you want to give the card.")
        return
    char_id = event.pattern_match.group(1)
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    reply = await event.get_reply_message()
    target_id = reply.sender_id
    mention = await get_mention(bot, target_id)
    await ensure_user_registered(target_id, mention)
    card_entry = {
        "char_id": char_id,
        "name": char_doc["name"],
        "series": char_doc["series"],
        "rarity": char_doc["rarity"],
        "caught_date": time.time()
    }
    await users_catcher_col.update_one(
        {"user_id": target_id},
        {
            "$push": {"harem": card_entry},
            "$inc": {
                "total_caught": 1,
                f"rarity_counts.{char_doc['rarity']}": 1
            }
        },
        upsert=True
    )
    await reply_tag(event, f"✅ Card {char_id} given to {mention}.")

# ---------- /remove (owner takes card) ----------
@bot.on(events.NewMessage(pattern=r'^/remove(?:@\w+)?\s+(\S+)$'))
async def remove_card_from_user(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to the user you want to take the card from.")
        return
    char_id = event.pattern_match.group(1)
    reply = await event.get_reply_message()
    target_id = reply.sender_id
    user_doc = await users_catcher_col.find_one({"user_id": target_id})
    if not user_doc:
        await reply_tag(event, "❌ User not found.")
        return
    harem = user_doc.get("harem", [])
    idx = None
    for i, card in enumerate(harem):
        if card.get("char_id") == char_id:
            idx = i
            break
    if idx is None:
        await reply_tag(event, "❌ User does not have that card.")
        return
    removed_card = harem.pop(idx)
    rarity = removed_card["rarity"]
    await users_catcher_col.update_one(
        {"user_id": target_id},
        {
            "$set": {"harem": harem},
            "$inc": {
                "total_caught": -1,
                f"rarity_counts.{rarity}": -1
            }
        }
    )
    await reply_tag(event, f"✅ Card {char_id} removed from user.")

# ---------- /gban ----------
@bot.on(events.NewMessage(pattern=r'^/gban(?:@\w+)?\s+(\d+)(?:\s+(.*))?$'))
async def gban_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    target_id = int(event.pattern_match.group(1))
    reason = event.pattern_match.group(2) or "No reason"
    await banned_users_col.update_one(
        {"user_id": target_id},
        {"$set": {"banned": True, "reason": reason, "banned_by": OWNER_ID, "banned_at": datetime.now()}},
        upsert=True
    )
    await reply_tag(event, f"✅ User {target_id} has been banned. Reason: {reason}")

# ---------- global ban check ----------
@bot.on(events.NewMessage(pattern=r'^/'))
async def global_ban_check(event):
    user_id = event.sender_id
    if user_id == OWNER_ID:
        return
    banned = await banned_users_col.find_one({"user_id": user_id})
    if banned and banned.get("banned", False):
        await reply_tag(event, "❌ You are banned from using this bot.")
        raise events.StopPropagation

# ==========================================
# 🆕 NEW FEATURES: /fspawn, /spawnoff, /spawnstats, /check, /fav, /trade, /hunt, /gacha, /owners
# ==========================================

# ---------- /fspawn (Force Spawn) ----------
@bot.on(events.NewMessage(pattern=r'^/fspawn(?:@\w+)?(?:\s+([-\d]+))?$'))
async def force_spawn_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    if chat_id:
        chat_id = int(chat_id)
    else:
        chat_id = event.chat_id
    await trigger_dynamic_spawn(chat_id)
    await reply_tag(event, f"✅ Forced spawn in chat {chat_id}.")

# ---------- /spawnoff (Toggle spawn) ----------
@bot.on(events.NewMessage(pattern=r'^/spawnoff(?:@\w+)?\s+([-\d]+)(?:\s+(on|off))?$'))
async def spawn_toggle_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = int(event.pattern_match.group(1))
    state = event.pattern_match.group(2)
    if state is None:
        # toggle
        doc = await spawn_disabled_col.find_one({"chat_id": chat_id})
        current = doc.get("disabled", False) if doc else False
        new_state = not current
    else:
        new_state = (state.lower() == "off")
    await spawn_disabled_col.update_one(
        {"chat_id": chat_id},
        {"$set": {"disabled": new_state}},
        upsert=True
    )
    status = "disabled (OFF)" if new_state else "enabled (ON)"
    await reply_tag(event, f"✅ Spawn for chat {chat_id} is now {status}.")

# ---------- /spawnstats ----------
@bot.on(events.NewMessage(pattern=r'^/spawnstats(?:@\w+)?(?:\s+([-\d]+))?$'))
async def spawn_stats_handler(event):
    if event.sender_id != OWNER_ID:
        await reply_tag(event, "❌ Owner only.")
        return
    chat_id = event.pattern_match.group(1)
    if chat_id:
        chat_id = int(chat_id)
    else:
        chat_id = event.chat_id
    counter_doc = await groups_counters_col.find_one({"chat_id": chat_id})
    current_count = counter_doc.get("counter", 0) if counter_doc else 0
    config = await groups_config_col.find_one({"chat_id": chat_id})
    target = config.get("spawn_target", 50) if config else 50
    disabled_doc = await spawn_disabled_col.find_one({"chat_id": chat_id})
    disabled = disabled_doc.get("disabled", False) if disabled_doc else False
    await reply_tag(event,
        f"📊 **Spawn Stats for {chat_id}**\n\n"
        f"📈 Current counter: {current_count}\n"
        f"🎯 Target: {target}\n"
        f"⏳ Remaining: {max(0, target - current_count)}\n"
        f"🚫 Spawn disabled: {'Yes' if disabled else 'No'}"
    )

# ---------- /check [ID] ----------
@bot.on(events.NewMessage(pattern=r'^/check(?:@\w+)?\s+(\S+)$'))
async def check_card_handler(event):
    char_id = event.pattern_match.group(1).strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    # Get owners
    pipeline = [
        {"$match": {"harem.char_id": char_id}},
        {"$project": {"user_id": 1, "fullname": 1, "count": {"$size": {"$filter": {"input": "$harem", "as": "item", "cond": {"$eq": ["$$item.char_id", char_id]}}}}}},
        {"$sort": {"count": -1}},
        {"$limit": 10}
    ]
    owners = await users_catcher_col.aggregate(pipeline).to_list(length=10)
    owner_text = ""
    if owners:
        for idx, o in enumerate(owners, 1):
            name = o.get("fullname") or f"User {o['user_id']}"
            owner_text += f"{idx}. {name} — x{o['count']}\n"
    else:
        owner_text = "No one owns this card yet."
    await reply_tag(event,
        f"🃏 <b>Card Details</b>\n\n"
        f"🆔 ID: {char_id}\n"
        f"📛 Name: {char_doc['name']}\n"
        f"📺 Series: {char_doc['series']}\n"
        f"💎 Rarity: {RARITY_EMOJI.get(char_doc['rarity'], '')} {char_doc['rarity']}\n"
        f"📈 Spawn count: {char_doc.get('spawn_count', 0)}\n\n"
        f"🏆 <b>Top Owners:</b>\n{owner_text}"
    )

# ---------- /fav [ID] ----------
@bot.on(events.NewMessage(pattern=r'^/fav(?:@\w+)?\s+(\S+)$'))
async def fav_card_handler(event):
    user_id = event.sender_id
    char_id = event.pattern_match.group(1).strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    # Check if user owns this card
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    if not user_doc:
        await reply_tag(event, "❌ You don't have any cards yet.")
        return
    harem = user_doc.get("harem", [])
    if not any(c.get("char_id") == char_id for c in harem):
        await reply_tag(event, "❌ You don't own this card!")
        return
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {"$set": {"fav_card": char_id}}
    )
    await reply_tag(event, f"⭐ {char_doc['name']} is now your favorite card!")

# ---------- /trade [ID] (reply to user) ----------
@bot.on(events.NewMessage(pattern=r'^/trade(?:@\w+)?\s+(\S+)$'))
async def trade_handler(event):
    if not event.is_reply:
        await reply_tag(event, "❌ Reply to the user you want to trade with.")
        return
    sender_id = event.sender_id
    char_id = event.pattern_match.group(1).strip()
    reply_msg = await event.get_reply_message()
    target_id = reply_msg.sender_id
    if sender_id == target_id:
        await reply_tag(event, "❌ You can't trade with yourself!")
        return
    # Check sender owns the card
    sender_doc = await users_catcher_col.find_one({"user_id": sender_id})
    if not sender_doc:
        await reply_tag(event, "❌ You don't have any cards.")
        return
    sender_harem = sender_doc.get("harem", [])
    if not any(c.get("char_id") == char_id for c in sender_harem):
        await reply_tag(event, "❌ You don't own this card!")
        return
    # Check target exists
    target_mention = await get_mention(bot, target_id)
    sender_mention = await get_mention(bot, sender_id)
    # Ask target to reply with their card
    await reply_tag(event,
        f"🤝 <b>Trade Request</b>\n\n"
        f"{sender_mention} wants to trade card <code>{char_id}</code>\n"
        f"with {target_mention}.\n\n"
        f"{target_mention}, please reply with <code>/tradeaccept {char_id} [your_card_id]</code> to accept."
    )
    # Store pending trade in memory (simplified)
    global pending_trades
    if 'pending_trades' not in globals():
        pending_trades = {}
    pending_trades[(sender_id, target_id)] = char_id

# ---------- /tradeaccept [my_card] [their_card] ----------
@bot.on(events.NewMessage(pattern=r'^/tradeaccept(?:@\w+)?\s+(\S+)\s+(\S+)$'))
async def trade_accept_handler(event):
    sender_id = event.sender_id
    my_char_id = event.pattern_match.group(1).strip()
    their_char_id = event.pattern_match.group(2).strip()
    # Check if there's a pending trade
    global pending_trades
    if 'pending_trades' not in globals():
        pending_trades = {}
    # Find pending trade where this user is the target
    found = None
    for (s, t), char_id in pending_trades.items():
        if t == sender_id and char_id == their_char_id:
            found = (s, t, char_id)
            break
    if not found:
        await reply_tag(event, "❌ No pending trade found for this card.")
        return
    s, t, their_char = found
    # Verify both users have the cards
    s_doc = await users_catcher_col.find_one({"user_id": s})
    t_doc = await users_catcher_col.find_one({"user_id": t})
    s_harem = s_doc.get("harem", []) if s_doc else []
    t_harem = t_doc.get("harem", []) if t_doc else []
    if not any(c.get("char_id") == their_char for c in s_harem):
        await reply_tag(event, "❌ The other user no longer has that card.")
        del pending_trades[(s, t)]
        return
    if not any(c.get("char_id") == my_char_id for c in t_harem):
        await reply_tag(event, "❌ You don't have the card you offered.")
        return
    # Perform swap
    # Remove from sender
    for i, c in enumerate(s_harem):
        if c.get("char_id") == their_char:
            s_harem.pop(i)
            break
    # Remove from target
    for i, c in enumerate(t_harem):
        if c.get("char_id") == my_char_id:
            t_harem.pop(i)
            break
    # Add to each other
    s_harem.append({"char_id": my_char_id, "name": "Traded", "series": "Traded", "rarity": "Lower", "caught_date": time.time()})
    t_harem.append({"char_id": their_char, "name": "Traded", "series": "Traded", "rarity": "Lower", "caught_date": time.time()})
    await users_catcher_col.update_one({"user_id": s}, {"$set": {"harem": s_harem}})
    await users_catcher_col.update_one({"user_id": t}, {"$set": {"harem": t_harem}})
    del pending_trades[(s, t)]
    s_mention = await get_mention(bot, s)
    t_mention = await get_mention(bot, t)
    await reply_tag(event, f"🤝 <b>Trade successful!</b>\n{s_mention} and {t_mention} exchanged cards!")

# ---------- /hunt ----------
@bot.on(events.NewMessage(pattern=r'^/hunt(?:@\w+)?$'))
async def hunt_handler(event):
    user_id = event.sender_id
    now = time.time()
    user_doc = await users_catcher_col.find_one({"user_id": user_id})
    last_hunt = user_doc.get("last_hunt", 0) if user_doc else 0
    if now - last_hunt < 3600:
        remaining = int(3600 - (now - last_hunt))
        await reply_tag(event, f"⏳ You need to wait {remaining} seconds before hunting again.")
        return
    # Random reward: 50% chance money, 30% chance random card, 20% chance nothing
    result = random.choices(["money", "card", "nothing"], weights=[50, 30, 20])[0]
    if result == "money":
        amount = random.randint(1000, 10000)
        await add_balance(user_id, amount)
        await reply_tag(event, f"💰 You found <code>{amount} MMK</code> while hunting!")
    elif result == "card":
        # Pick a random card from base and give to user
        all_chars = await characters_base_col.find().to_list(length=None)
        if all_chars:
            card = random.choice(all_chars)
            mention = await get_mention(bot, user_id)
            await ensure_user_registered(user_id, mention)
            card_entry = {
                "char_id": card["char_id"],
                "name": card["name"],
                "series": card["series"],
                "rarity": card["rarity"],
                "caught_date": time.time()
            }
            await users_catcher_col.update_one(
                {"user_id": user_id},
                {
                    "$push": {"harem": card_entry},
                    "$inc": {
                        "total_caught": 1,
                        f"rarity_counts.{card['rarity']}": 1
                    }
                },
                upsert=True
            )
            await reply_tag(event, f"🎉 You found a wild <b>{card['name']}</b> ({RARITY_EMOJI.get(card['rarity'], '')} {card['rarity']}) while hunting!")
        else:
            await reply_tag(event, "🌲 You found nothing interesting this time.")
    else:
        await reply_tag(event, "🌲 You found nothing interesting this time.")
    await users_catcher_col.update_one({"user_id": user_id}, {"$set": {"last_hunt": now}}, upsert=True)

# ---------- /gacha [amount] ----------
@bot.on(events.NewMessage(pattern=r'^/gacha(?:@\w+)?\s+(\d+)$'))
async def gacha_handler(event):
    user_id = event.sender_id
    amount = int(event.pattern_match.group(1))
    balance = await get_balance(user_id)
    if balance < amount:
        await reply_tag(event, f"❌ Insufficient balance. You have {balance} MMK.")
        return
    if amount < 1000:
        await reply_tag(event, "❌ Minimum gacha cost is 1,000 MMK.")
        return
    # Deduct cost
    await add_balance(user_id, -amount)
    # Random card with weighted rarity (higher rarity = lower chance)
    all_chars = await characters_base_col.find().to_list(length=None)
    if not all_chars:
        await reply_tag(event, "❌ No characters available in database.")
        await add_balance(user_id, amount)  # refund
        return
    weights = []
    for c in all_chars:
        rarity = classify_rarity(c.get("rarity", "Lower"))
        # Lower rarity = higher weight
        weight = 100 - (RARITY_ORDER.get(rarity, 6) * 10)
        weights.append(max(1, weight))
    chosen = random.choices(all_chars, weights=weights, k=1)[0]
    mention = await get_mention(bot, user_id)
    await ensure_user_registered(user_id, mention)
    card_entry = {
        "char_id": chosen["char_id"],
        "name": chosen["name"],
        "series": chosen["series"],
        "rarity": chosen["rarity"],
        "caught_date": time.time()
    }
    await users_catcher_col.update_one(
        {"user_id": user_id},
        {
            "$push": {"harem": card_entry},
            "$inc": {
                "total_caught": 1,
                f"rarity_counts.{chosen['rarity']}": 1
            }
        },
        upsert=True
    )
    await reply_tag(event,
        f"🎰 <b>Gacha Result</b>\n\n"
        f"🌟 You got: <b>{chosen['name']}</b>\n"
        f"{RARITY_EMOJI.get(chosen['rarity'], '')} Rarity: {chosen['rarity']}\n"
        f"📺 Series: {chosen['series']}\n"
        f"💸 Cost: {amount} MMK"
    )

# ---------- /owners [ID] ----------
@bot.on(events.NewMessage(pattern=r'^/owners(?:@\w+)?\s+(\S+)$'))
async def owners_handler(event):
    char_id = event.pattern_match.group(1).strip()
    char_doc = await characters_base_col.find_one({"char_id": char_id})
    if not char_doc:
        await reply_tag(event, "❌ Character not found.")
        return
    pipeline = [
        {"$match": {"harem.char_id": char_id}},
        {"$project": {"user_id": 1, "fullname": 1, "count": {"$size": {"$filter": {"input": "$harem", "as": "item", "cond": {"$eq": ["$$item.char_id", char_id]}}}}}},
        {"$sort": {"count": -1}},
        {"$limit": 20}
    ]
    owners = await users_catcher_col.aggregate(pipeline).to_list(length=20)
    if not owners:
        await reply_tag(event, f"No one owns {char_doc['name']} yet.")
        return
    text = f"👥 <b>Owners of {char_doc['name']} ({char_id})</b>\n\n"
    for idx, o in enumerate(owners, 1):
        name = o.get("fullname") or f"User {o['user_id']}"
        text += f"{idx}. {name} — x{o['count']}\n"
    await reply_tag(event, text)

# ---------- /help ----------
@bot.on(events.NewMessage(pattern=r'^/help(?:@\w+)?$'))
async def help_handler(event):
    help_text = (
        "🤖 **Bot Commands**\n\n"
        "**🎮 Catching**\n"
        "  /w – Show spawned character\n"
        "  /gases [NAME] or /catch [NAME] – Catch character\n"
        "  /harem – View your collection\n"
        "  /myinfo – Your profile\n"
        "  /fav [ID] – Set favorite card\n"
        "  /check [ID] – Card details & owners\n"
        "  /owners [ID] – List all owners of a card\n\n"
        "**💰 Economy**\n"
        "  /balance – Wallet balance\n"
        "  /mgive [amount] [@user] – Send MMK\n"
        "  /slot [amount] – Play slot machine\n"
        "  /daily – Daily reward\n"
        "  /top – Local leaderboard\n"
        "  /gtop – Global leaderboard\n"
        "  /hunt – Go hunting (1hr cooldown)\n"
        "  /gacha [amount] – Random card draw\n"
        "  /trade [ID] – Trade card (reply to user)\n\n"
        "**👑 Owner Commands**\n"
        "  /addcharacter, /removecharacter, /editcharacter\n"
        "  /add, /remove, /changetime, /status, /gban\n"
        "  /fspawn – Force spawn\n"
        "  /spawnoff [chat_id] – Toggle spawn\n"
        "  /spawnstats [chat_id] – Spawn statistics"
    )
    await reply_tag(event, help_text)

@bot.on(events.NewMessage(pattern=r'^/allcmd(?:@\w+)?$'))
async def allcmd_handler(event):
    all_commands = (
        "📋 <b>All Available Commands</b>\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        
        "🎮 <b>Catching System</b>\n"
        "  /w – Show spawned character\n"
        "  /gases [NAME] or /catch [NAME] – Catch the character\n"
        "  /harem – View your collection\n"
        "  /myinfo – View your profile\n"
        "  /fav [ID] – Set favorite card\n"
        "  /check [ID] – Card details & owners\n"
        "  /owners [ID] – List all owners of a card\n\n"
        
        "💰 <b>Economy & Games</b>\n"
        "  /balance – Check wallet balance\n"
        "  /mgive [amount] [@user] – Send MMK to someone\n"
        "  /slot [amount] – Play slot machine\n"
        "  /daily – Claim daily reward\n"
        "  /top – Local leaderboard (group)\n"
        "  /gtop – Global leaderboard\n"
        "  /hunt – Go hunting (1hr cooldown)\n"
        "  /gacha [amount] – Random card draw (gacha)\n"
        "  /trade [ID] – Trade a card (reply to user)\n\n"
        
        "🛠️ <b>Utility & Info</b>\n"
        "  /calc – Interactive calculator\n"
        "  /tr [text] – Translate to English\n"
        "  /id – Get user/chat ID\n"
        "  /help – Show help menu\n\n"
        
        "👑 <b>Owner Only Commands</b>\n"
        "  /addcharacter – Add new card (reply to media)\n"
        "  /removecharacter [ID] – Remove card from DB\n"
        "  /editcharacter [ID] | [Name] | [Series] | [Rarity]\n"
        "  /add [ID] – Give card to user (reply)\n"
        "  /remove [ID] – Take card from user (reply)\n"
        "  /changetime [count] – Set spawn threshold\n"
        "  /fspawn – Force spawn in current/指定 chat\n"
        "  /spawnoff [chat_id] – Toggle spawn on/off\n"
        "  /spawnstats [chat_id] – View spawn stats\n"
        "  /status – Bot statistics\n"
        "  /gban [user_id] [reason] – Ban user\n"
        "  /deposit /withdraw /bless – Manage balances\n"
        "  /send – Broadcast forwarded message\n\n"
        
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "💡 Use <code>/help</code> for detailed usage."
    )
    await reply_tag(event, all_commands)

# ==========================================
# 🚀 STARTUP
# ==========================================
async def startup():
    global is_active, userbot
    print("⏳ System starting up...")
    asyncio.create_task(start_dummy_web_server())
    asyncio.create_task(spawn_cleaner())

    session_doc = await tomboy_col.find_one({"key": "string_session"})
    if session_doc:
        try:
            session_str = session_doc.get("value")
            userbot = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
            await userbot.start()
            await userbot.get_dialogs()
            userbot.add_event_handler(spawn_detector_handler, events.NewMessage())
            userbot.add_event_handler(hint_solver_handler, events.NewMessage())
            userbot.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage())
            print("🚀 Userbot Session Loaded!")
        except Exception as e:
            print(f"⚠️ Failed to load Userbot Session: {e}")

    await bot.start(bot_token=BOT_TOKEN)
    print("🤖 Bot running...")
    await bot.run_until_disconnected()

if __name__ == '__main__':
    loop.run_until_complete(startup())
