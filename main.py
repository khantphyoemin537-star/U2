import os  # 👈 Render ရဲ့ Port ကို ဖတ်ဖို့အတွက်
import asyncio
import random
import time
import logging
import re  # 👈 Catch Command များကို Regex ဖြင့် တိကျစွာဆွဲထုတ်ရန်
from telethon import TelegramClient, events, errors, functions, Button  # 👈 Button အား ထည့်သွင်းထားသည်
from telethon.sessions import StringSession
from motor.motor_asyncio import AsyncIOMotorClient
from deep_translator import GoogleTranslator  # 👈 ဘာသာပြန်စနစ်အတွက် သွင်းထားသည်

# ==========================================
# ⚙️ CONFIGURATION (Credentials)
# ==========================================
MONGO_URI = "mongodb+srv://khantphyoemin537_db_user:9VRKiaeZkz7rJdpz@cluster0.w6tgi8j.mongodb.net/?appName=Cluster0&tlsAllowInvalidCertificates=true"
APP_ID = 39584681
APP_HASH = 'c8c0685d6dd5b9e546093ea90d27733b'
BOT_TOKEN = '8616292394:AAEwH3GPZQRNNck9Er6WK_ksl57n1P0OVHo'

OWNER_ID = 6226241065
SPECIFIC_GROUP = -1003834579058

# 🎯 NEW CHAT & BOT CONFIGURATIONS
SPAWN_BOT_ID = 6157455819
HINT_BOT_ID = 8506436817
WAIFU_CHAT_ID = -1003834579058

# Global States
spawn_tracker = {}            # Waifu Chat ထဲက ID တွေကို မူရင်း Group ID နဲ့ ချိတ်ဆက်ပေးမယ့် မြန်နှုန်းမြင့် Map
last_spawn_chat_id = None     # Hint Bot က Reply မပြန်ခဲ့ရင် သုံးမယ့် Fallback Group ID
HINT_REGEX = re.compile(r"(/catch\s+[^\n]+)") 
is_catch_stopped = False      # OWNER က Manual ထိန်းချုပ်ရန် စတိတ် (Default: အလုပ်လုပ်မည်)
is_active = False             # Auto-Reply State
SYMBOLS = ["🍒", "🍋", "🔔", "💎", "7️⃣"]     # Slot Game ပြေးကွက် သင်္ကေတများ

# MongoDB Setup
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]  
tomboy_col = db["tomboy_col"]  
reply_save_col = db["reply_save_col"]  
slot_col = db["slot_col"]              # Slot Game ရဲ့ Wallet Balance များကို သိမ်းဆည်းမည့်နေရာ
tomgaygp_col = db["tomgaygp_col"] 
# 💡 Python 3.10+ နှင့် Render အတွက် Event Loop ကြိုတင်တည်ဆောက်ခြင်း
loop = asyncio.new_event_loop()
asyncio.set_event_loop(loop)

# Initialize Official Bot Client
bot = TelegramClient('official_bot_session', APP_ID, APP_HASH, loop=loop)
userbot = None  

# ==========================================
# 💾 ASYNC MONGODB SLOT WALLET DATABASE HELPERS
# ==========================================
async def get_balance(user_id):
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေအား DB မှ ဆွဲထုတ်ရန် (မရှိပါက ၁ သောင်း အလကားပေးမည်) """
    doc = await slot_col.find_one({"user_id": user_id})
    if not doc:
        await slot_col.insert_one({"user_id": user_id, "balance": 0})
        return 0
    return doc.get("balance", 0)

async def set_balance(user_id, amount):
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေအား DB တွင် အသစ်ပြင်ဆင်သိမ်းဆည်းရန် """
    await slot_col.update_one({"user_id": user_id}, {"$set": {"balance": amount}}, upsert=True)

# ==========================================
# 🌍 DUMMY HTTP SERVER FOR RENDER HEALTH CHECK
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

# ⏱️ /catch command အား ၁ စက္ကန့်အကြာတွင် အလိုအလျောက် ပြန်ဖျက်ပေးမည့် သီးသန့် Task
async def delete_catch_message_delayed(client, chat_id, msg_id):
    try:
        await asyncio.sleep(1)
        await client.delete_messages(chat_id, msg_id)
        print(f"🗑️ Auto-deleted /catch message {msg_id} after 1 second.")
    except Exception as e:
        print(f"❌ Failed to delete /catch message: {e}")

# ==========================================
# ⚔️ NEW ANIME SPAWN DETECTOR & CATCHER HANDLERS
# ==========================================
async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in event.text:
            
            if event.chat_id in [-1001947407821, -1003067509601]:
                return  

            if any(emoji in event.text for emoji in ["🔵", "🟣"]):
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
                if target_group in [-1001947407821, -1003067509601]:
                    return
                try:
                    delay_time = random.uniform(0.3, 0.5) 
                    
                    async with event.client.action(target_group, 'typing'):
                        await asyncio.sleep(delay_time)
                        
                    sent_msg = await event.client.send_message(target_group, catch_command)
                    print(f"🎯 Caught character with delay {delay_time:.2f}s")
                    
                    asyncio.create_task(delete_catch_message_delayed(event.client, target_group, sent_msg.id))
                    
                except Exception as e:
                    print(f"❌ Catch Error: {e}")

async def catch_success_forwarder_handler(event):
    if event.sender_id == SPAWN_BOT_ID and event.text:
        # 1. Spawn Bot ရဲ့ စာထဲမှာ trigger စာသား ပါမပါ အရင်စစ်မယ်
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!" in event.text:
            try:
                # 2. လက်ရှိ Userbot ရဲ့ Profile အချက်အလက်ကို Dynamic ဆွဲထုတ်မယ် (နာမည်ပြောင်းလည်း အလုပ်လုပ်အောင်လို့ပါ)
                me = await event.client.get_me()
                first_name = me.first_name.lower() if me.first_name else ""
                last_name = me.last_name.lower() if me.last_name else ""
                full_name = f"{first_name} {last_name}".strip()
                username = me.username.lower() if me.username else ""
                
                # စာလုံး အကြီး/အသေး မရွေး မိစေရန် lower() ပြောင်းစစ်မယ်
                text_lower = event.text.lower()
                
                # 3. First Name, Full Name သို့မဟုတ် Username တစ်ခုခု စာထဲမှာ ပါဝင်နေသလား စစ်ဆေးခြင်း
                is_own_card = False
                if first_name and first_name in text_lower:
                    is_own_card = True
                elif full_name and full_name in text_lower:
                    is_own_card = True
                elif username and username in text_lower:
                    is_own_card = True
                elif event.message.mentioned: # Backup အနေနဲ့ Bot က Tag ခေါ်ရင်လည်း အလုပ်လုပ်မယ်
                    is_own_card = True
                    
                # မိမိကတ် ဟုတ်တယ်ဆိုရင် Specific Group ထဲ Forward လှမ်းပို့မယ်
                if is_own_card:
                    await event.message.forward_to(SPECIFIC_GROUP)
                    print("📦 Forwarded YOUR OWN success catch card report to SPECIFIC_GROUP.")
                    
            except Exception as e:
                print(f"❌ Success Card Forward Error: {e}")

# ==========================================
# 📢 USERBOT MASS BROADCAST SYSTEM
# ==========================================
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
                        
                    except errors.rpcerrorlist.FloodWaitError as e:
                        print(f"⚠️ FloodWait မိသွားသဖြင့် {e.seconds} စက္ကန့် စောင့်ဆိုင်းနေရသည်။")
                        await asyncio.sleep(e.seconds)
                        try:
                            await event.client.send_message(dialog.id, target_msg)
                            success_count += 1
                        except Exception:
                            fail_count += 1
                            
                    except Exception as e:
                        fail_count += 1
                        continue
            
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

            reply_text = (
                f"`{text} = {result}`\n\n"
                f"📣 For support - @Rashxdl"
            )
            await event.reply(reply_text)
            
        except Exception:
            pass

# ==========================================
# ⚡ SYSTEM 2: INTERACTIVE CALCULATOR (INLINE)
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
        
    text += (
        f"🔢 **Expression:** `0`\n\n"
        f"📣 For support - @Rashxdl"
    )
    await event.respond(text, buttons=calc_keyboard(user_id))

@bot.on(events.CallbackQuery)
async def handle_calc(event):
    data = event.data.decode('utf-8')
    msg = await event.get_message()
    
    if "_" in data:
        action, allowed_user_id = data.split("_", 1)
        allowed_user_id = int(allowed_user_id)
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
        
    new_text += (
        f"🔢 **Expression:** `{display_expr}`\n\n"
        f"📣 For support - @Rashxdl"
    )

    if msg.text != new_text:
        try:
            await event.edit(new_text, buttons=calc_keyboard(allowed_user_id))
        except Exception:
            pass
    await event.answer()

# ========================================================
# ⚡ SYSTEM 3: ENGLISH TRANSLATION ENGINE (/tr)
# ========================================================
@bot.on(events.NewMessage(pattern=r'(?i)^/tr(.*)'))
async def translate_to_english(event):
    text_to_translate = event.pattern_match.group(1).strip()
    
    if not text_to_translate and event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg and reply_msg.text:
            text_to_translate = reply_msg.text

    if not text_to_translate:
        await event.reply(
            "❌ **အသုံးပြုပုံ:**\n"
            "1. `/tr မင်္ဂလာပါ` (စာတိုက်ရိုက်ရိုက်ပြီး ပြန်ခြင်း)\n"
            "2. တခြားသူစာကို Reply ပြန်ပြီး `/tr` ဟု ရိုက်ခြင်း"
        )
        return

    try:
        translated_text = GoogleTranslator(source='auto', target='en').translate(text_to_translate)
        reply_text = (
            f"🔤 **Translated to English:**\n\n"
            f"`{translated_text}`\n\n"
            f"📣 For support - @Rashxdl"
        )
        await event.reply(reply_text)
    except Exception as e:
        logging.error(f"Translation Error: {e}")
        await event.reply("⚠️ ဘာသာပြန်ရတာ အဆင်မပြေဖြစ်သွားပါတယ်။ ခဏနေမှ ပြန်ကြိုးစားကြည့်ပါ။")

# ========================================================
# 🎰 SYSTEM 4: TELETHON PORTED SLOT GAME (WITH ANIMATION)
# ========================================================
@bot.on(events.NewMessage(pattern=r'(?i)^/balance'))
async def balance_handler(event):
    user_id = event.sender_id
    bal = await get_balance(user_id)
    await event.reply(f"💰 **Balance:** {bal:,} MMK")

@bot.on(events.NewMessage(pattern=r'(?i)^/slot(?:\s+(\d+))?'))
async def slot_handler(event):
    args = event.pattern_match.group(1)
    if not args:
        await event.reply("🎰 **Usage:** `/slot <amount>`")
        return
        
    try:
        bet = int(args.strip())
    except ValueError:
        await event.reply("❌ **Invalid amount.**")
        return

    user_id = event.sender_id
    balance = await get_balance(user_id)

    if bet <= 0:
        return

    if balance < bet:
        await event.reply("❌ **Not enough balance.**")
        return

    # 🔒 Exploit Protection: လည်နေတုန်း ထပ်မနှိပ်နိုင်အောင် ငွေကို DB ထဲမှာ ကြိုနှုတ်ထားမည်
    balance -= bet
    await set_balance(user_id, balance)

    # 🔄 Initial Spinning Message
    status_msg = await event.reply("🎰 **[ 🔄 | 🔄 | 🔄 ]**\n\n*Reels are spinning...* 🎰")
    
    # 🎬 Spin Animation Loop
    for _ in range(3):
        await asyncio.sleep(0.5)
        fake_reels = [random.choice(SYMBOLS) for _ in range(3)]
        try:
            await status_msg.edit(f"🎰 **[ {' | '.join(fake_reels)} ]**\n\n*Spinning...* 🔄")
        except Exception:
            pass

    # Real Spin Result Calculation
    reels = [random.choice(SYMBOLS) for _ in range(3)]
    payout = 0

    if reels == ["7️⃣", "7️⃣", "7️⃣"]:
        payout = bet * 5
    elif reels[0] == reels[1] == reels[2]:
        payout = bet * 2
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]:
        payout = bet * 1.5

    balance += payout
    await set_balance(user_id, balance)

    win_status = f"🎉 **Win:** +{payout:,} MMK" if payout > 0 else "😭 **You Lost!**"
    
    try:
        await status_msg.edit(
            f"🎰 **[ {' | '.join(reels)} ]**\n\n"
            f"💵 **Bet:** {bet:,} MMK\n"
            f"{win_status}\n"
            f"💰 **Balance:** {balance:,} MMK"
        )
    except Exception:
        await event.reply(
            f"🎰 **[ {' | '.join(reels)} ]**\n\n"
            f"💵 **Bet:** {bet:,} MMK\n"
            f"{win_status}\n"
            f"💰 **Balance:** {balance:,} MMK"
        )

@bot.on(events.NewMessage(pattern=r'(?i)^/deposit(?:\s+(\d+)\s+(\d+))?'))
async def deposit_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1) or not match.group(2):
        await event.reply("⚠️ **Usage:** `/deposit <user_id> <amount>`")
        return
    target_user_id = int(match.group(1))
    amount = int(match.group(2))
    
    balance = await get_balance(target_user_id)
    await set_balance(target_user_id, balance + amount)
    await event.reply(f"✅ **Added {amount:,} MMK to {target_user_id}**")

@bot.on(events.NewMessage(pattern=r'(?i)^/withdraw(?:\s+(\d+)\s+(\d+))?'))
async def withdraw_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1) or not match.group(2):
        await event.reply("⚠️ **Usage:** `/withdraw <user_id> <amount>`")
        return
    target_user_id = int(match.group(1))
    amount = int(match.group(2))
    
    balance = await get_balance(target_user_id)
    if balance < amount:
        await event.reply("❌ **Insufficient balance.**")
        return
        
    await set_balance(target_user_id, balance - amount)
    await event.reply(f"✅ **Removed {amount:,} MMK from {target_user_id}**")

# 🔮 OWNER ONLY BLESS COMMAND
@bot.on(events.NewMessage(pattern=r'(?i)^/bless(?:\s+(\d+))?'))
async def bless_handler(event):
    if event.sender_id != OWNER_ID:
        return
    match = event.pattern_match
    if not match.group(1):
        await event.reply("🔮 **Usage:** `/bless <amount>`")
        return
    amount = int(match.group(1))
    
    balance = await get_balance(OWNER_ID)
    await set_balance(OWNER_ID, balance + amount)
    await event.reply(f"✨ **Blessing Received!** Added {amount:,} MMK to your own wallet. 🔮")

# ⚡ [FIXED] CLEAN & READABLE ENGLISH TEXT FOR /START
@bot.on(events.NewMessage(pattern=r'(?i)^/start$'))
async def general_start_handler(event):
    """ အထွေထွေ အသုံးပြုသူများအတွက် Start Menu လမ်းညွှန် """
    if event.chat_id == SPECIFIC_GROUP and event.sender_id == OWNER_ID:
        return  
        
    user_id = event.sender_id
    await get_balance(user_id)  
    user = await event.get_sender()
    first_name = user.first_name if user else "User"
    
    welcome_text = (
       f"🎰 **Welcome {first_name}!**\n\n"
       f"Here are the features available in this bot:\n\n"
       f"🔢 **Calculator:** Type `/calc` to use the interactive panel, or simply send a math expression (e.g., `5+5+10`) for an instant result.\n"
       f"🔤 **Translator:** Use `/tr <text>` or reply to any message with `/tr` to translate it into English.\n"
       f"🎰 **Slot Game:**\n"
       f"• `/slot <amount>` - Play the slot machine\n"
       f"• `/balance` - Check your current wallet balance"
    )  
    await event.reply(welcome_text)
# =========================================================================
@bot.on(events.NewMessage)
async def group_tracker_and_notifier(event):
    """ Bot ရှိနေသမျှ Group တိုင်းကို စောင့်ကြည့်မှတ်သားပြီး Owner DM သို့ သတင်းပို့မည့် စနစ် """
    if event.is_private or not event.is_group:
        return

    chat_id = event.chat_id
    
    # 1. Group အချက်အလက်များကို DB ထဲတွင် ရှိ/မရှိ အရင်စစ်ဆေးမည်
    exists = await tomgaygp_col.find_one({"chat_id": chat_id})
    if not exists:
        try:
            # Group Detail များကို တိကျစွာ ဆွဲထုတ်ခြင်း
            chat_entity = await event.get_input_chat()
            full_chat = await bot(functions.channels.GetFullChannelRequest(channel=chat_entity))
            
            title = event.chat.title if hasattr(event.chat, 'title') else "Unknown Group"
            member_count = full_chat.full_chat.participants_count if hasattr(full_chat.full_chat, 'participants_count') else "N/A"
            
            # Bot တွင် Admin Permission ပေးထားခြင်း ရှိမရှိ စစ်ဆေးရန်
            is_admin = "No"
            invite_link = "Not Available"
            if event.chat.admin_rights:
                is_admin = "Yes"
                # Admin ဖြစ်ပါက Invite Link ဖန်တီး၍ Dynamic ဆွဲထုတ်မည်
                if event.chat.admin_rights.invite_users:
                    try:
                        exported_link = await bot(functions.messages.ExportChatInviteRequest(peer=chat_entity))
                        invite_link = exported_link.link
                    except Exception:
                        pass

            # 2. Database `tomgaygp_col` ထဲသို့ တန်ဖိုးအသစ် ထည့်သွင်းသိမ်းဆည်းမည်
            await tomgaygp_col.update_one(
                {"chat_id": chat_id},
                {
                    "$set": {
                        "chat_id": chat_id,
                        "title": title,
                        "members": member_count,
                        "is_admin": is_admin,
                        "invite_link": invite_link,
                        "added_at": time.time()
                    }
                },
                upsert=True
            )

            # 3. Bot Owner ၏ DM သို့ အသေးစိတ် Notification ပေးပို့ခြင်း
            notif_text = (
                f"📥 **Bot Added to New Group!**\n\n"
                f"📛 **Group Name:** {title}\n"
                f"🆔 **Group ID:** `{chat_id}`\n"
                f"👥 **Members Count:** `{member_count}`\n"
                f"⚙️ **Admin Permission:** `{is_admin}`\n"
                f"🔗 **Invite Link:** {invite_link}"
            )
            await bot.send_message(OWNER_ID, notif_text)
            print(f"✅ Successfully logged & notified group: {title} ({chat_id})")

        except Exception as e:
            print(f"⚠️ Failed to track group info for {chat_id}: {e}")
# =========================================================================
# 🪪 UPDATED: BEAUTIFUL /ID COMMAND HANDLER (NO BOLD TAGS & REPLY/MENTION SUPPORT)
# =========================================================================
@bot.on(events.NewMessage(pattern=r'(?i)^/id(?:\\s+([\\w@]+))?'))
async def beautiful_id_handler(event):
    """ User ID သို့မဟုတ် Group ID ကို Reply / Mention စနစ်ဖြင့် ပုံစံလှလှလေး ပြသပေးမည့် စနစ် """
    
    target_user = None
    mention_arg = event.pattern_match.group(1)

    # 1. တခြားသူစာကို Reply (စာထောက်) ထားလျှင် ၎င်းလူ၏ အချက်အလက်ကို ယူမည်
    if event.is_reply:
        reply_msg = await event.get_reply_message()
        if reply_msg:
            target_user = await reply_msg.get_sender()
            
    # 2. Username ဖြင့် မန်းရှင်းခေါ်ထားလျှင် (ဥပမာ - /id @username)
    elif mention_arg:
        try:
            target_user = await bot.get_entity(mention_arg)
        except Exception:
            await event.reply("ရှာမတွေ့ပါ။ Username မှန်ကန်မှု ရှိမရှိ ပြန်စစ်ဆေးပေးပါ။")
            return
            
    # 3. ဘာမှမပါလျှင် ရိုက်နှိပ်လိုက်သော မိမိကိုယ်တိုင်၏ အချက်အလက်ကို ပြမည်
    else:
        target_user = await event.get_sender()

    # User ရဲ့ အချက်အလက်များကို ခွဲထုတ်ခြင်း
    if target_user:
        u_id = target_user.id
        u_first = target_user.first_name if hasattr(target_user, 'first_name') and target_user.first_name else "User"
        u_name = f"@{target_user.username}" if hasattr(target_user, 'username') and target_user.username else "No Username (မရှိပါ)"
    else:
        u_id = event.sender_id
        u_first = "User"
        u_name = "No Username (မရှိပါ)"

    # Private Chat (DM) ထဲမှာ စစ်ဆေးခြင်း
    if event.is_private:
        id_card = (
            "🪪 USER PROFILE CARD\n" 
            f"👤 Name: {u_first}\n"
            f"🆔 User ID: {u_id}\n"
            f"🌐 Username: {u_name}\n"
            "📣 For support - @Rashxdl"
        )
        await event.reply(id_card)
        return

    # Group ထဲမှာ စစ်ဆေးခြင်း (Group ရဲ့ Info ပါ တစ်ခါတည်းပြပေးမည်)
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
        await event.reply(id_card)
        
# =========================================================================
# ⚙️ UPDATED: UNIVERSAL FORWARD BROADCAST BY /SEND COMMAND (Official Bot Only)
# =========================================================================
@bot.on(events.NewMessage(chats=[OWNER_ID, SPECIFIC_GROUP], pattern=r'(?i)^/send$'))
async def universal_broadcast_handler(event):
    """ Text, Stk, Gif, Video, Photo, Voice မရွေး Group တိုင်းဆီသို့ မူရင်းအတိုင်း Forward လှမ်းလုပ်မည့် စနစ် """
    if event.sender_id != OWNER_ID:
        return

    if not event.is_reply:
        await event.reply("❌ **အသုံးပြုပုံ:** Forward လုပ်ချင်သော Message ကို Reply ထောက်ပြီး `/send` ဟု ရိုက်ပေးပါ။")
        return

    status_msg = await event.reply("🔄 **Universal Group Forwarding စတင်နေပါပြီ...**")

    # DB ထဲရှိ သိုလှောင်ထားသော Group အားလုံးကို ဆွဲထုတ်ခြင်း
    cursor = tomgaygp_col.find({})
    groups = await cursor.to_list(length=1000)

    if not groups:
        await status_msg.edit("❌ **Database ထဲမှာ မှတ်သားထားတဲ့ Group တစ်ခုမှ မရှိသေးပါခင်ဗျာ။**")
        return

    success_count = 0
    fail_count = 0

    for gp in groups:
        target_chat_id = gp.get("chat_id")
        try:
            # 💡 bot.forward_messages ကို အသုံးပြုပြီး မူရင်းစာကို အစစ်အမှန် Forward လုပ်ပေးခြင်း
            await bot.forward_messages(target_chat_id, event.reply_to_msg_id, event.chat_id)
            success_count += 1
            # Flood Wait ကာကွယ်ရန် Safe Delay ထည့်သွင်းထားသည်
            await asyncio.sleep(random.uniform(3.0, 5.0))

        except errors.rpcerrorlist.FloodWaitError as e:
            print(f"⚠️ FloodWait မိသွားသဖြင့် {e.seconds} စက္ကန့် စောင့်ဆိုင်းနေရသည်။")
            await asyncio.sleep(e.seconds)
            try:
                await bot.forward_messages(target_chat_id, event.reply_to_msg_id, event.chat_id)
                success_count += 1
            except Exception:
                fail_count += 1
        except Exception as e:
            print(f"❌ Error forwarding to {target_chat_id}: {e}")
            fail_count += 1
            continue

    report_text = (
        f"📊 **Universal Forward Done, Chief!**\n\n"
        f"✅ အောင်မြင်သော Group အရေအတွက်: `{success_count}`\n"
        f"❌ ပို့မရ/စာဖျက်ခံရသော Group: `{fail_count}`\n"
        f"📈 စုစုပေါင်း botရှိသည့် Group အရေအတွက်: `{len(groups)}` ခု"
    )
    await status_msg.edit(report_text)
    
# ==========================================
# 🤖 OFFICIAL BOT COMMAND HANDLERS
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
            await event.reply("❌ **String Session မတွေ့ရှိပါ။**")
            return
            
        await tomboy_col.update_one(
            {"key": "string_session"},
            {"$set": {"value": session_str}},
            upsert=True
        )
        await event.reply("✅ String Session ကို `gasses_col` ထဲမှာ အောင်မြင်စွာ သိမ်းပြီးပါပြီ။ Userbot ချိတ်ဆက်နေသည်...")
        
        try:
            if userbot:
                await userbot.disconnect()
            userbot = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
            await userbot.start()
            await userbot.get_dialogs()
            
            # Register Handlers (NameError ဖြစ်စေမည့် မရှိသော function အား ဖယ်ရှားထားသည်)
            userbot.add_event_handler(spawn_detector_handler, events.NewMessage())
            userbot.add_event_handler(hint_solver_handler, events.NewMessage())
            userbot.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage()) 
            
            await event.reply("🚀 Userbot is Live with Manual Sniper Mod!")
        except Exception as e:
            await event.reply(f"❌ Userbot အလုပ်မလုပ်ပါ: {e}")

    elif cmd == "/cstop":
        is_catch_stopped = True
        await event.reply("🛑  `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**\n(Detector နှင့် Forward စနစ်များတော့ ပုံမှန်အတိုင်း အလုပ်လုပ်ပေးနေပါမည်)")

    elif cmd == "/cstart":
        is_catch_stopped = False
        await event.reply("✅ `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်စတင်လိုက်ပါပြီ။**")
        return

# ==========================================
# 🚀 SYSTEM STARTUP LOGIC
# ==========================================
async def startup():
    global is_active, userbot
    print("⏳ System starting up and loading configurations from MongoDB...")
    
    asyncio.create_task(start_dummy_web_server())

    try:
        deleted = await reply_save_col.delete_many({"$expr": {"$lt": [{"$strLenCP": "$trigger"}, 3]}})
        if deleted.deleted_count > 0:
            print(f"🧹 Cleaned up {deleted.deleted_count} short garbage triggers from DB.")
    except Exception as clean_err:
        print(f"⚠️ DB Cleanup Warning: {clean_err}")

    status_doc = await tomboy_col.find_one({"key": "bot_status"})
    if status_doc and status_doc.get("value") == "active":
        is_active = True
        print("➡️ Auto-Reply Status: ACTIVE")

    session_doc = await tomboy_col.find_one({"key": "string_session"})
    if session_doc:
        try:
            session_str = session_doc.get("value")
            userbot = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
            await userbot.start()
            await userbot.get_dialogs()
            
            # Register Handlers at Startup
            userbot.add_event_handler(spawn_detector_handler, events.NewMessage())
            userbot.add_event_handler(hint_solver_handler, events.NewMessage())
            userbot.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage()) 
            
            print("🚀 Userbot Session Successfully Loaded from DB!")
        except Exception as e:
            print(f"⚠️ Failed to load existing Userbot Session: {e}")
    else:
        print("💡 No String Session found in DB yet.")

    await bot.start(bot_token=BOT_TOKEN)
    print("🤖 Official Bot is running...")
    await bot.run_until_disconnected()

if __name__ == '__main__':
    # 💡 Render ၏ Python 3.14 Environment အတွက် Event Loop နှင့် ပတ်ခြင်း
    loop.run_until_complete(startup())
