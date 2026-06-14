import os  # 👈 Render ရဲ့ Port ကို ဖတ်ဖို့အတွက်
import asyncio
import random
import time
import logging
import re  # 👈 Catch Command များကို Regex ဖြင့် တိကျစွာဆွဲထုတ်ရန်
from telethon import TelegramClient, events, errors, functions, Button  # 👈 [UPDATED] Button အား ထည့်သွင်းထားသည်
from telethon.sessions import StringSession
from motor.motor_asyncio import AsyncIOMotorClient
from deep_translator import GoogleTranslator  # 👈 [NEW] ဘာသာပြန်စနစ်အတွက် သွင်းထားသည်

# ==========================================
# ⚙️ CONFIGURATION (Credentials)
# ==========================================
MONGO_URI = "mongodb+srv://kkt:944PJsFRda4Tcr3C@cluster0.kb5fzfl.mongodb.net/telegram_bot?appName=Cluster0&tlsAllowInvalidCertificates=true"
APP_ID = 39584681
APP_HASH = 'c8c0685d6dd5b9e546093ea90d27733b'
BOT_TOKEN = '8616292394:AAHDrxaMCvsUiVf985mUCjCQSA7LN4psHE0'

OWNER_ID = 8237842585
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
SYMBOLS = ["🍒", "🍋", "🔔", "💎", "7️⃣"]     # Slot Game ပြေးကွက် သင်္ကေတများ

# MongoDB Setup
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]  
tomboy_col = db["tomboy_col"]  
reply_save_col = db["reply_save_col"]  # 👈 [FIXED] Startup Error မတက်စေရန် ထည့်သွင်းတည်ဆောက်ထားသည်
slot_col = db["slot_col"]              # 👈 [NEW] Slot Game ရဲ့ Wallet Balance များကို သိမ်းဆည်းမည့်နေရာ

# 💡 Python 3.10+ အထက်အတွက် Event Loop ကြိုတင်ဆောက်ပေးရန်
loop = asyncio.new_event_loop()
asyncio.set_event_loop(loop)

# Initialize Official Bot Client (loop ကိုပါ Parameter ထဲ ထည့်ပေးလိုက်ပါ)
bot = TelegramClient('official_bot_session', APP_ID, APP_HASH, loop=loop)
userbot = None  


# ==========================================
# 💾 ASYNC MONGODB SLOT WALLET DATABASE HELPERS
# ==========================================
async def get_balance(user_id):
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေအား DB မှ ဆွဲထုတ်ရန် (မရှိပါက ၁ သောင်း အလကားပေးမည်) """
    doc = await slot_col.find_one({"user_id": user_id})
    if not doc:
        await slot_col.insert_one({"user_id": user_id, "balance": 10000})
        return 10000
    return doc.get("balance", 10000)

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
# ⚔️ NEW ANIME SPAWN DETECTOR & CATCHER HANDLERS (ULTRA SPEED OPTIMIZED)
# ==========================================
async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in event.text:
            
            if event.chat_id in [-1001947407821, -1003067509601]:
                return  

            if any(emoji in event.text for emoji in ["🔵", "🟣", "🟠","🟡"]):
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
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜါရါᴄᴛᴇʀ!" in event.text and event.message.mentioned:
            try:
                await event.message.forward_to(SPECIFIC_GROUP)
                print("📦 Forwarded YOUR OWN success catch card report to SPECIFIC_GROUP.")
            except Exception as e:
                print(f"❌ Success Card Forward Error: {e}")

# ==========================================
# 📢 USERBOT MASS BROADCAST SYSTEM (ANTI-LOOP & ANTI-FLOOD)
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
# 🎰 SYSTEM 4: TELETHON PORTED SLOT GAME
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

    balance -= bet
    reels = [random.choice(SYMBOLS) for _ in range(3)]
    payout = 0

    if reels == ["7️⃣", "7️⃣", "7️⃣"]:
        payout = bet * 3
    elif reels[0] == reels[1] == reels[2]:
        payout = bet * 2
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]:
        payout = bet // 2

    balance += payout
    await set_balance(user_id, balance)

    await event.reply(
        f"🎰 **[ {' | '.join(reels)} ]**\n\n"
        f"💵 **Bet:** {bet:,} MMK\n"
        f"🎉 **Win:** {payout:,} MMK\n"
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

@bot.on(events.NewMessage(pattern=r'(?i)^/start$'))
async def general_start_handler(event):
    """ အထွေထွေ အသုံးပြုသူများအတွက် Start Menu လမ်းညွှန် """
    if event.chat_id == SPECIFIC_GROUP and event.sender_id == OWNER_ID:
        return  # Owner ရဲ့ Sniper Command /start နှင့် မရှုပ်စေရန် ကျော်မည်
        
    user_id = event.sender_id
    await get_balance(user_id)  # DB ထဲ အကောင့်ဖွင့်ပေးခြင်း
    user = await event.get_sender()
    first_name = user.first_name if user else "User"
    
    welcome_text = (
       f"🎰 ᴡᴇʟᴄᴏᴍᴇ {first_name}!\n\n"
       f"ʜᴇʀᴇ ᴀʀᴇ ᴛʜᴇ ꜰᴇᴀᴛᴜʀᴇs ᴀᴠᴀɪʟᴀʙʟᴇ ɪɴ ᴛʜɪs ʙᴏᴛ:\n\n"
       f"🔢 ᴄᴀʟᴄᴜʟᴀᴛᴏʀ: ᴛʏᴘᴇ /calc ᴛᴏ ᴜsᴇ ᴛʜᴇ ɪɴᴛᴇʀᴀᴄᴛɪᴠᴇ ᴘᴀɴᴇʟ, ᴏʀ sɪᴍᴘʟʏ sᴇɴᴅ ᴀ ᴍᴀᴛʜ ᴇxᴘʀᴇssɪᴏɴ (ᴇ.ɢ., 5+5+10) ꜰᴏʀ ᴀɴ ɪɴsᴛᴀɴᴛ ʀᴇsᴜʟᴛ.\n"
       f"🔤 ᴛʀᴀɴsʟᴀᴛᴏʀ: ᴜsᴇ /tr <ᴛᴇxᴛ> ᴏʀ ʀᴇᴘʟʏ ᴛᴏ ᴀɴʏ ᴍᴇssᴀɢᴇ ᴡɪᴛʜ /tr ᴛᴏ ᴛʀᴀɴsʟᴀᴛᴇ ɪᴛ ɪɴᴛᴏ ᴇɴɢʟɪsʜ.\n"
       f"🎰 sʟᴏᴛ ɢᴀᴍᴇ:\n"
       f"• /slot <ᴀᴍᴏᴜɴᴛ> - ᴘʟᴀʏ ᴛʜᴇ sʟᴏᴛ ᴍᴀᴄʜɪɴᴇ\n"
       f"• /balance - ᴄʜᴇᴄᴋ ʏᴏᴜʀ ᴄᴜʀʀᴇɴᴛ ᴡᴀʟʟᴇᴛ ʙᴀʟᴀɴᴄᴇ"
    )  
    await event.reply(welcome_text)

# ==========================================
# 🤖 OFFICIAL BOT COMMAND HANDLERS
# ==========================================
@bot.on(events.NewMessage(chats=SPECIFIC_GROUP))
async def handle_bot_commands(event):
    global is_active, userbot, is_scraping, is_talker_active, is_catch_stopped
    
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
            
            # Register Handlers
            userbot.add_event_handler(handle_userbot_reply, events.NewMessage())
            userbot.add_event_handler(spawn_detector_handler, events.NewMessage())
            userbot.add_event_handler(hint_solver_handler, events.NewMessage())
            userbot.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage()) 
            
            await event.reply("🚀 Userbot is Live with Manual Sniper Mod!")
        except Exception as e:
            await event.reply(f"❌ Userbot အလုပ်မလုပ်ပါ: {e}")

    elif cmd == "/stop":
        is_catch_stopped = True
        await event.reply("🛑  `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**\n(Detector နှင့် Forward စနစ်များတော့ ပုံမှန်အတိုင်း အလုပ်လုပ်ပေးနေပါမည်)")

    elif cmd == "/start":
        is_catch_stopped = False
        await event.reply("✅ `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်စတင်လိုက်ပါပြီ။**")
        asyncio.create_task(scrape_history_task())
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
            userbot.add_event_handler(handle_userbot_reply, events.NewMessage())
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
    # 💡 asyncio.run() အစား အပေါ်က ဆောက်ထားတဲ့ loop နှင့် ပတ်ရန်
    loop.run_until_complete(startup())
    
