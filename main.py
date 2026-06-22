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
MONGO_URI = "mongodb+srv://kkt:h1BdaMt7nxW9jTXa@cluster0.kb5fzfl.mongodb.net/?appName=Cluster0&tlsAllowInvalidCertificates=true"
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
shop_items_col = db["shop_items_col"]  # 🛒 ဆိုင်ခန်းထဲရှိ Item စာရင်းသိုလှောင်ရန်
inventory_col = db["inventory_col"]    # 🎒 User များပိုင်ဆိုင်သည့် ပစ္စည်းများသိမ်းရန်

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
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေအား DB မှ ဆွဲထုတ်ရန် """
    doc = await slot_col.find_one({"user_id": user_id})
    if not doc:
        await slot_col.insert_one({"user_id": user_id, "balance": 0})
        return 0
    return doc.get("balance", 0)

async def set_balance(user_id, amount):
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေအား DB တွင် အသစ်ပြင်ဆင်သိမ်းဆည်းရန် """
    await slot_col.update_one({"user_id": user_id}, {"$set": {"balance": amount}}, upsert=True)

# ==========================================
# 📊 COLLECTION POINT & RANK SYSTEM (MLBB STYLE)
# ==========================================
def get_collection_title(cp):
    """ Collection Point အလိုက် MLBB ကဲ့သို့ အဆင့်သတ်မှတ်ချက်ပေးရန် """
    if cp >= 100000: return "World collector 🌍"
    if cp >= 80000: return "Honour 🎖️"
    if cp >= 50000: return "Mythic 🌟"
    if cp >= 30000: return "Legend 🏆"
    if cp >= 10000: return "Epic 💎"
    if cp >= 5000: return "Grandmaster 👑"
    if cp >= 3000: return "Master ⚔️"
    if cp >= 1000: return "Elite 🛡️"
    if cp >= 500: return "Beginner 🔰"
    return "Newbie 👶"

async def get_user_total_cp(user_id):
    """ အသုံးပြုသူတစ်ဦးချင်းစီ ပိုင်ဆိုင်ထားသော Item စုစုပေါင်းမှ CP ကို တွက်ချက်ရန် """
    inv = await inventory_col.find_one({"user_id": user_id})
    if not inv or "items" not in inv:
        return 0
    
    total_cp = 0
    for item_id, qty in inv["items"].items():
        if qty > 0:
            item = await shop_items_col.find_one({"item_id": int(item_id)})
            if item:
                total_cp += item.get("cp", 0) * qty
    return total_cp

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
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!" in event.text:
            try:
                me = await event.client.get_me()
                first_name = me.first_name.lower() if me.first_name else ""
                last_name = me.last_name.lower() if me.last_name else ""
                full_name = f"{first_name} {last_name}".strip()
                username = me.username.lower() if me.username else ""
                
                text_lower = event.text.lower()
                
                is_own_card = False
                if first_name and first_name in text_lower:
                    is_own_card = True
                elif full_name and full_name in text_lower:
                    is_own_card = True
                elif username and username in text_lower:
                    is_own_card = True
                elif event.message.mentioned:
                    is_own_card = True
                    
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
# ========================================================
# 📊 SYSTEM 4.2: ADVANCED LEADERBOARD (BALANCE & POINTS)
# ========================================================
async def fetch_leaderboard(client, event, mode):
    """ Database မှ Balance သို့မဟုတ် Points အလိုက် Top 10 ကို ဆွဲထုတ်ပေးသည့် Helper Function """
    field = "balance" if mode == "balance" else "points" # <- Database ထဲက field နာမည်များ
    title = "🏆 **TOP 10 RICHEST USERS (LEADERBOARD)** 🏆" if mode == "balance" else "⭐ **TOP 10 HIGHEST POINTS (LEADERBOARD)** ⭐"
    unit = "MMK" if mode == "balance" else "Points"
    
    # ကြီးစဉ်ငယ်လိုက် လူ ၁၀ ဦး ဆွဲထုတ်ခြင်း
    cursor = slot_col.find().sort(field, -1).limit(10)
    top_list = await cursor.to_list(length=10)
    
    if not top_list:
        return "❌ **Leaderboard မှာ ပြသစရာ လူစာရင်း မရှိသေးပါခင်ဗျာ။**"
        
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
            user_mention = f"အသုံးပြုသူ (`{user_id}`)"
            
        leaderboard_text += f"{medal} {user_mention} — `{val:,}` {unit}\n"
        
    leaderboard_text += "\n📣 For support - @Rashxdl"
    return leaderboard_text

def leaderboard_buttons():
    """ အောက်ကပြမည့် Inline Button များ """
    return [
        [
            Button.inline("💰 Balance Top", "top_balance"),
            Button.inline("⭐ Points Top", "top_points")
        ]
    ]

# ၁။ /top Text Command ကို ဖတ်မည့်အပိုင်း (Default အနေဖြင့် Balance ကို အရင်ပြမည်)
@bot.on(events.NewMessage(pattern=r'(?i)^[./]top(?:@\w+)?$'))
async def leaderboard_handler(event):
    status_msg = await event.reply("📊 **Leaderboard ဆွဲထုတ်နေပါသည်... ခေတ္တစောင့်ဆိုင်းပေးပါ။**")
    text = await fetch_leaderboard(event.client, event, "balance")
    await status_msg.edit(text, buttons=leaderboard_buttons())

# ၂။ Inline Button နှိပ်လိုက်လျှင် ပြောင်းလဲပေးမည့် Callback အပိုင်း
@bot.on(events.CallbackQuery(pattern=r'^top_'))
async def leaderboard_callback_handler(event):
    data = event.data.decode('utf-8')
    mode = "balance" if data == "top_balance" else "points"
    
    await event.answer() # Button loading စက်ဝိုင်းလေးကို ပိတ်ခြင်း
    
    text = await fetch_leaderboard(event.client, event, mode)
    
    msg = await event.get_message()
    if msg.text != text:
        try:
            await event.edit(text, buttons=leaderboard_buttons())
        except Exception:
            pass
            
    # ✨ အရေးကြီးဆုံးအချက်: အခြား Calculator Callback တွေဆီ စီးဆင်းမသွားအောင် ဖြတ်တောက်လိုက်ခြင်း
    raise events.StopPropagation

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

# ==========================================
# 🎰 SYSTEM 4: TELETHON PORTED SLOT GAME
# ==========================================
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
    await set_balance(user_id, balance)

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
# ========================================================
# 🎁 SYSTEM 4.1: DAILY REWARD (24 HOURS COOLDOWN)
# ========================================================
@bot.on(events.NewMessage(pattern=r'(?i)^[./]daily(?:@\w+)?$'))
async def daily_reward_handler(event):
    user_id = event.sender_id
    current_time = time.time()
    
    # Database မှ အသုံးပြုသူ၏ လက်ရှိ Balance နှင့် နောက်ဆုံး Daily ယူခဲ့သည့် အချိန်ကို ဆွဲထုတ်ခြင်း
    doc = await slot_col.find_one({"user_id": user_id})
    
    last_daily = doc.get("last_daily", 0) if doc else 0
    balance = doc.get("balance", 0) if doc else 0
    
    # ၂၄ နာရီ စက္ကန့် တွက်ချက်ခြင်း (24 * 3600 = 86400 စက္ကန့်)
    cooldown = 86400
    elapsed_time = current_time - last_daily
    
    if elapsed_time < cooldown:
        # ကျန်ရှိသည့် အချိန်ကို နာရီ၊ မိနစ်၊ စက္ကန့် ပုံစံပြောင်းခြင်း
        remaining_time = cooldown - elapsed_time
        hours = int(remaining_time // 3600)
        minutes = int((remaining_time % 3600) // 60)
        seconds = int(remaining_time % 60)
        
        await event.reply(
            f"❌ **Daily Reward ကို ရယူပြီးသား ဖြစ်နေပါတယ်!**\n\n"
            f"⏳ နောက်တစ်ကြိမ် ထပ်မံရယူနိုင်ရန် စောင့်ဆိုင်းရန်အချိန် -\n"
            f"👉 `{hours:02d} နာရီ {minutes:02d} မိနစ် {seconds:02d} စက္ကန့်` ကျန်ပါသေးသည်။"
        )
        return

    # ၂၄ နာရီ ပြည့်ပြီဆိုပါက ငွေ ၅၀,၀၀၀ ထည့်ပေးပြီး အချိန်ကို Update လုပ်မည်
    new_balance = balance + 50000
    await slot_col.update_one(
        {"user_id": user_id},
        {"$set": {"balance": new_balance, "last_daily": current_time}},
        upsert=True
    )
    
    await event.reply(
        f"🎉 **Daily Reward အောင်မြင်စွာ ရယူပြီးပါပြီ!**\n\n"
        f"🎁 ယနေ့အတွက် ဆုကြေး: `50,000` MMK\n"
        f"💰 သင့်ရဲ့ လက်ရှိ စုစုပေါင်းကျန်ငွေ: `{new_balance:,}` MMK"
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

@bot.on(events.NewMessage(pattern=r'(?i)^/start$'))
async def general_start_handler(event):
    if event.chat_id == SPECIFIC_GROUP and event.sender_id == OWNER_ID:
        return  
        
    user_id = event.sender_id
    await get_balance(user_id)  
    user = await event.get_sender()
    first_name = user.first_name if user else "User"
    
    welcome_text = (
       f"🎰 **Welcome {first_name}!**\n\n"
       f"Here are the features available in this bot:\n\n"
       f"🛒 **Shop System:** Type `/shop` to view and purchase collection items!\n"
       f"🎒 **My Info:** Type `/myinfo` to view your balance, collection points, and rank tier.\n"
       f"🔢 **Calculator:** Type `/calc` to use the interactive panel.\n"
       f"🔤 **Translator:** Use `/tr <text>` to translate to English.\n"
       f"🎰 **Slot Game:** `/slot <amount>` to play."
    )  
    await event.reply(welcome_text)

# ==========================================
# 🛒 SHOP, INVENTORY, GIFT & ADMIN SYSTEMS
# ==========================================

def get_page_keyboard(items, page):
    """ Shop ရဲ့ စာမျက်နှာအလိုက် Inline Buttons ပုံစံတည်ဆောက်ရန် """
    buttons = []
    # Item များကို ၂ ခုတစ်တွဲ တန်းစီမည်
    row = []
    for idx, item in enumerate(items):
        item_id = item["item_id"]
        name = item["name"]
        row.append(Button.inline(f"{item_id}. {name}", f"shop_view_{item_id}_{page}"))
        if len(row) == 2 or idx == len(items) - 1:
            buttons.append(row)
            row = []
            
    # Navigation Buttons (Prev / Next)
    prev_page = 10 if page == 1 else page - 1
    next_page = 1 if page == 10 else page + 1
    
    nav_row = [
        Button.inline("◀️ Prev", f"shop_page_{prev_page}"),
        Button.inline(f"{page}/10", "shop_stay"),
        Button.inline("▶️ Next", f"shop_page_{next_page}")
    ]
    buttons.append(nav_row)
    return buttons

@bot.on(events.NewMessage(pattern=r'(?i)^/shop$'))
async def shop_command_handler(event):
    """ /shop command ဖြင့် ပစ္စည်းအရောင်းဆိုင် ဖွင့်လှစ်ပေးခြင်း """
    page = 1
    # Page 1 အတွက် Item စာရင်းအား DB မှ ဆွဲထုတ်ခြင်း (8 items per page)
    cursor = shop_items_col.find({"item_id": {"$gte": 1, "$lte": 8}}).sort("item_id", 1)
    items = await cursor.to_list(length=8)
    
    text = "🛒 **What do you want to buy?**\n\n"
    for item in items:
        text += f"{item['item_id']}. {item['name']}\n"
        
    await event.reply(text, buttons=get_page_keyboard(items, page))

@bot.on(events.NewMessage(pattern=r'(?i)^/myinfo$'))
async def myinfo_handler(event):
    """ အသုံးပြုသူ၏ လက်ကျန်ငွေ၊ Collection Points၊ Rank နှင့် ပစ္စည်းစာရင်းပြသခြင်း """
    # Owner က တခြားသူကို စစ်ဆေးခြင်း ရှိမရှိ စစ်ဆေးရန်
    target_user_id = event.sender_id
    user_label = "Your"
    
    if event.sender_id == OWNER_ID:
        if event.is_reply:
            rep = await event.get_reply_message()
            target_user_id = rep.sender_id
            user_label = "Target User"
        elif len(event.text.split()) > 1:
            try:
                target_user_id = int(event.text.split()[1])
                user_label = f"User ({target_user_id})"
            except ValueError:
                pass

    balance = await get_balance(target_user_id)
    total_cp = await get_user_total_cp(target_user_id)
    rank_tier = get_collection_title(total_cp)
    await slot_col.update_one({"user_id": target_user_id}, {"$set": {"points": total_cp}}, upsert=True)
    
    inv_doc = await inventory_col.find_one({"user_id": target_user_id})
    inv_text = ""
    
    if inv_doc and "items" in inv_doc:
        for item_id, qty in sorted(inv_doc["items"].items(), key=lambda x: int(x[0])):
            if qty > 0:
                item = await shop_items_col.find_one({"item_id": int(item_id)})
                if item:
                    inv_text += f"• {item['name']} (ID: {item_id}) x{qty}\n"
                    
    if not inv_text:
        inv_text = "No items owned yet. 🎒"

    info_msg = (
        f"🪪 **{user_label.upper()} PROFILE CARD**\n\n"
        f"💵 **Balance:** {balance:,} MMK\n"
        f"🔰 **Collection Points:** {total_cp:,}\n"
        f"🏆 **Collector Rank:** {rank_tier}\n\n"
        f"🎒 **Owned Items Inventory:**\n{inv_text}"
    )
    await event.reply(info_msg)

@bot.on(events.NewMessage(pattern=r'(?i)^/gift\s+(\d+)'))
async def gift_item_handler(event):
    """ /gift {item_id} ဖြင့် တခြားသူအား ပစ္စည်းလက်ဆောင်ပေးခြင်း (CP အလိုအလျောက် ပြောင်းလဲမည်) """
    if not event.is_reply:
        await event.reply("❌ **အသုံးပြုပုံ:** ပစ္စည်းပေးလိုသူ၏ စာအား Reply ထောက်ပြီး `/gift {item_id}` ဟု ရိုက်ပေးပါ။")
        return
        
    try:
        item_id = int(event.pattern_match.group(1))
    except ValueError:
        await event.reply("❌ **မှားယွင်းသော Item ID ဖြစ်ပါသည်။**")
        return
        
    sender_id = event.sender_id
    reply_msg = await event.get_reply_message()
    receiver_id = reply_msg.sender_id
    
    if sender_id == receiver_id:
        await event.reply("❌ ကိုယ့်ပစ္စည်းကိုယ် ပြန်လက်ဆောင်ပေးလို့ မရပါဘူးခင်ဗျာ။")
        return

    # ပစ္စည်းရှိမရှိ စစ်ဆေးခြင်း
    item = await shop_items_col.find_one({"item_id": item_id})
    if not item:
        await event.reply("❌ ဤ Item ID အား ဆိုင်ခန်းထဲတွင် ရှာမတွေ့ပါ။")
        return

    sender_inv = await inventory_col.find_one({"user_id": sender_id})
    if not sender_inv or "items" not in sender_inv or sender_inv["items"].get(str(item_id), 0) <= 0:
        await event.reply(f"❌ သင့်မှာ {item['name']} မရှိပါသဖြင့် လက်ဆောင်ပေး၍မရပါ။")
        return

    # ဒေတာဘေ့စ်တွင် ပစ္စည်းလွှဲပြောင်းခြင်း
    await inventory_col.update_one({"user_id": sender_id}, {"$inc": {f"items.{item_id}": -1}})
    await inventory_col.update_one({"user_id": receiver_id}, {"$inc": {f"items.{item_id}": 1}}, upsert=True)
    
    # တွက်ချက်မှုအသစ်များ ရယူရန်
    sender_cp = await get_user_total_cp(sender_id)
    receiver_cp = await get_user_total_cp(receiver_id)

    gift_success_text = (
        f"🎁 **Successfully Gifted!**\n\n"
        f"👤 ပေးပို့သူထံမှ {item['name']} x1 ကို လွှဲပြောင်းပေးလိုက်ပါပြီ။\n"
        f"📉 Your Collection Point is now: {sender_cp:,}\n"
        f"📈 Receiver Collection Point is now: {receiver_cp:,}"
    )
    await event.reply(gift_success_text)

# ==========================================
# ⚙️ OWNER ADMIN COMMANDS SYSTEM
# ==========================================
@bot.on(events.NewMessage(pattern=r'(?i)^/additem\s+(\d+)\s+(.+)\s+(\d+)\s+(\d+)'))
async def admin_add_item(event):
    if event.sender_id != OWNER_ID: return
    m = event.pattern_match
    item_id, name, price, cp = int(m.group(1)), m.group(2).strip(), int(m.group(3)), int(m.group(4))
    
    await shop_items_col.update_one(
        {"item_id": item_id},
        {"$set": {"item_id": item_id, "name": name, "price": price, "cp": cp}},
        upsert=True
    )
    await event.reply(f"✅ **Item Added/Updated:** {name} (ID: {item_id}) | Price: {price} | CP: {cp}")

@bot.on(events.NewMessage(pattern=r'(?i)^/removeitem\s+(\d+)'))
async def admin_remove_item(event):
    if event.sender_id != OWNER_ID: return
    item_id = int(event.pattern_match.group(1))
    res = await shop_items_col.delete_one({"item_id": item_id})
    if res.deleted_count > 0:
        await event.reply(f"✅ Item ID {item_id} ကို ဆိုင်ခန်းထဲမှ ဖျက်သိမ်းပြီးပါပြီ။")
    else:
        await event.reply("❌ ပစ္စည်းရှာမတွေ့ပါ။")

@bot.on(events.NewMessage(pattern=r'(?i)^/editprice\s+(\d+)\s+(\d+)'))
async def admin_edit_price(event):
    if event.sender_id != OWNER_ID: return
    item_id, new_price = int(event.pattern_match.group(1)), int(event.pattern_match.group(2))
    res = await shop_items_col.update_one({"item_id": item_id}, {"$set": {"price": new_price}})
    if res.modified_count > 0:
        await event.reply(f"✅ Item ID {item_id} ၏ ဈေးနှုန်းကို {new_price:,} MMK သို့ ပြောင်းလဲပြီးပါပြီ။")
    else:
        await event.reply("❌ ပြင်ဆင်၍မရပါ (သို့မဟုတ်) Item ID မရှိပါ။")

@bot.on(events.NewMessage(pattern=r'(?i)^/editrarity\s+(\d+)\s+(\d+)'))
async def admin_edit_rarity(event):
    if event.sender_id != OWNER_ID: return
    item_id, new_cp = int(event.pattern_match.group(1)), int(event.pattern_match.group(2))
    res = await shop_items_col.update_one({"item_id": item_id}, {"$set": {"cp": new_cp}})
    if res.modified_count > 0:
        await event.reply(f"✅ Item ID {item_id} ၏ Collection Point ကို {new_cp} သို့ ပြောင်းလဲပြီးပါပြီ။")
    else:
        await event.reply("❌ ပြင်ဆင်၍မရပါ (သို့မဟုတ်) Item ID မရှိပါ။")


# ==========================================
# 🎛️ GLOBAL CALLBACK QUERY ROUTER (CALCULATOR & SHOP INTERACTION)
# ==========================================
@bot.on(events.CallbackQuery)
async def global_callback_handler(event):
    data = event.data.decode('utf-8')
    user_id = event.sender_id
    
    # ------------------ SHOP SYSTEM CALLBACKS ------------------
    if data.startswith("shop_"):
        await event.answer() # အဝိုင်းလည်နေတာ ရပ်ရန်
        
        if data == "shop_stay":
            return
            
        # စာမျက်နှာပြောင်းလဲခြင်း (Pagination)
        if data.startswith("shop_page_"):
            page = int(data.split("_")[2])
            start_id = (page - 1) * 8 + 1
            end_id = page * 8
            
            cursor = shop_items_col.find({"item_id": {"$gte": start_id, "$lte": end_id}}).sort("item_id", 1)
            items = await cursor.to_list(length=8)
            
            text = "🛒 **What do you want to buy?**\n\n"
            for item in items:
                text += f"{item['item_id']}. {item['name']}\n"
                
            await event.edit(text, buttons=get_page_keyboard(items, page))
            return
            
        # ပစ္စည်းတစ်ခုချင်းစီ၏ အသေးစိတ်အချက်အလက်ကို ကြည့်ရှုခြင်း
        if data.startswith("shop_view_"):
            parts = data.split("_")
            item_id = int(parts[2])
            page = int(parts[3])
            
            item = await shop_items_col.find_one({"item_id": item_id})
            if not item: return
            
            balance = await get_balance(user_id)
            
            detail_text = (
                f"📦 **{item['name']}**\n\n"
                f"💰 **Price :** {item['price']:,} MMK\n"
                f"🔰 **Collection point :** {item['cp']}\n\n"
                f"💵 **Your Balance :** {balance:,} MMK\n"
                f"──────────────\n"
                f"Do you want to buy this item?"
            )
            
            buttons = [
                [Button.inline("🛒 Buy Now", f"shop_buy_{item_id}_{page}")],
                [Button.inline("⬅️ Back", f"shop_page_{page}")]
            ]
            await event.edit(detail_text, buttons=buttons)
            return
            
        # ပစ္စည်းဝယ်ယူခြင်းလုပ်ငန်းစဉ်
        if data.startswith("shop_buy_"):
            parts = data.split("_")
            item_id = int(parts[2])
            page = int(parts[3])
            
            item = await shop_items_col.find_one({"item_id": item_id})
            if not item: return
            
            balance = await get_balance(user_id)
            price = item['price']
            
            if balance < price:
                # ငွေမလုံလောက်ပါက ပြသမည့် စာမျက်နှာ
                fail_text = (
                    f"❌ **Insufficient Balance!**\n\n"
                    f"💰 **Price :** {price:,} MMK\n"
                    f"💵 **Your Balance :** {balance:,} MMK"
                )
                buttons = [[Button.inline("⬅️ Back to Shop", f"shop_page_{page}")]]
                await event.edit(fail_text, buttons=buttons)
                return
                
            # ငွေနုတ်ပြီး Inventory ထဲထည့်ခြင်း
            new_balance = balance - price
            await set_balance(user_id, new_balance)
            await inventory_col.update_one({"user_id": user_id}, {"$inc": {f"items.{item_id}": 1}}, upsert=True)
            await slot_col.update_one({"user_id": user_id}, {"$inc": {"points": item.get("cp", 0)}}, upsert=True)
            
            success_text = (
                f"✅ **Successfully purchased!**\n\n"
                f"{item['name']} x1\n"
                f"-{price:,} MMK\n\n"
                f"**Remaining Balance :**\n"
                f"{new_balance:,} MMK"
            )
            buttons = [[Button.inline("⬅️ Back to Shop", f"shop_page_{page}")]]
            await event.edit(success_text, buttons=buttons)
            return

    # ------------------ CALCULATOR SYSTEM CALLBACKS ------------------
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
            await event.reply("ရှာမတွေ့ပါ။ Username မှန်ကန်မှု ရှိမရှိ ပြန်စစ်ဆေးပေးပါ။")
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
        await event.reply(id_card)
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
        await event.reply(id_card)
        
@bot.on(events.NewMessage(chats=[OWNER_ID, SPECIFIC_GROUP], pattern=r'(?i)^/send$'))
async def universal_broadcast_handler(event):
    if event.sender_id != OWNER_ID:
        return

    if not event.is_reply:
        await event.reply("❌ **အသုံးပြုပုံ:** Forward လုပ်ချင်သော Message ကို Reply ထောက်ပြီး `/send` ဟု ရိုက်ပေးပါ။")
        return

    status_msg = await event.reply("🔄 **Universal Group Forwarding စတင်နေပါပြီ...**")

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
            await bot.forward_messages(target_chat_id, event.reply_to_msg_id, event.chat_id)
            success_count += 1
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
        await event.reply("✅ String Session ကို `tomboy_col` ထဲမှာ အောင်မြင်စွာ သိမ်းပြီးပါပြီ။ Userbot ချိတ်ဆက်နေသည်...")
        
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

async def init_shop_items():
    """ Bot စတက်ချိန်တွင် Item ၈၀ စလုံးကို ဒေတာဘေ့စ်ထဲသို့ အလိုအလျောက် သွင်းပေးရန် သီးသန့်စနစ် """
    count = await shop_items_col.count_documents({})
    if count >= 80:
        print("📦 Shop items are already initialized in MongoDB.")
        return

    print("⚙️ Initializing 80 shop items into MongoDB...")
    
    # Item အမည်များ စာရင်းတည်ဆောက်ခြင်း
    names_list = [
        "Bread", "Cake", "Fish", "Apple", "Avocado", "Banana", "Sandwich", "Potato",
        "Cat", "Dog", "Rabbit", "Fox", "Wolf", "Tiger", "Panda", "Dragon Egg",
        "Wooden Shield", "Iron Shield", "Helmet", "Chestplate", "Gloves", "Boots", "Ring", "Necklace",
        "Wood", "Bamboo", "Leather", "Rope", "Cloth", "Feather", "Bone", "Crystal",
        "Wheat", "Corn", "Carrot", "Tomato", "Onion", "Pumpkin", "Cabbage", "Chili",
        "Wooden Sword", "Iron Sword", "Steel Sword", "Bow", "Arrow", "Dagger", "Spear", "Axe",
        "Salmon", "Tuna", "Octopus", "Squid", "Oyster", "Pearl", "Seaweed", "Coral",
        "T-Shirt", "Hoodie", "Jacket", "Gloves", "Hat", "Scarf", "Sneakers", "Backpack",
        "Magic Crystal", "Fire Crystal", "Water Crystal", "Wind Crystal", "Earth Crystal", "Magic Orb", "Spell Book", "Enchanted Gem",
        "Diamond", "Pink diamond", "Star opal", "Dragon diamond", "Diamond ring", "Academy Gold", "Crude oil", "Infinity Diamonds"
    ]
    
    # ဈေးနှုန်းနှင့် CP စည်းမျဉ်းများ သတ်မှတ်ခြင်း
    for idx, name in enumerate(names_list):
        item_id = idx + 1
        
        if 1 <= item_id <= 8:
            price, cp = 60000, 50
        elif 9 <= item_id <= 16:
            price, cp = 90000, 100
        elif 17 <= item_id <= 24:
            price, cp = 130000, 200
        elif 25 <= item_id <= 32:
            price, cp = 150000, 400
        elif 33 <= item_id <= 40:
            price, cp = 300000, 500
        elif 41 <= item_id <= 48:
            price, cp = 400000, 800
        elif 49 <= item_id <= 56:
            price, cp = 900000, 1200
        elif 57 <= item_id <= 64:
            price, cp = 1000000, 1800
        elif 65 <= item_id <= 72:
            price, cp = 2000000, 2000
        elif 73 <= item_id <= 80:
            price, cp = 4000000, 5000
            
        await shop_items_col.update_one(
            {"item_id": item_id},
            {"$set": {"item_id": item_id, "name": name, "price": price, "cp": cp}},
            upsert=True
        )
    print("✅ 80 Shop items initialization successful!")

async def startup():
    global is_active, userbot
    print("⏳ System starting up and loading configurations from MongoDB...")
    
    # Item စာရင်း ၈၀ အား DB ထဲသို့ စတင်ထည့်သွင်းခြင်း
    await init_shop_items()
    
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
    loop.run_until_complete(startup())
