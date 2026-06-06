import os
import asyncio
import random
import time
import logging
import re
from datetime import datetime
from telethon import TelegramClient, events, errors
from telethon.sessions import StringSession
from motor.motor_asyncio import AsyncIOMotorClient

# ==========================================
# ⚙️ CONFIGURATION (Credentials)
# ==========================================
MONGO_URI = "mongodb+srv://khantphyoemin537_db_user:9VRKiaeZkz7rJdpz@cluster0.w6tgi8j.mongodb.net/telegram_bot?appName=Cluster0&tlsAllowInvalidCertificates=true"
APP_ID = 31566870
APP_HASH = '579663bdeae6426ca3c7e9feb3f9ca35'
BOT_TOKEN = '8111794244:AAGpkLE7h5x_IYFvjkVCbJosDC1TFbCGxcQ'

OWNER_ID = 6015356597
SPECIFIC_GROUP = -1003999318284

# 🎯 BOT ID CONFIGURATIONS
SPAWN_BOT_ID = 6157455819
HINT_BOT_ID = 8506436817
WAIFU_CHAT_ID = -1003999318284

# Global States & Multi-Client Tracking
running_clients = {}          # { "session_string": client_instance }
processed_spawns = set()      # Spawn ထပ်မံ Forward မဖြစ်စေရန် ထိန်းပေးမည့် Cache
spawn_tracker = {}            # Waifu Chat မက်ဆေ့ခ်ျ ID နှင့် မူရင်း Group ID ချိတ်ဆက်ပေးမည့် Map
group_clients_tracker = {}    # { group_id: {client_id1, client_id2} } ဘယ်ဂရုထဲမှာ ဘယ်ဖောက်သည်တွေရှိလဲ မှတ်မည့်နေရာ
last_spawn_chat_id = None     
is_catch_stopped = False      
HINT_REGEX = re.compile(r"(/catch\s+[^\n]+)") 

# MongoDB Setup
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]
sessions_col = db["user_sessions"]  

# Initialize Official Bot Client
bot = TelegramClient('official_bot_session', APP_ID, APP_HASH)

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
        print(f"🌍 Dummy HTTP Server started on port {port} for Render!")
        async with server:
            await server.serve_forever()
    except Exception as e:
        print(f"❌ Failed to start Dummy Web Server: {e}")

# ==========================================
# 🗑️ AUTO-DELETE /CATCH COMMAND TASK
# ==========================================
async def delete_catch_message_delayed(client, chat_id, msg_id):
    try:
        await asyncio.sleep(1)
        await client.delete_messages(chat_id, msg_id)
        print(f"🗑️ Auto-deleted /catch message {msg_id} after 1 second.")
    except Exception as e:
        print(f"❌ Failed to delete /catch message: {e}")

# ==========================================
# ⚔️ ULTRA SPEED MULTI-ACCOUNT CATCHER SYSTEM
# ==========================================
async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker, processed_spawns, group_clients_tracker
    
    if event.sender_id == SPAWN_BOT_ID and event.text:
        text_content = event.text
        
        # ⚡ [FIXED] တောင်းဆိုထားသည့်အတိုင်း စာသားအပြည့်အစုံ ကွက်တိပါဝင်မှသာ အလုပ်လုပ်ရန် စစ်ဆေးခြင်း
        # Small Caps စာသားပုံစံ နှစ်ကြောင်းစလုံး မဖြစ်မနေ ပါဝင်ရမည်ဖြစ်ပြီး စာလုံးအချို့ပါရုံနှင့် မလုပ်တော့ပါ
        is_spawn_msg = (
            "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in text_content and
            "ᴀᴅᴅ ᴛʜɪs ᴄʜᴀʀᴀᴄᴛᴇʀ ᴛᴏ ʏᴏᴜʀ ʜᴀʀᴇᴍ ᴜsɪɴɢ /catch" in text_content
        )
        
        if is_spawn_msg:
            # 🚫 Safe Zone Groups
            if event.chat_id in [-1003580630982, -1004067509608]:
                return  

            # Rare Emojis စစ်ထုတ်ခြင်း
            if any(emoji in text_content for emoji in ["🔵", "🟣", "🟠"]):
                return  

            orig_chat_id = event.chat_id
            last_spawn_chat_id = orig_chat_id  
            
            # လက်ရှိဂရုထဲမှာ ဒီ Spawn ကို လန်းမြင်ရတဲ့ ဖောက်သည်အကောင့်တွေကို Dynamic အရင်ဆုံး မှတ်သားမည်
            client_id = getattr(event.client, 'me_id', None)
            if client_id:
                if orig_chat_id not in group_clients_tracker:
                    group_clients_tracker[orig_chat_id] = set()
                group_clients_tracker[orig_chat_id].add(client_id)

            # ⚡ Smart Deduplication: ဘယ်သူပဲအရင်မြင်မြင် Waifu Chat ဆီ တစ်ခါပဲ Forward သွားစေရန်
            spawn_key = f"{orig_chat_id}_{event.id}"
            if spawn_key in processed_spawns:
                return
            processed_spawns.add(spawn_key)
            
            if len(processed_spawns) > 300:
                processed_spawns.remove(next(iter(processed_spawns)))
            
            try:
                # ပုံ သို့မဟုတ် ဗီဒီယိုဖြစ်စေ Caption နှင့်တကွ Waifu Chat ဆီ ဖော်ဝါ့ဒ်လုပ်ပြီး /waifu ဟု Reply ပြန်ခြင်း
                fwd_msg = await event.message.forward_to(WAIFU_CHAT_ID)
                reply_msg = await fwd_msg.reply("/waifu")
                
                spawn_tracker[fwd_msg.id] = orig_chat_id
                spawn_tracker[reply_msg.id] = orig_chat_id
                
                if len(spawn_tracker) > 200:
                    spawn_tracker.pop(next(iter(spawn_tracker)))
                    
            except Exception as e:
                print(f"❌ Forward Spawn Error: {e}")


async def hint_solver_handler(event):
    global last_spawn_chat_id, spawn_tracker, is_catch_stopped, group_clients_tracker
    
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
                if target_group in [-1003580630982, -1004067509608]:
                    return
                try:
                    client_id = getattr(event.client, 'me_id', None)
                    valid_clients = group_clients_tracker.get(target_group, set())
                    
                    # လက်ရှိဂရုထဲမှာ တကယ်ရှိနေတဲ့ အကောင့်ဖြစ်မှသာ စာလှမ်းအော်မည်
                    if client_id and client_id not in valid_clients:
                        return
                    
                    # ဂရုတူအချင်းချင်းကြားတွင် Flood မမိစေရန် Delay ခွဲပေးခြင်း
                    delay_time = random.uniform(0.5, 0.6) 
                    await asyncio.sleep(delay_time)
                    
                    sent_msg = await event.client.send_message(target_group, catch_command)
                    
                    # ပို့ပြီးသား /catch စာသားကို ၁ စက္ကန့်အကြာတွင် ပြန်ဖျက်ခြင်း
                    asyncio.create_task(delete_catch_message_delayed(event.client, target_group, sent_msg.id))
                    
                except Exception as e:
                    pass


async def catch_success_forwarder_handler(event):
    """ ဖောက်သည်အကောင့်များထဲမှ တစ်ခုခု ကတ်မိသွားရင် သတ်မှတ် Group ထဲ Forward ပို့ပေးမည့်စနစ် """
    if event.sender_id == SPAWN_BOT_ID and event.text:
        text_content = event.text
        
        is_success_msg = any(trigger in text_content or trigger in text_content.upper() for trigger in [
            "YOU GOT A NEW CHARACTER!", 
            "%sOU GOT A NEW CHARACTER!" % "ʏ", # Unicode compatibility safe check
            "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!", 
            "NORTHROP", 
            "NORDSTROM"
        ])
        
        if is_success_msg:
            # ⚡ [FIXED] လက်ရှိ အလုပ်လုပ်နေတဲ့ Userbot အကောင့်ကိုယ်တိုင်ကို မန်းရှင်းခေါ်ထားတာ သေချာမှသာ Forward လုပ်မည့်စနစ်
            client_id = getattr(event.client, 'me_id', None)
            is_me_mentioned = False
            
            # ၁။ Telethon ရဲ့ Built-in Mention စစ်ချက် (Username Mention အတွက်)
            if event.message.mentioned:
                is_me_mentioned = True
            
            # ၂။ Text Mention Entity ထဲမှာ မိမိရဲ့ User ID တကယ်ပါမပါ သေချာအောင် ထပ်ဆင့် Double-Check စစ်ခြင်း
            if not is_me_mentioned and event.message.entities:
                for entity in event.message.entities:
                    if hasattr(entity, 'user_id') and entity.user_id == client_id:
                        is_me_mentioned = True
                        break
                        
            # မိမိအကောင့်ကို တကယ်မန်းရှင်းခေါ်ပြီး ဂုဏ်ပြုစာပို့ထားတာ ဟုတ်မှသာ SPECIFIC_GROUP ဆီ Forward လှမ်းတင်မည်
            if is_me_mentioned:
                try:
                    await event.message.forward_to(SPECIFIC_GROUP)
                    print(f"📦 [Account: {client_id}] Successfully forwarded caught card report to SPECIFIC_GROUP.")
                except Exception as e:
                    print(f"❌ Success Card Forward Error: {e}")

# ==========================================
# 🚀 DYNAMIC CLIENT STARTER FUNCTION
# ==========================================
async def start_new_userbot(session_str):
    global running_clients
    if session_str in running_clients:
        return True
    try:
        client = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
        await client.start()
        
        me = await client.get_me()
        client.me_id = me.id
        
        client.add_event_handler(spawn_detector_handler, events.NewMessage())
        client.add_event_handler(hint_solver_handler, events.NewMessage())
        client.add_event_handler(catch_success_forwarder_handler, events.NewMessage())
        
        running_clients[session_str] = client
        return True
    except Exception as e:
        print(f"❌ Failed to launch userbot session: {e}")
        return False

# ==========================================
# 🤖 OFFICIAL BOT COMMAND HANDLERS
# ==========================================
@bot.on(events.NewMessage(chats=SPECIFIC_GROUP))
async def handle_bot_commands(event):
    global is_catch_stopped, running_clients
    
    if event.sender_id != OWNER_ID:
        return

    cmd = event.message.text.strip() if event.message.text else ""

    if cmd.startswith("/string2"):
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
            
        await sessions_col.update_one(
            {"session_str": session_str},
            {"$set": {"session_str": session_str, "added_at": datetime.utcnow()}},
            upsert=True
        )
        
        await event.reply("⏳ String Session အသစ်ကို DB ထဲသိမ်းပြီးပါပြီ။ လှမ်းချိတ်ဆက်နေသည်...")
        
        success = await start_new_userbot(session_str)
        if success:
            await event.reply(f"🚀 **Userbot အသစ် အသက်ဝင်လာပါပြီ!**\nစုစုပေါင်း Active ဖောက်သည်အကောင့်: `{len(running_clients)}` ခု ရှိသွားပါပြီ Chief!")
        else:
            await event.reply("❌ အဆိုပါ String Session အား ချိတ်ဆက်၍မရပါ (Expired ဖြစ်နေနိုင်သည်)။")

    elif cmd == "/stop":
        is_catch_stopped = True
        await event.reply("🛑 **Chief! အကောင့်အားလုံးရဲ့ `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**")

    elif cmd == "/start":
        is_catch_stopped = False
        await event.reply("✅ **Chief! အကောင့်အားလုံးရဲ့ `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်အသက်သွင်းလိုက်ပါပြီ။**")

    elif cmd == "/status":
        await event.reply(f"📊 **System Status Check:**\n\n👤 Total Active Accounts: `{len(running_clients)}` ခု\n⚙️ Sniper Status: `{'STOPPED 🛑' if is_catch_stopped else 'RUNNING ⚡'}`")

# ==========================================
# 🚀 SYSTEM STARTUP LOGIC (LOAD ALL SESSIONS)
# ==========================================
async def startup():
    print("⏳ Loading multi-account configurations from MongoDB...")
    asyncio.create_task(start_dummy_web_server())

    cursor = sessions_col.find({})
    session_docs = await cursor.to_list(length=500) 
    
    if session_docs:
        print(f"Found {len(session_docs)} sessions in database. Starting activation loop...")
        tasks = [start_new_userbot(doc["session_str"]) for doc in session_docs]
        await asyncio.gather(*tasks)
        print(f"🎉 Successfully loaded `{len(running_clients)}` active accounts concurrently!")
    else:
        print("💡 No String Sessions found in MongoDB. Use /string2 to add accounts.")

    await bot.start(bot_token=BOT_TOKEN)
    print("🤖 Official Main Bot is successfully running...")
    await bot.run_until_disconnected()

if __name__ == '__main__':
    asyncio.run(startup())
