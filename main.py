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
# ⚙️ CONFIGURATION (Credentials - FIXED TO ORIGINAL)
# ==========================================
MONGO_URI = "mongodb+srv://khantphyoemin537_db_user:9VRKiaeZkz7rJdpz@cluster0.w6tgi8j.mongodb.net/telegram_bot?appName=Cluster0&tlsAllowInvalidCertificates=true"
APP_ID = 39584681
APP_HASH = 'c8c0685d6dd5b9e546093ea90d27733b'
BOT_TOKEN = '8575371720:AAEWWV42CGrwooM_joiJXdo2iEw2_7atyXU'

OWNER_ID = 6015356597
SPECIFIC_GROUP = -1004296091424
COOLDOWN_TIME = 15

# 🎯 BOT ID CONFIGURATIONS
SPAWN_BOT_ID = 6157455819
HINT_BOT_ID = 8506436817
WAIFU_CHAT_ID = -1004296091424

# Global States & Multi-Client Trackers
running_clients = {}          # { "session_string": client_instance }
processed_spawns = set()      # Spawn တစ်ခါပဲ Forward ဖြစ်စေရန် Cache
processed_catches = set()     # အကောင့်တွေအချင်းချင်း /catch လုမအော်စေရန်အုပ်ထိန်းမှု Cache
spawn_tracker = {}            # Waifu Chat ID နှင့် မူရင်း Group ID ချိတ်ဆက်မှု Map
last_spawn_chat_id = None     
is_active = False
is_scraping = False
is_talker_active = False       
message_count = 0
spam_tasks = {}
user_cooldowns = {}
is_catch_stopped = False      
HINT_REGEX = re.compile(r"(/catch\s+[^\n]+)") 

# MongoDB Setup
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]
reply_save_col = db["reply_save_col"]
target_bots_col = db["target_bots"]  
config_col = db["config_col"]
talk_col = db["random_talk"]   
filters_col = db["filters"]
multi_sessions_col = db["multi_user_sessions"] # Multi-Account အတွက် သီးသန့် Collection

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
        print(f"🌍 Dummy HTTP Server started on port {port} for Render Health Check!")
        async with server:
            await server.serve_forever()
    except Exception as e:
        print(f"❌ Failed to start Dummy Web Server: {e}")

# ==========================================
# 🗑️ ANTI-FLOOD DELAYED DELETION TASKS
# ==========================================
async def delete_bot_message_delayed(event, bot_msg_id, cmd_msg_id=0):
    try:
        await asyncio.sleep(3)
        to_delete = [bot_msg_id]
        if cmd_msg_id:
            to_delete.append(cmd_msg_id)
        await event.client.delete_messages(event.chat_id, to_delete)
    except Exception:
        pass

async def delete_catch_message_delayed(client, chat_id, msg_id):
    try:
        await asyncio.sleep(1)
        await client.delete_messages(chat_id, msg_id)
        print(f"🗑️ Auto-deleted /catch message {msg_id} after 1 second.")
    except Exception as e:
        print(f"❌ Failed to delete /catch message: {e}")

# ==========================================
# ⚔️ ANTI-FLOOD RAID / SPAM TASK SYSTEM
# ==========================================
async def run_raid_spam_task(event, reply_msg_id, chat_id):
    try:
        while True:
            pipeline = [{"$sample": {"size": 1}}]
            cursor = filters_col.aggregate(pipeline)
            docs = await cursor.to_list(length=1)
            
            if docs:
                reply_text = docs[0].get("text") or docs[0].get("word") or "🎯"
                try:
                    await event.client.send_message(chat_id, reply_text, reply_to=reply_msg_id)
                    await asyncio.sleep(1.0)
                except errors.rpcerrorlist.FloodWaitError as e:
                    await asyncio.sleep(e.seconds)
                except Exception:
                    await asyncio.sleep(1.0)
            else:
                await asyncio.sleep(2.0)
    except asyncio.CancelledError:
        print(f"🛑 Raid Task Stopped for Chat ID: {chat_id}")

# ==========================================
# ⚔️ ANIME SPAWN DETECTOR & CATCHER HANDLERS
# ==========================================
async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker, processed_spawns
    
    if event.sender_id == SPAWN_BOT_ID and event.text:
        # Strict Full Matching to avoid false triggers
        is_spawn_msg = (
            "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in event.text and
            "A CHARACTER HAS SPAWNED IN THE CHAT!" in event.text.upper()
        )
        
        if is_spawn_msg:
            if event.chat_id in [-1004296091424, -1004396091424]:
                return  

            if any(emoji in event.text for emoji in ["🔵", "🟣", "🟠"]):
                return  

            orig_chat_id = event.chat_id
            last_spawn_chat_id = orig_chat_id  
            
            # Smart Deduplication: အကောင့်တစ်ခုက Forward လုပ်ပြီးရင် ကျန်အကောင့်များကျော်သွားမည်
            spawn_key = f"{orig_chat_id}_{event.id}"
            if spawn_key in processed_spawns:
                return
            processed_spawns.add(spawn_key)
            
            if len(processed_spawns) > 200:
                processed_spawns.remove(next(iter(processed_spawns)))
            
            try:
                fwd_msg = await event.message.forward_to(WAIFU_CHAT_ID)
                reply_msg = await fwd_msg.reply("/waifu")
                
                spawn_tracker[fwd_msg.id] = orig_chat_id
                spawn_tracker[reply_msg.id] = orig_chat_id
                
                if len(spawn_tracker) > 200:
                    spawn_tracker.pop(next(iter(spawn_tracker)))
            except Exception:
                pass

async def hint_solver_handler(event):
    global last_spawn_chat_id, spawn_tracker, is_catch_stopped, processed_catches
    
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
                if target_group in [-1004296091424, -1004396091424]:
                    return
                
                # Coordinated Catch: ဤမက်ဆေ့ခ်ျအတွက် အကောင့်တစ်ခုပဲ Catch အော်စေရန် ထိန်းချုပ်ခြင်း
                catch_key = f"{target_group}_{event.reply_to_msg_id}"
                if catch_key in processed_catches:
                    return
                processed_catches.add(catch_key)
                
                try:
                    delay_time = random.uniform(0.5, 0.8) 
                    async with event.client.action(target_group, 'typing'):
                        await asyncio.sleep(delay_time)
                        
                    sent_msg = await event.client.send_message(target_group, catch_command)
                    print(f"🎯 [Account: Caught] Sent command to group: {target_group}")
                    
                    asyncio.create_task(delete_catch_message_delayed(event.client, target_group, sent_msg.id))
                except Exception as e:
                    print(f"❌ Catch Error: {e}")

async def catch_success_forwarder_handler(event):
    """ မိမိအကောင့် သီးသန့်မန်းရှင်းပါမှ သတ်မှတ် Group ဆီ Report လှမ်းတင်ပေးမည့် Double-Check စနစ် """
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!" in event.text or "YOU GOT A NEW CHARACTER!" in event.text.upper():
            
            client_me = await event.client.get_me()
            client_id = client_me.id
            is_me_mentioned = False
            
            if event.message.mentioned:
                is_me_mentioned = True
                
            if not is_me_mentioned and event.message.entities:
                for entity in event.message.entities:
                    if hasattr(entity, 'user_id') and entity.user_id == client_id:
                        is_me_mentioned = True
                        break
                        
            if is_me_mentioned:
                try:
                    await event.message.forward_to(SPECIFIC_GROUP)
                    print(f"📦 Successfully forwarded caught card for account: {client_id}")
                except Exception as e:
                    print(f"❌ Success Card Forward Error: {e}")

# ==========================================
# 🧠 USERBOT EVENT HANDLER (COLLECTIVE CHAT SYSTEM)
# ==========================================
async def handle_userbot_reply(event):
    global is_active, user_cooldowns, is_talker_active, message_count, spam_tasks
    
    if not event.message or event.message.text is None:
        return

    cmd = event.message.text.strip()

    if event.out:  
        if cmd == "သေမယ်နော်" and event.is_reply:
            if event.chat_id in spam_tasks:
                spam_tasks[event.chat_id].cancel()
            reply_msg = await event.get_reply_message()
            task = asyncio.create_task(run_raid_spam_task(event, reply_msg.id, event.chat_id))
            spam_tasks[event.chat_id] = task
            await event.delete()  
            return
        elif cmd == "ဖာသည်မသား":
            if event.chat_id in spam_tasks:
                spam_tasks[event.chat_id].cancel()
                del spam_tasks[event.chat_id]
            await event.delete()  
            return

    if event.chat_id != SPECIFIC_GROUP:
        return

    if event.sender_id == OWNER_ID and cmd == "/ဖျက်မည်":
        if event.is_reply:
            reply_msg = await event.get_reply_message()
            reply_sender = await reply_msg.get_sender()
            if reply_sender and reply_sender.bot:
                bot_id = reply_sender.id
                await target_bots_col.update_one(
                    {"bot_id": bot_id},
                    {"$set": {"bot_id": bot_id, "username": reply_sender.username}},
                    upsert=True
                )
                await event.reply(f"🎯 Bot ID: `{bot_id}` ကို မှတ်ပြီးပါပြီ။")
                asyncio.create_task(delete_bot_message_delayed(event, reply_msg.id, event.id))
                return

    sender = await event.get_sender()
    if sender and sender.bot:
        is_target = await target_bots_col.find_one({"bot_id": event.sender_id})
        if is_target:
            asyncio.create_task(delete_bot_message_delayed(event, event.id, 0))
            return

    if is_talker_active:
        if event.out or (sender and sender.bot):
            return
        user_text = event.message.text.strip()
        if not user_text:
            return

        message_count += 1
        if message_count >= 8:
            message_count = 0
            pipeline = [{"$sample": {"size": 1}}]
            cursor = talk_col.aggregate(pipeline)
            random_docs = await cursor.to_list(length=1)

            if random_docs:
                reply_text = random_docs[0].get("text")
                if reply_text:
                    try:
                        await event.client.send_read_acknowledge(event.chat_id, max_id=event.id)
                        typing_delay = max(2.0, min(len(reply_text) * 0.1, 5.0))
                        async with event.client.action(event.chat_id, 'typing'):
                            await asyncio.sleep(typing_delay)
                        await event.respond(reply_text)
                    except Exception:
                        pass
            return

    if not is_active or event.out or (sender and sender.bot):
        return

    user_text = event.message.text.strip().lower()
    if not user_text:
        return

    user_id = event.sender_id
    current_time = time.time()
    if user_id in user_cooldowns and (current_time - user_cooldowns[user_id] < COOLDOWN_TIME):
        return
    user_cooldowns[user_id] = current_time

    try:
        reply_text = None
        match_pipeline = [
            {"$match": {
                "$and": [
                    {"$expr": {"$gte": [{"$strLenCP": "$trigger"}, 3]}},
                    {"trigger": {"$regex": user_text, "$options": "i"}}
                ]
            }},
            {"$sample": {"size": 1}}
        ]
        cursor_match = reply_save_col.aggregate(match_pipeline)
        matched_docs = await cursor_match.to_list(length=1)

        if matched_docs and matched_docs[0].get("responses"):
            reply_text = random.choice(matched_docs[0]["responses"])
        else:
            if random.random() < 0.20:  
                pipeline_fallback = [{"$sample": {"size": 1}}]
                cursor_fallback = reply_save_col.aggregate(pipeline_fallback)
                random_docs = await cursor_fallback.to_list(length=1)
                
                if random_docs and random_docs[0].get("responses"):
                    reply_text = random.choice(random_docs[0]["responses"])
                else:
                    cursor_talk = talk_col.aggregate(pipeline_fallback)
                    random_talk_docs = await cursor_talk.to_list(length=1)
                    reply_text = random_talk_docs[0].get("text") if random_talk_docs else None
            else:
                return

        if reply_text:
            await event.client.send_read_acknowledge(event.chat_id, max_id=event.id)
            async with event.client.action(event.chat_id, 'voice'):
                await asyncio.sleep(random.uniform(1.5, 3.5))
            await event.reply(reply_text)
    except Exception as e:
        print(f"❌ Auto-Reply Error: {e}")

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
                        await asyncio.sleep(e.seconds)
                        try:
                            await event.client.send_message(dialog.id, target_msg)
                            success_count += 1
                        except Exception:
                            fail_count += 1
                    except Exception:
                        fail_count += 1
            
            await status_msg.edit(f"📊 **Broadcast လုပ်ငန်းစဉ် ပြီးဆုံးပါပြီ Chief!**\n\n✅ အောင်မြင်: `{success_count}` ခု\n❌ ပို့မရ: `{fail_count}` ခု")

# ==========================================
# 📥 USERBOT SCRAPING TASK
# ==========================================
async def scrape_history_task():
    global is_scraping, running_clients
    if not running_clients:
        await bot.send_message(SPECIFIC_GROUP, "❌ Active Userbot အကောင့်မရှိသေးပါ။ /string ဖြင့် အရင်ထည့်ပေးပါ။")
        return

    is_scraping = True
    await bot.send_message(SPECIFIC_GROUP, "📥 စာဟောင်းများမှ Reply များကို စတင်မှတ်သားနေပါပြီ...")
    
    # ရရှိနိုင်သော ပထမဆုံး အကောင့်အား Worker အဖြစ် အသုံးပြုမည်
    worker_client = next(iter(running_clients.values()))
    
    try:
        msg_cache = {}
        total_saved = 0
        FETCH_LIMIT = 50000    

        async for msg in worker_client.iter_messages(SPECIFIC_GROUP, limit=FETCH_LIMIT):
            if msg and msg.text:
                msg_cache[msg.id] = msg.text.strip()

        async for msg in worker_client.iter_messages(SPECIFIC_GROUP, limit=FETCH_LIMIT):
            if not is_scraping:
                break
            try:
                if msg and msg.reply_to_msg_id and msg.text:
                    parent_id = msg.reply_to_msg_id
                    parent_text = msg_cache.get(parent_id)
                    reply_text = msg.text.strip()

                    if parent_text and reply_text:
                        trigger = parent_text.lower()
                        if (trigger.startswith(('/', '.', 'မှတ်', 'reply')) or reply_text.startswith(('/', '.', 'မှတ်', 'reply')) or "http" in trigger or "@" in trigger):
                            continue

                        existing_doc = await reply_save_col.find_one({"trigger": trigger})
                        if existing_doc:
                            if reply_text not in existing_doc.get("responses", []):
                                await reply_save_col.update_one({"trigger": trigger}, {"$push": {"responses": reply_text}})
                                total_saved += 1
                        else:
                            await reply_save_col.insert_one({"trigger": trigger, "responses": [reply_text]})
                            total_saved += 1

                        if total_saved % 100 == 0:
                            await bot.send_message(SPECIFIC_GROUP, f"🚀 စာစောင် ပေါင်း {total_saved} ခု DB ထဲ မှတ်ပြီးပါပြီ!")
                        await asyncio.sleep(0.02)
            except Exception:
                continue

        await bot.send_message(SPECIFIC_GROUP, f"🎉 အောင်မြင်စွာ Reply စုစုပေါင်း {total_saved} ခုကို DB ထဲ သိမ်းဆည်းပြီးပါပြီ!")
    except Exception as e:
        await bot.send_message(SPECIFIC_GROUP, f"❌ Scraping ပြဿနာတက်ခဲ့သည်: {e}")
    finally:
        is_scraping = False

# ==========================================
# 🚀 DYNAMIC CLIENT INSTANCE LAUNCHER
# ==========================================
async def start_new_userbot(session_str):
    global running_clients
    if session_str in running_clients:
        return True
    try:
        client = TelegramClient(StringSession(session_str), APP_ID, APP_HASH)
        await client.start()
        
        # Register Handlers to individual instance
        client.add_event_handler(handle_userbot_reply, events.NewMessage())
        client.add_event_handler(spawn_detector_handler, events.NewMessage())
        client.add_event_handler(hint_solver_handler, events.NewMessage())
        client.add_event_handler(mass_broadcast_handler, events.NewMessage(outgoing=True))
        client.add_event_handler(catch_success_forwarder_handler, events.NewMessage())
        
        running_clients[session_str] = client
        return True
    except Exception as e:
        print(f"❌ Failed to launch userbot instance: {e}")
        return False

# ==========================================
# 🤖 OFFICIAL BOT COMMAND HANDLERS
# ==========================================
@bot.on(events.NewMessage(chats=SPECIFIC_GROUP))
async def handle_bot_commands(event):
    global is_active, is_scraping, is_talker_active, is_catch_stopped, running_clients
    
    if event.sender_id != OWNER_ID:
        return

    cmd = event.message.text.strip() if event.message.text else ""

    # /string command ဖြင့် အကောင့်အသစ်များကို အကန့်အသတ်မရှိ တိုးမြှင့်ထည့်သွင်းနိုင်ခြင်း
    if cmd.startswith("/string"):
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
            
        await multi_sessions_col.update_one(
            {"session_str": session_str},
            {"$set": {"session_str": session_str, "added_at": datetime.utcnow()}},
            upsert=True
        )
        await event.reply("⏳ Session အား Multi-DB ထဲသိမ်းဆည်းပြီးပါပြီ။ လှမ်းချိတ်ဆက်နေသည်...")
        
        success = await start_new_userbot(session_str)
        if success:
            await event.reply(f"🚀 **Userbot အကောင့်အသစ် Live ဖြစ်သွားပါပြီ!**\nစုစုပေါင်း Active Accounts: `{len(running_clients)}` ခု")
        else:
            await event.reply("❌ အဆိုပါ String Session အား ချိတ်ဆက်၍မရပါ (မာန်ဗော်တာ သို့မဟုတ် Expired ဖြစ်နိုင်သည်)")

    elif cmd == "/stop":
        is_catch_stopped = True
        await event.reply("🛑 **Chief! `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**")

    elif cmd == "/start":
        is_catch_stopped = False
        await event.reply("✅ **Chief! `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်စတင်လိုက်ပါပြီ။**")

    elif cmd == "/ဟိုက်":
        is_active = True
        await event.reply("စာလိုက်ထောက်ပီ")

    elif cmd == "/ဟိုက်း":
        is_active = False
        await event.reply("စာလိုက်ထောက်တော့ဘူးမောတယ်")

    elif cmd == "/ပြောမယ်":
        is_talker_active = True
        await event.reply("💬 Talker mode activated.")
     
    elif cmd == "/မပြောဘူး":
        is_talker_active = False
        await event.reply("🔇 Talker mode deactivated.")

    elif cmd == "/replyမှတ်":
        if is_scraping:
            await event.reply("⚠️ ယခုအချိန်တွင် စာမှတ်ခြင်းအလုပ် လုပ်ဆောင်နေဆဲဖြစ်သည်!")
            return
        asyncio.create_task(scrape_history_task())
        
    elif cmd == "/status":
        await event.reply(f"📊 **System Multi-Account Status:**\n\n👤 Total Active Accounts: `{len(running_clients)}` ခု\n⚙️ Catcher Sniper: `{'STOPPED 🛑' if is_catch_stopped else 'RUNNING ⚡'}`\n🤖 Auto-Reply: `{'ON ✅' if is_active else 'OFF ❌'}`")

# ==========================================
# 🚀 SYSTEM STARTUP LOGIC
# ==========================================
async def startup():
    global is_active
    print("⏳ Loading multi-account configurations from MongoDB...")
    asyncio.create_task(start_dummy_web_server())

    # 1. Old System Legacy Session ကိုပါ ကောက်ယူပေးခြင်း (Backward Compatibility)
    legacy_doc = await config_col.find_one({"key": "string_session"})
    if legacy_doc:
        legacy_session = legacy_doc.get("value")
        await multi_sessions_col.update_one(
            {"session_str": legacy_session},
            {"$set": {"session_str": legacy_session, "added_at": datetime.utcnow()}},
            upsert=True
        )

    # 2. Multi-Sessions အကောင့်များအားလုံးကို DB ထဲမှ ဆွဲထုတ်၍ ပြိုင်တူနှိုးခြင်း
    cursor = multi_sessions_col.find({})
    session_docs = await cursor.to_list(length=500)
    
    if session_docs:
        print(f"Found {len(session_docs)} sessions in DB. Activating loops...")
        tasks = [start_new_userbot(doc["session_str"]) for doc in session_docs]
        await asyncio.gather(*tasks)
        print(f"🎉 Fully loaded `{len(running_clients)}` accounts simultaneously!")
    else:
        print("💡 No String Sessions found in DB yet.")

    await bot.start(bot_token=BOT_TOKEN)
    print("🤖 Official Bot is running smoothly...")
    await bot.run_until_disconnected()

if __name__ == '__main__':
    asyncio.run(startup())

