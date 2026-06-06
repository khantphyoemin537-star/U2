import os  # 👈 Render ရဲ့ Port ကို ဖတ်ဖို့အတွက်
import asyncio
import random
import time
import logging
import re  # 👈 Catch Command များကို Regex ဖြင့် တိကျစွာဆွဲထုတ်ရန်
from telethon import TelegramClient, events, errors, functions
from telethon.sessions import StringSession
from motor.motor_asyncio import AsyncIOMotorClient

# ==========================================
# ⚙️ CONFIGURATION (Credentials)
# ==========================================
MONGO_URI = "mongodb+srv://khantphyoemin537_db_user:9VRKiaeZkz7rJdpz@cluster0.w6tgi8j.mongodb.net/telegram_bot?appName=Cluster0&tlsAllowInvalidCertificates=true"
APP_ID = 39584681
APP_HASH = 'c8c0685d6dd5b9e546093ea90d27733b'
BOT_TOKEN = '8111794244:AAGpkLE7h5x_IYFvjkVCbJosDC1TFbCGxcQ'

OWNER_ID = 6015356597
SPECIFIC_GROUP = -1003999318284
COOLDOWN_TIME = 15

# 🎯 NEW CHAT & BOT CONFIGURATIONS
SPAWN_BOT_ID = 6157455819
HINT_BOT_ID = 8506436817
WAIFU_CHAT_ID = -1003999318284

# Global States
is_active = False
is_scraping = False
is_adding_contacts = False  
user_cooldowns = {}
is_talker_active = False       
message_count = 0
spam_tasks = {}
spawn_tracker = {}            # Waifu Chat ထဲက ID တွေကို မူရင်း Group ID နဲ့ ချိတ်ဆက်ပေးမယ့် မြန်နှုန်းမြင့် Map
last_spawn_chat_id = None     # Hint Bot က Reply မပြန်ခဲ့ရင် သုံးမယ့် Fallback Group ID
HINT_REGEX = re.compile(r"(/catch\s+[^\n]+)") 
is_catch_stopped = False      # 👈 [NEW] OWNER က Manual ထိန်းချုပ်ရန် စတိတ် (Default: အလုပ်လုပ်မည်)

# MongoDB Setup
client_mongo = AsyncIOMotorClient(MONGO_URI)
db = client_mongo["telegram_bot"]
reply_save_col = db["reply_save_col"]
target_bots_col = db["target_bots"]  
config_col = db["config_col"]
talk_col = db["random_talk"]   
filters_col = db["filters"]

# Initialize Official Bot Client
bot = TelegramClient('official_bot_session', APP_ID, APP_HASH)
userbot = None  

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
# 🗑️ ANTI-FLOOD DELAYED DELETION TASK
# ==========================================
async def delete_bot_message_delayed(event, bot_msg_id, cmd_msg_id=0):
    try:
        await asyncio.sleep(3)
        to_delete = [bot_msg_id]
        if cmd_msg_id:
            to_delete.append(cmd_msg_id)
            
        await event.client.delete_messages(event.chat_id, to_delete)
        print(f"🗑️ Auto-deleted message {bot_msg_id} after delay.")
        
    except errors.rpcerrorlist.FloodWaitError as e:
        print(f"⚠️ FloodWait Caught! Must wait {e.seconds} seconds.")
        await asyncio.sleep(e.seconds)
        try:
            await event.client.delete_messages(event.chat_id, to_delete)
        except Exception:
            pass
    except Exception as e:
        print(f"❌ Error during delayed deletion: {e}")

# ⏱️ [NEW] /catch command အား ၁ စက္ကန့်အကြာတွင် အလိုအလျောက် ပြန်ဖျက်ပေးမည့် သီးသန့် Task
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
                    await event.client.send_message(
                        chat_id, 
                        reply_text, 
                        reply_to=reply_msg_id
                    )
                    await asyncio.sleep(1.0)
                    
                except errors.rpcerrorlist.FloodWaitError as e:
                    print(f"⚠️ FloodWait မိသွားသဖြင့် {e.seconds} စက္ကန့် စောင့်ဆိုင်းနေသည်။")
                    await asyncio.sleep(e.seconds)
                except Exception as e:
                    print(f"❌ Spam Error: {e}")
                    await asyncio.sleep(1.0)
            else:
                await asyncio.sleep(2.0)
                
    except asyncio.CancelledError:
        print(f"🛑 Chat ID: {chat_id} တွင် Raid လုပ်ငန်းစဉ် ရပ်တန့်ပြီး။")

# ==========================================
# ⚔️ NEW ANIME SPAWN DETECTOR & CATCHER HANDLERS (ULTRA SPEED OPTIMIZED)
# ==========================================
async def spawn_detector_handler(event):
    global last_spawn_chat_id, spawn_tracker
    """ Spawn Bot က ပုံ/ဗီဒီယိုနှင့် စာပို့လာပါက ဖမ်းဆီး၍ Forward ပို့မည့်စနစ် """
    if event.sender_id == SPAWN_BOT_ID and event.text:
        if "ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ ɪɴ ᴛʜᴇ ᴄʜᴀᴛ!" in event.text:
            
            # 🚫 Ban ခံရခြင်းမှ ကာကွယ်ရန် သတ်မှတ်ထားသော Group ID များဖြစ်ပါက လုံးဝ ငြိမ်နေစေရန်
            if event.chat_id in [-1001947407820, -1003067509608]:
                return  

            # 1. ⚡ 🔵 🟣 🟠 ပါဝင်လာပါက မည်သည့်အလုပ်မှ မလုပ်ဘဲ လုံးဝ ငြိမ်နေစေရန်
            if any(emoji in event.text for emoji in ["🔵", "🟣", "🟠"]):
                return  

            # 2. ⚡ ကျန်တဲ့ အီမိုဂျီအမျိုးအစားအားလုံးအတွက် အလုပ်လုပ်မည့်အပိုင်း
            orig_chat_id = event.chat_id
            last_spawn_chat_id = orig_chat_id  
            
            try:
                # Waifu Chat ထံ တိုက်ရိုက် Forward ပို့ခြင်း
                fwd_msg = await event.message.forward_to(WAIFU_CHAT_ID)
                
                # Forward ပြီးတာနဲ့ /waifu လို့ ချက်ချင်း Reply ပြန်အော်မည်
                reply_msg = await fwd_msg.reply("/waifu")
                
                # Hint Solver အတွက် ID များကို အမြန်မှတ်သားခြင်း
                spawn_tracker[fwd_msg.id] = orig_chat_id
                spawn_tracker[reply_msg.id] = orig_chat_id
                
                if len(spawn_tracker) > 100:
                    spawn_tracker.pop(next(iter(spawn_tracker)))
                    
            except Exception:
                pass


async def hint_solver_handler(event):
    global last_spawn_chat_id, spawn_tracker, is_catch_stopped
    """ Hint ပေးသော Bot ထံမှ /catch command ကို copy ယူပြီး မူရင်း Group ဆီသို့ အမြန်လှမ်းပို့မည့်စနစ် """
    
    # 🛑 [NEW] OWNER က stop ထားပါက /catch သွားမပို့တော့ဘဲ Skip မည်
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
                    delay_time = random.uniform(1.2, 1.6) 
                    
                    async with event.client.action(target_group, 'typing'):
                        await asyncio.sleep(delay_time)
                        
                    # 🎯 /catch လှမ်းပို့ပြီး ပို့လိုက်သော message object ကို ဖမ်းယူခြင်း
                    sent_msg = await event.client.send_message(target_group, catch_command)
                    print(f"🎯 Caught character with delay {delay_time:.2f}s")
                    
                    # 🗑️ [NEW] ပို့ပြီးတာနဲ့ ၁ စက္ကန့်အကြာမှာ ထို /catch မက်ဆေ့ချ်ကို ပြန်ဖျက်ခိုင်းခြင်း
                    asyncio.create_task(delete_catch_message_delayed(event.client, target_group, sent_msg.id))
                    
                except Exception as e:
                    print(f"❌ Catch Error: {e}")

# 📦 [UPDATED] မိမိကိုယ်တိုင် ဖမ်းမိတဲ့ ကတ် Report များကိုသာ Specific Group ထံ Forward ပေးမည့်စနစ်
async def catch_success_forwarder_handler(event):
    """ Spawn Bot က ကတ်မိသွားလို့ ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ! ဟု ပို့လာပြီး မိမိကို Mention ခေါ်ထားမှသာ Forward ပေးမည် """
    if event.sender_id == SPAWN_BOT_ID and event.text:
        
        # 🔍 စာသားထဲမှာ ပါဝင်ရမည့်အပြင် event.message.mentioned (မိမိအကောင့်ကို Tag ခေါ်ထားခြင်း) ဖြစ်မှသာ အလုပ်လုပ်မည်
        if "ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ!" in event.text and event.message.mentioned:
            try:
                await event.message.forward_to(SPECIFIC_GROUP)
                print("📦 Forwarded YOUR OWN success catch card report to SPECIFIC_GROUP.")
            except Exception as e:
                print(f"❌ Success Card Forward Error: {e}")



# ==========================================
# 🧠 USERBOT EVENT HANDLER (COLLECTIVE & RAID SYSTEM)
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
                await event.reply(f"🎯 Bot ID: `{bot_id}` (@{reply_sender.username}) ကို မှတ်ပြီးပါပြီ။")
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
                    except Exception as e:
                        print(f"❌ Talker Error: {e}")
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
# 📥 USERBOT SCRAPING TASK (Emoji Preserved & 50,000 Limit)
# ==========================================
async def scrape_history_task():
    global is_scraping, userbot
    if not userbot:
        await bot.send_message(SPECIFIC_GROUP, "❌ Userbot အသက်မဝင်သေးပါ။ /string အရင်လုပ်ပေးပါ။")
        return

    is_scraping = True
    await bot.send_message(SPECIFIC_GROUP, "📥 စာဟောင်းများမှ Reply များကို စတင်မှတ်သားနေပါပြီ...")
    
    try:
        msg_cache = {}
        total_saved = 0
        TARGET_LIMIT = 0   
        FETCH_LIMIT = 0    

        try:
            async for msg in userbot.iter_messages(SPECIFIC_GROUP, limit=FETCH_LIMIT):
                if msg and msg.text:
                    msg_cache[msg.id] = msg.text.strip()
        except Exception as cache_err:
            print(f"⚠️ Cache warning: {cache_err}")

        async for msg in userbot.iter_messages(SPECIFIC_GROUP, limit=FETCH_LIMIT):
            if not is_scraping or total_saved >= TARGET_LIMIT:
                break
            
            try:
                if msg and msg.reply_to_msg_id and msg.text:
                    parent_id = msg.reply_to_msg_id
                    parent_text = msg_cache.get(parent_id)
                    reply_text = msg.text.strip()

                    if parent_text and reply_text:
                        trigger = parent_text.lower()
                        
                        if (trigger.startswith(('/', '.', 'မှတ်', 'reply')) or 
                            reply_text.startswith(('/', '.', 'မှတ်', 'reply')) or 
                            "http" in trigger or "http" in reply_text or "@" in trigger):
                            continue

                        existing_doc = await reply_save_col.find_one({"trigger": trigger})
                        if existing_doc:
                            if reply_text not in existing_doc.get("responses", []):
                                await reply_save_col.update_one(
                                    {"trigger": trigger},
                                    {"$push": {"responses": reply_text}}
                                )
                                total_saved += 1
                        else:
                            await reply_save_col.insert_one({"trigger": trigger, "responses": [reply_text]})
                            total_saved += 1

                        if total_saved % 100 == 0:
                            await bot.send_message(SPECIFIC_GROUP, f"🚀 စာစောင် ပေါင်း {total_saved} ခု DB ထဲ မှတ်ပြီးပါပြီ!")
                        
                        await asyncio.sleep(0.04)  
            except Exception as single_msg_err:
                print(f"⚠️ Skipped a message due to: {single_msg_err}")
                continue

        await bot.send_message(SPECIFIC_GROUP, f"🎉 အောင်မြင်စွာ Reply စုစုပေါင်း {total_saved} ခုကို DB ထဲ သိမ်းဆည်းပြီးပါပြီ!")
    except Exception as e:
        await bot.send_message(SPECIFIC_GROUP, f"❌ Scraping ပြဿနာတက်ခဲ့သည်: {e}")
    finally:
        is_scraping = False


# ==========================================
# 🤖 OFFICIAL BOT COMMAND HANDLERS
# ==========================================
@bot.on(events.NewMessage(chats=SPECIFIC_GROUP))
async def handle_bot_commands(event):
    global is_active, userbot, is_scraping, is_talker_active, is_catch_stopped
    
    if event.sender_id != OWNER_ID:
        return

    cmd = event.message.text.strip() if event.message.text else ""

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
            
        await config_col.update_one(
            {"key": "string_session"},
            {"$set": {"value": session_str}},
            upsert=True
        )
        await event.reply("✅ String Session ကို DB မှာ အောင်မြင်စွာ သိမ်းပြီးပါပြီ။ Userbot ချိတ်ဆက်နေသည်...")
        
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
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage()) # 👈 [NEW] Success Report Forwarder
            
            await event.reply("🚀 Userbot is Live with Manual Sniper Mod!")
        except Exception as e:
            await event.reply(f"❌ Userbot အလုပ်မလုပ်ပါ: {e}")

    # 🛑 [NEW] /catch စနစ်အား ကိုယ်တိုင်ပိတ်မည့် Command
    elif cmd == "/stop":
        is_catch_stopped = True
        await event.reply("🛑 **Chief! `/catch` လုပ်ငန်းစဉ်ကို ရပ်ဆိုင်းလိုက်ပါပြီ။**\n(Detector နှင့် Forward စနစ်များတော့ ပုံမှန်အတိုင်း အလုပ်လုပ်ပေးနေပါမည်)")

    # ✅ [NEW] /catch စနစ်အား ပြန်လည်စတင်မည့် Command
    elif cmd == "/start":
        is_catch_stopped = False
        await event.reply("✅ **Chief! `/catch` လုပ်ငန်းစဉ်ကို ပြန်လည်စတင်လိုက်ပါပြီ။**")

    elif cmd == "/ဟိုက်":
        is_active = True
        await config_col.update_one({"key": "bot_status"}, {"$set": {"value": "active"}}, upsert=True)
        await event.reply("စာလိုက်ထောက်ပီ")

    elif cmd == "/ဟိုက်း":
        is_active = False
        await config_col.update_one({"key": "bot_status"}, {"$set": {"value": "inactive"}}, upsert=True)
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

    status_doc = await config_col.find_one({"key": "bot_status"})
    if status_doc and status_doc.get("value") == "active":
        is_active = True
        print("➡️ Auto-Reply Status: ACTIVE")

    session_doc = await config_col.find_one({"key": "string_session"})
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
            userbot.add_event_handler(catch_success_forwarder_handler, events.NewMessage()) # 👈 [NEW] Success Report Forwarder  
            
            print("🚀 Userbot Session Successfully Loaded from DB!")
        except Exception as e:
            print(f"⚠️ Failed to load existing Userbot Session: {e}")
    else:
        print("💡 No String Session found in DB yet.")

    await bot.start(bot_token=BOT_TOKEN)
    print("🤖 Official Bot is running...")
    await bot.run_until_disconnected()

if __name__ == '__main__':
    asyncio.run(startup())

