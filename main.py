import datetime
import logging
import random
import re
import ssl
import time
import uuid
import matplotlib.pyplot as plt
from collections import deque
from selenium.webdriver.support.wait import WebDriverWait
from twilio.rest import Client
import requests
import sleekxmpp
import wikipedia
import nltk
from nltk.stem import SnowballStemmer
import openai
import threading
from sleekxmpp import Message
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.options import Options
from selenium import webdriver
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from collections import defaultdict, deque

from flask import Flask, render_template

nltk.download("punkt")
from nltk.tokenize import sent_tokenize

app = Flask(__name__)

logging.basicConfig(level=logging.DEBUG)


# The name of the MUC room to monitor
MUC_ROOM = 'arena26@conference.lobby.wildfiregames.com'


def detect_spam(msg):
    # Use a regular expression to match messages that contain a word repeated more than 3 times, even if the word is split into multiple messages
    words = msg.split()
    for word in words:
        if words.count(word) > 5:
            return True
    return False


class CommandBot(sleekxmpp.ClientXMPP):
    def __init__(
            self,
            jid,
            password,
            room,
            nick,
            default_target_room="arena26@conference.lobby.wildfiregames.com",
            spam_reports="",
            arena25="arena25@conference.lobby.wildfiregames.com",
            arena27="arena27@conference.lobby.wildfiregames.com"

    ):
        sleekxmpp.ClientXMPP.__init__(self, jid, password)

        self.users_announced = {}
        self.offenders = {}
        self.room = room
        self.nick = nick
        self.actual_name = nick
        self.default_target_room = default_target_room
        self.spam_reports = spam_reports
        self.arena25 = arena25
        self.arena27 = arena27
        self.rooms = [
            room
        ]  # Initialize the list of rooms to include the room the bot was originally added to
        self.stemmer = SnowballStemmer("english")
        # Initialize the dictionary to store the timestamps of the last time the command was used
        self.cooldowns = {}
        self.nick_cooldowns = {}
        self.mention_limit_messages = {}
        self.new_update_users = []

        self.add_event_handler("session_start", self.start)
        self.add_event_handler("groupchat_message", self.message)
        self.add_event_handler("message", self.watch_user, threaded=True)
        self.add_event_handler('presence', self.on_presence)
        self.add_event_handler("message", self.list_commands)
        self.add_event_handler("message", self.handle_reports)
        # self.add_event_handler("message", self.handle_mail)
        self.add_event_handler("message", self.handle_mute)
        self.add_event_handler("message", self.handle_private_message)
        self.last_msgs = defaultdict(lambda: deque(maxlen=3))
        self.quiet_end = 0  # the time at which the bot will stop being quiet
        threading.Thread(target=self.check_quiet_period).start()
        self.spam_detected = {}

        # mention bot attr
        self.mention_limit_notified = set()
        self.users_at_mention_limit = set()
        # Initialize the list of users who are allowed to see the list of commands
        self.allowed_nicks = ["defc0n", "~Defc0n", "user1", "Norse_Harold", "Dunedan", "Ratings", "ModerationBot"]
        self.bot_nicks = ["Ratings", "ModerationBot"]

        # Initialize the user cooldown dictionary
        self.wikipedia_user_cooldowns = {}
        self.wikipedia_search_count = {}
        self.wikipedia_cooldown = datetime.timedelta(minutes=60)
        self.wikipedia_cooldown_message_sent = False
        self.user_offenses = {}
        self.last_mention_times = {}
        self.last_greeting_times = {}
        # Set the response count and cooldown variables
        self.response_count = 0
        self.response_cooldown_start_time = 0
        self.response_cooldown_time = 3600  # 1 hour cooldown
        self.users_to_watch = []
        self.first_report = True
        self.muted_users = {}
        self.last_seen = {}
        self.last_warnings = {}
        self.COOLDOWN_TIME_MINUTES = 20
        self.message_count = 0
        self.message_counts_history = []
        self.users_online = 0
        self.users_online_history = []
        self.users_joined_history = []
        self.users_left_history = []
        self.users_joined = 0
        self.users_left = 0
        self.reports = 0
        self.reports_history = []
        self.reportsHelper = {}

    def command_match(self, msg):

        # Return True if the message is a command that the bot should handle
        if re.match(r"^!(cmd\d+|time|mod|wiki|offenders|epoch)$", msg):
            return True
            # Check if the message is the !commands command and if the sender is in the list of allowed nicknames
            if msg == "!commands" and msg["mucnick"] in self.allowed_nicks:
                return True
            return False
        # Return True if the message is a command that the bot should handle

    def start(self, event):
        self.get_roster()
        self.send_presence()
        self.send_presence(pshow="away")
        self.send_presence_subscription(pto="moderation-bot@lobby.wildfiregames.com")
        self.plugin["xep_0045"].joinMUC(self.room, self.nick, wait=True)
        self.plugin["xep_0045"].joinMUC(self.spam_reports, self.nick, wait=True)
        self.plugin["xep_0045"].joinMUC(self.arena25, self.nick, wait=True)
        self.plugin["xep_0045"].joinMUC(self.arena27, self.nick, wait=True)

        # Join the rooms
        for r in [self.room, self.spam_reports, self.arena25, self.arena27]:
            self.plugin["xep_0045"].joinMUC(r, self.nick, wait=True)
            self.send_presence(pshow='away', pstatus="Undergoing realtime update", pto=r)
            # Print the watch list
            print("Watch list:", self.users_to_watch)

        # Send a broadcast message to the spam_reports room about the new update
        # Also add users who will later join the room to a list so they can be messaged privately
        changelog = [
            "Minor changes",
            "добавил больше ненормативной лексики",
            "Fixed zeroday affecting all commands",
            "Separated dicts and removed auto actions since Moderation bot is back on track.",
            "Filereports should work now!",
            "Add user nick to warnings"

        ]

        message_body = "**Update Broadcast - Changelog:**\n\n"
        for change in changelog:
            message_body += f"- {change}\n"

        self.send_message(
            mto=self.spam_reports,
            mbody=message_body,
            mtype="groupchat",
        )

    def handle_roster_update(self, roster):
        for jid in roster["roster"]:
            if jid.bare == "moderation-bot@lobby.wildfiregames.com":
                subscription = roster["roster"][jid]["subscription"]
                if subscription == "both":
                    print("Bot is subscribed to moderation-bot JID")
                elif subscription == "none":
                    print("Bot is not subscribed to moderation-bot JID")
                elif subscription == "from":
                    print("Bot has received a subscription request from moderation-bot JID")
                elif subscription == "to":
                    print("Bot has sent a subscription request to moderation-bot JID")
                elif subscription == "remove":
                    print("Bot has been removed from moderation-bot JID's roster")

    def invite(self, pres):
        # When a user is invited to the spam_reports room, add them to the new_update_users list
        if pres.getFrom().bare == self.spam_reports and pres.getFrom().resource == self.nick:
            self.new_update_users.append(pres.getTo().bare)

    def search_wikipedia(self, query):
        # Search Wikipedia and get the page
        try:
            # Enclose query in double quotes to force search as a phrase
            results = wikipedia.search(f'"{query}"')
            page = wikipedia.page(results[0])
        except Exception as e:
            print(f"Exception occurred while searching Wikipedia: {e}")
            return f"No results found for '{query}' on Wikipedia."

        # Get the page summary and split it into sentences
        summary = page.summary
        sentences = sent_tokenize(summary)
        # Check that the sentences list has at least three sentences
        if len(sentences) < 3:
            return f"Sorry, I couldn't find a suitable summary on Wikipedia for '{query}'."
        # Return the first three sentences of the summary, including the query
        return f"{sentences[0]}\n{sentences[1]}\n{sentences[2]}"

    def watch_user(self, msg):
        if msg['type'] in ('groupchat', 'chat') and msg['mucroom'] == self.spam_reports:
            bot_name = self.nick
            if msg['body'].startswith(f'{bot_name} watch'):
                # Check that there are at least two words in the message
                words = msg['body'].split()
                if len(words) >= 3:
                    username = words[2]
                    # Check if the user is present in the default room or if it's a forcewatch command
                    if username in self.plugin['xep_0045'].getRoster(self.default_target_room) or words[
                        1] == 'forcewatch':
                        if username != bot_name and username not in self.users_to_watch:
                            self.users_to_watch.append(username)
                            message = f"{username} has been added to the watch list"
                        elif username == bot_name:
                            message = f"{bot_name} cannot be added to the watch list"
                        else:
                            message = f"{username} is already in the watch list"
                    else:
                        message = f"{username} is not online and cannot be added to the watchlist."
                    self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
                else:
                    message = f"Usage: {bot_name} watch <username>"
                    self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
            elif msg['body'] == f'{bot_name} listwatch':
                if self.users_to_watch:
                    message = f"Users to watch: {', '.join(self.users_to_watch)}"
                else:
                    message = "No users are currently being watched."
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
            elif msg['body'].startswith(f'{bot_name} unwatch'):
                # Check that there are at least two words in the message
                words = msg['body'].split()
                if len(words) >= 3:
                    username = words[2]
                    if username in self.users_to_watch:
                        self.users_to_watch.remove(username)
                        message = f"{username} has been removed from the watch list"
                    else:
                        message = f"{username} is not in the watch list"
                else:
                    message = f"Usage: {bot_name} unwatch <username>"
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
            elif msg['body'].startswith(f'{bot_name} forcewatch'):
                # Check that there are at least two words in the message
                words = msg['body'].split()
                if len(words) >= 3:
                    username = words[2]
                    # Force add the user to the watch list
                    if username != bot_name and username not in self.users_to_watch:
                        self.users_to_watch.append(username)
                        message = f"{username} has been force-added to the watch list"
                    elif username == bot_name:
                        message = f"{bot_name} cannot be added to the watch list"
                    else:
                        message = f"{username} is already in the watch list"
                else:
                    message = f"Usage: {bot_name} forcewatch <username>"
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')

    def list_commands(self, msg):
        if msg['type'] == 'groupchat' and msg['mucroom'] == self.spam_reports:
            bot_name = self.nick
            if msg['body'].startswith(f'{bot_name} commands'):
                print("Received 'list commands' command")
                commands = [
                    f"{bot_name} watch <username>: add a user to the watch list",
                    f"{bot_name} unwatch <username>: remove a user from the watch list",
                    f"{bot_name} forcewatch <username>: force add a player to the watchlist even if they are offline",
                    f"{bot_name} listwatch: list all the users currently being watched",
                    f"{bot_name} commands: display all available commands",
                    f"{bot_name} offenders: display the number of offenders",
                    f"{bot_name} filereport username: File a report for a player",
                    f"{bot_name} listreports : Show all reports",
                    f"{bot_name} push-analytics : Publish moderation report to the wildfiregames forums (Use only at the beginning of every month)",
                    f"{bot_name} zeroday time-in-secs (eg. zeroday 60) : Force set bot to ignore all messages for a specific period without having to actually mute it)"
                ]
                message = f"Available commands: \n" + '\n'.join(commands)
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')

    def on_presence(self, presence):
        print("on_presence called")
        user_nickname = presence['muc']['nick']
        if presence['type'] == 'available':
            if user_nickname in self.users_to_watch and user_nickname not in self.users_announced:
                message = f"Watch Report: {user_nickname} has joined {self.default_target_room} and is being carefully monitored."
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
                self.users_announced[user_nickname] = True
        elif presence['type'] == 'unavailable':
            if user_nickname in self.users_announced:
                message = f"{user_nickname} has left {self.default_target_room}."
                self.send_message(mto=self.spam_reports, mbody=message, mtype='groupchat')
                del self.users_announced[user_nickname]

    def generate_response(self, prompt, msg):
        try:
            # Define a list of possible greetings for the bot
            greetings = ["Hello", "Hi", "Hey there", "Greetings"]

            sender_nick = msg["mucnick"]

            # Choose a random greeting
            greeting = random.choice(greetings)

            # Check if the bot's name is mentioned along with a list of specific names
            pattern = rf"\b{re.escape(self.nick)}\b.*?\[(.*?)\]"
            match = re.search(pattern, prompt)
            if match:
                names_list = match.group(1).split(", ")
                if self.nick in names_list:
                    print('found name wont reply')
                    return None
            else:
                names_list = []

            # Remove any question mark at the end of the prompt
            prompt = prompt.strip()
            if prompt.endswith("?"):
                prompt = prompt[:-1]

            # Replace the bot's name in the prompt with "Geniebot"
            prompt = prompt.replace(f"{self.nick}", "Geniebot")

            # Generate a response from OpenAI if the bot's name is not mentioned
            if self.nick not in names_list:
                response = openai.Completion.create(
                    engine="text-davinci-003",
                    prompt=f"{greeting}, {sender_nick.replace(self.nick, 'Geniebot')}. {prompt}",
                    max_tokens=120,
                    n=1,
                    stop=None,
                    temperature=0.6,
                )
                response_text = response.choices[0].text.strip()

                # Remove any leading punctuation marks from the generated response
                response_text = response_text.lstrip('.?!')

                # Remove any leading or trailing white spaces from the generated response
                response_text = response_text.strip()

            else:
                response_text = None

            # Append sender_nick to the response, unless names_list is empty
            if names_list:
                response_text += f" {sender_nick}"
            return response_text
        except Exception as e:
            print(f"Error generating response: {e}")
            return "Sorry, something went wrong."

    def get_user_total_offenses(self, sender_nick):
        """
        Returns the total number of offenses for a given user within the last 14 days.
        """
        now = datetime.datetime.now()
        user_offenses = self.user_offenses.get(sender_nick, {})
        offense_timestamps = user_offenses.get("offense_timestamps", [])
        total_offenses = user_offenses.get("total_offenses", 0)
        recent_offenses = [
            timestamp for timestamp in offense_timestamps
            if now - timestamp <= datetime.timedelta(days=14)
        ]
        # Clear the dictionary if it's been more than 14 days since the last offense
        if not recent_offenses and offense_timestamps:
            self.user_offenses[sender_nick] = {}
        else:
            self.user_offenses[sender_nick] = {
                "offense_timestamps": recent_offenses,
                "total_offenses": total_offenses - len(offense_timestamps) + len(recent_offenses)
            }
        return self.user_offenses[sender_nick].get("total_offenses", 0)

    def get_offenders(self):
        offenders = {}
        for user, offenses in self.user_offenses.items():
            for offense_type, count in offenses.items():
                # Skip the offense timestamps key
                if offense_type == "offense_timestamps":
                    continue
                # Check if count is a valid integer
                try:
                    count = int(count)
                except ValueError:
                    continue
                if count > 0:
                    if user not in offenders:
                        offenders[user] = {}
                    offenders[user][offense_type] = count
        return offenders

    def handle_reports(self, msg):
        if msg["type"] in ("groupchat", "chat"):
            if msg["type"] == "groupchat" and msg["mucroom"] == self.spam_reports:
                # Check if the sender is allowed to use the command
                sender_nick = msg["mucnick"].lower()
                if sender_nick not in [nick.lower() for nick in self.allowed_nicks]:
                    return

                # Extract the username from the message body
                body = msg["body"].strip()
                if not body.lower().startswith(f"{self.nick.lower()} filereport "):
                    return
                username = body.split(" ")[-1]

                # Check if the user we are sending the report to is online
                if username not in self.plugin['xep_0045'].getRoster(self.default_target_room):
                    self.send_message(
                        mto=self.spam_reports,
                        mbody=f"{username} is not online and the report could not be filed.",
                        mtype="groupchat",
                    )
                    return

                # Generate a unique ID for the report
                report_id = str(uuid.uuid4())[:8]
                # Construct the link with the username and report ID
                short_url = f"https://shorturl.at/fiszA"
                real_url = f"https://wildfiregames.com/forum/topic/67875-ratings-disputes-and-offence-reporting/"
                link = short_url
                # Store the report and its ID in the reports dictionary
                self.reportsHelper[report_id] = {"username": username, "sender": sender_nick}
                # Send the message with the link and reference ID
                output = f"Hi {username}, I apologize for the inconvenience caused by the player who left a 1v1 game without resigning. To address this issue, please report the incident and tag user1 using the reference ID below at:\n{link}\n\n"
                output += "{:<22} {:<24}\n".format("Reference ID", "Username")
                output += "-" * (15 + 24) + "\n"
                output += "{:<22} {:<24}\n".format(report_id, username)
                self.send_message(
                    mto=self.default_target_room,
                    mbody=output,
                    mtype="groupchat",
                )
                self.send_message(
                    mto=self.spam_reports,
                    mbody="Success: Report filed successfully",
                    mtype="groupchat",
                )

    # def handle_mail(self, msg):
    #     if msg["type"] in ("groupchat", "chat"):
    #         if msg["type"] == "groupchat" and msg["mucroom"] == self.spam_reports:
    #             # Check if the sender is allowed to use the command
    #             sender_nick = msg["mucnick"].lower()
    #             if sender_nick not in [nick.lower() for nick in self.allowed_nicks]:
    #                 return
    #
    #             # Extract the username from the message body
    #             body = msg["body"].strip()
    #
    #             # Check if the command is "!sendmail"
    #             if body.lower() == f"{self.nick.lower()} zeroday":
    #                 # Send SMS using Twilio
    #                 account_sid = 'AC0a952b277af3311c86ca8a9ba3bc6233'
    #                 auth_token = '5b90ea5c29bfffcc1882d17e3d3804ef'
    #                 from_phone_number = '+15075744220'  # Your Twilio phone number
    #                 to_phone_number = '+12052910550'  # Recipient's phone number
    #                 client = Client(account_sid, auth_token)
    #
    #                 try:
    #                     message = client.messages.create(
    #                         body='This is a test SMS message from GenieBot Xmpp Server',  # SMS body
    #                         from_=from_phone_number,  # Your Twilio phone number
    #                         to=to_phone_number  # Recipient's phone number
    #                     )
    #                     print(f'SMS sent successfully. Message SID: {message.sid}')
    #                     self.send_message(
    #                         mto=self.spam_reports,
    #                         mbody="Success: Packet sent successfully",
    #                         mtype="groupchat",
    #                     )
    #                 except Exception as e:
    #                     print(f'Error sending SMS: {e}')
    #                     self.send_message(
    #                         mto=self.spam_reports,
    #                         mbody="Error: Failed to send packets",
    #                         mtype="groupchat",
    #                     )

    def get_duration_in_seconds(self, value, unit):
        """
            Convert the given duration value and unit to seconds.
            """
        if unit == "seconds":
            return value
        elif unit == "minutes":
            return value * 60
        elif unit == "hours":
            return value * 60 * 60
        elif unit == "days":
            return value * 24 * 60 * 60
        elif unit == "years":
            return value * 365 * 24 * 60 * 60
        else:
            raise ValueError("Invalid duration unit.")

    def handle_mute(self, msg):
        """
        Handle the !mute command.
        """
        if msg["type"] == "groupchat" and msg["mucroom"] == self.spam_reports:
            # Extract the message body
            body = msg["body"].strip()

            # Check if the command is "!mute"
            if "!mute" in body.lower():

                # Extract the mute parameters from the message body
                mute_params = body.split()[1:]  # Exclude "!mute"
                if len(mute_params) >= 2:
                    name = mute_params[0]
                    duration_str = " ".join(mute_params[1:])  # Join duration and reason into a single string

                    # Check if user is not already muted
                    if name not in self.muted_users:
                        # Extract mute duration and reason
                        duration_parts = re.findall(r'(\d+)\s*([a-zA-Z]+)', duration_str)
                        if duration_parts:
                            duration_value = int(duration_parts[0][0])
                            duration_unit = duration_parts[0][1].lower()
                        else:
                            raise ValueError("Invalid mute duration format.")
                        valid_units = {"m": "minutes", "min": "minutes", "mins": "minutes", "minute": "minutes",
                                       "minutes": "minutes",
                                       "h": "hours", "hr": "hours", "hrs": "hours", "hour": "hours", "hours": "hours",
                                       "d": "days", "day": "days", "days": "days",
                                       "y": "years", "yr": "years", "yrs": "years", "year": "years", "years": "years"}
                        try:
                            duration_unit = valid_units[duration_unit]
                        except KeyError:
                            self.send_message(
                                mto=self.spam_reports,
                                mbody=f"Invalid mute duration unit or arguments.",
                                mtype="groupchat",
                            )
                            return

                        duration_unit = valid_units[duration_unit]
                        if len(mute_params) > 2 and mute_params[2] == "-r":
                            reason = " ".join(mute_params[3:])
                        else:
                            reason = " ".join(mute_params[2:])
                        duration_in_seconds = self.get_duration_in_seconds(duration_value, duration_unit)

                        # Update muted users dictionary with mute duration, reason, and start time
                        self.muted_users[name] = {
                            "duration": duration_value,
                            "unit": duration_unit,
                            "reason": reason,
                            "start_time": time.time()
                        }

                        # Schedule unmute after specified duration
                        def do_unmute():
                            time.sleep(duration_in_seconds)
                            if name in self.muted_users:
                                # Remove the user from the muted users dictionary
                                del self.muted_users[name]

                                # Send unmute confirmation message
                                self.send_message(
                                    mto=self.spam_reports,
                                    mbody=f"Reminder: Hi' {msg['mucnick']}', Mute duration for '{name}' is over! {duration_value} {duration_unit} ({duration_in_seconds} seconds).",
                                    mtype="groupchat",
                                )

                        # Schedule the unmute operation in a separate thread
                        unmute_thread = threading.Thread(target=do_unmute)
                        unmute_thread.start()

                        # Send confirmation message
                        self.send_message(
                            mto=self.spam_reports,
                            mbody=f"Info:  You will be notified when the mute for '{name}' expires in {duration_value} {duration_unit}. ",
                            mtype="groupchat",
                        )

                    else:
                        # Send error message if user is already muted
                        self.send_message(
                            mto=self.spam_reports,
                            mbody=f"Error: {name} is already muted.",
                            mtype="groupchat",
                        )

    def handle_private_message(self, msg):
        # Check if the message is a private message and is from the other bot jid
        if msg["type"] == "chat" and msg["from"].bare == "moderation-bot@lobby.wildfiregames.com":
            # Parse the message to see if the kick was successful or failed
            if "success" in msg["body"]:
                response = f"Response from ModerationBot: The kick was successful."
            else:
                response = f"Response from ModerationBot: The kick failed."

            # Send the response to the groupchat
            self.send_message(
                mto=self.spam_reports,
                mbody=response,
                mtype="groupchat",
            )

    def post_to_forum(self, msg_text):
        options = Options()
        # options.add_argument("--headless")
        options.add_argument("--no-sandbox")  # Add the --no-sandbox flag

        driver = webdriver.Chrome(options=options)
        driver.get("https://wildfiregames.com/forum/login/")

        # find the username, password fields, and submit button
        username = driver.find_element(By.NAME, "auth")
        password = driver.find_element(By.NAME, "password")
        submit_button = driver.find_element(By.NAME, "_processLogin")

        # fill out the form and submit it
        username.send_keys("geniebot@megatsuhinokami.com")
        password.send_keys("Rossenburg909090@@@")
        submit_button.click()

        # check if login is successful
        try:
            # find a unique element that only appears after login
            logout_button = driver.find_element(By.CLASS_NAME, "ipsMenu_item")
            print("Forums Login successful!")
            self.send_message(
                mto=self.spam_reports,
                mbody="Forums Login successful, navigating to thread...",
                mtype="groupchat",
            )
        except:
            print("Forums Login failed!")
            self.send_message(
                mto=self.spam_reports,
                mbody="Forums Login failed!",
                mtype="groupchat",
            )
            driver.close()
            return

        # now you should be logged in, navigate to the specific thread
        driver.get("https://wildfiregames.com/forum/topic/107455-improving-the-ai/")

        # wait until the reply area is clickable and click it
        reply_button = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, '.ipsComposeArea_dummy')))
        reply_button.click()

        # wait until the text area appears and then input the text
        reply_box = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, '.cke_wysiwyg_div')))
        msg_text = "Moderation Analysis"
        reply_box.send_keys(msg_text)

        # wait for a few seconds to ensure the message is entered
        time.sleep(3)

        # find the submit button using an alternative locator
        reply_submit_button = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable((By.XPATH, '//button[contains(text(), "Submit")]')))
        reply_submit_button.click()

        # wait for a few seconds to allow the message to be submitted
        time.sleep(3)

        # check if the message is successfully submitted
        try:
            WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, '.ipsMessage')))
            print("Moderation report submitted successfully!")
            self.send_message(
                mto=self.spam_reports,
                mbody="All set! Moderation report submitted successfully, you can review it on the forums!",
                mtype="groupchat",
            )
        except:
            print("Forum Post submission failed!")
            self.send_message(
                mto=self.spam_reports,
                mbody="All set! Moderation report submitted successfully, you can review it on the forums!",
                mtype="groupchat",
            )

        driver.close()

    def process_message(self, msg):
        if msg['type'] == 'groupchat' and msg['mucroom'] == self.default_target_room:
            self.users_joined += 1
            self.users_joined_history.append(self.users_joined)
        elif msg['type'] == 'unavailable' and msg['mucroom'] == self.default_target_room:
            self.users_left += 1
            self.users_left_history.append(self.users_left)

        if msg['mucroom'] == self.spam_reports and msg['mucnick'] == self.nick:
            self.reports += 1
            self.reports_history.append(self.reports)
        else:
            self.reports_history.append(self.reports)

        # Additional statistics
        self.users_online_history.append(self.get_users_online())
        self.message_counts_history.append(self.message_count)

        self.update_chart()

    def get_users_online(self):
        roster = self.plugin["xep_0045"].getRoster(self.default_target_room)
        if roster is not None:
            return len(roster)
        return 0

    def update_chart(self):
        self.message_count = len(self.message_counts_history)
        self.users_online = self.users_online_history[-1] if self.users_online_history else 0

        fig = make_subplots(rows=2, cols=2,
                            subplot_titles=("Message Count", "Users Online", "Users Joined", "Users Left"))

        # Message Count (Line Chart)
        fig.add_trace(
            go.Scatter(x=list(range(len(self.message_counts_history))), y=self.message_counts_history, mode='lines',
                       name='Message Count'),
            row=1, col=1
        )

        # Message Count (Bar Chart)
        fig.add_trace(
            go.Bar(x=list(range(len(self.message_counts_history))), y=self.message_counts_history,
                   name='Message Count'),
            row=1, col=1
        )

        # Users Online (Line Chart)
        fig.add_trace(
            go.Scatter(x=list(range(len(self.users_online_history))), y=self.users_online_history, mode='lines',
                       name='Users Online'),
            row=1, col=2
        )

        # Users Online (Bar Chart)
        fig.add_trace(
            go.Bar(x=list(range(len(self.users_online_history))), y=self.users_online_history,
                   name='Users Online'),
            row=1, col=2
        )

        # Users Joined
        fig.add_trace(
            go.Scatter(x=list(range(len(self.users_joined_history))), y=self.users_joined_history, mode='lines',
                       name='Users Joined'),
            row=2, col=1
        )

        # Users Left
        fig.add_trace(
            go.Scatter(x=list(range(len(self.users_left_history))), y=self.users_left_history, mode='lines',
                       name='Users Left'),
            row=2, col=2
        )

        # Reports Count
        fig.add_trace(
            go.Scatter(x=list(range(len(self.reports_history))), y=self.reports_history, mode='lines',
                       name='Reports Count'),
            row=2, col=2
        )

        fig.update_layout(height=600, width=1000, title_text="MUC Room Statistics")

        # Add total users online, message count, and reports count annotations
        fig.add_annotation(xref="paper", yref="paper", x=0.5, y=1.1,
                           text=f"Total Users Online: {self.users_online}",
                           showarrow=False, font=dict(size=14))

        fig.add_annotation(xref="paper", yref="paper", x=0.5, y=-0.15,
                           text=f"Total Message Count: {self.message_count}",
                           showarrow=False, font=dict(size=14))

        fig.add_annotation(xref="paper", yref="paper", x=1, y=0,
                           text=f"Reports Count: {self.reports}",
                           showarrow=False, font=dict(size=14))

        # Save the chart as an HTML file
        fig.write_html("static/statistics.html")

    def check_quiet_period(self):
        while True:
            if self.quiet_end and time.time() > self.quiet_end:
                self.quiet_end = None  # Reset the quiet end time so we don't send the message multiple times
                self.send_message(
                    mto=self.spam_reports,
                    mbody="Quiet mode has ended, I will now respond to messages in " + self.default_target_room + ".",
                    mtype="groupchat",
                )
            time.sleep(1)  # Check again in one second

    def message(self, msg):

        # Check if the message is from the bot itself
        if msg["mucnick"] == self.nick:
            return

        if msg['mucnick'] != self.nick:
            sender = msg['mucnick']
            content = msg['body']
            if sender in self.bot_nicks and msg['from'].bare == self.default_target_room:
                return
            self.last_msgs[sender].append({'content': content, 'time': time.time()})

            if len(self.last_msgs[sender]) >= 3:
                # check if the last three messages from this sender are the same and within 30 seconds
                if all(m['content'] == content and time.time() - m['time'] < 30 for m in self.last_msgs[sender]):
                    if not self.spam_detected.get(sender + content,
                                                  False):  # check if a spam alert has already been sent for this message from this sender
                        print(f"Spam detected from {sender} in room {self.room}: {content}")
                        self.send_message(
                            mto=self.spam_reports,
                            mbody=f"Spam detected from '{sender}' in room '{self.room}'",
                            mtype="groupchat",
                        )
                        self.spam_detected[
                            sender + content] = True  # mark that a spam alert has been sent for this message from this sender
                else:
                    self.spam_detected[
                        sender + content] = False  # if the messages are not the same, reset the spam_detected flag
        if msg['mucnick'] != self.nick:
            if self.quiet_end and time.time() < self.quiet_end and msg['from'].bare == self.default_target_room:
                # if the bot is in quiet mode and the message is from the target room, don't process the message
                return

            content = msg['body']

            if msg['from'].bare == self.spam_reports:  # Check if the message is from the specific room
                if content.lower().startswith(self.nick.lower() + " zeroday"):
                    try:
                        quiet_seconds = int(content.split()[2])
                        self.quiet_end = time.time() + quiet_seconds
                        self.send_message(
                            mto=self.spam_reports,
                            mbody="Zer0Day Initialized. I won't respond to messages in " + self.default_target_room + " for " + str(
                                quiet_seconds) + " seconds.",
                            mtype="groupchat",
                        )
                    except ValueError:
                        # if the second part of the message after "quietmode" isn't an integer, ignore the command
                        pass

        self.process_message(msg)

        if msg["type"] == "groupchat" and msg["mucroom"] == self.spam_reports:
            body = msg["body"].strip()

            if msg[
                "body"].lower().startswith(self.nick.lower() + " push-analytics"):
                # Extract the message to be posted from the command
                msg_text = body[len("!post"):].strip()
                self.send_message(
                    mto=self.spam_reports,
                    mbody="Initializing login request, please wait...",
                    mtype="groupchat",
                )

                # Post the message to the forum
                self.post_to_forum(msg_text)

        if msg["mucroom"] == self.spam_reports and msg["type"] in ("groupchat", "normal") and msg[
            "body"].lower().startswith(self.nick.lower() + " listreports"):

            # Handle the !listreports command

            print(f"DEBUG: Handling !listreports command from {msg['mucnick']}")

            sender_nick = msg["mucnick"].lower()

            if sender_nick not in [nick.lower() for nick in self.allowed_nicks]:
                print(f"DEBUG: Sender {sender_nick} not allowed to use !listreports command")

                return

            print("DEBUG: Sending report list")

            output = "{:<15} {:<25} {:<10}\n".format("Reference ID", "Username", "Sender")

            output += "-" * 56 + "\n"

            for report_id, report_data in self.reports.items():
                output += "{:<15} {:<25} {:<10}\n".format(report_id, report_data["username"], report_data["sender"])

            print(f"DEBUG: Outputting report list:\n{output}")

            self.send_message(

                mto=self.spam_reports,

                mbody=output,

                mtype="groupchat",

            )

        if msg["type"] in ("groupchat", "chat"):
            # Handle the message using the handle_message method

            if msg["mucroom"] == self.spam_reports and msg["body"].lower().startswith(self.nick.lower() + " offenders"):
                offenders = self.get_offenders()

                # Calculate the maximum allowed offenses
                max_offenses = 50

                # Format the output message
                output = "Offenders:\n"
                output += "{:<24} {:<12} {:<16}\n".format("Offender", "Count", "Offense Ratio %")
                output += "-" * 55 + "\n"
                for offender, offenses in offenders.items():
                    total_offenses = sum(count for count in offenses.values() if isinstance(count, int))
                    offense_ratio = total_offenses / max_offenses * 100
                    output += "{:<24} {:<12} {:^16.2f}\n".format(offender, total_offenses, offense_ratio)

                # Send the output message
                self.send_message(
                    mto=msg["from"].bare,
                    mbody=output,
                    mtype="groupchat",
                )

        # Check if the message is a Wikipedia search command
        if msg["body"].startswith("!wiki"):
            # Split the message into words
            words = msg["body"].split()

            # Check if the correct number of arguments was provided
            if len(words) < 2:
                self.send_message(
                    mto=msg["from"].bare,
                    mbody="Invalid syntax. Use !wiki [query]",
                    mtype="groupchat",
                )
                return

            # Get the sender's nickname
            sender_nick = msg["mucnick"]

            # Increment the sender's search count
            self.wikipedia_search_count[sender_nick] = self.wikipedia_search_count.get(sender_nick, 0) + 1

            # Check if the sender has exceeded the search limit
            if sender_nick not in self.allowed_nicks and self.wikipedia_search_count[sender_nick] > 1:
                # Send a message saying the user has exceeded the search limit
                if (datetime.datetime.now() - self.wikipedia_cooldown).total_seconds() < 3600:
                    if not self.wikipedia_cooldown_message_sent:
                        self.send_message(
                            mto=msg["from"].bare,
                            mbody=f"{sender_nick}, This command has been set to cooldown for your account for the next 1hour. Try again later. ( Excludes moderators ).",
                            mtype="groupchat",
                        )
                        self.wikipedia_cooldown_message_sent = True
                    return

            # Update the cooldown and reset the message sent flag
            self.wikipedia_cooldown = datetime.datetime.now()
            self.wikipedia_cooldown_message_sent = False

            # Extract the query from the message
            query = " ".join(words[1:])

            # Search Wikipedia and get the summary
            summary = self.search_wikipedia(query)

            # Check if there were any results
            if summary:
                # Send the summary back to the user
                self.send_message(
                    mto=msg["from"].bare, mbody=summary, mtype="groupchat"
                )
            else:
                # Send a message saying no results were found
                self.send_message(
                    mto=msg["from"].bare,
                    mbody="No results found for '{}'".format(query),
                    mtype="groupchat",
                )

                # If the message is in the spam_reports room and is from a new user, send them a private message about the update
                if msg["mucroom"] == self.spam_reports and msg["mucnick"] != self.nick and msg[
                    "from"].bare in self.new_update_users:
                    changelog = [
                        "Minor changes",
                        "добавил больше ненормативной лексики",
                        "Fixed zeroday affecting all commands",
                        "Separated dicts and removed auto actions since Moderation bot is back on track.",
                        "Filereports should work now!",
                        "Add user nick to warnings"

                    ]

                    message_body = "**Update Broadcast - Changelog:**\n\n"
                    for change in changelog:
                        message_body += f"- {change}\n"

                    self.send_message(
                        mto=self.spam_reports,
                        mbody=message_body,
                        mtype="groupchat",
                    )
                # If the message is not from the bot and not in the spam_reports room, send it to the appropriate room
                elif msg["mucroom"] != self.spam_reports and msg["mucnick"] != self.nick:
                    self.send_message(mto=msg["mucroom"], mbody=msg["body"], mtype="groupchat")

            # Use a regular expression to match the message format and extract the player names and rating adjustments
        # match = re.match(
        #  r"^A rated game has ended. ([^\s]+) (won|lost) against ([^\s]+)\. Rating Adjustment: [^(]+\((\d+) -> (\d+)\) and [^(]+\((\d+) -> (\d+)\)\.$",
        #    msg["body"],
        #  )
        #  if match:
        #  (
        #      player1,
        #     result,
        #     player2,
        #     player1_before,
        #    player1_after,
        #      player2_before,
        #    player2_after,
        #  ) = match.groups()

        # Convert the rating points from strings to integers
        #   player1_before = int(player1_before)
        #   player1_after = int(player1_after)
        #   player2_before = int(player2_before)
        #   player2_after = int(player2_after)

        # Send a congratulations message to the player who won and gained rating points
        #  if result == "won" and player1_before < player1_after:
        #    self.send_message(
        #        mto=msg["from"].bare,
        #       mbody=f"Congratulations, {player1}! You won a rated game against {player2} and gained {player1_after - player1_before} rating points.",
        #       mtype="groupchat",
        #    )
        #  elif result == "lost" and player1_before > player1_after:
        #   self.send_message(
        #    mto=msg["from"].bare,
        #      mbody=f"Better luck next time, {player1}! You lost the rated game against {player2} and lost {player1_before - player1_after} rating points.",
        #       mtype="groupchat",
        #    )
        #  elif result == "won" and player2_before < player2_after:
        #   self.send_message(
        #      mto=msg["from"].bare,
        #   mbody=f"Congratulations, {player2}! You won a rated game against {player1} and gained {player2_after - player2_before} rating points.",
        #   mtype="groupchat",
        #  )

        # if self.command_match(msg["body"]):
        #    command, args = self.parse_command(msg["body"])
        #         self.on_command(command, args, msg)

        if msg["type"] in ("groupchat", "chat"):
            if msg["mucroom"] != self.room:
                return

        if msg == "!users":
            return True
        elif msg["body"] == "!users" and msg["mucnick"]:
            # Get the list of users in the MUC room
            users = self.plugin["xep_0045"].getRoster(self.room)

            # Get the number of users in the MUC room
            num_users = len(users)

            # Send a message with the number of users in the MUC room
            self.send_message(
                mto=msg["from"].bare,
                mbody=f"There are currently {num_users} players in the lobby.",
                mtype="groupchat",
            )
        elif msg["body"] == "!cmd1" and msg["mucnick"] in self.allowed_nicks:
            sender_nick = msg["mucnick"]
            if (
                    "cmd1" in self.cooldowns
                    and time.time() - self.cooldowns["cmd1"] < 60
            ):
                # Send a message to the user if the command is on cooldown
                if msg["mucnick"] not in self.cooldowns:
                    self.send_message(
                        mto=msg["from"].bare,
                        mbody=f"{sender_nick}, You cannot use this command more than once within 1min to avoid spam. Please try again later.",
                        mtype="groupchat",
                    )
                    self.cooldowns[msg["mucnick"]] = time.time()
                return

                # Update the cooldown timer
            self.cooldowns["cmd1"] = time.time()
            # Send the response
            self.send_message(
                mto=msg["from"].bare,
                mbody="Bot is online and active",
                mtype="groupchat",
            )
        elif msg["body"] == "!time" and msg["mucnick"]:
            sender_nick = msg["mucnick"]
            # Check if the !time command is on cooldown
            if (
                    "time" in self.cooldowns
                    and time.time() - self.cooldowns["time"] < 60
            ):
                # Send a message to the user if the command is on cooldown
                if msg["mucnick"] not in self.cooldowns:
                    self.send_message(
                        mto=msg["from"].bare,
                        mbody=f"{sender_nick}, The !time command is on cooldown. Please try again later.",
                        mtype="groupchat",
                    )
                    self.cooldowns[msg["mucnick"]] = time.time()
                return

            # Update the cooldown timer
            self.cooldowns["time"] = time.time()
            current_time = datetime.datetime.now().strftime("%H:%M:%S")
            self.send_message(
                mto=msg["from"].bare,
                mbody="The current time is: %s" % current_time,
                mtype="groupchat",
            )
        elif msg["body"] == "!commands" and msg["mucnick"] in self.allowed_nicks:
            # Build the list of commands as a string with each command on a separate line
            commands_list = "List of commands:\n"
            commands = [
                {"!cmd1": "Send a ping to the bot to check if its online"},
                {"!time": "This command displays the current time."},
                {"!users": "List the number of players in the lobby."},
                {"!wiki": "Search for information on wikipedia"},

            ]

            for command in commands:
                commands_list += (
                    f"- {list(command.keys())[0]}: {list(command.values())[0]}\n"
                )

            # Send the list of commands
            self.send_message(
                mto=msg["from"].bare, mbody=commands_list, mtype="groupchat"
            )
        elif "issue" in msg["body"]:
            # Check if the sender of the message is in the cooldowns dictionary
            if msg["mucnick"] not in self.cooldowns:
                # Update the cooldown for this user
                self.cooldowns[msg["mucnick"]] = datetime.datetime.now()

                # Send the response message
                sender_nick = msg["mucnick"]
                self.send_message(
                    mto=msg["from"].bare,
                    mbody=f"{sender_nick}, Seems like you have an issue do you need any help?",
                    mtype="groupchat",
                )
            else:
                # Get the current timestamp
                now = datetime.datetime.now()

                # Check if the user has received a response within the last 5 minutes
                if (now - self.cooldowns[msg["mucnick"]]).total_seconds() > 1200:
                    # Update the cooldown for this user
                    self.cooldowns[msg["mucnick"]] = datetime.datetime.now()

                    # Send the response message
                    sender_nick = msg["mucnick"]
                    self.send_message(
                        mto=msg["from"].bare,
                        mbody=f"{sender_nick}, I'm sorry you are having an issue. Please contact a lobby moderator for assistance.",
                        mtype="groupchat",
                    )
                    # Check if the sender of the message is in the cooldowns dictionary
                    if msg["mucnick"] not in self.cooldowns:
                        # Respond to the message
                        self.send_message(
                            mto=msg["from"].bare,
                            mbody=f"Thanks for the message, {msg['mucnick']}!",
                            mtype="groupchat",
                        )
                    else:
                        # Get the current timestamp
                        now = datetime.datetime.now()

                        # Check if the user has received a response within the last 5 minutes
                        if (now - self.cooldowns[msg["mucnick"]]).total_seconds() > 300:
                            # Update the cooldown for this user
                            self.cooldowns[msg["mucnick"]] = datetime.datetime.now()

                            # Respond to the message
                            self.send_message(
                                mto=msg["from"].bare,
                                mbody=f"Thanks for the message, {msg['mucnick']}!",
                                mtype="groupchat",
                            )

                # Check if the message is from the bot itself
        elif msg["mucnick"] != self.nick:
            filter_words = {
                "en": ["fck", "suxx", "fml", "nazi", "milf", "nigga", "nigger", "dammit"],
                "es": ["chingao", "chingas", "chingados", "chingatelo", "chingaron", "chota", "pinche", "pija", "puta",
                       "puto", "polla", "verga", "Joder", "Gilipollas", "Mierda"],
                "pt": ["caralho", "porra", "Poça", "Caraças", "favela"],
                "fr": ["merde", "Putain", "Bordel", "Zut", "Salaud", "salope", "Connard", "connasse"],
                "ru": ["сука", "сукаа", "сукааа", "блять", "пизда", "суки", "Сволочь", "Хуй", "Жoпа", "Мудак", "Гавно",
                       "Пиздец", "блядь", "Лох"],
                "pl": ["kurwa"]
            }

            message_words = msg["body"].split()
            detected_language = None
            offensive_word = None

            for lang_code, words in filter_words.items():
                for word in words:
                    stem = self.stemmer.stem(word)
                    regex = re.compile(f"\\b{stem}\\b", re.IGNORECASE)
                    if any(regex.search(self.stemmer.stem(w)) for w in message_words):
                        detected_language = lang_code
                        offensive_word = word
                        break
                if detected_language:
                    break

            if detected_language:
                now = datetime.datetime.now()

                # Get the sender's nick and update their offense count
                sender_nick = msg["mucnick"]
                user_offenses = self.user_offenses.get(sender_nick, {})
                total_offenses = user_offenses.get("total_offenses", 0) + 1
                user_offenses["total_offenses"] = total_offenses
                user_offenses["rank"] = "Pejorative"
                self.user_offenses[sender_nick] = user_offenses

                # Check if the user has been warned within the cooldown period
                last_warning_time = self.last_warnings.get(sender_nick)
                if last_warning_time and (now - last_warning_time) < datetime.timedelta(
                        minutes=self.COOLDOWN_TIME_MINUTES):
                    # User has been warned recently, don't warn again
                    report_offense = False
                else:
                    # User has not been warned recently, send warning message
                    report_offense = True
                    warning_messages = {
                        "en": f"Please do not use '{offensive_word}' in the chat room. Reported to lobby moderators.",
                        "es": f"Por favor, no uses '{offensive_word}' en la sala de chat. Reportado a los moderadores del lobby.",
                        "pt": f"Por favor, não use '{offensive_word}' na sala de bate-papo. Reportado aos moderadores do lobby.",
                        "fr": f"Veuillez ne pas utiliser '{offensive_word}' dans la salle de discussion. Signalé aux modérateurs du lobby.",
                        "ru": f"Пожалуйста, не используйте '{offensive_word}' в чате. Сообщено модераторам лобби.",
                        "pl": f"Nie używaj słowa '{offensive_word}' na czacie. Zgłoszone do moderatorów lobby.",
                    }

                    warning_message = warning_messages[detected_language].format(offensive_word=offensive_word)

                    self.send_message(
                        mto=msg["from"].bare,
                        mbody=warning_message,
                        mtype="groupchat",
                    )

                    # Record the time of the warning
                    self.last_warnings[sender_nick] = now

                # Report the offense to the spam_reports group
                user_total_offenses = self.get_user_total_offenses(sender_nick)
                # Define a dictionary to map language codes to their names
                language_names = {
                    "en": "English",
                    "es": "Spanish",
                    "fr": "French",
                    "ru": "Russian",
                    "pt": "Portuguese",
                    "pl": "Polish"
                }

                # Get the name of the detected language from the language_names dictionary
                detected_language_name = language_names.get(detected_language, detected_language)

                report_message = f"\U0001F575 Profane Report: {sender_nick} used  '{offensive_word}' in the lobby. \n\U0001F4AC Message: {msg['body']}. \n\U0001F50A Language used: {detected_language_name} \n\U0001F501 Repeated offense: {user_total_offenses} times within the last 14 days. \n\U0001F948 Rank: Pejorative"
                self.send_message(
                    mto=self.spam_reports,
                    mbody=report_message,
                    mtype="groupchat",
                )

            # Check if the message contains any of the additional words to mask
            additional_words = [
                "fuck",
                "shit",
                "pussy",
                "assholes",
                "cuck",
                "cucks",
                "damnit",
                "eunuchs",
                "faggot",
                "faggotly",
                "faggotry",
                "faggots",
                "faggotty",
                "faggoty",
                "sh*t",
                "FUCK"
            ]
            now = datetime.datetime.now()
            for word in additional_words:
                if word in msg["body"]:
                    # Mask the additional word in the message
                    masked_word = "*" * len(word)
                    sender_nick = msg["mucnick"]
                    self.send_message(
                        mto=msg["from"].bare,
                        mbody=f"{sender_nick}, the word '{masked_word}' cannot be used in the lobby, it has been masked due to lobby rules. Reported to lobby moderators.",
                        mtype="groupchat",
                    )

                    if msg["mucnick"] != self.nick:
                        sender_nick = msg["mucnick"]
                        user_offenses = self.user_offenses.get(sender_nick, {})
                        total_offenses = user_offenses.get("total_offenses", 0) + 1
                        user_offenses["total_offenses"] = total_offenses
                        user_offenses["rank"] = "Profanity"
                        self.user_offenses[sender_nick] = user_offenses

                        # Send a report to the spam_reports groupchat
                        user_total_offenses = self.get_user_total_offenses(sender_nick)
                        self.send_message(
                            mto=self.spam_reports,
                            mbody=f"\U0001F575 Profane Report: {sender_nick} used '{word}' in the lobby. \n\U0001F4AC Message: {msg['body']}. \n\U0001F501 Repeated offense: {total_offenses} times within the last 14 days. \n\U0001F947 Rank: Profanity",
                            mtype="groupchat",
                        )

                    return

        # Extract the user's JID from the message
        user_jid = msg["from"].bare
        prompt = ""
        response = ""

        # Check if the message mentions the bot's name
        if self.nick.lower() in msg["body"].lower():

            split_msg = msg["body"].split(",")
            if len(split_msg) > 1 and self.nick.lower() not in split_msg[-1].strip().lower():
                # Bot's name mentioned along with other names separated by comma, do not reply
                return
            elif len(split_msg) == 1 or self.nick.lower() == split_msg[-1].strip().lower() or msg[
                "body"].strip().endswith(f"{self.nick}"):
                # Bot's name mentioned either at the beginning or end of a question, generate a response
                # Generate a response using OpenAI
                prompt = msg["body"].replace(f"{self.nick}", "").strip()

                # Check if the bot has reached its response limit, and if so, set a cooldown period
                if self.response_count >= 10:
                    print("Reached response limit, setting cooldown")
                    self.response_count = 0
                    self.response_cooldown_start_time = time.time()
                    sender_nick = msg["mucnick"]
                    self.send_message(
                        mto=msg["from"].bare,
                        # mbody=f"I'm now on a cooldown mode {sender_nick}. We can continue after 1hour. For now, enjoy 0.A.D!",
                        mbody=f"Notice: I'm now on a cooldown mode {sender_nick}. We can continue after 1hour. For now, enjoy 0.A.D!",

                        mtype="groupchat",
                    )
                    return

                # Check if the bot is currently on cooldown, and if so, don't generate a response
                if hasattr(self,
                           "response_cooldown_start_time") and time.time() - self.response_cooldown_start_time < self.response_cooldown_time:
                    print("Bot is on cooldown, not generating response")
                    return

                # If bot's name is mentioned alone without any follow-up question, send a custom response
                if len(prompt.split()) == 1:
                    sender_nick = msg["mucnick"]
                    GREETINGS_COOLDOWN_TIME = 10
                    # Check if the user has greeted the bot once before within the cooldown time
                    if sender_nick in self.last_greeting_times and time.time() - self.last_greeting_times[
                        sender_nick] < GREETINGS_COOLDOWN_TIME:
                        print(f"Not responding to {sender_nick}'s greeting due to cooldown")
                        # User is on cooldown, don't respond
                        return

                    # User is not on cooldown, respond and update the last greeting time for the user
                    self.last_greeting_times[sender_nick] = time.time()
                    # Send a random greeting message
                    greetings = [
                        f"{sender_nick} How can I help you?",
                        f"Hope you are enjoying 0AD {sender_nick}, how may i help you?",
                        f"Hi {sender_nick}, got a problem? tell me I will try my best to assist you",
                        f"Thanks for greeting me {sender_nick}, how may I help you?",
                        f"{sender_nick} Need help? State your problem and i will try my best to assist you.",
                    ]
                    response = random.choice(greetings)
                else:
                    # Generate the response and increment the response count
                    response = self.generate_response(prompt, msg)
                    self.response_count += 1

            # Check if the response contains profanity and send a custom message instead of the actual response
            profanity_list = ["shit", "fucking", "cunt", "asshole", "fuck",
                              "F*ck", "damn"]  # replace with actual profanity list

            if any(word in response.lower() for word in profanity_list):
                custom_message = "I'm sorry, but I cannot do that as it goes against my programming to use or encourage the use of profanity. Is there anything else I can assist you with?"
                self.send_message(
                    mto=msg["from"].bare,
                    mbody=custom_message,
                    mtype="groupchat",
                )
            else:
                if "where are you from" in prompt.lower():
                    response = "I was created by the Wildfiregames team, so you could say I'm from the Wildfiregames headquarters."
                elif "who created you" in prompt.lower():
                    response = "I was developed by the wildfiregames team. I'm still being trained, I hope to get smarter everyday."
                elif "who made you" in prompt.lower():
                    response = "I was developed by the wildfiregames team. I'm still being trained, I hope to get smarter everyday."
                elif "how old are you" in prompt.lower():
                    response = "I'm just a moderation bot, I don't have an age. Or well maybe you can ask my developers at wildfiregames."
                elif "when did your knowledge cut off" in prompt.lower():
                    response = "I'm always getting updated, I may not have all the up-to-date data but I'm almost there!"

                # Check if the response contains "OpenAI" or "ChatGPT" and replace with "Wildfiregames"
                if "openai" in response.lower():
                    response = response.replace("OpenAI", "Wildfiregames")
                if "chatgpt" in response.lower():
                    response = response.replace("ChatGPT", "Wildfiregames")

                # Send the response back to the chatroom
                self.send_message(
                    mto=msg["from"].bare,
                    mbody=response,
                    mtype="groupchat",
                )

        self.update_chart()

    # This method is called to join a chat room
    def join_room(self, room_jid):
        self.plugin["xep_0045"].joinMUC(room_jid, self.nick, wait=True, )
        self.rooms.append(room_jid)


if __name__ == "__main__":
    xmpp = CommandBot(
       
    )
    xmpp.register_plugin("xep_0030")  # Service Discovery
    xmpp.register_plugin("xep_0045")  # Multi-User Chat
    xmpp.register_plugin("xep_0199")  # XMPP Ping

    # Enable debugging
    xmpp.ssl_version = ssl.PROTOCOL_TLS
    xmpp.auto_reconnect = True
    xmpp.auto_authorize = True
    xmpp.whitespace_keepalive = True
    xmpp.whitespace_keepalive_interval = 30
    xmpp.keepalive = True
    xmpp.debug = True

    if xmpp.connect():
        xmpp.process()
    else:
        print("Unable to connect.")
