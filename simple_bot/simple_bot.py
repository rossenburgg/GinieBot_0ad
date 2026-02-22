"""Minimal XMPP bot for joining lobby rooms.

This script connects to the Wildfire Games lobby, joins a small set of
multi-user chat rooms, and keeps its presence set to "away". It is intended
as a stripped-down alternative to the full-featured GinieBot found in
``main.py``.
"""

import logging
import os
import ssl
from collections import defaultdict
from typing import Iterable, Optional, Sequence

import sleekxmpp
from dotenv import load_dotenv

# Default conference rooms to join.
DEFAULT_ROOMS = (
    "arena25@conference.lobby.wildfiregames.com",
    "arena26@conference.lobby.wildfiregames.com",
    "arena27@conference.lobby.wildfiregames.com",
    "helpers@conference.lobby.wildfiregames.com",
    "arena28@conference.lobby.wildfiregames.com",

)


class SimplePresenceBot(sleekxmpp.ClientXMPP):
    """A bare-bones XMPP client that only joins rooms and stays away."""

    def __init__(self, jid: str, password: str, nickname: str, rooms: Sequence[str]):
        super().__init__(jid, password)

        self.nickname = nickname
        self.rooms = tuple(rooms)
        self.room_confirmations = {}
        self.room_join_attempts = defaultdict(int)
        self.display_nicks = {}

        self.add_event_handler("session_start", self._on_session_start)

    # ------------------------------------------------------------------
    # Event handlers
    # ------------------------------------------------------------------
    def _handle_room_presence(self, presence):
        """Record when occupants (including us) appear in a room."""
        muc_info = presence['muc']
        if not muc_info or 'room' not in muc_info:
            return

        room = muc_info['room']
        nick = muc_info['nick']
        show = presence.get('show') or 'available'
        status = presence.get('status') or ''
        jid = muc_info.get('jid')

        if jid and jid.bare == self.boundjid.bare:
            self.room_confirmations[room] = True
            self.display_nicks[room] = nick
            logging.info(
                "Confirmed membership in %s as displayed nick '%s' (show=%s status=%s)",
                room,
                nick,
                show,
                status,
            )
        else:
            logging.info(
                "Occupant %s joined %s (show=%s status=%s)",
                nick,
                room,
                show,
                status,
            )

    def _verify_membership(self, room: str):
        """Ensure we actually appear in the room, retrying if necessary."""
        if self.room_confirmations.get(room):
            logging.info("Membership for %s already confirmed", room)
            return

        attempts = self.room_join_attempts[room]
        if attempts >= 3:
            logging.error("Unable to confirm presence in %s after %d attempts", room, attempts)
            return

        logging.warning(
            "Presence in %s not yet confirmed (attempt %d) – retrying join",
            room,
            attempts + 1,
        )
        self.room_join_attempts[room] += 1

        muc = self.plugin["xep_0045"]
        muc.joinMUC(room, self.nickname, wait=True)
        self.send_presence(pshow="away", pstatus="Monitoring lobby", pto=room)
        self.schedule(f"verify-{room}", 3, self._verify_membership, kwargs={"room": room})

    def _on_session_start(self, _):
        """Join configured rooms once the session is ready."""
        logging.info("Session started; sending presence and joining rooms")
        # Get the roster before entering rooms.
        self.get_roster()

        # Publish away presence globally.
        self.send_presence(pshow="away", pstatus="Monitoring lobby")

        muc = self.plugin["xep_0045"]
        self.room_confirmations = {}
        for room in self.rooms:
            logging.info("Joining room: %s", room)
            self.room_confirmations[room] = False
            self.room_join_attempts[room] = 0

            self.add_event_handler(
                f"muc::{room}::presence",
                self._handle_room_presence,
            )
            logging.info("Attempting join for %s using nick '%s'", room, self.nickname)
            muc.joinMUC(room, self.nickname, wait=True)
            # Ensure our presence inside each room stays away as well.
            self.send_presence(pshow="away", pstatus="Monitoring lobby", pto=room)

            self.schedule(f"verify-{room}", 3, self._verify_membership, kwargs={"room": room})

        logging.info("Joined %d rooms", len(self.rooms))


def _read_env_sequence(var_name: str) -> Iterable[str]:
    """Split a comma-separated environment variable into room JIDs."""
    value = os.getenv(var_name)
    if not value:
        return ()
    return tuple(room.strip() for room in value.split(",") if room.strip())


def build_bot_from_env(logger: Optional[logging.Logger] = None) -> SimplePresenceBot:
    """Construct a ``SimplePresenceBot`` using environment configuration.

    Parameters
    ----------
    logger:
        Optional logger for reporting configuration issues. Falls back to the
        module-level ``logging`` if not supplied.

    Returns
    -------
    SimplePresenceBot
        A bot instance configured with credentials and target rooms from
        environment variables.

    Raises
    ------
    ValueError
        If any mandatory environment variables are missing.
    """

    active_logger = logger or logging.getLogger(__name__)

    env_file = os.getenv("XMPP_ENV_FILE")
    if env_file:
        load_dotenv(env_file, override=True)
    else:
        load_dotenv(override=True)

    jid = os.getenv("XMPP_JID")
    password = os.getenv("XMPP_PASSWORD")
    nickname = os.getenv("XMPP_NICKNAME")

    missing = [
        name
        for name, value in (
            ("XMPP_JID", jid),
            ("XMPP_PASSWORD", password),
            ("XMPP_NICKNAME", nickname),
        )
        if not value
    ]
    if missing:
        joined = ", ".join(missing)
        active_logger.error("Missing required environment variables: %s", joined)
        raise ValueError(f"Missing required environment variables: {joined}")

    rooms = _read_env_sequence("XMPP_ROOMS") or DEFAULT_ROOMS

    bot = SimplePresenceBot(jid, password, nickname, rooms)

    # Add minimal plugins needed for MUC participation.
    bot.register_plugin("xep_0030")  # Service Discovery
    bot.register_plugin("xep_0045")  # Multi-User Chat
    bot.register_plugin("xep_0199")  # XMPP Ping

    bot.ssl_version = ssl.PROTOCOL_TLS
    bot.auto_reconnect = True
    bot.auto_authorize = True
    bot.whitespace_keepalive = True
    bot.whitespace_keepalive_interval = 30

    return bot


def run_bot(bot: SimplePresenceBot, *, logger: Optional[logging.Logger] = None) -> int:
    """Connect the provided bot and block until it disconnects."""

    active_logger = logger or logging.getLogger(__name__)

    active_logger.info("Connecting as %s", bot.boundjid.bare)
    try:
        if bot.connect():
            active_logger.info("Connection established; entering processing loop")
            bot.process(block=True)
            active_logger.info("Disconnected cleanly")
            return 0

        active_logger.error("Unable to connect to XMPP server")
        return 1
    finally:
        bot.disconnect(wait=False)


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

    try:
        bot = build_bot_from_env()
    except ValueError:
        return 1

    return run_bot(bot)


if __name__ == "__main__":
    raise SystemExit(main())
