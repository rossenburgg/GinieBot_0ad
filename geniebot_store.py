"""SQLite persistence for GinieBot moderation state.

Tables:
    reports(id, reporter, reported_user, reason, room, created_at)
    offenders(nick PRIMARY KEY, offenses, last_offense_at)
    watchlist(nick PRIMARY KEY, added_by, added_at, force)

The database path comes from the GENIEBOT_DB environment variable and
defaults to ./geniebot.db. If the file cannot be opened (bad path,
read-only filesystem), the store falls back to an in-memory database so
the bot keeps running without persistence, and logs a warning.
"""

from __future__ import annotations

import datetime
import logging
import os
import sqlite3

LOGGER = logging.getLogger(__name__)

SCHEMA = """
CREATE TABLE IF NOT EXISTS reports (
    id TEXT PRIMARY KEY,
    reporter TEXT NOT NULL,
    reported_user TEXT NOT NULL,
    reason TEXT NOT NULL DEFAULT '',
    room TEXT NOT NULL DEFAULT '',
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS offenders (
    nick TEXT PRIMARY KEY,
    offenses INTEGER NOT NULL DEFAULT 0,
    last_offense_at TEXT
);
CREATE TABLE IF NOT EXISTS watchlist (
    nick TEXT PRIMARY KEY,
    added_by TEXT NOT NULL DEFAULT '',
    added_at TEXT NOT NULL,
    force INTEGER NOT NULL DEFAULT 0
);
"""


def _utcnow_iso() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


class GenieBotStore:
    """Thin SQLite wrapper for the bot's moderation state."""

    def __init__(self, path: str | None = None):
        self.path = path or os.getenv("GENIEBOT_DB", "./geniebot.db")
        self.persistent = True
        try:
            # Touch the parent dir so a nested GENIEBOT_DB path works.
            parent = os.path.dirname(os.path.abspath(self.path))
            os.makedirs(parent, exist_ok=True)
            self._conn = sqlite3.connect(self.path)
        except (OSError, sqlite3.Error) as exc:
            LOGGER.warning("Could not open %s (%s); using in-memory store", self.path, exc)
            self._conn = sqlite3.connect(":memory:")
            self.persistent = False
        self._conn.row_factory = sqlite3.Row
        self._conn.executescript(SCHEMA)
        self._conn.commit()

    # ------------------------------------------------------------------
    # reports
    # ------------------------------------------------------------------
    def add_report(self, report_id: str, reporter: str, reported_user: str,
                   reason: str = "", room: str = "") -> None:
        self._conn.execute(
            "INSERT OR REPLACE INTO reports (id, reporter, reported_user, reason, room, created_at)"
            " VALUES (?, ?, ?, ?, ?, ?)",
            (report_id, reporter, reported_user, reason, room, _utcnow_iso()),
        )
        self._conn.commit()

    def list_reports(self) -> list[dict]:
        cur = self._conn.execute("SELECT * FROM reports ORDER BY created_at DESC")
        return [dict(row) for row in cur.fetchall()]

    # ------------------------------------------------------------------
    # offenders
    # ------------------------------------------------------------------
    def record_offense(self, nick: str, total_offenses: int,
                       last_offense_at: str | None = None) -> None:
        self._conn.execute(
            "INSERT INTO offenders (nick, offenses, last_offense_at) VALUES (?, ?, ?)"
            " ON CONFLICT(nick) DO UPDATE SET offenses=excluded.offenses,"
            " last_offense_at=excluded.last_offense_at",
            (nick, total_offenses, last_offense_at or _utcnow_iso()),
        )
        self._conn.commit()

    def get_offender(self, nick: str) -> dict | None:
        cur = self._conn.execute("SELECT * FROM offenders WHERE nick = ?", (nick,))
        row = cur.fetchone()
        return dict(row) if row else None

    def list_offenders(self) -> list[dict]:
        cur = self._conn.execute("SELECT * FROM offenders ORDER BY offenses DESC")
        return [dict(row) for row in cur.fetchall()]

    # ------------------------------------------------------------------
    # watchlist
    # ------------------------------------------------------------------
    def add_watch(self, nick: str, added_by: str = "", force: bool = False) -> None:
        self._conn.execute(
            "INSERT OR REPLACE INTO watchlist (nick, added_by, added_at, force)"
            " VALUES (?, ?, ?, ?)",
            (nick, added_by, _utcnow_iso(), int(force)),
        )
        self._conn.commit()

    def remove_watch(self, nick: str) -> None:
        self._conn.execute("DELETE FROM watchlist WHERE nick = ?", (nick,))
        self._conn.commit()

    def is_watched(self, nick: str) -> bool:
        cur = self._conn.execute("SELECT 1 FROM watchlist WHERE nick = ?", (nick,))
        return cur.fetchone() is not None

    def list_watch(self) -> list[dict]:
        cur = self._conn.execute("SELECT * FROM watchlist ORDER BY added_at")
        return [dict(row) for row in cur.fetchall()]

    def close(self) -> None:
        self._conn.close()
