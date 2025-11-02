"""Render deployment entrypoint exposing HTTP health checks.

This module hosts a FastAPI web service that starts the XMPP bot in a
background thread. Keeping the bot inside a web service prevents Render's
free tier from idling the process after 15 minutes, because periodic
keep-alive requests will hit the exposed HTTP endpoint.
"""

from __future__ import annotations

import logging
import os
import threading
import time
from datetime import datetime, timezone
from typing import Any, Dict, Optional

import httpx
from fastapi import FastAPI
from fastapi.responses import JSONResponse

from simple_bot.simple_bot import SimplePresenceBot, build_bot_from_env, run_bot

LOGGER = logging.getLogger("render_service")
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

BOT_RESTART_DELAY = int(os.getenv("BOT_RESTART_DELAY", "15"))
KEEPALIVE_INTERVAL = int(os.getenv("KEEPALIVE_INTERVAL", "600"))
BOT_ENABLED = os.getenv("BOT_ENABLED", "true").strip().lower() not in {"0", "false", "no"}

# Resolve the URL we should ping to keep the service warm. Render exposes the
# public hostname via RENDER_EXTERNAL_URL; allow an explicit override.
def _resolve_keepalive_url() -> Optional[str]:
    return os.getenv("KEEPALIVE_URL") or os.getenv("RENDER_EXTERNAL_URL")


class BotSupervisor:
    """Run the XMPP bot in a resilient background thread."""

    def __init__(self, *, enabled: bool = True) -> None:
        self._enabled = enabled
        self._stop_event = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._lock = threading.Lock()
        self._bot: Optional[SimplePresenceBot] = None
        self.state: Dict[str, Any] = {
            "running": False,
            "restart_count": 0,
            "last_start": None,
            "last_stop": None,
            "last_result": None,
            "last_error": None,
            "enabled": self._enabled,
        }

    # ------------------------------------------------------------------
    def start(self) -> None:
        if not self._enabled:
            LOGGER.info("Bot supervisor disabled via BOT_ENABLED")
            return

        if self._thread and self._thread.is_alive():
            return

        self._stop_event.clear()
        self._thread = threading.Thread(target=self._worker, name="xmpp-bot", daemon=True)
        self._thread.start()

    # ------------------------------------------------------------------
    def stop(self) -> None:
        self._stop_event.set()
        with self._lock:
            if self._bot is not None:
                try:
                    self._bot.disconnect(wait=False)
                except Exception:  # pragma: no cover - defensive
                    LOGGER.exception("Failed to disconnect bot during shutdown")
        if self._thread:
            self._thread.join(timeout=20)

    # ------------------------------------------------------------------
    def _worker(self) -> None:
        while not self._stop_event.is_set():
            try:
                bot = build_bot_from_env(LOGGER)
            except ValueError as exc:
                LOGGER.error("Bot configuration error: %s", exc)
                self.state.update(
                    {
                        "running": False,
                        "last_error": str(exc),
                        "last_result": "config-error",
                        "last_stop": datetime.now(timezone.utc).isoformat(),
                    }
                )
                # Configuration is broken; retry later to allow env updates.
                self._wait_with_stop(BOT_RESTART_DELAY)
                continue

            with self._lock:
                self._bot = bot

            self.state.update(
                {
                    "running": True,
                    "last_start": datetime.now(timezone.utc).isoformat(),
                    "last_error": None,
                }
            )

            try:
                result = run_bot(bot, logger=LOGGER)
                self.state.update(
                    {
                        "running": False,
                        "last_result": result,
                        "last_stop": datetime.now(timezone.utc).isoformat(),
                    }
                )
                LOGGER.info("Bot exited with status code %s", result)
            except Exception as exc:  # pragma: no cover - defensive
                LOGGER.exception("Bot crashed: %s", exc)
                self.state.update(
                    {
                        "running": False,
                        "last_error": str(exc),
                        "last_result": "exception",
                        "last_stop": datetime.now(timezone.utc).isoformat(),
                    }
                )
            finally:
                with self._lock:
                    self._bot = None

            if self._stop_event.is_set():
                break

            self.state["restart_count"] += 1
            self._wait_with_stop(BOT_RESTART_DELAY)

    # ------------------------------------------------------------------
    def _wait_with_stop(self, seconds: int) -> None:
        for _ in range(seconds):
            if self._stop_event.is_set():
                break
            time.sleep(1)


class KeepAlive(threading.Thread):
    """Background thread that pings the service URL to prevent idling."""

    def __init__(self, url: Optional[str]) -> None:
        super().__init__(name="keepalive", daemon=True)
        self.url = url
        self._stop_event = threading.Event()

    def run(self) -> None:  # pragma: no cover - thread w/ network
        if not self.url:
            LOGGER.warning("No keepalive URL configured; the service may idle on free tier")
            return

        LOGGER.info("Starting keepalive pings to %s every %s seconds", self.url, KEEPALIVE_INTERVAL)
        while not self._stop_event.wait(timeout=KEEPALIVE_INTERVAL):
            try:
                response = httpx.get(self.url.rstrip("/") + "/healthz", timeout=10)
                LOGGER.debug("Keepalive status %s", response.status_code)
            except Exception as exc:
                LOGGER.warning("Keepalive ping failed: %s", exc)

    def stop(self) -> None:
        self._stop_event.set()


supervisor = BotSupervisor(enabled=BOT_ENABLED)
keepalive = KeepAlive(_resolve_keepalive_url())
app = FastAPI(title="GinieBot", version="1.0.0")


@app.on_event("startup")
def startup_event() -> None:
    LOGGER.info("Starting XMPP bot supervisor")
    supervisor.start()
    keepalive.start()


@app.on_event("shutdown")
def shutdown_event() -> None:
    LOGGER.info("Stopping XMPP bot supervisor")
    keepalive.stop()
    supervisor.stop()


@app.get("/healthz")
def healthz() -> JSONResponse:
    """Return a snapshot of the bot state."""
    payload = {
        "status": "ok" if supervisor.state.get("running") else "starting",
        "bot": supervisor.state,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }
    return JSONResponse(payload)


@app.get("/")
@app.get("/status")
def root_status() -> Dict[str, Any]:
    """Provide a lightweight status payload for manual checks."""
    return {
        "message": "GinieBot is running",
        "running": supervisor.state.get("running", False),
        "restart_count": supervisor.state.get("restart_count", 0),
        "last_error": supervisor.state.get("last_error"),
    }