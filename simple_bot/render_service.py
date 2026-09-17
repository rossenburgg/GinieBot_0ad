"""Render deployment entrypoint exposing HTTP health checks.

This module hosts a FastAPI web service that starts the XMPP bot in a
background thread. Keeping the bot inside a web service prevents Render's
free tier from idling the process after 15 minutes, because periodic
keep-alive requests will hit the exposed HTTP endpoint.
"""

from __future__ import annotations

import hmac
import logging
import os
import sys
import threading
import time
from datetime import datetime, timezone
from typing import Any, Dict, Optional

import httpx
from fastapi import Depends, FastAPI, HTTPException, Query, Request
from fastapi.responses import HTMLResponse, JSONResponse

from simple_bot.simple_bot import SimplePresenceBot, build_bot_from_env, run_bot

# The admin dashboard reads the same SQLite database the full bot writes to.
# geniebot_store.py lives in the repository root, one level above this file.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

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


# ---------------------------------------------------------------------------
# Admin dashboard (token-protected)
# ---------------------------------------------------------------------------
# Set ADMIN_TOKEN in the environment to enable these endpoints. Every request
# must carry the token either as ?token=<token> or as an
# Authorization: Bearer <token> header. Without a configured ADMIN_TOKEN the
# endpoints stay disabled instead of being left open.
ADMIN_TOKEN = os.getenv("ADMIN_TOKEN", "").strip()


def _open_store():
    """Open the shared SQLite database the full bot writes to."""
    try:
        from geniebot_store import GenieBotStore
    except ImportError as exc:  # pragma: no cover - defensive
        raise HTTPException(status_code=503, detail="Moderation database module unavailable") from exc
    try:
        return GenieBotStore()
    except Exception as exc:  # pragma: no cover - defensive
        raise HTTPException(status_code=503, detail=f"Could not open moderation database: {exc}") from exc


def require_admin_token(request: Request, token: Optional[str] = Query(default=None)) -> bool:
    if not ADMIN_TOKEN:
        raise HTTPException(status_code=503, detail="Admin dashboard is disabled (ADMIN_TOKEN is not set)")
    provided = (token or "").strip()
    auth = request.headers.get("Authorization", "")
    if auth.lower().startswith("bearer "):
        provided = provided or auth[7:].strip()
    if not provided or not hmac.compare_digest(provided, ADMIN_TOKEN):
        raise HTTPException(status_code=401, detail="Invalid or missing admin token")
    return True


def _rows_to_dicts(rows):
    return [dict(row) for row in rows]


@app.get("/admin", response_class=HTMLResponse)
def admin_dashboard(authorized: bool = Depends(require_admin_token)) -> str:
    """Serve a small self-contained dashboard page (token stays in the URL)."""
    return """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>GinieBot admin</title>
<style>
body { font-family: system-ui, sans-serif; max-width: 960px; margin: 2rem auto; padding: 0 1rem; }
h1 { font-size: 1.4rem; }
table { border-collapse: collapse; width: 100%; margin: 1rem 0; }
th, td { border: 1px solid #ccc; padding: 0.4rem 0.6rem; text-align: left; font-size: 0.85rem; }
th { background: #f4f4f4; }
section { margin-top: 2rem; }
#stats { font-size: 0.9rem; color: #444; }
.error { color: #a00; }
</style>
</head>
<body>
<h1>GinieBot moderation admin</h1>
<p id="stats">Loading…</p>
<section><h2>Reports</h2><div id="reports">Loading…</div></section>
<section><h2>Offenders</h2><div id="offenders">Loading…</div></section>
<section><h2>Watchlist</h2><div id="watchlist">Loading…</div></section>
<script>
const token = new URLSearchParams(location.search).get("token") || "";
const api = (path) => fetch(path + "?token=" + encodeURIComponent(token)).then(r => {
  if (!r.ok) throw new Error("HTTP " + r.status);
  return r.json();
});
function table(el, rows) {
  if (!rows.length) { el.textContent = "None."; return; }
  const cols = Object.keys(rows[0]);
  el.innerHTML = "<table><thead><tr>" + cols.map(c => "<th>" + c + "</th>").join("") +
    "</tr></thead><tbody>" + rows.map(r => "<tr>" + cols.map(c =>
      "<td>" + (r[c] == null ? "" : String(r[c]).replace(/</g, "&lt;")) + "</td>").join("") +
    "</tr>").join("") + "</tbody></table>";
}
function fail(el, err) { el.innerHTML = '<span class="error">' + err.message + "</span>"; }
Promise.all([api("/admin/api/stats"), api("/admin/api/reports"),
             api("/admin/api/offenders"), api("/admin/api/watchlist")])
  .then(([stats, reports, offenders, watchlist]) => {
    document.getElementById("stats").textContent =
      "Reports: " + stats.reports + " | Offenders: " + stats.offenders +
      " | Watched: " + stats.watchlist + " | DB: " + stats.db;
    table(document.getElementById("reports"), reports);
    table(document.getElementById("offenders"), offenders);
    table(document.getElementById("watchlist"), watchlist);
  })
  .catch(err => { document.getElementById("stats").innerHTML =
    '<span class="error">Failed to load: ' + err.message + "</span>"; });
</script>
</body>
</html>
"""


@app.get("/admin/api/stats")
def admin_stats(authorized: bool = Depends(require_admin_token)) -> Dict[str, Any]:
    store = _open_store()
    try:
        return {
            "reports": len(store.list_reports()),
            "offenders": len(store.list_offenders()),
            "watchlist": len(store.list_watch()),
            "db": store.path,
        }
    finally:
        store.close()


@app.get("/admin/api/reports")
def admin_reports(authorized: bool = Depends(require_admin_token)):
    store = _open_store()
    try:
        return _rows_to_dicts(store.list_reports())
    finally:
        store.close()


@app.get("/admin/api/offenders")
def admin_offenders(authorized: bool = Depends(require_admin_token)):
    store = _open_store()
    try:
        return _rows_to_dicts(store.list_offenders())
    finally:
        store.close()


@app.get("/admin/api/watchlist")
def admin_watchlist(authorized: bool = Depends(require_admin_token)):
    store = _open_store()
    try:
        return _rows_to_dicts(store.list_watch())
    finally:
        store.close()