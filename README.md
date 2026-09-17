# GinieBot_0ad

XMPP bots for the Wildfire Games (0 A.D.) lobby.

- `main.py`: the full-featured GinieBot with moderation, spam detection, watch lists, player reports, mute, Wikipedia lookup, AI replies, analytics charts, forum posting, lobby rating lookups, and SQLite persistence.
- `simple_bot/simple_bot.py`: a stripped-down helper that only joins a few lobby rooms and keeps its presence set to away.
- `simple_bot/render_service.py`: FastAPI web service wrapping the simple bot, with a token-protected `/admin` dashboard over the moderation database.
- `geniebot_store.py`: SQLite persistence layer for reports, offenders, and the watchlist (shared by the full bot and the admin dashboard).

## Full bot

### Prerequisites

- Python 3.10+
- `slixmpp` (the maintained fork of sleekxmpp), installed from `requirements-full.txt`.

### Required environment variables

- `XMPP_JID`: Full JID of the bot account (for example, `bot@lobby.wildfiregames.com`).
- `XMPP_PASSWORD`: Password for the account.

Optional:

- `XMPP_NICKNAME`: Nickname inside rooms (default: `GinieBot`).
- `XMPP_ROOM`: Primary room to monitor (default: `arena26@conference.lobby.wildfiregames.com`).
- `XMPP_SPAM_REPORTS`: Room JID where reports and alerts go.
- `XMPP_DEFAULT_TARGET_ROOM`, `XMPP_ARENA25`, `XMPP_ARENA27`: Override room JIDs.
- `OPENAI_API_KEY`: Enables AI replies (needs `openai` package).
- `FORUM_USER` / `FORUM_PASS`: Forum credentials for the analytics push command (needs `selenium` package).
- `GENIEBOT_DB`: Path to the SQLite database holding reports, offenders, and the watchlist (default: `./geniebot.db`). Falls back to in-memory storage if the file cannot be opened. Never commit this file; it is covered by `.gitignore`.

Extra features degrade gracefully: without `wikipedia`/`nltk` there is no wiki lookup, without `openai` no AI replies, without `selenium` no forum posting, without `plotly` no charts. Install what you want from `requirements-full.txt`.

### Feature notes

- **Smarter spam detection**: beyond the old repeated-word check, the bot now flags rate spam (more than 6 messages in 10 seconds), caps shouting (long messages that are mostly uppercase), and link spam (more than 2 URLs in one message, or the same URL repeated 3+ times). Alerts go to the spam-reports room, at most one per user every 5 minutes.
- **Rating lookup**: `{bot nick} rating <player>` queries the lobby's XMPP profile service and reports rating, highest rating, rank, games played, wins, and losses. Note: the lobby server only answers profile queries from clients whose XMPP resource starts with `0ad` (for example `bot@lobby.wildfiregames.com/0adbot`). Connecting with such a resource also makes the server track the bot as a leaderboard player; that is the operator's call.
- **Persistence**: reports, offender counts, and the watchlist are stored in SQLite and reloaded on startup, so they survive restarts.

### Run it

```bash
cp .env.example .env  # edit the copy with your credentials
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements-full.txt
python main.py
```

Run from the repository root so `geniebot_store.py` is importable.

## Simple presence bot

The lightweight bot lives in `simple_bot/`. It automatically joins `arena25`, `arena26`, and `helpers` on the Wildfire Games lobby and advertises an away presence. No moderation, analytics, or command handling is bundled with this version.

### Prerequisites

- Python 3.9+
- `slixmpp`
- `python-dotenv`

### Required environment variables

Set these variables before launching the bot:

- `XMPP_JID`: Full JID of the bot account (for example, `bot@lobby.wildfiregames.com`).
- `XMPP_PASSWORD`: Password for the account.
- `XMPP_NICKNAME`: Nickname the bot should present inside the rooms.

Optional:

- `XMPP_ROOMS`: Comma-separated list of room JIDs to join. When omitted, the bot defaults to the three rooms listed above.
- `ADMIN_TOKEN`: Token protecting the `/admin` dashboard and `/admin/api/*` JSON endpoints served by `render_service.py`. Leave unset to keep them disabled. Pass it per request as `?token=<token>` or an `Authorization: Bearer <token>` header.
- `GENIEBOT_DB`: Path to the SQLite moderation database the admin dashboard reads (default: `./geniebot.db`; same value the full bot should use).

### Run it

```bash
cp .env.example .env  # edit the copy with your credentials
python3 -m venv .venv
source .venv/bin/activate
pip install -r simple_bot/requirements.txt
PYTHONPATH=. python simple_bot/simple_bot.py
```

`PYTHONPATH=.` is required so the `simple_bot` package is found when running the script path directly. (Running it without that fails with `ModuleNotFoundError: No module named 'simple_bot'`.)

The script keeps running until interrupted, reconnecting automatically when the connection drops.

### Admin dashboard

`simple_bot/render_service.py` is the Render web-service entrypoint. Besides the bot supervisor and `/healthz`, it serves a token-protected admin dashboard over the same SQLite database the full bot writes to:

- `GET /admin`: HTML dashboard with report, offender, and watchlist tables.
- `GET /admin/api/reports`, `/admin/api/offenders`, `/admin/api/watchlist`: JSON data.
- `GET /admin/api/stats`: JSON counts plus the database path in use.

Set `ADMIN_TOKEN` to a long random value and pass it as `?token=<token>` or an `Authorization: Bearer <token>` header. Requests without a valid token get `401`; if `ADMIN_TOKEN` is unset the endpoints return `503` (disabled) instead of being left open.

You can override the default `.env` path by setting `XMPP_ENV_FILE=/absolute/path/to/envfile` if you prefer to store credentials elsewhere.

## Render deployment

The repo includes a `render.yaml` that declares a background worker named `xmpp-bot`. The worker uses `requirements.txt` at the project root (which delegates to `simple_bot/requirements.txt`) and launches `python simple_bot/simple_bot.py`.

Steps to deploy on Render:

1. Push this repository to GitHub (or another git host supported by Render).
2. In Render, create a new **Background Worker**, select the repo/branch, and let the build command/defaults come from `render.yaml`.
3. Add environment variables in the web UI:
	- `XMPP_JID`
	- `XMPP_PASSWORD`
	- `XMPP_NICKNAME`
	- `XMPP_ROOMS` (optional override)
4. Deploy. The free plan allows up to 750 runtime hours per month before the worker is paused.
