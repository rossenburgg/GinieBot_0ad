# GinieBot_0ad

XMPP bots for the Wildfire Games (0 A.D.) lobby.

- `main.py`: the full-featured GinieBot with moderation, spam detection, watch lists, player reports, mute, Wikipedia lookup, AI replies, analytics charts, and forum posting.
- `simple_bot/simple_bot.py`: a stripped-down helper that only joins a few lobby rooms and keeps its presence set to away.

## Full bot

### Prerequisites

- Python 3.10+
- `sleekxmpp` is vendored in this repo, no install needed.

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

Extra features degrade gracefully: without `wikipedia`/`nltk` there is no wiki lookup, without `openai` no AI replies, without `selenium` no forum posting, without `plotly` no charts. Install what you want from `requirements-full.txt`.

### Run it

```bash
cp .env.example .env  # edit the copy with your credentials
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements-full.txt
PYTHONPATH=. python main.py
```

`PYTHONPATH=.` is required so the vendored `sleekxmpp` package is found.

## Simple presence bot

The lightweight bot lives in `simple_bot/`. It automatically joins `arena25`, `arena26`, and `helpers` on the Wildfire Games lobby and advertises an away presence. No moderation, analytics, or command handling is bundled with this version.

### Prerequisites

- Python 3.9+
- `sleekxmpp`
- `python-dotenv`

### Required environment variables

Set these variables before launching the bot:

- `XMPP_JID`: Full JID of the bot account (for example, `bot@lobby.wildfiregames.com`).
- `XMPP_PASSWORD`: Password for the account.
- `XMPP_NICKNAME`: Nickname the bot should present inside the rooms.

Optional:

- `XMPP_ROOMS`: Comma-separated list of room JIDs to join. When omitted, the bot defaults to the three rooms listed above.

### Run it

```bash
cp .env.example .env  # edit the copy with your credentials
python3 -m venv .venv
source .venv/bin/activate
pip install -r simple_bot/requirements.txt
PYTHONPATH=. python simple_bot/simple_bot.py
```

`PYTHONPATH=.` is required so the vendored `sleekxmpp` package is found. (Running the script path directly without it fails with `ModuleNotFoundError: No module named 'sleekxmpp'`.)

The script keeps running until interrupted, reconnecting automatically when the connection drops.

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
