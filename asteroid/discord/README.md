# asteroid on Discord: an interactions endpoint

One function, `app.handle(body, headers)`, that answers Discord's signed slash-command requests. It does not need a bot to stay connected: Discord POSTs each command to a public HTTPS URL, and this code verifies the request and replies.

## Commands
- `/status`: the verified-findings count from `RESULTS.md`.
- `/check PROGRAM`: runs one top-level `.ath` program with `--no-lean` and replies with its summary line. Only top-level `.ath` files are accepted (not `hello.ath`, which needs Lean). Nothing else runs.

## Safety
- Every request's Ed25519 signature is checked against the application's public key; anything else gets 401.
- It writes nothing to the repository.
- The bot token is never needed here; the endpoint only needs the **public** key.

## Run it
Needs `pynacl` (`pip install pynacl`). Environment: `DISCORD_PUBLIC_KEY` (hex, from the Developer Portal) and `REPO_DIR` (a checkout of this repo). Put `app.handle` behind any HTTPS host (a small WSGI/ASGI wrapper, a serverless function, or a tunnel). In the portal, set the Interactions Endpoint URL to that address; Discord pings it to verify. Register `/status` and `/check` once with the bot token (kept out of the repo).

Tests: `python3 -I asteroid/discord/test_app.py` (needs `pynacl`).
