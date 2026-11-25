# Gemini at the workshop

## 1. Web chat

Use the Gemini web app. No key is needed.

1. Open the Gemini web app and sign in.
2. Copy a prompt from the workshop sheet and paste it into the chat.
3. Read the answer. Check its label. Confirm which model replied.
4. Never paste a key or password into the chat.

## 2. API route

You need a key saved through the environment's Network secrets for
generativelanguage.googleapis.com. The session proxy then adds it to
requests for that host. The script does not read or send a key.

Run it from the repository root:

    python3 -I workshop/api/gemini.py "your prompt"

Exit codes:

- 0: the prompt was sent and the answer printed.
- 1: refused by the budget, or an error (HTTP error, network, bad reply).
- 3: not authorised. The key is not saved for this host yet.

The budget limits each call to 8192 tokens, 10 calls a minute and 200 calls a day.

## 3. Current status

Checked on 2026-11-25. One run of `python3 -I workshop/api/gemini.py "hello"` returned:

    not authorised: the credential is not saved for this host yet

Exit code: 3.

The key is not saved for this host yet. Save it in Network secrets, then run again.
