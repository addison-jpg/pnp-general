#!/usr/bin/env python3
"""Send one prompt to gemini-2.0-flash through the budget. Standard library only.

No key is read or sent here. The session proxy adds the saved credential for this host.
"""
import json, os, sys, time, urllib.error, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)  # python3 -I does not add the script directory to sys.path
import budget

HOST = "generativelanguage.googleapis.com"
URL = f"https://{HOST}/v1beta/models/gemini-2.0-flash:generateContent"
LOG = os.path.join(HERE, "calls.jsonl")

def read_counts(now):
    """Return (calls in the last 60 seconds, calls today) from the log, UTC day."""
    today = time.strftime("%Y-%m-%d", time.gmtime(now))
    last_minute = today_count = 0
    try:
        with open(LOG) as f:
            for line in f:
                if not line.strip():
                    continue
                row = json.loads(line)
                if now - row["t"] < 60: last_minute += 1
                if row["day"] == today: today_count += 1
    except FileNotFoundError:
        pass
    return last_minute, today_count

def main():
    if len(sys.argv) != 2:
        print("usage: python3 -I workshop/api/gemini.py \"prompt\"")
        return 2
    prompt = sys.argv[1]
    now = time.time()
    # Estimate: about 4 characters per token. A rough figure, not a tokenizer count.
    req = {"host": HOST, "prompt_tokens": len(prompt) // 4, "max_output": 512, "prompt": prompt}
    last_minute, today = read_counts(now)
    ok, why = budget.allow(req, last_minute, today)
    if not ok:
        print(f"refused: {why}")
        return 1

    body = json.dumps({"contents": [{"parts": [{"text": prompt}]}],
                       "generationConfig": {"maxOutputTokens": 512}}).encode()
    # Log before sending, so every request sent is counted.
    with open(LOG, "a") as f:
        f.write(json.dumps({"t": now, "day": time.strftime("%Y-%m-%d", time.gmtime(now)), "host": HOST}) + "\n")
    try:
        with urllib.request.urlopen(urllib.request.Request(
                URL, data=body, method="POST", headers={"Content-Type": "application/json"}), timeout=60) as r:
            data = json.loads(r.read())
        print(data["candidates"][0]["content"]["parts"][0]["text"])
        return 0
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            print("not authorised: the credential is not saved for this host yet")
            return 3
        print(f"error: HTTP {e.code}")
        return 1
    except urllib.error.URLError as e:
        print(f"error: network refused or unreachable ({e.reason})")
        return 1
    except (ValueError, KeyError, IndexError, TypeError):
        print("error: unexpected response shape")
        return 1

if __name__ == "__main__":
    sys.exit(main())
