#!/usr/bin/env python3
"""A context and call budget for model API endpoints, checked exactly. Standard library only.

A request is ALLOWED only if all hold:
  1. the host is on the allowlist (one host: generativelanguage.googleapis.com);
  2. prompt tokens + max output tokens <= the per-call context cap (default 8192);
  3. calls in the last 60 seconds < the per-minute cap (default 10);
  4. calls today < the daily cap (default 200);
  5. the prompt contains no secret-like string (a key pattern is refused, not sent).
Rules are checked in that order; the first failure is the reason. Limits are constants, so the budget is exact.
Run: python3 -I workshop/api/budget.py   (last line is JSON)
"""
import json, re, time

HOSTS = {"generativelanguage.googleapis.com"}
CONTEXT_CAP = 8192
PER_MINUTE = 10
PER_DAY = 200
SECRET = re.compile(r"(AIza[0-9A-Za-z_\-]{20,}|sk-[A-Za-z0-9]{20,}|-----BEGIN [A-Z ]*PRIVATE KEY-----)")

def allow(req, calls_last_minute, calls_today):
    if req["host"] not in HOSTS: return False, "host not on the allowlist"
    if req["prompt_tokens"] + req["max_output"] > CONTEXT_CAP: return False, "prompt plus output exceeds the context cap"
    if calls_last_minute >= PER_MINUTE: return False, "per-minute cap reached"
    if calls_today >= PER_DAY: return False, "daily cap reached"
    if SECRET.search(req["prompt"]): return False, "secret-like string in the prompt: refused, not sent"
    return True, "allowed"

def main():
    t0 = time.time()
    ok = {"host": "generativelanguage.googleapis.com", "prompt_tokens": 500, "max_output": 512, "prompt": "What is the Beauvoir mirror?"}
    cases = [
        (ok, 0, 0, True),
        (dict(ok, host="example.com"), 0, 0, False),
        (dict(ok, prompt_tokens=8000, max_output=512), 0, 0, False),
        (dict(ok, prompt_tokens=8192 - 512, max_output=512), 0, 0, True),
        (ok, 10, 0, False),
        (ok, 9, 0, True),
        (ok, 0, 200, False),
        (dict(ok, prompt="my key is AIza" + "x" * 35), 0, 0, False),
    ]
    for req, m, d, want in cases:
        got, why = allow(req, m, d)
        assert got == want, f"{why} (expected {want})"
    print(f"{len(cases)} cases: the rules allow and refuse exactly as stated")
    print(f"limits: context {CONTEXT_CAP} tokens, {PER_MINUTE} per minute, {PER_DAY} per day, one host")
    print("PASS")
    print(json.dumps({"states": len(cases), "seconds": round(time.time() - t0, 4), "context_cap": CONTEXT_CAP,
                      "per_minute": PER_MINUTE, "per_day": PER_DAY}))

if __name__ == "__main__":
    main()
