import json, os, sys, tempfile
from nacl.signing import SigningKey
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import app
fails = 0
def check(name, cond):
    global fails
    print(("PASS " if cond else "FAIL ") + name); fails += (not cond)
sk = SigningKey.generate(); pub = sk.verify_key.encode().hex()
def signed(body: bytes, ts="1700000000"):
    sig = sk.sign(ts.encode() + body).signature.hex()
    return {"x-signature-ed25519": sig, "x-signature-timestamp": ts}
repo = tempfile.mkdtemp()
open(os.path.join(repo, "RESULTS.md"), "w").write("# Results\n\n135 verified findings -> RESULTS.md\n")
open(os.path.join(repo, "gravity.ath"), "w").write("")
open(os.path.join(repo, "hello.ath"), "w").write("")
env = {"DISCORD_PUBLIC_KEY": pub, "REPO_DIR": repo}
ping = json.dumps({"type": 1}).encode()
check("PING with a valid signature answers type 1", app.handle(ping, signed(ping), env) == (200, {"type": 1}))
bad = dict(signed(ping)); bad["x-signature-ed25519"] = "00" * 64
check("a forged signature is rejected", app.handle(ping, bad, env)[0] == 401)
check("a valid signature over a different body is rejected", app.handle(ping, signed(b'{"type":2}'), env)[0] == 401)
check("a missing signature is rejected", app.handle(ping, {}, env)[0] == 401)
st = json.dumps({"type": 2, "data": {"name": "status"}}).encode()
code, out = app.handle(st, signed(st), env)
check("/status reports the verified count", code == 200 and "verified findings: 135" in out["data"]["content"])
ck = json.dumps({"type": 2, "data": {"name": "check", "options": [{"value": "../etc/passwd"}]}}).encode()
code, out = app.handle(ck, signed(ck), env)
check("/check refuses a path outside the allowlist", code == 200 and "not an allowed program" in out["data"]["content"])
ck2 = json.dumps({"type": 2, "data": {"name": "check", "options": [{"value": "hello.ath"}]}}).encode()
code, out = app.handle(ck2, signed(ck2), env)
check("/check refuses hello.ath (needs Lean)", "not an allowed program" in out["data"]["content"])
un = json.dumps({"type": 2, "data": {"name": "rm"}}).encode()
check("unknown commands are refused, not run", "unknown command" in app.handle(un, signed(un), env)[1]["data"]["content"])
print(f"{fails} failures")
sys.exit(1 if fails else 0)
