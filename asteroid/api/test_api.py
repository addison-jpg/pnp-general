import json, os, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import api
fails = 0
def check(name, cond):
    global fails
    print(("PASS " if cond else "FAIL ") + name); fails += (not cond)
r = tempfile.mkdtemp(); os.makedirs(os.path.join(r, "center", "shards"))
rows = [{"kind": "finding", "id": "a1", "program": "brain", "word": "checked-finite", "text": "x", "runner": "python3 -I x.py"},
        {"kind": "finding", "id": "a2", "program": "brain", "word": "open", "text": "y"},
        {"kind": "finding", "id": "a3", "program": "cosmos", "word": "tested", "text": "z", "why_not": ["no second seat"]},
        {"kind": "cell", "id": "c1", "program": "brain", "text": "cell"}]
open(os.path.join(r, "center", "shards", "s.jsonl"), "w").write("\n".join(json.dumps(x) for x in rows) + "\n")
open(os.path.join(r, "frames.jsonl"), "w").write("\n".join(json.dumps(x) for x in [{"claim": "a", "score": 1, "status": "OPEN"}, {"claim": "b", "score": 3, "status": "OPEN"}, {"claim": "c", "score": 9, "status": "TRUE"}]) + "\n")
for f in ("gravity.ath", "hello.ath"): open(os.path.join(r, f), "w").write("")
env = {"REPO_DIR": r}
rt = lambda m, p, q=None, b=b"", h=None, e=env: api.route(m, p, q or {}, b, h or {}, e)
check("health", rt("GET", "/health") == (200, {"ok": True}))
c, s = rt("GET", "/status"); check("status counts only verified findings", c == 200 and s["verified"] == 1 and s["by_label"] == {"checked-finite": 1})
check("results filter by program", rt("GET", "/results", {"program": ["brain"]})[1][0]["id"] == "a1" and rt("GET", "/results", {"program": ["cosmos"]})[1] == [])
check("frames sorted by score, status filter", [x["claim"] for x in rt("GET", "/frames", {"status": ["open"]})[1]] == ["b", "a"])
check("programs exclude hello.ath", rt("GET", "/programs")[1] == ["gravity.ath"])
check("check refuses a path", rt("POST", "/check", b=b'{"program":"../x.ath"}')[0] == 400)
check("check refuses hello.ath", rt("POST", "/check", b=b'{"program":"hello.ath"}')[0] == 400)
check("check refuses bad json", rt("POST", "/check", b=b"{")[0] == 400)
e2 = dict(env, API_KEY="k")
check("check needs the key when API_KEY is set", rt("POST", "/check", b=b'{"program":"gravity.ath"}', e=e2)[0] == 401)
check("a wrong key is refused", rt("POST", "/check", b=b'{"program":"gravity.ath"}', h={"x-api-key": "no"}, e=e2)[0] == 401)
check("unknown route is 404", rt("GET", "/nope")[0] == 404 and rt("POST", "/status")[0] == 404)
print(f"{fails} failures"); sys.exit(1 if fails else 0)
