"""Test of asteroid/ext_qwen.py without the model: the generator is mocked.
Checks: candidates are judged in scratch (TRUE, FALSE, REJECTED); a proposal never writes a record or a frame and
never counts as a claim; the cache makes reruns deterministic; a missing model prints a message and changes nothing.
Run from the repository root:  python3 -I asteroid/tests/test_qwen.py      (exit 1 on any FAIL)"""
import hashlib, json, os, re, subprocess, sys, tempfile
sys.path.insert(0, os.getcwd())
from asteroid import ext_qwen as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

def digest(p):
    try: return hashlib.sha256(open(p, "rb").read()).hexdigest()
    except OSError: return None

with tempfile.TemporaryDirectory() as d:
    os.environ["ASTEROID_QWEN_CACHE"] = os.path.join(d, "cache.json")
    out = []; say = out.append
    prog = os.path.join(d, "p.ath")
    open(prog, "w").write('seq sq = [1, 4, 9, 16, 25, 36]\nrecord . x checked "never"\nframe "a" reading "b" -> none label open\npropose t "x"\n')
    evil = ('claim formula sq = "n**2"\nclaim formula sq = "n**3"\n'
            'record asteroid bad checked-finite "a proposal must not write this"\n'
            'frame "x" reading "y" -> none label open\ncheck "python3 -I language/check.py"\nclaim! formula sq = "n"\n')
    calls = []
    def fake(model, system, user, k): calls.append(user); return evil
    X.generate = fake
    watched = [os.path.join(X.ROOT, "asteroid", "findings.jsonl"), os.path.join(X.ROOT, "frames.jsonl"), os.path.join(X.ROOT, "language", "findings.jsonl")]
    before = [digest(p) for p in watched]
    X.propose("t", "squares", "0.5B", 6, prog, 4, say)
    vs = [v for _, v in X.PROPOSALS["t"]]
    print("\n".join(out))
    want("context keeps only pure definitions", "record" not in calls[0] and "frame" not in calls[0] and "seq sq" in calls[0])
    want("true candidate is TRUE", vs[0] == "TRUE")
    want("false candidate is FALSE", vs[1].startswith("FALSE"))
    want("record, frame, check and claim! candidates are REJECTED", all(v.startswith("REJECTED") for v in vs[2:]))
    want("no record or frame file changed", [digest(p) for p in watched] == before)
    out.clear(); X.propose("t", "squares", "0.5B", 6, prog, 4, say)
    want("rerun hits the cache (no second model call), same verdicts", len(calls) == 1 and [v for _, v in X.PROPOSALS["t"]] == vs and "cached" in out[0])
    def broken(*a): raise RuntimeError("no python with transformers")
    X.generate = broken; out.clear()
    X.propose("u", "something else", "0.5B", 2, prog, 4, say)
    want("missing model: a message, nothing proposed", "model unavailable" in out[0] and "u" not in X.PROPOSALS)

    # a whole program: the proposal does not count as a claim, and a record after it is gated only by real claims
    cache = json.load(open(os.environ["ASTEROID_QWEN_CACHE"]))
    rec_dir = os.path.join(d, "recs"); os.makedirs(rec_dir)
    p2 = os.path.join(d, "q.ath")
    open(p2, "w").write('seq sq = [1, 4, 9, 16, 25, 36]\npropose t "squares" n 6\n')
    env = dict(os.environ, ASTEROID_FRAMES=os.path.join(d, "frames.jsonl"), ASTEROID_QWEN_PYTHON="/nonexistent")
    # seed the cache for this exact prompt so no model is needed
    user = "Task: squares\nNames already defined:\nseq sq = [1, 4, 9, 16, 25, 36]\nGive up to 6 candidate lines."
    key = hashlib.sha256(json.dumps([X.MODELS["0.5B"], X.SYSTEM, user, 6]).encode()).hexdigest()
    cache[key] = {"model": X.MODELS["0.5B"], "task": "squares", "k": 6, "text": evil}; json.dump(cache, open(os.environ["ASTEROID_QWEN_CACHE"], "w"))
    r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", p2], capture_output=True, text=True, env=env)
    print(r.stdout.strip()); print(r.stderr.strip()[-400:]) if r.stderr.strip() else None
    want("program run: exit 0, proposals print verdicts, summary counts 0 claims",
         r.returncode == 0 and "1 of 6 candidates TRUE" in r.stdout and "claims: 0 true, 0 false" in r.stdout)
    want("program run wrote no frames file and no record", not os.path.exists(env["ASTEROID_FRAMES"]) and os.listdir(rec_dir) == [])
    want("no record or frame file in the repository changed", [digest(p) for p in watched] == before)
print("FAIL" if fails else "PASS")
sys.exit(1 if fails else 0)
