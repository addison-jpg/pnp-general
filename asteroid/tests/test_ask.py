"""Test of asteroid/ext_ask.py: the `ask "QUESTION"` statement. It prints an answer from data and is not a claim.
Run from the repository root:  python3 -I asteroid/tests/test_ask.py      (exit 1 on any FAIL)"""
import hashlib, json, os, subprocess, sys, tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, os.getcwd())
from asteroid import ext_ask as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond, show=""):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name); print("     got:", str(show)[:500])

want("handle ignores a line that is not ask", X.handle("claim s = [1]", {"script": "x", "ln": 1}) is False and X.handle("asking", {"script": "x", "ln": 1}) is False)

def snap(d):
    return {os.path.join(b, f): hashlib.sha256(open(os.path.join(b, f), "rb").read()).hexdigest() for b, _, fs in os.walk(d) for f in fs}

with tempfile.TemporaryDirectory() as fx, tempfile.TemporaryDirectory() as work:
    os.makedirs(os.path.join(fx, "center", "shards")); os.makedirs(os.path.join(fx, "core", "ontology", "tags"))
    open(os.path.join(fx, "center", "shards", "a.jsonl"), "w").write(
        json.dumps({"kind": "finding", "program": "p", "id": "i1", "word": "checked", "why_not": [], "text": "a time fact"}) + "\n" +
        json.dumps({"kind": "finding", "program": "p", "id": "i2", "word": "tested", "why_not": ["x"], "text": "a sampled fact"}) + "\n")
    open(os.path.join(fx, "frames.jsonl"), "w").write(json.dumps({"source": "Time frame", "reading": "r", "claim": "none", "label": "open", "score": 0.1, "status": "OPEN"}) + "\n")
    tag = lambda k, rows: {"status": "proposed tags, unreviewed", "kind": k, "rows": rows, "proposed_vocabulary": {"status": "proposed, not adopted", "tags": []}}
    json.dump(tag("culture", [{"corpus": "carseat", "name": "w", "reading": "r", "tags": ["fixed-point"], "label": "analogy", "label_word": "analogy", "file": "f"}]),
              open(os.path.join(fx, "core", "ontology", "tags", "tags_culture.json"), "w"))
    json.dump(tag("formal", [{"pillar": "physics", "name": "res", "reading": None, "tags": ["fixed-point"], "label": "checked-finite", "label_word": "checked-finite", "file": "g"}]),
              open(os.path.join(fx, "core", "ontology", "tags", "tags_formal.json"), "w"))
    prog = os.path.join(work, "t.ath")
    open(prog, "w").write('seq s = [1, 2, 3]\nclaim s = [1, 2]\n'
                          'ask "how many results are verified"\nask "show frames about time"\nask "what links carseat and physics"\n'
                          'ask "which results use fixed-point"\nask "show findings about time"\nask "what connects carseat and physics"\nask "show frames about $(touch %s/pwned)"\nask "gibberish"\n' % work)
    before = snap(fx)
    fr = os.path.join(work, "frames.jsonl")
    env = dict(os.environ, ASK_ROOT=fx, ASTEROID_FRAMES=fr)
    r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", prog], capture_output=True, text=True, env=env)
    print(r.stdout.strip()[-1500:]); print(r.stderr.strip()[-300:]) if r.stderr.strip() else None
    out = r.stdout
    want("program exits 0", r.returncode == 0, r.stderr)
    want("answers are printed with labels", "[checked] 1 verified findings recorded as checked" in out and "1 of 2 results are verified in all" in out and "[open] frame OPEN: Time frame" in out, out)
    want("a tag row prints as [proposed], never as checked", "[proposed] result physics: res (row label: checked-finite;" in out and "[checked-finite] result" not in out, out)
    want("current findings: show findings about time prints the finding with its label", "1 findings about time: 1 verified" in out and "[checked] finding p/i1: a time fact (verified" in out, out)
    want("what connects: the shared tag is [proposed]", "[proposed] shared tags (1): fixed-point" in out, out)
    want("links answer", "carseat and physics share 1 tags: fixed-point" in out, out)
    want("not a claim: the claims line counts only the one real claim", "claims: 1 true, 0 false" in out, out)
    want("ask lines say they are not claims", out.count("(a question, not a claim)") == 8)
    want("an unparseable question prints did not understand and the grammar, and the program goes on", "did not understand: gibberish" in out and "Grammar" in out)
    want("a shell word in the question is data: refused, nothing run", "did not understand: show frames about $(touch" in out and not os.path.exists(os.path.join(work, "pwned")))
    want("no frame or record written (frames file not created)", not os.path.exists(fr))
    want("no file changed in the data folder", snap(fx) == before)
    open(prog, "w").write('ask show frames\n')
    r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", prog], capture_output=True, text=True, env=env)
    want("ask without quotes is a plain error naming the form", r.returncode != 0 and 'ask "QUESTION"' in (r.stdout + r.stderr), r.stdout + r.stderr)
print(f"\n{len(fails)} failed" if fails else "\nall passed")
sys.exit(1 if fails else 0)
