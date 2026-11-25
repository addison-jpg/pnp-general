"""Test of asteroid/ext_frame.py: frames that pass, fail, have no claim, or claim too much.
Run from the repository root:  python3 -I asteroid/tests/test_frame.py      (exit 1 on any FAIL)"""
import json, os, re, subprocess, sys, tempfile
sys.path.insert(0, os.getcwd())
from asteroid import ext_frame as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

want("score formula", X.score(3, True, "checked-finite", 80) == 3 / 80 and abs(X.score(2, False, "open", 160) - 0.00375) < 1e-12)

with tempfile.TemporaryDirectory() as d:
    good = os.path.join(d, "good.ath"); open(good, "w").write('seq s = [1, 2, 3, 4, 5]\nclaim s = [1, 2, 3]\n')
    bad = os.path.join(d, "bad.ath"); open(bad, "w").write('seq s = [1, 2, 3]\nclaim s = [1, 2, 4]\n')
    prog = f'''seq s = [1, 1, 2, 3, 5, 8]
claim s = [1, 1, 2, 3, 5]
claim s = [1, 1, 2, 3, 6]
frame "A" reading "passes" -> 2 label checked-finite reach 3
frame "B" reading "line claim fails" -> 3 label checked-finite
frame "C" reading "no claim" -> none label tested reach 2 cost 160
frame "D" reading "claims Lean" -> 2 label checked
frame "E" reading "file passes" -> {good} label checked-infinite
frame "F" reading "file fails" -> {bad} label checked-finite
'''
    p = os.path.join(d, "t.ath"); open(p, "w").write(prog)
    fr = os.path.join(d, "frames.jsonl")
    env = dict(os.environ, ASTEROID_FRAMES=fr)
    cmd = [sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", p]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    print(r.stdout.strip()); print(r.stderr.strip()[-400:]) if r.stderr.strip() else None
    rows = {e["source"]: e for e in map(json.loads, open(fr))}
    want("six frames written", len(rows) == 6)
    want("A TRUE, score 3/80", rows["A"]["status"] == "TRUE" and rows["A"]["score"] == round(3 / 80, 6))
    want("B claim fails: OPEN, label forced to open", rows["B"]["status"] == "OPEN" and rows["B"]["label"] == "open" and "forced to open" in r.stdout)
    want("C no claim: OPEN, open, 2*0.3/160", rows["C"]["status"] == "OPEN" and rows["C"]["label"] == "open" and rows["C"]["score"] == 0.00375)
    want("D checked on a Python claim: downgraded", rows["D"]["label"] == "checked-finite" and "downgraded" in r.stdout)
    want("E file passes, checked-infinite downgraded", rows["E"]["status"] == "TRUE" and rows["E"]["label"] == "checked-finite")
    want("F file fails: OPEN, open", rows["F"]["status"] == "OPEN" and rows["F"]["label"] == "open")
    want("program exit 1 from the false claim, not the frames", r.returncode == 1 and "claims: 1 true, 1 false" in r.stdout)
    r2 = subprocess.run(cmd, capture_output=True, text=True, env=env)
    want("rerun keeps, no duplicates", len(open(fr).readlines()) == 6 and r2.stdout.count("kept in frames.jsonl") == 6)
    q = subprocess.run([sys.executable, "-I", "center.py", "queue"], capture_output=True, text=True, env=env)
    lines = [l for l in q.stdout.splitlines() if l and l[0].isdigit() and "open frames" not in l]
    scores = [float(l.split()[0]) for l in lines]
    want("queue lists the 3 open frames, highest first", q.returncode == 0 and len(lines) == 3 and scores == sorted(scores, reverse=True) and "3 open frames" in q.stdout)
    for bad_line in ('frame "X" reading "y" -> 99 label open', 'frame "X" reading "y" -> 2 label great', 'frame "X" reading "y" -> foo label open'):
        open(p, "w").write("seq s = [1, 2, 3]\nclaim s = [1, 2]\n" + bad_line + "\n")
        r3 = subprocess.run(cmd, capture_output=True, text=True, env=env)
        want(f"error: {bad_line[22:]}", r3.returncode != 0 and "Traceback" not in r3.stderr)
print(f"frame: {len(fails)} failures")
sys.exit(1 if fails else 0)
