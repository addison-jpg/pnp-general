#!/usr/bin/env python3
"""Differential test of the one-file asteroid (dist/linux/asteroid; dist/windows/asteroid.exe on Windows) against
`python3 -m asteroid`. Both run each program with --no-lean; the exit codes and the claim lines must be identical.
Programs: the root *.ath list of asteroid/tests/run_all_ath.py, asteroid/tests/notgate.ath, five of
asteroid/examples, a program with an `ask` line, one with a `propose` line (no model: both must say so and go on),
`--version`, a missing program (exit 2), and core/ontology/ask.py --model run as a Python file (exit 3).
Nothing in the repository is changed: frames go to a temporary copy of frames.jsonl ($ASTEROID_FRAMES), the model
cache to a temporary file, and asteroid/out is put back byte for byte after every run.
Run from anywhere:  python3 asteroid/tests/test_universal_exe.py [BINARY]   (exit 1 on any FAIL; skips if no binary)"""
import glob, os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "dist", "windows", "asteroid.exe") if os.name == "nt" else os.path.join(ROOT, "dist", "linux", "asteroid")
if not os.path.isfile(BIN):
    print(f"SKIP: no one-file asteroid at {BIN} (build it: see packaging/universal/asteroid.spec)"); sys.exit(0)
PY = [sys.executable, "-m", "asteroid"]
OUT = os.path.join(ROOT, "asteroid", "out")
TMP = tempfile.mkdtemp(prefix="asteroid_diff_")

progs = [p for p in sorted(glob.glob(os.path.join(ROOT, "*.ath"))) if os.path.basename(p) not in ("hello.ath", "first_light.ath")]
progs += [os.path.join(ROOT, "asteroid", "tests", "notgate.ath")]
progs += [os.path.join(ROOT, "asteroid", "examples", f) for f in ("first.ath", "prove.ath", "mixed.ath", "corpus.ath", "conjecture.ath")]
ask = os.path.join(TMP, "ask.ath")
open(ask, "w", encoding="utf-8").write('circuit c 2\nw = or 0 1\nset 0 1 -> w\nend\nclaim correct(c)\nask "how many results are verified"\nask "show open frames about time"\n')
prop = os.path.join(TMP, "propose.ath")
open(prop, "w", encoding="utf-8").write('seq s = [1, 4, 9, 16]\npropose s "a formula for s" n 1\nclaim s = [1, 4, 9, 16]\n')
cases = [(os.path.relpath(p, ROOT).replace(os.sep, "/"), ["--no-lean", p]) for p in progs]
cases += [("ask line (temp file)", ["--no-lean", ask]), ("propose line, no model (temp file)", ["--no-lean", prop]),
          ("--version", ["--version"]), ("version", ["version"]), ("missing program", ["--no-lean", os.path.join(TMP, "no_such.ath")])]
cases = [(n, PY + a, [BIN] + a) for n, a in cases]
# a Python file run by the binary as `python3 -I FILE` (how check and frame lines run child programs); no model here: exit 3
ASKQ = ["-I", os.path.join("core", "ontology", "ask.py"), "--model", "what is open about time"]
cases += [("ask.py --model, no model", [sys.executable] + ASKQ, [BIN] + ASKQ)]

def snapshot():
    snap = {}
    for d, _, fs in os.walk(OUT):
        for f in fs:
            p = os.path.join(d, f); snap[p] = open(p, "rb").read()
    return snap

def restore(snap):
    for d, _, fs in os.walk(OUT):
        for f in fs:
            p = os.path.join(d, f)
            if p not in snap: os.remove(p)
    for p, b in snap.items():
        if not os.path.isfile(p) or open(p, "rb").read() != b:
            os.makedirs(os.path.dirname(p), exist_ok=True); open(p, "wb").write(b)

def run(cmd, tag, i):
    frames = os.path.join(TMP, f"frames_{tag}_{i}.jsonl"); shutil.copyfile(os.path.join(ROOT, "frames.jsonl"), frames)
    env = dict(os.environ, ASTEROID_FRAMES=frames, ASTEROID_QWEN_CACHE=os.path.join(TMP, f"qwen_{tag}_{i}.json"), NO_COLOR="1")
    env.pop("ASTEROID_ROOT", None)
    snap = snapshot(); t0 = time.time()
    try: r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=1800)
    finally: restore(snap)
    return r.returncode, r.stdout, r.stderr, time.time() - t0

claim_line = re.compile(r"^(\d+: claim |claims: )")
def claims(out): return [l for l in out.splitlines() if claim_line.match(l)]

git = lambda: subprocess.run(["git", "status", "--porcelain", "--ignored"], cwd=ROOT, capture_output=True, text=True).stdout
before = git(); bad = []
print(f"binary: {BIN} ({os.path.getsize(BIN) / 2**20:.1f} MiB)")
print(f"{'program':<40} {'python':>6} {'binary':>6} {'claims':>6} {'same claims':>11} {'same stdout':>11} {'py s':>6} {'bin s':>6}")
for i, (name, pcmd, bcmd) in enumerate(cases):
    pc, po, pe, pt = run(pcmd, "py", i)
    bc, bo, be, bt = run(bcmd, "bin", i)
    same = claims(po) == claims(bo); ok = pc == bc and same
    if name == "missing program": ok = ok and pc == 2
    if name.startswith("propose"): ok = ok and "model unavailable" in po and "model unavailable" in bo
    if name.startswith("ask"): ok = ok and po == bo and "(a question, not a claim)" in bo
    if name.endswith("version"): ok = ok and po == bo and pc == 0
    if name.startswith("ask.py"): ok = ok and po == bo and pc == 3 and "the model is not available" in bo
    print(f"{name:<40} {pc:>6} {bc:>6} {len(claims(po)):>6} {('yes' if same else 'NO'):>11} {('yes' if po == bo else 'no'):>11} {pt:>6.1f} {bt:>6.1f}  {'ok' if ok else 'FAIL'}")
    if not ok:
        bad.append(name)
        for l in (pe.strip().splitlines()[-3:] + be.strip().splitlines()[-3:]): print("      " + l)
shutil.rmtree(TMP, ignore_errors=True)
if git() != before: print("FAIL: the repository changed during the test"); bad.append("repository unchanged")
print(f"{len(cases) - len([b for b in bad if b != 'repository unchanged'])} of {len(cases)} cases agree")
if bad: print("FAIL: " + ", ".join(bad)); sys.exit(1)
print("PASS")
