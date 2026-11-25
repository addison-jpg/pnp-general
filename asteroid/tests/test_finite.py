"""Test of asteroid/ext_finite.py: the formula evaluator, and a program with true and deliberately false claims.
Run from the repository root:  python3 -I asteroid/tests/test_finite.py      (exit 1 on any FAIL)"""
import os, re, subprocess, sys, tempfile
sys.path.insert(0, os.getcwd())
from asteroid import ext_finite as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

ev = lambda s, n: X.ev(X.parse(s), {"n": n})
want("(2n-3)!! at n=1..5", [ev("(2*n - 3)!!", n) for n in range(1, 6)] == [1, 1, 3, 15, 105])
want("n! and C", ev("n!", 6) == 720 and ev("C(n, 2)", 5) == 10 and ev("C(n, 7)", 5) == 0)
want("precedence", ev("2 + 3 * n ** 2", 2) == 14 and ev("-n ** 2", 3) == -9 and ev("(n + 1)!", 3) == 24)
want("Bell by sum", [ev("sum(k, 0, n, sum(j, 0, k, (-1)**j * C(k, j) * (k - j)**n) // k!)", n) for n in range(1, 7)] == [1, 2, 5, 15, 52, 203])
for bad in ("7 // 2", "(-3)!", "2 ** (0 - 1)", "m + 1", "n +", "1.5"):
    try: ev(bad, 1); want(f"rejects {bad}", False)
    except ValueError: want(f"rejects {bad}", True)

for big in ("sum(k, 0, 10**12, 0)", "(10**7)!", "C(10**9, 5)", "(10**8)!!"):
    try: ev(big, 1); want(f"bounds {big}", False)
    except ValueError: want(f"bounds {big}", True)
want("passed needs a PASS line", X._passed("x\nPASS\n{}") and not X._passed("FAIL a\nPASS") and not X._passed("all PASS"))
X.SEQ["e"] = []
want("empty formula claim is FALSE", X.claim_expr('formula e = "1 // 0"', False, {})[0] is False)
X.SEQ["e"] = [1, 2]
want("empty literal claim is FALSE", X.claim_expr("e = []", False, {"script": "t", "ln": 1})[0] is False)
try: X.claim_expr("e = [1-2]", False, {"script": "t", "ln": 1}); want("bad literal is an error", False)
except SystemExit as e: want("bad literal is an error", "not an integer" in str(e))

prog = '''seq cat = [1, 1, 2, 5, 14, 42, 132]
seq ps = [1, 2, 4, 9, 23, 65, 197]
seq bell = from privacy/fingerprints.json "Bell numbers"
claim cat = [1, 1, 2, 5, 14]
claim cat = [1, 1, 2, 5, 15]
claim cat matches ps partial
claim cat matches ps diff
claim formula cat = "C(2*n - 2, n - 1) // n"
claim formula cat = "n!"
claim formula cat = "n // 2"
claim formula bell = "sum(k, 0, n, sum(j, 0, k, (-1)**j * C(k, j) * (k - j)**n) // k!)"
claim bell matches cat
check "python3 -I brain/neuron/check.py"
check "python3 -I asteroid/tests/finite_nopass.py"
'''
expect = [True, False, True, False, True, False, False, True, False, True, False]
nopass = os.path.join("asteroid", "tests", "finite_nopass.py")
open(nopass, "w").write("print('no verdict here')\n")
try:
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "t.ath"); open(p, "w").write(prog)
        r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", p], capture_output=True, text=True)
finally: os.remove(nopass)
got = [m.group(1) == "TRUE" for m in re.finditer(r": python (TRUE|FALSE)", r.stdout)]
print(r.stdout.strip()); print(r.stderr.strip()[-400:]) if r.stderr.strip() else None
want("program verdicts", got == expect)
want("summary counts", f"claims: {expect.count(True)} true, {expect.count(False)} false" in r.stdout)
want("exit 1 when a claim is false", r.returncode == 1)
print(f"finite: {len(fails)} failures")
if not fails: print("PASS")
sys.exit(1 if fails else 0)
