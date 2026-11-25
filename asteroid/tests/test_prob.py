"""Test of asteroid/ext_prob.py: exact finite distributions, with true and deliberately false claims.
Run from the repository root:  python3 -I asteroid/tests/test_prob.py      (exit 1 on any FAIL)"""
import os, re, subprocess, sys, tempfile
from fractions import Fraction
sys.path.insert(0, os.getcwd())
from asteroid import ext_prob as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

d = X.parse_dist("H: 1/2, T: 1/2", "t")
want("coin", d == {"H": Fraction(1, 2), "T": Fraction(1, 2)})
p = X.product(d, X.parse_dist("1: 1/3, 2: 2/3", "t"))
want("product sums to 1", sum(p.values()) == 1 and p["H.2"] == Fraction(1, 3))
for bad in ("a: 1/2, b: 1/3", "a: 1/2, b: 0.5", "a: -1/2, b: 3/2", "a: 1/0", "a: 1/2, a: 1/2", ""):
    try: X.parse_dist(bad, "t"); want(f"rejects {{{bad}}}", False)
    except SystemExit: want(f"rejects {{{bad}}}", True)

prog = '''dist coin = {H: 1/2, T: 1/2}
dist die = {1: 1/6, 2: 1/6, 3: 1/6, 4: 1/6, 5: 1/6, 6: 1/6}
dist pair = coin * die
claim prob die (2, 4, 6) = 1/2
claim prob die (2, 4, 6) = 1/3
claim expect die = 7/2
claim expect die = 3
claim prob pair (H.6, T.6) = 1/6
claim prob pair (H.6) = 1/6
claim prob die (7) = 0
claim expect coin = 1/2
claim not prob die (1) = 1/2
'''
expect = [True, False, True, False, True, False, False, False, True]
with tempfile.TemporaryDirectory() as dd:
    f = os.path.join(dd, "t.ath"); open(f, "w").write(prog)
    r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", f], capture_output=True, text=True)
got = [m.group(1) == "TRUE" for m in re.finditer(r": python (TRUE|FALSE)", r.stdout)]
print(r.stdout.strip()); print(r.stderr.strip()[-400:]) if r.stderr.strip() else None
want("program verdicts (false claims print FALSE)", got == expect)
want("summary counts", f"claims: {expect.count(True)} true, {expect.count(False)} false" in r.stdout)
want("exit 1 when a claim is false", r.returncode == 1)
print(f"prob: {len(fails)} failures")
if not fails: print("PASS")
sys.exit(1 if fails else 0)
