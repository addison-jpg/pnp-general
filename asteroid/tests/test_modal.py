"""Test of asteroid/ext_modal.py: Kripke frames, with true and deliberately false claims.
Run from the repository root:  python3 -I asteroid/tests/test_modal.py      (exit 1 on any FAIL)"""
import os, re, subprocess, sys, tempfile
sys.path.insert(0, os.getcwd())
from asteroid import ext_modal as X
if sys.argv[1:]: sys.exit(f"unknown arguments: {sys.argv[1:]}")
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

# relation counts on 3 worlds, known sequences: reflexive 2^6, transitive 171 (A006905), equivalence 5 (Bell)
want("512 relations on 3", len(X.all_frames(3, ["any"])) == 512)
want("64 reflexive", len(X.all_frames(3, ["reflexive"])) == 64)
want("171 transitive", len(X.all_frames(3, ["transitive"])) == 171)
want("5 equivalences", len(X.all_frames(3, ["reflexive", "symmetric", "transitive"])) == 5)
want("reflexive+euclidean = equivalence", X.all_frames(3, ["reflexive", "euclidean"]) == X.all_frames(3, ["reflexive", "symmetric", "transitive"]))
want("serial count 7^3", len(X.all_frames(3, ["serial"])) == 343)
# euclidean, brute force against the definition
def euc(s):
    n = len(s); R = lambda a, b: s[a] >> b & 1
    return all(R(b, c) for a in range(n) for b in range(n) for c in range(n) if R(a, b) and R(a, c))
want("euclidean agrees with definition", all(X.has(s, "euclidean") == euc(s) for s in X.all_frames(3, ["any"])))
want("parse precedence", X.parse("p & q -> r | ~p") == ("->", ("&", ("atom", "p"), ("atom", "q")), ("|", ("atom", "r"), ("~", ("atom", "p")))))
for bad in ("p &", "[] ", "p $ q", "(p"):
    try: X.parse(bad); want(f"rejects {bad!r}", False)
    except ValueError: want(f"rejects {bad!r}", True)

prog = '''kripke A3 = all 3 any
kripke R3 = all 3 reflexive
kripke t = worlds 3 rel [(0,1),(1,2)] val p {2}
claim valid R3 "[]p -> p"
claim valid A3 "[]p -> p"
claim invalid A3 "[]p -> p"
claim invalid R3 "[]p -> p"
claim defines A3 "[]p -> [][]p" transitive
claim defines A3 "[]p -> [][]p" reflexive
claim valid A3 "[](p -> q) -> ([]p -> []q)"
claim worlds t "<>p" = {1}
claim worlds t "<>p" = {0, 1}
claim worlds t "<><>p" = {0}
claim valid A3 "[]p -> p & q & r & s"
claim worlds t "<>q" = {1}
'''
expect = [True, False, True, False, True, False, True, True, False, True, False, False]
with tempfile.TemporaryDirectory() as dd:
    f = os.path.join(dd, "t.ath"); open(f, "w").write(prog)
    r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", f], capture_output=True, text=True)
got = [m.group(1) == "TRUE" for m in re.finditer(r": python (TRUE|FALSE)", r.stdout)]
print(r.stdout.strip()); print(r.stderr.strip()[-400:]) if r.stderr.strip() else None
want("program verdicts (false claims print FALSE)", got == expect)
want("countermodel printed", "countermodel:" in r.stdout)
want("too many atoms is FALSE, not slow", "too large" in r.stdout)
want("summary counts", f"claims: {expect.count(True)} true, {expect.count(False)} false" in r.stdout)
want("exit 1 when a claim is false", r.returncode == 1)
for bad in ("kripke x = all 5 any", "kripke x = all 3 dense", "kripke x = worlds 2 rel [(0,2)]"):
    with tempfile.TemporaryDirectory() as dd:
        f = os.path.join(dd, "b.ath"); open(f, "w").write(bad + "\n")
        r = subprocess.run([sys.executable, "-I", os.path.join("asteroid", "asteroid.py"), "--no-lean", f], capture_output=True, text=True)
    want(f"error on {bad!r}", r.returncode != 0 and "python TRUE" not in r.stdout)
print(f"modal: {len(fails)} failures")
if not fails: print("PASS")
sys.exit(1 if fails else 0)
