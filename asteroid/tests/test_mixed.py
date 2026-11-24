"""Cross-check of asteroid/ext_mixed.py: the direct naive mixed slack / MixedStep against continuous.py, on two small circuits.
Run from the repository root:  python3 -I asteroid/tests/test_mixed.py"""
import sys, os, json
sys.path.insert(0, os.getcwd()); sys.path.insert(0, os.path.join(os.getcwd(), "one-not/tools/search"))
import asteroid.asteroid as A      # sets up sys.path for core / continuous
from asteroid import ext_mixed as X
circuits = {
  "tiny": {"n": 4, "sets": [[0, 1, 2], [2, 3]], "gates": [["or", 0, 1], ["or", 4, 2], ["or", 2, 3]], "outs": [5, 6]},
  "ess_rand_clean_744": json.load(open("one-not/data/witnesses/ess_rand_clean_744.json")),
}
for name, c in circuits.items():
    c = {k: c[k] for k in ("n", "sets", "gates", "outs")}; n = c["n"]; w = X._tables(c); bad = 0; states = 0
    for R in range(1 << n):
        cnt, base = X._C().slack_table(c, R, parts=True)
        for Q in range(1 << n):
            if Q & R: continue
            states += 1; j = X._compress(Q, R, n)
            if X.direct_parts(c, Q, R, w) != (int(cnt[j]), int(base[j])): bad += 1
    hold_d, ns, pos = X.direct_mixedstep(c); hold_c, m, k = X.mixedstep_holds(c)
    print(f"{name}: n={n} {states} states, {bad} disagreements in (witnesses, base); mixedstep direct {hold_d} vs continuous {hold_c} (margin {m}); states with base>0: {pos}")
    assert bad == 0 and hold_d == hold_c and states == 3 ** n
print("cross-check OK")
