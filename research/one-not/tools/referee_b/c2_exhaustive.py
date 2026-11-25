"""C2 data check (task boards/tasks/c2-under-no-rewire.md): EXHAUSTIVE over all cubes Q ⊆ [n] (n <= NMAX).
Discovery only; own code. Same F2 as f2_test.py (real circuit, OR gates, Z ⊇ Q, Z ∩ S_w = ∅, g(Z) = 0, g(Z+e_u) = g(Z+e_u') = 1).
For every Q with positive base (sum of d_w over alive sets > 0): is there v ∉ Q (v in an alive set) with
gain = |F2(Q) \\ F2(Q ∪ v)| >= cost = sum_{alive w ∋ v} d_w ?  Also reports MU (base <= |F2(Q)|) over all Q.
Usage: python3 -I c2_exhaustive.py files... [--nmax 9] [--out r.json]
"""
import json, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P
from f2_test import prep


def run(c):
    T, bit, full, B = prep(c)
    if not c.correct(T):
        return None
    n = c.n
    up = [full] * (1 << n)
    for Q in range(1, 1 << n):
        v = (Q & -Q).bit_length() - 1
        up[Q] = up[Q & (Q - 1)] & bit[v]
    keys = list(B.items())
    gidx = {}
    for (i, w), _ in keys:
        gidx.setdefault(i, len(gidx))
    setmask = [sum(1 << u for u in S) for S in c.sets]
    F = [0] * (1 << n)
    for Q in range(1 << n):
        m = 0
        for (i, w), b in keys:
            if not (setmask[w] & Q) and b & up[Q]:
                m |= 1 << gidx[i]
        F[Q] = m
    res = Counter(); fails = []
    for Q in range(1 << n):
        alive = [w for w, S in enumerate(c.sets) if len(S) >= 2 and not (setmask[w] & Q)]
        base = sum(len(c.sets[w]) - 1 for w in alive)
        if base <= 0:
            continue
        res["cubes"] += 1
        f = bin(F[Q]).count("1")
        if base > f:
            res["MU_fail"] += 1
        ok = False; best = None
        for v in range(n):
            if (Q >> v) & 1 or not any((setmask[w] >> v) & 1 for w in alive):
                continue
            gain = bin(F[Q] & ~F[Q | (1 << v)]).count("1")
            cost = sum(len(c.sets[w]) - 1 for w in alive if (setmask[w] >> v) & 1)
            if best is None or gain - cost > best[0]:
                best = (gain - cost, v, gain, cost)
            if gain >= cost:
                ok = True
                break
        if not ok:
            res["STEP_fail"] += 1
            fails.append(([v for v in range(n) if (Q >> v) & 1], base, f, best))
    return res, fails


if __name__ == "__main__":
    args = sys.argv[1:]
    NMAX = int(args[args.index("--nmax") + 1]) if "--nmax" in args else 9
    out = args[args.index("--out") + 1] if "--out" in args else None
    files = [a for i, a in enumerate(args) if not a.startswith("--") and (i == 0 or args[i - 1] not in ("--nmax", "--out"))]
    tot = Counter(); ex = []
    for p in files:
        for k, d in P.items(p):
            if not (isinstance(d, dict) and "gates" in d and "sets" in d):
                continue
            c = P.Circ(d)
            if not c.ok1 or c.n > NMAX:
                continue
            r = run(c)
            if r is None:
                continue
            res, fails = r
            tot["circuits"] += 1
            tot.update(res)
            if fails:
                tot["circuits_with_STEP_fail"] += 1
                if len(ex) < 50:
                    ex.append((c.n, len(c.gates), f"{p}#{k}", fails[:3]))
    r = {**tot, "STEP_fail_examples": sorted(ex)[:20]}
    s = json.dumps(r, indent=1)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
