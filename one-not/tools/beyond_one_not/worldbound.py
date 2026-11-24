"""The world bound (task beyond-one-not, statement S5; README items C4, T6).
A circuit with t NOT gates and each NOT gate replaced by a constant is a monotone circuit (a face). At an input x the face
given by the actual NOT outputs agrees with the circuit. So on a subcube (Q, R) (points of Q fixed to 1, of R fixed to 0) on which
the NOT outputs are constant, a monotone circuit with at most (#AND/OR gates) gates computes the restricted Boolean sum, and by
the rung-0 theorem (Wegener, Mehlhorn; checked in one-not/lean as bound_of_noNot):
      #AND/OR gates(C)  >=  worldbound(C) := max over such subcubes of base(Q, R).
For ONE NOT gate with input function h (monotone): the worst h gives exactly
      W1(S) = max over x of min(b1(x), b0(x)),   b1(x) = base(Q = x, R = empty),  b0(x) = base(Q = empty, R = complement of x)
(b1 falls and b0 rises along x, so the best cut is a threshold on them).
  python3 -I one-not/tools/beyond_one_not/worldbound.py systems       W1 on small systems and designs, the weight-band strategy
  python3 -I one-not/tools/beyond_one_not/worldbound.py circuits      worldbound(C) against the AND/OR gate count on the corpus"""
import sys, os, json, glob, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'search'))
from core import tables, correct, nots
import numpy as np

def design(n, D):
    """Lines of the cyclic plane from a perfect difference set D mod n (checked)."""
    diffs = sorted((a - b) % n for a in D for b in D if a != b)
    assert diffs == list(range(1, n)), "not a perfect difference set"
    return [sorted((d + i) % n for d in D) for i in range(n)]

SYSTEMS = [("two triples", 5, [[0, 1, 2], [0, 3, 4]]), ("triangle of triples", 6, [[0, 1, 2], [2, 3, 4], [4, 5, 0]]),
           ("two 4-sets", 7, [[0, 1, 2, 3], [0, 4, 5, 6]]), ("Pasch", 6, [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]),
           ("Fano, q = 2", 7, design(7, [0, 1, 3])), ("PG(2,3)", 13, design(13, [0, 1, 3, 9])),
           ("PG(2,4)", 21, design(21, [3, 6, 7, 12, 14]))]

def b1b0(n, sets):
    x = np.arange(1 << n, dtype=np.int64); b1 = np.zeros(1 << n, dtype=np.int64); b0 = np.zeros(1 << n, dtype=np.int64)
    pc = lambda v: sum((v >> i) & 1 for i in range(n))
    for S in sets:
        m = sum(1 << u for u in S); k = pc(x & m)
        b1 += np.where(k == 0, len(S) - 1, 0); b0 += np.maximum(k - 1, 0)
    return x, b1, b0, pc(x)

def cmd_systems():
    print("system | n | sets | base | W1 = max_x min(b1, b0) | W1 / base | a best x (points set to 1 in the up world) | weight bands: t -> value")
    for name, n, sets in SYSTEMS:
        base = sum(len(S) - 1 for S in sets); x, b1, b0, wt = b1b0(n, sets)
        v = np.minimum(b1, b0); i = int(v.argmax()); W1 = int(v[i])
        # weight-band strategy with t NOT gates: 2^t bands of weights; a subcube inside the band [lo, hi] has |Q| >= lo and
        # n - |R| <= hi; its base is at most the largest of min over ... computed exactly as max over pairs Q <= Y, |Q| >= lo, |Y| <= hi
        bands = {}
        if n <= 7:
            pts = range(1 << n); pcx = [bin(p).count('1') for p in pts]
            def baseQY(Q, Y): return sum(max(len([u for u in S if Y >> u & 1]) - 1, 0) for S in sets if not any(Q >> u & 1 for u in S))
            for t in range(1, 4):
                B = 1 << t; cuts = [round(j * (n + 1) / B) for j in range(B + 1)]; best = 0
                for j in range(B):
                    lo, hi = cuts[j], cuts[j + 1] - 1
                    if hi < lo: continue
                    for Q in pts:
                        if pcx[Q] != lo: continue        # smallest Q in the band is best
                        rest = [u for u in range(n) if not Q >> u & 1]
                        for F in itertools.combinations(rest, min(hi - lo, len(rest))):
                            best = max(best, baseQY(Q, Q | sum(1 << u for u in F)))
                bands[t] = best
        print(f"  {name} | {n} | {len(sets)} | {base} | {W1} | {W1 / base:.2f} | {[u for u in range(n) if i >> u & 1]} | {bands if bands else 'not computed (n > 7)'}")

def cmd_circuits():
    print("file | n | NOT gates | AND/OR gates | base | worldbound | live NOT patterns | AND/OR gates >= worldbound")
    bad = 0; tot = 0
    files = sorted(glob.glob('one-not/data/witnesses/*.json') + glob.glob('one-not/data/witnesses/nonlocal/*.json') + glob.glob('one-not/data/beyond_one_not/essential_*.json'))
    for p in files:
        try: d = json.load(open(p))
        except Exception: continue
        if not isinstance(d, dict) or 'gates' not in d or d['n'] > 8: continue
        c = {"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']}
        if not correct(c) or nots(c) < 1: continue
        n = c['n']; w = tables(n, c['gates']); nk = [n + k for k, g in enumerate(c['gates']) if g[0] == 'not']
        pat = [sum((w[k] >> x & 1) << i for i, k in enumerate(nk)) for x in range(1 << n)]
        best = 0; full = (1 << n) - 1
        for Q in range(1 << n):
            Y = full                                      # enumerate Y >= Q (Y = complement of R)
            sub = full ^ Q; F = sub
            while True:
                Y = Q | F
                # all points between Q and Y have the same NOT pattern?
                ok = True; G = F; pq = pat[Q]
                while True:
                    if pat[Q | G] != pq: ok = False; break
                    if G == 0: break
                    G = (G - 1) & F
                if ok:
                    b = sum(max(sum(1 for u in S if Y >> u & 1) - 1, 0) for S in c['sets'] if not any(Q >> u & 1 for u in S))
                    best = max(best, b)
                if F == 0: break
                F = (F - 1) & sub
        binary = len(c['gates']) - nots(c); base = sum(len(S) - 1 for S in c['sets']); tot += 1; bad += binary < best
        print(f"  {os.path.basename(p)} | {n} | {nots(c)} | {binary} | {base} | {best} | {len(set(pat))} | {binary >= best}")
    print(f"worldbound | {tot} correct circuits with at least one NOT gate and n <= 8 | failures of AND/OR gates >= worldbound: {bad}")

if __name__ == "__main__":
    {"systems": cmd_systems, "circuits": cmd_circuits}[sys.argv[1]]()
