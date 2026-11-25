"""MergeSDR on the instances: classes V_w = distinct merge sets M_z(w); conflict graph H: members of different classes
that share a gate. Checks: exact SDR existence (backtracking), Haxell's 2Δ condition (min |V_w| >= 2 Δ(H)),
the Aharoni-Haxell matching condition ν(∪_{w∈I} V_w) > r(|I|-1) (r = max d_w), and universal merges U(w)."""
import sys, json, itertools
from mzmatroid import merge_set
def sdr(classes):
    order = sorted(range(len(classes)), key=lambda i: len(classes[i]))
    used = set(); pick = {}
    def bt(k):
        if k == len(order): return True
        i = order[k]
        for M in classes[i]:
            if not (M & used):
                used.update(M); pick[i] = M
                if bt(k + 1): return True
                used.difference_update(M); del pick[i]
        return False
    return bt(0), dict(pick)
def nu(sets):  # max number of pairwise disjoint sets (brute force with pruning)
    sets = list(set(sets)); best = [0]
    def rec(i, used, c):
        if c + (len(sets) - i) <= best[0]: return
        if i == len(sets): best[0] = max(best[0], c); return
        if not (sets[i] & used): rec(i + 1, used | sets[i], c + 1)
        rec(i + 1, used, c)
    rec(0, frozenset(), 0); return best[0]
rows = []
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    V = []
    for S in sets:
        Sm = sum(1 << u for u in S)
        V.append(sorted({merge_set(n, gates, S, z) for z in range(1 << n) if not z & Sm}, key=sorted))
    U = [frozenset.intersection(*Vw) for Vw in V]
    ok, pick = sdr(V)
    deg = {}
    for (a, Va), (b, Vb) in itertools.combinations(enumerate(V), 2):
        for M in Va:
            for N in Vb:
                if M & N: deg[(a, M)] = deg.get((a, M), 0) + 1; deg[(b, N)] = deg.get((b, N), 0) + 1
    Delta = max(deg.values(), default=0); mincls = min(len(x) for x in V)
    r = max(len(S) - 1 for S in sets)
    ah_fail = None
    for k in range(2, len(V) + 1):
        for I in itertools.combinations(range(len(V)), k):
            if nu([M for i in I for M in V[i]]) <= r * (k - 1): ah_fail = (I, r * (k - 1)); break
        if ah_fail: break
    print(f.split('/')[-1], f"| SDR {'YES' if ok else 'NO'} | class sizes {[len(x) for x in V]} | Δ={Delta} | Haxell 2Δ <= min class: {mincls >= 2*Delta}",
          f"| |U(w)| {[len(u) for u in U]} U disjoint {all(not (a & b) for a, b in itertools.combinations(U, 2))}",
          f"| Aharoni-Haxell ν-condition fails at I={ah_fail[0] if ah_fail else None}")
