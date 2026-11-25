"""F2 family test (coord 12:43, board integrator's family-table.md). Discovery only; own code.
F2(Q) = OR gates g with: an alive set w (S_w ∩ Q = ∅, |S_w| >= 2), a point Z ⊇ Q with Z ∩ S_w = ∅, u != u' in S_w,
REAL g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1 (real circuit, NOT as is).
(1) MU:   sum_{alive w} d_w <= |F2(Q)|                     (d_w = |S_w| - 1)
(2) STEP: some v with |F2(Q) \\ F2(Q ∪ {v})| >= sum_{alive w ∋ v} d_w  (v ranges over variables in alive sets, v ∉ Q)
Q = ∅ always, plus NQ random Q of size 1-2 (fixed seed). Precompute B[g][w] = bitset of Z (Z ∩ S_w = ∅) admitting a
pair u != u'; then F2(Q) = {g : ∃ alive w, B[g][w] & UP(Q) != 0}, UP(Q) = bitset of points ⊇ Q.
Usage: python3 -I f2_test.py files... [--nq 2] [--out r.json]
"""
import json, random, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P


def prep(c):
    n, Pn = c.n, 1 << c.n
    T = c.table()
    full = (1 << Pn) - 1
    bit = [sum(1 << x for x in range(Pn) if (x >> v) & 1) for v in range(n)]
    sets = [S for S in c.sets]
    B = {}
    for k, g in enumerate(c.gates):
        if g[0] != "or":
            continue
        i = n + k
        Tg = T[i]
        zero = full ^ Tg
        A = [zero & (Tg >> (1 << u)) & (full ^ bit[u]) for u in range(n)]  # Z: g(Z)=0, g(Z+e_u)=1, bit u of Z = 0
        for w, S in enumerate(sets):
            if len(S) < 2:
                continue
            avoid = full
            for u in S:
                avoid &= full ^ bit[u]
            acc = 0
            for a in range(len(S)):
                for b in range(a + 1, len(S)):
                    acc |= A[S[a]] & A[S[b]]
            acc &= avoid
            if acc:
                B[(i, w)] = acc
    return T, bit, full, B


def up(Q, bit, full):
    m = full
    for v in Q:
        m &= bit[v]
    return m


def F2(c, B, Q, bit, full):
    U = up(Q, bit, full)
    alive = {w for w, S in enumerate(c.sets) if len(S) >= 2 and not (set(S) & Q)}
    return {i for (i, w), b in B.items() if w in alive and b & U}, alive


if __name__ == "__main__":
    args = sys.argv[1:]
    NQ = int(args[args.index("--nq") + 1]) if "--nq" in args else 2
    out = args[args.index("--out") + 1] if "--out" in args else None
    files = [a for i, a in enumerate(args) if not a.startswith("--") and (i == 0 or args[i - 1] not in ("--nq", "--out"))]
    rng = random.Random(951)
    st = Counter(); fails_mu = []; fails_step = []; tight = Counter()
    for p in files:
        for k, d in P.items(p):
            if not (isinstance(d, dict) and "gates" in d and "sets" in d):
                continue
            c = P.Circ(d)
            if not c.ok1 or c.n > 16:
                continue
            T, bit, full, B = prep(c)
            if not c.correct(T):
                continue
            st["circuits"] += 1
            Qs = [set()]
            for _ in range(NQ):
                Qs.append(set(rng.sample(range(c.n), rng.choice([1, 2]))))
            for Q in Qs:
                F, alive = F2(c, B, Q, bit, full)
                need = sum(len(c.sets[w]) - 1 for w in alive)
                if not alive:
                    continue
                st["tests"] += 1
                if need > len(F):
                    st["MU_fail"] += 1
                    fails_mu.append((c.n, len(c.gates), f"{p}#{k}", sorted(Q), need, len(F)))
                elif need == len(F):
                    tight["MU_tight"] += 1
                vs = sorted({v for w in alive for v in c.sets[w]} - Q)
                ok = False; best = None
                for v in vs:
                    F_v, _ = F2(c, B, Q | {v}, bit, full)
                    gain = len(F - F_v)
                    cost = sum(len(c.sets[w]) - 1 for w in alive if v in c.sets[w])
                    if best is None or gain - cost > best[0]:
                        best = (gain - cost, v, gain, cost)
                    if gain >= cost:
                        ok = True
                        break
                if not ok:
                    st["STEP_fail"] += 1
                    fails_step.append((c.n, len(c.gates), f"{p}#{k}", sorted(Q), best))
    r = {**st, **tight, "MU_fail_smallest": sorted(fails_mu)[:10], "STEP_fail_smallest": sorted(fails_step)[:10]}
    s = json.dumps(r, indent=1)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
