"""The U-GAME (fable-global-price.md, Theorem G): exact function-level reach of Theorem U (Lean disjoint_gp /
runMT_disjoint_of_le).  Input: the lifted output functions O_w on {0,1}^(n+1) (monotone).  A system for w is a
maximal zero point zeta of O_w and |S_w| minimal one-points (atoms) of O_w, pairwise disjoint outside zeta.
Certificate w -> w': at most one atom of w is not <= zeta_w'.  WON iff systems exist with a certificate for
every pair.  (Normal form: maximal zeros and minimal atoms lose nothing, Lemma N of the note.)
solve(N, S, O) returns {w: (zeta, atoms)} or None.   O[w] = list of 0/1 over the 2^N lifted points.
"""
import itertools

def maximal_zeros(O, N):
    return [x for x in range(1 << N) if not O[x] and all(x >> v & 1 or O[x | 1 << v] for v in range(N))]

def minimal_ones(O, N):
    return [x for x in range(1 << N) if O[x] and not any(x >> v & 1 and O[x & ~(1 << v)] for v in range(N))]

def solve(N, S, O, cap=20000):
    m = len(S)
    Z = [maximal_zeros(O[w], N) for w in range(m)]
    A = [minimal_ones(O[w], N) for w in range(m)]
    opts = []
    for w in range(m):
        k = len(S[w]); o = {}
        for zi, z in enumerate(Z[w]):
            cnt = 0
            def rec(start, chosen, used):
                nonlocal cnt
                if cnt > cap: return
                if len(chosen) == k:
                    cnt += 1
                    sig = tuple(tuple(sum(1 for a in chosen if a & ~z2) <= 1 for z2 in Z[v]) if v != w else () for v in range(m))
                    key = (zi, sig)
                    if key not in o: o[key] = (z, tuple(chosen))
                    return
                for i in range(start, len(A[w])):
                    a = A[w][i]
                    if (a & ~z) & used: continue
                    chosen.append(a); rec(i + 1, chosen, used | (a & ~z)); chosen.pop()
            rec(0, [], 0)
        # drop dominated signatures (same zero, pointwise weaker certificates)
        keys = list(o)
        keep = [k1 for k1 in keys if not any(k2 != k1 and k2[0] == k1[0] and all(all(y or not x for x, y in zip(s1, s2))
                for s1, s2 in zip(k1[1], k2[1])) and k2[1] != k1[1] for k2 in keys)]
        opts.append([(k1[0], k1[1], o[k1]) for k1 in keep])
        if not opts[-1]: return None
    order = sorted(range(m), key=lambda w: len(opts[w])); ch = {}
    def ok(w, a, v, b):          # certificate between option a of w and option b of v
        return a[1][v][b[0]] or b[1][w][a[0]]
    def go(i):
        if i == m: return True
        w = order[i]
        for a in opts[w]:
            if all(ok(w, a, v, ch[v]) for v in order[:i]):
                ch[w] = a
                if go(i + 1): return True
                del ch[w]
        return False
    return {w: ch[w][2] for w in ch} if go(0) else None

def dd_outputs(n, S, h):
    """DD-normal lifted outputs: O_w(x, 0) = s_w & h, O_w(x, 1) = s_w | h."""
    P = 1 << n; O = []
    for R in S:
        Rm = sum(1 << u for u in R)
        O.append([1 if (x & Rm and h[x]) else 0 for x in range(P)] + [1 if (x & Rm or h[x]) else 0 for x in range(P)])
    return O
