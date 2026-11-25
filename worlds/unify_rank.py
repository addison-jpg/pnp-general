"""UNIFY_ALL part 1 (join A) and part 3 (rhyme D), tested on the stored circuits.

For a stored circuit (one-not/data/witnesses/*.json) take the PHC@0 instance of U1 section 2.3 at the single point 0:
payers E = wire classes (function up to complement) whose flip set at 0 meets some set S_w in >= 2 points; the
hyperedge of payer g in set w is D_w(g) = {u in S_w : g(e_u) != g(0)}.
  f(J)  = sum_w (|S_w| - c_w(J))      the potential of F1's Lemma D (c_w = components of S_w under the payers of J)
  T(A)  = min_{B subset A} f(B) + |A - B|     the unit truncation (Unify.lean::trunc with c = 1)
Checked for every subset (2^|E| of them, |E| <= CAP):
  lip     max_{J, e} f(J + e) - f(J): the largest number of sets one gate merges for at once (f is lip-Lipschitz)
  phc     T(E) == f(E)                (Unify.lean::trunc_eq_iff: this IS the deletion form of PHC)
  submod  T(A) + T(B) >= T(A | B) + T(A & B) for all A, B that differ from A & B by one payer each (enough)
  mmi_f, mmi_T   triples of single payers a, b, c with r(ab) + r(ac) + r(bc) < r(a) + r(b) + r(c) + r(abc):
                 violations of monogamy of mutual information, the inequality that min-cuts satisfy
                 (lean/PEqualNP/Philosophy/BeauvoirQG.lean::rt_mmi)
Run from the repository root:  python3 -I worlds/unify_rank.py one-not/data/witnesses/*.json one-not/data/witnesses/nonlocal/general*.json
Last line: {"states": subsets examined, "seconds": s}; exit 0 iff phc and submod hold on every instance.
"""
import json, sys, time, itertools
sys.path.insert(0, 'one-not/research/open')
CAP = 20

def comps(pts, edges):
    lab = {c: c for c in pts}
    def fd(c):
        while lab[c] != c: lab[c] = lab[lab[c]]; c = lab[c]
        return c
    k = len(pts)
    for e in edges:
        e = list(e); r = fd(e[0])
        for x in e[1:]:
            s = fd(x)
            if s != r: lab[s] = r; k -= 1
    return k

def instance(f):
    from B5_flip_hall import tables, correct
    c = json.load(open(f)); n = c['n']; S = [list(R) for R in c['sets']]
    w, M = tables(n, c['gates']); assert correct(c, w)
    cls = {}
    for t in w: cls.setdefault(min(t, M ^ t), t)
    hyp = {}
    for g, t in cls.items():
        hs = [frozenset(u for u in R if (t >> (1 << u) & 1) != (t & 1)) for R in S]
        if any(len(h) >= 2 for h in hs): hyp[g] = hs
    return n, sum(g[0] == 'not' for g in c['gates']), S, hyp

def study(f):
    n, nots, S, hyp = instance(f)
    E = sorted(hyp); m = len(E)
    if m > CAP: return dict(file=f.split('/')[-1], payers=m, skipped='over cap'), 0
    N = 1 << m
    F = [0] * N
    for J in range(N):
        F[J] = sum(len(R) - comps(R, [hyp[E[k]][i] for k in range(m) if J >> k & 1 and len(hyp[E[k]][i]) >= 2])
                   for i, R in enumerate(S))
    T = [0] * N
    for A in range(1, N):
        best = F[A]; B = A
        while B:
            low = B & -B; B ^= low
            if T[A ^ low] + 1 < best: best = T[A ^ low] + 1
        T[A] = best
    lip = max((F[J | 1 << k] - F[J] for J in range(N) for k in range(m) if not J >> k & 1), default=0)
    sub = 0
    for A in range(N):
        for a in range(m):
            if A >> a & 1: continue
            for b in range(a + 1, m):
                if A >> b & 1: continue
                if T[A | 1 << a] + T[A | 1 << b] < T[A | 1 << a | 1 << b] + T[A]: sub += 1
    def mmi(r):
        v = 0
        for a, b, c in itertools.combinations(range(m), 3):
            x, y, z = 1 << a, 1 << b, 1 << c
            if r[x | y] + r[x | z] + r[y | z] < r[x] + r[y] + r[z] + r[x | y | z]: v += 1
        return v
    need = sum(len(R) - 1 for R in S)
    return dict(file=f.split('/')[-1], n=n, nots=nots, sets=len(S), payers=m, need=need, fE=F[N - 1], TE=T[N - 1],
                lip=lip, phc=T[N - 1] == F[N - 1] == need, submod_fail=sub, mmi_f=mmi(F), mmi_T=mmi(T),
                triples=m * (m - 1) * (m - 2) // 6), N

if __name__ == '__main__':
    t0 = time.time(); ok = True; states = 0
    for f in sys.argv[1:]:
        r, N = study(f); states += N; print(json.dumps(r))
        if 'phc' in r and (not r['phc'] or r['submod_fail']): ok = False
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2)}))
    sys.exit(0 if ok else 1)
