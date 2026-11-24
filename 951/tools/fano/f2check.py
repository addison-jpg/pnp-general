# f2check.py (scaffold 951, 2026-11-24): exhaustive F2 test at EVERY Q ⊆ points, self-contained.
# F2(Q) = OR gates g with an alive w (S_w ∩ Q = ∅), Z ⊇ Q, Z ∩ S_w = ∅, u ≠ u' ∈ S_w: REAL g(Z)=0, g(Z+e_u)=g(Z+e_u')=1.
# MU(Q): Σ_{alive w} d_w ≤ |F2(Q)|.  STEP(Q): some alive v ∉ Q with |F2(Q) − F2(Q∪v)| ≥ Σ_{alive w ∋ v} d_w.
#   python3 f2check.py IN.jsonl          prints totals and the smallest failure (if any)
# Landed by coord (scaffold cannot push).
import sys, json

def tables(c):
    n, G = c['n'], c['gates']; R = 1 << n; full = (1 << R) - 1
    T = [sum(((r >> i) & 1) << r for r in range(R)) for i in range(n)]
    for g in G:
        a = T[g[1]]
        T.append(full & ~a if g[0] == 'not' else (a & T[g[2]] if g[0] == 'and' else a | T[g[2]]))
    return T

def f2_all(c):
    n = c['n']; R = 1 << n; full = (1 << R) - 1; T = tables(c)
    ors = [n + k for k, g in enumerate(c['gates']) if g[0] == 'or']
    bit = [sum(1 << r for r in range(R) if r >> v & 1) for v in range(n)]
    pts = sorted({v for S in c['sets'] for v in S}); sets = [set(S) for S in c['sets']]
    good = {}
    for w, S in enumerate(c['sets']):
        avoid = full
        for u in S: avoid &= ~bit[u]
        for g in ors:
            two = one = 0
            for u in S:
                x = (T[g] >> (1 << u)) & ~bit[u] & full; two |= one & x; one |= x
            m = ~T[g] & two & avoid
            if m: good[(w, g)] = m
    F = {}
    for qb in range(1 << len(pts)):
        Q = frozenset(pts[i] for i in range(len(pts)) if qb >> i & 1); qm = full
        for v in Q: qm &= bit[v]
        F[Q] = {g for (w, g), m in good.items() if not (sets[w] & Q) and m & qm}
    mu_fail, step_fail = [], []
    for Q, FQ in F.items():
        alive = [w for w in range(len(sets)) if not sets[w] & Q]
        if len(FQ) < sum(len(sets[w]) - 1 for w in alive): mu_fail.append(sorted(Q))
        av = sorted({v for w in alive for v in sets[w]} - Q)
        if av and not any(len(FQ - F[Q | {v}]) >= sum(len(sets[w]) - 1 for w in alive if v in sets[w]) for v in av):
            step_fail.append(sorted(Q))
    return mu_fail, step_fail, len(F)

if __name__ == '__main__':
    tot = nq = 0; fails = []
    for i, line in enumerate(open(sys.argv[1])):
        d = json.loads(line); c = {k: d[k] for k in ('n', 'sets', 'gates', 'outs')}
        mf, sf, q = f2_all(c); tot += 1; nq += q
        if mf or sf: fails.append((len(c['gates']), i, d.get('src'), mf[:3], sf[:3]))
    fails.sort()
    print(json.dumps({'circuits': tot, 'Q_cases': nq, 'MU_or_STEP_failing_circuits': len(fails), 'smallest': fails[:1]}))
