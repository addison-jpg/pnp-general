# Second, independent check of a counterexample to Conjecture C3_k: truth tables as big integers, straight from the definition
# of realWitness (no shared code with c3_dnf.py or f2lib.py).  Checks correctness of the circuit on all 2^n inputs, then
# slack(Q + D) - slack(Q) for every set D of at most cap unfixed points.  Serves README items L5, C3.
# Run: python3 -I research/one-not/tools/kill_tests/c3_tab.py FILE.json [cap] [Q as comma list]     (n = 24: about 1 GB, a few minutes)
import sys, json, itertools
d = json.load(open(sys.argv[1])); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 2
Q0 = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 and sys.argv[3] else []
n = d['n']; S = d['sets']; G = d['gates']; outs = d['outs']; P = 1 << n; FULL = (1 << P) - 1
assert sum(g[0] == 'not' for g in G) <= 1 and all(len(R) >= 2 for R in S) and all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(S, 2))
X = []
for v in range(n):                      # table of x_v: blocks of 2^v zeros then 2^v ones, by doubling
    t = ((1 << (1 << v)) - 1) << (1 << v); w = 1 << (v + 1)
    while w < P: t |= t << w; w *= 2
    X.append(t)
W = list(X)
for g in G: W.append(FULL ^ W[g[1]] if g[0] == 'not' else (W[g[1]] & W[g[2]] if g[0] == 'and' else W[g[1]] | W[g[2]]))
for o, R in zip(outs, S):
    t = 0
    for u in R: t |= X[u]
    assert W[o] == t, 'circuit incorrect'
wm = []                                 # (gate, set index, table of the zero points Z of the set at which the gate has a witness)
for k, g in enumerate(G):
    if g[0] != 'or': continue
    t = W[n + k]; nt = FULL ^ t
    for wi, R in enumerate(S):
        av = nt
        for u in R: av &= FULL ^ X[u]
        if not av: continue
        one = two = 0
        for u in R:
            a = av & (t >> (1 << u)); two |= one & a; one |= a
        if two: wm.append((n + k, wi, two))
def slack(Q):
    cb = FULL
    for v in Q: cb &= X[v]
    alive = [wi for wi, R in enumerate(S) if not set(R) & set(Q)]
    al = set(alive); F = {i for i, wi, M in wm if wi in al and M & cb}
    b = sum(len(S[wi]) - 1 for wi in alive)
    return len(F) - b, b
s0, b0 = slack(Q0); free = [v for v in range(n) if v not in Q0]; best = {}
for k in range(1, cap + 1):
    for D in itertools.combinations(free, k):
        s, b = slack(Q0 + list(D))
        if b < b0 and (k not in best or s - s0 < best[k][0]): best[k] = (s - s0, list(D))
print(d.get('name'), 'n', n, 'gates', len(G), 'correct on all', P, 'inputs; Q', Q0, 'base', b0, 'slack', s0)
print('least slack(Q+D) - slack(Q) over D with |D| = j and smaller base:', {k: v[0] for k, v in best.items()}, 'at', {k: v[1] for k, v in best.items()})
print('C3_%d at this cube:' % cap, 'FAILS' if all(v[0] > 0 for v in best.values()) else 'holds')
