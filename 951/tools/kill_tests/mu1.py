# research (type-A increment, 12:2x): WORLD-1-ONLY counting.  For every set w and EVERY Z with h(Z) = 0, Z ∩ S_w = ∅ (Lean
# PureValid .one Z), M1(w, Z) = merge run of the C_1 tables (NOT := 1) at zero point Z with atoms e_u.
#   PROVED (W1 argument): every M1(w, Z) is disjoint from K_1(v) = M1(v, top_v) for every free v ≠ w (h(top_v) = 0).
#   So MU follows from  INC1_A:  |∪_{w type A, Z} M1(w, Z)| >= Σ_{type A} d_w   (W1 gives Σ_free d_w disjoint gates).
# Checks INC1_A, MU1 = |∪_{all w, Z} M1(w, Z)| >= base, and the PROVED disjointness (as a sanity check).
# Run from the repository root:  python3 951/tools/kill_tests/mu1.py <ROOT> [NMAX]
import sys, os, itertools, collections, functools
ROOT = sys.argv[1] if len(sys.argv) > 1 else '951'; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
sys.argv = ['x', ROOT, str(NMAX)]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st = collections.Counter(); hist = collections.defaultdict(collections.Counter); fails = collections.defaultdict(list)
for name, n, S, G, outs in circuits():
    if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    Wr = tables(n, G, 'real'); W1 = tables(n, G, 1); P_ = 1 << n
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    st['circuits'] += 1
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    top = [(P_ - 1) & ~sum(1 << u for u in R) for R in S]; d = [len(R) - 1 for R in S]
    A = [w for w in range(len(S)) if hb(top[w])]; Fr = [w for w in range(len(S)) if not hb(top[w])]
    M1 = []
    for w, R in enumerate(S):
        free = top[w]; Z = free; cl = set()
        while True:
            if not hb(Z): cl.add(merges(W1, n, G, R, Z, {u: 1 << u for u in R}))
            if Z == 0: break
            Z = (Z - 1) & free
        M1.append(cl)
        if any(len(C) != d[w] for C in cl): st['GM VIOLATION'] += 1
    K = {v: merges(W1, n, G, S[v], top[v], {u: 1 << u for u in S[v]}) for v in Fr}
    st['sanity: M1(w,Z) meets K_1(v), v free != w (must be 0)'] += sum(1 for w in range(len(S)) for C in M1[w] for v in Fr if v != w and C & K[v])
    UA = frozenset().union(*[C for w in A for C in M1[w]]) if A else frozenset()
    Uall = frozenset().union(*[C for M in M1 for C in M])
    a = len(UA) - sum(d[w] for w in A); b = len(Uall) - sum(d)
    hist['INC1_A slack |∪ type-A M1| - Σ_A d'][a] += 1; hist['MU1 slack |∪ all M1| - base'][b] += 1
    if a < 0 and len(fails['INC1_A']) < 5: fails['INC1_A'].append((name, n, S, A, len(G)))
    if b < 0 and len(fails['MU1']) < 5: fails['MU1'].append((name, n, S, len(G)))
for k, v in st.items(): print('%-60s %d' % (k, v))
for k, v in hist.items(): print('%-40s' % k, dict(sorted(v.items())))
for k, v in fails.items(): print('FAIL', k, len(v), v)
