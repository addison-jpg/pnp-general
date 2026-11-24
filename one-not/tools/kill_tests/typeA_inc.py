# research (coord 12:09): TYPE-A INCREMENT for MU.  Free sets: h(top_w) = 0, class K_1(w) = I1 at top_w (pairwise disjoint, W1).
# INC: |U \ K_free| >= sum_{type A} d_w,  K_free = union of the free K_1(w).  Then MU = sum_free d_w + sum_A d_w <= |U|.
# U is bracketed:  U_E2 (ext.py E2 menus: I1 at maximal Z, I0 at top_w per atom; a SUBSET of the Lean U)  and
#                  UC   (mu_induct.py count sets: OR gates merging >= 2 atoms at a valid zero point of either world; a SUPERSET).
# Also the type-A-only form INC_A: |union of the type-A sets' E2 classes \ K_free| >= sum_A d_w (counts only type-A classes).
# Run from the repository root:  python3 one-not/tools/kill_tests/typeA_inc.py one-not [NMAX]
import sys, os, json, itertools, collections, functools
ROOT = sys.argv[1] if len(sys.argv) > 1 else 'one-not'; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
sys.argv = ['x', ROOT, str(NMAX)]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
def UC(n, G, W0, W1, hb, sets, avoid=0):
    P_ = 1 << n; ors = [n + k for k, g in enumerate(G) if g[0] == 'or']; out = set()
    for R in sets:
        Rm = sum(1 << u for u in R); free = (P_ - 1) & ~Rm & ~avoid; Z = free
        while True:
            w1 = not hb(Z); w0 = all(hb(Z | 1 << u) for u in R)
            for g in ors:
                if g in out: continue
                if w1 and not (W1[g] >> Z) & 1 and sum((W1[g] >> (Z | 1 << u)) & 1 for u in R) >= 2: out.add(g)
                elif w0 and not (W0[g] >> Z) & 1 and sum((W0[g] >> (Z | 1 << u)) & 1 for u in R) >= 2: out.add(g)
            if Z == 0: break
            Z = (Z - 1) & free
    return out
st = collections.Counter(); hist = collections.defaultdict(collections.Counter); fails = collections.defaultdict(list)
for name, n, S, G, outs in circuits():
    if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); W1 = tables(n, G, 1); P_ = 1 << n
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    st['circuits'] += 1
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    top = [(P_ - 1) & ~sum(1 << u for u in R) for R in S]; d = [len(R) - 1 for R in S]
    A = [w for w in range(len(S)) if hb(top[w])]; Fr = [w for w in range(len(S)) if not hb(top[w])]
    menus = []
    for w, R in enumerate(S):
        Rm = sum(1 << u for u in R); rest = [v for v in range(n) if v not in R]; cl = set()
        for r in range(len(rest) + 1):
            for zz in itertools.combinations(rest, r):
                z = sum(1 << v for v in zz)
                if not hb(z) and all(hb(z | 1 << v) for v in rest if not z >> v & 1): cl.add(merges(W1, n, G, R, z, {u: 1 << u for u in R}))
        if hb(top[w]):
            per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 3000):
                cl.add(merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)}))
        menus.append(cl)
    K = {w: merges(W1, n, G, S[w], top[w], {u: 1 << u for u in S[w]}) for w in Fr}
    if any(K[a] & K[b] for a, b in itertools.combinations(Fr, 2)): st['W1 VIOLATION (free classes meet)'] += 1
    Kf = frozenset().union(*K.values()) if Fr else frozenset()
    UE2 = frozenset().union(*[C for M in menus for C in M]); UCs = UC(n, G, W0, W1, hb, S)
    UCA = UC(n, G, W0, W1, hb, [S[w] for w in A]); UCF = UC(n, G, W0, W1, hb, [S[w] for w in Fr])
    Fpts = sum(1 << u for v in Fr for u in S[v]); UCN = UC(n, G, W0, W1, hb, [S[w] for w in A], Fpts)
    st['sanity: UC_N(A) ∩ K_free (P2, must be 0)'] += len(frozenset(UCN) & Kf)
    st['K_free ⊆ UC (must hold)'] += Kf <= frozenset(UCs)
    UA = frozenset().union(*[C for w in A for C in menus[w]]) if A else frozenset()
    I0A = []
    for w in A:
        R = S[w]; Rm = sum(1 << u for u in R); per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
        I0A += [merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)}) for ms in itertools.islice(itertools.product(*per), 3000)]
    U0A = frozenset().union(*I0A) if I0A else frozenset()
    c1 = {}; c0 = {}
    for w in A:
        R = S[w]; Rm = sum(1 << u for u in R); rest = [v for v in range(n) if v not in R]; c1[w] = set()
        for r in range(len(rest) + 1):
            for zz in itertools.combinations(rest, r):
                z = sum(1 << v for v in zz)
                if not hb(z) and all(hb(z | 1 << v) for v in rest if not z >> v & 1): c1[w].add(merges(W1, n, G, R, z, {u: 1 << u for u in R}))
        per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
        c0[w] = {merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)}) for ms in itertools.islice(itertools.product(*per), 3000)}
    heavyA = {w for w in A if any(hb(1 << u) for u in S[w])}
    def cnt(world1):
        cl = [C for w in A for C in (c1[w] if w in world1 else c0[w])]
        return (len(frozenset().union(*cl) - Kf) if cl else 0) - need
    need = sum(d[w] for w in A); st['circuits with a type-A set'] += bool(A)
    for lab, val in (('INC_A  (type-A E2 classes only)', len(UA - Kf) - need), ('INC0   (type-A I0 classes at top_w only, E6 counting)', len(U0A - Kf) - need), ('INC0 w/o K_free removal (|U0A| - Σ_A d)', len(U0A) - need), ('CANON-a: world 1 iff the type-A set has a heavy point', cnt(heavyA)), ('CANON-b: world 0 iff it has a heavy point', cnt(set(A) - heavyA)), ('INC    (U_E2, subset of Lean U)', len(UE2 - Kf) - need),
                     ('INC    (UC, superset of Lean U)', len(UCs - Kf) - need), ('INC_UC_A (type-A UC gates only) |UC(A) \\ K_free| - Σ_A d', len(frozenset(UCA) - Kf) - need), ('MU_UC |UC| - base', len(UCs) - sum(d)), ('INC_N: type-A UC gates at zero points avoiding all free points, |UC_N(A)| - Σ_A d', len(UCN) - need), ('free UC beyond K_free |UC(free) \\ K_free|', len(frozenset(UCF) - Kf)), ('MU     (U_E2) |U|-base', len(UE2) - sum(d))):
        hist[lab][val] += 1
        if val < 0 and len(fails[lab]) < 4: fails[lab].append((name, S, [w for w in A]))
    if A:
        # per type-A set: does SOME class avoid K_free entirely?  how many class gates fall in K_free (min over its classes)?
        for w in A:
            mk = min(len(C & Kf) for C in menus[w]); st['type-A sets'] += 1; st['type-A sets with a class avoiding K_free'] += (mk == 0)
            hist['min over classes of |C ∩ K_free| (type-A set)'][mk] += 1
for k, v in st.items(): print('%-50s %d' % (k, v))
for k, v in hist.items(): print('%-50s' % k, dict(sorted(v.items())))
for k, v in fails.items(): print('FAIL', k, len(v), v)
