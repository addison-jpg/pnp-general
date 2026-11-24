# research (type-A increment, 12:3x): MU by PEELING SETS on the same circuit (no minimality, no heredity: dropping a set keeps
# every other set's menu).  U(F) = union of the E2 menus (ext.py: I1 at maximal Z, I0 at top_w) of the sets in F.
#  PI(F):  some w ∈ F has  |U(w) \ U(F - w)| >= d_w   (w brings d_w gates no other set of F has).
#  PEEL:   an elimination order w_m, w_{m-1}, ... with PI at every step (then MU(F) holds by induction on |F|).
# Also: is PI ever met by a type-A set / a free set only, and does K_1(v) of a free v stay private (K_1(v) ∩ U(F - v) = ∅)?
# Run from the repository root:  python3 one-not/tools/kill_tests/peel_mu.py <ROOT> [NMAX]
import sys, os, itertools, collections, functools
ROOT = sys.argv[1] if len(sys.argv) > 1 else 'one-not'; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
sys.argv = ['x', ROOT, str(NMAX)]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st = collections.Counter(); fails = collections.defaultdict(list)
for name, n, S, G, outs in circuits():
    if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); W1 = tables(n, G, 1); P_ = 1 << n
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    st['circuits'] += 1
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    top = [(P_ - 1) & ~sum(1 << u for u in R) for R in S]; d = [len(R) - 1 for R in S]
    Uw = []
    for w, R in enumerate(S):
        Rm = sum(1 << u for u in R); rest = [v for v in range(n) if v not in R]; cl = set()
        for r in range(len(rest) + 1):
            for zz in itertools.combinations(rest, r):
                z = sum(1 << v for v in zz)
                if not hb(z) and all(hb(z | 1 << v) for v in rest if not z >> v & 1): cl.add(merges(W1, n, G, R, z, {u: 1 << u for u in R}))
        if hb(top[w]):
            per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 3000): cl.add(merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)}))
        Uw.append(frozenset().union(*cl))
    def U(F): return frozenset().union(*[Uw[w] for w in F]) if F else frozenset()
    def pi(F): return [w for w in F if len(Uw[w] - U([v for v in F if v != w])) >= d[w]]
    full = list(range(len(S))); p = pi(full)
    lastout = max(full, key=lambda w: outs[w]); st['rule: latest output satisfies PI'] += lastout in p
    if lastout not in p and len(fails['latest output']) < 6: fails['latest output'].append((name, S, len(G), lastout))
    Aset = [w for w in full if hb(top[w])]
    if Aset:
        la = max(Aset, key=lambda w: outs[w]); st['rule: latest type-A output satisfies PI (circuits with type A)'] += la in p
        st['circuits with type A'] += 1
        st['every type-A set satisfies PI'] += all(w in p for w in Aset)
    st['sets'] += len(full); st['sets satisfying PI (full family)'] += len(p)
    order = sorted(full, key=lambda w: outs[w]); okc = True
    for k in range(1, len(order)):
        w = order[k]
        if len(Uw[w] - U(order[:k])) < d[w]: okc = False
    st['OUTPUT-ORDER peel: every set has d_w class gates outside the classes of EARLIER-output sets'] += okc
    if not okc and len(fails['OUTPUT-ORDER']) < 6: fails['OUTPUT-ORDER'].append((name, S, len(G)))
    st['class gates (E2 union per set)'] += sum(len(Uw[w]) for w in full); st['class gates AFTER own output wire'] += sum(1 for w in full for g in Uw[w] if g > outs[w])
    st['PI on the full family'] += bool(p); st['PI met by a type-A set'] += any(hb(top[w]) for w in p)
    st['PI met only by free sets'] += bool(p) and not any(hb(top[w]) for w in p)
    for v in full:
        if not hb(top[v]):
            Kv = merges(W1, n, G, S[v], top[v], {u: 1 << u for u in S[v]}); st['free sets'] += 1
            st['free K_1(v) private (∩ U(S - v) = ∅)'] += not (Kv & U([x for x in full if x != v]))
    @functools.lru_cache(None)
    def peel(F):
        if len(F) <= 1: return True
        return any(peel(tuple(x for x in F if x != w)) for w in pi(list(F)))
    ok = peel(tuple(full)); st['PEEL order exists'] += ok
    if not p and len(fails['PI full']) < 6: fails['PI full'].append((name, S, len(G)))
    if not ok and len(fails['PEEL']) < 6: fails['PEEL'].append((name, S, len(G)))
for k, v in st.items(): print('%-50s %d' % (k, v))
for k, v in fails.items(): print('FAIL', k, len(v), v)
