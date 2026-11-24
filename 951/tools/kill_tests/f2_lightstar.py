# research (coord 12:49): LIGHT-STAR test for the F2 step x_v := 1 in LIGHT instances (research-F2-light.md §4).
# F2(Q): OR gates g with a REAL witness: alive w (S_w ∩ Q = ∅), Z ⊇ Q, Z ∩ S_w = ∅, a ≠ b ∈ S_w, real g(Z) = 0,
#        real g(Z + e_a) = real g(Z + e_b) = 1.   gain(v) = |F2(Q) \ F2(Q + v)|, cost(v) = Σ_{alive w ∋ v} d_w.
# LIGHT: h not constant on the cube {Z ⊇ Q} and h(Q + e_u) = 0 for every alive point u.
# LIGHT-STAR(v): |(∪_{alive w ∋ v} M_Q(w)  ∪  K0(v)) \ F2(Q + v)| >= cost(v),  M_Q(w) = Lemma-M merge run of the real tables
#        at zero point Q with atoms Q + e_u (real = C_1 there in a light instance), K0(v) = {g ∈ F2(Q): C_0(g)(Q + e_v) = 1}.
#        LIGHT-STAR(v) implies gain(v) >= cost(v).  Tested: for SOME v, and for v of least h-influence.
# Run from the repository root:  python3 951/tools/kill_tests/f2_lightstar.py <ROOT> [NMAX]
import sys, os, itertools, collections, functools
ROOT = sys.argv[1] if len(sys.argv) > 1 else '951'; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 9
sys.argv = ['x', ROOT, str(NMAX)]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st = collections.Counter(); bad = collections.defaultdict(list)
for name, n, S, G, outs in circuits():
    if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); P_ = 1 << n; FULL = (1 << P_) - 1
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    st['circuits'] += 1
    h = Wr[[g for g in G if g[0] == 'not'][0][1]]; X = Wr[:n]
    ors = [n + k for k, g in enumerate(G) if g[0] == 'or']
    wit = {g: [] for g in ors}   # (set index, mask of zero points Z with a real witness for some pair of that set)
    for g in ors:
        for wi, R in enumerate(S):
            av = FULL
            for u in R: av &= FULL ^ X[u]
            M = 0
            for a, b in itertools.combinations(R, 2):
                M |= (FULL ^ Wr[g]) & (Wr[g] >> (1 << a)) & (Wr[g] >> (1 << b)) & av
            if M: wit[g].append((wi, M))
    def cube(Q):
        m = FULL
        for v in range(n):
            if Q >> v & 1: m &= X[v]
        return m
    def F2(Q):
        cb = cube(Q); return {g for g in ors if any(not any(Q >> u & 1 for u in S[wi]) and M & cb for wi, M in wit[g])}
    for Q in range(P_):
        A = [wi for wi, R in enumerate(S) if not any(Q >> u & 1 for u in R)]
        if not A: continue
        P = sorted({u for wi in A for u in S[wi]}); cb = cube(Q); hh = h & cb
        if hh in (0, cb) or any((h >> (Q | 1 << u)) & 1 for u in P): continue
        st['light instances'] += 1
        F = F2(Q); good = {}; star = {}
        for v in P:
            Fv = F2(Q | 1 << v); cost = sum(len(S[wi]) - 1 for wi in A if v in S[wi])
            bottom = set().union(*[merges(Wr, n, G, S[wi], Q, {u: Q | 1 << u for u in S[wi]}) for wi in A if v in S[wi]])
            k0 = {g for g in F if (W0[g] >> (Q | 1 << v)) & 1}
            if not bottom <= F: st['!! bottom merge not in F2(Q) (contradicts B)'] += 1
            good[v] = len(F - Fv) >= cost; star[v] = len((bottom | k0) - Fv) >= cost
        infl = {v: bin(((h >> (1 << v)) ^ h) & cb & (FULL ^ X[v])).count('1') for v in P}
        vmin = min(P, key=lambda v: (infl[v], v))
        st['F2 step good at SOME v'] += any(good.values()); st['F2 step good at EVERY v'] += all(good.values())
        st['LIGHT-STAR at SOME v'] += any(star.values()); st['LIGHT-STAR at least-influence v'] += star[vmin]
        st['points'] += len(P); st['points with LIGHT-STAR'] += sum(star.values()); st['points with gain >= cost'] += sum(good.values())
        if not any(star.values()) and len(bad['LIGHT-STAR fails at every v']) < 6: bad['LIGHT-STAR fails at every v'].append((name, S, bin(Q), {v: (good[v]) for v in P}))
        if not any(good.values()) and len(bad['F2 step fails at every v']) < 6: bad['F2 step fails at every v'].append((name, S, bin(Q)))
for k, v in st.items(): print('%-50s %d' % (k, v))
for k, v in bad.items(): print('FAIL', k, len(v), v)
