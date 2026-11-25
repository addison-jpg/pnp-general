# research: circuit-free description of the type-A menus and the three open collision types (coord task, 11 UTC).
# Run from the repository root:  python3 research/one-not/tools/kill_tests/typeA.py one-not [NMAX]
# (a) I1 zero points of set w (maximal in D = {h = 0} among points avoiding S_w) == top_w \ T for T a MINIMAL TRANSVERSAL
#     of Min_w = {minterms m of h with m ∩ S_w = ∅}; checked exactly.
# (b) I0 atoms m_u ∪ {u}, m_u a minterm with m_u ∩ S_w ⊆ {u} (definition; already circuit-free).
# (c) Collisions (merge sets intersect) between classes of different sets, classified by the h/set conditions that the
#     Lean disjointness lemmas leave open:  (i) I1 vs I1 with |S_w \ Z'| >= 2;  (ii) I0 vs I0 with some m_u meeting S_w';
#     (iii) I1(w) vs I0(w') .  A collision in a class that a lemma says is disjoint would be a KILL.
import sys, itertools, collections, functools, os
ROOT = sys.argv[1] if len(sys.argv) > 1 else 'research/one-not'; NM = sys.argv[2] if len(sys.argv) > 2 else '10'
sys.argv = ['x', ROOT, NM]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'canon.py')).read()
exec(src[:src.index("st=collections.Counter()")])
pc = lambda x: bin(x).count('1')
st = collections.Counter(); ex = collections.defaultdict(list)
for name, n, S, G, outs in circuits():
    if n > int(NM) or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); W1 = tables(n, G, 1); P_ = 1 << n
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    st['circuits'] += 1
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    Rm = [sum(1 << u for u in R) for R in S]; top = [(P_ - 1) & ~r for r in Rm]; d = [len(R) - 1 for R in S]
    I1 = []; I0 = []
    for w, R in enumerate(S):
        rest = [v for v in range(n) if v not in R]
        zs = [sum(1 << v for v in zz) for r in range(len(rest) + 1) for zz in itertools.combinations(rest, r)]
        Zdef = {z for z in zs if not hb(z) and all(hb(z | 1 << v) for v in rest if not z >> v & 1)}
        Minw = [m for m in mint if not m & Rm[w]]
        trans = [t for t in zs if all(m & t for m in Minw)]
        mintr = [t for t in trans if not any(t2 != t and (t2 & t) == t2 for t2 in trans)]
        Zchar = {top[w] & ~t for t in mintr}
        st['(a) sets'] += 1; st['(a) I1 points == top \\ minimal transversal of Min_w'] += (Zdef == Zchar)
        if Zdef != Zchar: ex['(a) MISMATCH'].append((name, w))
        I1.append([(z, merges(W1, n, G, R, z, {u: 1 << u for u in R})) for z in sorted(Zdef)])
        if hb(top[w]):
            per = [[m for m in mint if (m & Rm[w]) & ~(1 << u) == 0] for u in R]
            i0 = []
            for ms in itertools.islice(itertools.product(*per), 2000):
                i0.append((ms, merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)})))
            I0.append(i0)
        else:
            I0.append([])
    for w, v in itertools.permutations(range(len(S)), 2):
        Sw, Sv = Rm[w], Rm[v]
        if w < v:   # (i) I1(w) vs I1(v), symmetric
            for z, M in I1[w]:
                for z2, M2 in I1[v]:
                    k = max(pc(Sw & ~z2), pc(Sv & ~z)); col = bool(M & M2)
                    key = '(i) I1-I1 max(|S_w\\Z\'|,|S_v\\Z|)=' + ('<=1' if k <= 1 else '>=2')
                    st[key + ' pairs'] += 1; st[key + ' COLLIDE'] += col
                    if col and k <= 1: ex['KILL (i) collision with k<=1'].append((name, w, v, z, z2))
                    if col and k >= 2 and len(ex['(i) example']) < 3: ex['(i) example'].append((name, S[w], S[v], bin(z), bin(z2)))
            for ms, M in I0[w]:   # (ii) I0 vs I0, symmetric
                for ms2, M2 in I0[v]:
                    meet = any(m & Sv for m in ms) or any(m & Sw for m in ms2); col = bool(M & M2)
                    key = '(ii) I0-I0 some m meets the other set=' + str(meet)
                    st[key + ' pairs'] += 1; st[key + ' COLLIDE'] += col
                    if col and not meet: ex['KILL (ii) collision with all m avoiding'].append((name, w, v))
                    if col and meet and len(ex['(ii) example']) < 3: ex['(ii) example'].append((name, S[w], S[v], [bin(m) for m in ms], [bin(m) for m in ms2]))
        for z, M in I1[w]:        # (iii) I1(w) vs I0(v), ordered
            for ms2, M2 in I0[v]:
                attop = (z == top[w]); avoid = not any(m & Sw for m in ms2); col = bool(M & M2)
                key = '(iii) I1(w)-I0(v) Z=top_w:%s all m_v avoid S_w:%s' % (attop, avoid)
                st[key + ' pairs'] += 1; st[key + ' COLLIDE'] += col
                if col and attop and avoid: ex['KILL (iii) collision at top with avoiding minterms (contradicts CanonOneNot D)'].append((name, w, v))
                if col and not attop and len(ex['(iii) example']) < 3: ex['(iii) example'].append((name, S[w], S[v], bin(z), [bin(m) for m in ms2]))
for k, v in sorted(st.items()): print('%-78s %d' % (k, v))
for k, v in ex.items(): print(k, len(v), v[:3])
