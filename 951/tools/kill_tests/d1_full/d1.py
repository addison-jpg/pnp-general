# D1 kill test: K_1(w;Z) ∩ K_0(v;m)=∅ for every I1 point Z of w and every I0 choice m of v with all m_u' ∩ S_w = ∅.
# Uses canon.py's tables/merges and typeA.py's I1/I0 construction verbatim.
# usage: d1.py SHARD NSHARD NMAX BUDGET_SEC root1 root2 ...
import sys, os, time, itertools, collections, functools, json, glob
SH, NS, NM, BUD = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]); roots = sys.argv[5:]
HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = ['x', roots[0], str(NM)]
src = open(os.path.join(HERE, '..', 'canon.py')).read()
exec(src[:src.index("st=collections.Counter()")])
pc = lambda x: bin(x).count('1')
seen = set(); allc = []
for r in roots:
    ROOT = r
    for c in circuits():
        key = json.dumps(c[1:])
        if key in seen: continue
        seen.add(key); allc.append((c[0], r) + c[1:])
allc.sort(key=lambda c: c[2])
st = collections.Counter(); wit = []; t0 = time.time()
st['loaded'] = len(allc)
for idx, (name, root, n, S, G, outs) in enumerate(allc):
    if idx % NS != SH: continue
    if time.time() - t0 > BUD: st['STOPPED_AT_n'] = n; st['unprocessed_after_budget'] += 1; continue
    if n > NM or sum(1 for g in G if g[0] == 'not') != 1 or len(S) < 2: continue
    try: Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); W1 = tables(n, G, 1)
    except Exception: continue
    P_ = 1 << n
    if any(Wr[o] != functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S)): continue
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)) or any(len(R) < 2 for R in S): continue
    st['circuits'] += 1; st['circuits n=%02d' % n] += 1
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    Rm = [sum(1 << u for u in R) for R in S]; top = [(P_ - 1) & ~r for r in Rm]
    I1 = []; I0 = []
    for w, R in enumerate(S):
        rest = [v for v in range(n) if v not in R]
        zs = [sum(1 << v for v in zz) for r in range(len(rest) + 1) for zz in itertools.combinations(rest, r)]
        Zdef = {z for z in zs if not hb(z) and all(hb(z | 1 << v) for v in rest if not z >> v & 1)}
        I1.append([(z, merges(W1, n, G, R, z, {u: 1 << u for u in R})) for z in sorted(Zdef)])
        i0 = []
        if hb(top[w]):
            per = [[m for m in mint if (m & Rm[w]) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 2000):
                i0.append((ms, merges(W0, n, G, R, top[w], {u: ms[i] | 1 << u for i, u in enumerate(R)})))
        I0.append(i0)
    cc = 0
    for w, v in itertools.permutations(range(len(S)), 2):
        for z, M in I1[w]:
            for ms2, M2 in I0[v]:
                if any(m & Rm[w] for m in ms2): continue
                st['tuples'] += 1; cc += 1
                if M & M2:
                    st['COLLISIONS'] += 1
                    if len(wit) < 20: wit.append(dict(circuit=name, root=root, n=n, w=w, v=v, Sw=S[w], Sv=S[v], Z=z, m=list(ms2), shared=sorted(M & M2), gates=G, sets=S, outs=outs))
    if cc: st['circuits with >=1 tuple'] += 1
    st['pairs(w,v)'] += 0
print('shard', SH, 'elapsed %.0fs' % (time.time() - t0))
for k, v in sorted(st.items()): print('%-34s %d' % (k, v))
json.dump(wit, open(os.path.join(HERE, 'witnesses_shard%d.json' % SH), 'w'))
print('witnesses saved', len(wit))
