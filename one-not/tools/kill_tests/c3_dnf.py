# Conjecture C3_k on large circuits whose OR gates have MONOTONE real functions (twin trees, MATCH-C(k)): no truth tables.
# Serves README items L5, C3.  Method (independent of f2lib): each wire below the NOT gate gets its list of prime implicants;
# an OR gate above the NOT gate must be an output (real function OR(S_w), correctness is checked by c3_allq / f2lib for small n
# and by sampling here).  For monotone g: g in realWitness(Q) iff for some set w avoiding Q and u != u' in S_w there are
# implicants T, T' of g with T & S_w = {u}, T' & S_w = {u'} and g(Q + T - u + T' - u') = 0 (the least zero point).
# depth(Q) = least |D| with base(Q+D) < base(Q) and slack(Q+D) <= slack(Q).
# Run: python3 -I one-not/tools/kill_tests/c3_dnf.py match K [cap]   |  twin K [cap]  |  file F.json [cap]
import sys, os, json, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
def minimal(ms):
    ms = sorted(set(ms), key=lambda m: bin(m).count('1')); out = []
    for m in ms:
        if not any(o & m == o for o in out): out.append(m)
    return out
def load(d):
    n = d['n']; G = d['gates']; S = d['sets']; outs = d['outs']
    dnf = [[1 << v] for v in range(n)]; dep = [False] * n
    for k, g in enumerate(G):
        if g[0] == 'not': dnf.append(None); dep.append(True); continue
        a, b = g[1], g[2]; dp = dep[a] or dep[b]; dep.append(dp)
        if dp:
            i = n + k
            if g[0] == 'or' and i in outs: dnf.append([1 << u for u in S[outs.index(i)]])
            elif g[0] == 'or': raise ValueError('OR gate %d above the NOT gate is not an output' % i)
            else: dnf.append(None)
        elif g[0] == 'or': dnf.append(minimal(dnf[a] + dnf[b]))
        else: dnf.append(minimal([x | y for x in dnf[a] for y in dnf[b]]))
    smask = [sum(1 << u for u in R) for R in S]
    cands = {}
    for k, g in enumerate(G):
        if g[0] != 'or': continue
        i = n + k; ms = dnf[i]; cs = set()
        for w, sm in enumerate(smask):
            per = {}
            for T in ms:
                x = T & sm
                if x and x & (x - 1) == 0: per.setdefault(x, []).append(T & ~sm)
            for u, u2 in itertools.combinations(sorted(per), 2):
                for a in per[u]:
                    for b in per[u2]:
                        Z = a | b
                        if not any(m & Z == m for m in ms): cs.add((sm, Z))
        cs = [(sm, Z) for sm, Z in cs if not any(sm2 == sm and Z2 != Z and Z2 & Z == Z2 for sm2, Z2 in cs)]
        if cs: cands[i] = (ms, cs)
    return dict(n=n, S=S, smask=smask, cands=cands, G=G, outs=outs)
def inrw(c, i, Q):
    ms, cs = c['cands'][i]
    for sm, Z in cs:
        if sm & Q: continue
        Z |= Q
        if not any(m & Z == m for m in ms): return True
    return False
def witness(c, i, Q):
    # an explicit witness (set index, zero point Z, atoms u, u') for gate i at the cube Q, or None; checked by c3_cert.py
    ms, cs = c['cands'][i]
    for sm, Z0 in cs:
        if sm & Q: continue
        Z = Z0 | Q
        if any(m & Z == m for m in ms): continue
        at = sorted({(T & sm).bit_length() - 1 for T in ms if (T & sm) and (T & sm) & ((T & sm) - 1) == 0 and (T & ~sm) & ~Z == 0})
        if len(at) >= 2: return c['smask'].index(sm), Z, at[0], at[1]
    return None
def base(c, Q): return sum(len(R) - 1 for R, sm in zip(c['S'], c['smask']) if not sm & Q)
def rw(c, Q, among=None): return [i for i in (c['cands'] if among is None else among) if inrw(c, i, Q)]
def sample_correct(d, trials=2000, seed=1):
    n = d['n']; rng = random.Random(seed); pts = [0] + [1 << v for v in range(n)] + [(1 << u) | (1 << v) for u in range(n) for v in range(u)]
    pts += [rng.getrandbits(n) for _ in range(trials)] + [rng.getrandbits(n) & rng.getrandbits(n) & rng.getrandbits(n) for _ in range(trials)]
    for x in pts:
        val = [x >> v & 1 for v in range(n)]
        for g in d['gates']:
            val.append(1 - val[g[1]] if g[0] == 'not' else (val[g[1]] & val[g[2]] if g[0] == 'and' else val[g[1]] | val[g[2]]))
        for o, R in zip(d['outs'], d['sets']):
            if val[o] != int(any(val[u] for u in R)): return False
    return True
def depth(c, Q0=0, cap=4, all_min=False):
    # exact: least |D| (D unfixed) with base smaller and slack not larger; returns (depth or None, D, table of best slack change per size)
    n = c['n']; F0 = rw(c, Q0); b0 = base(c, Q0); s0 = len(F0) - b0
    free = [v for v in range(n) if not Q0 >> v & 1]; best = {}; found = [None]
    def rec(Q, F, start, size, D, lim):
        for idx in range(start, len(free)):
            v = free[idx]; Q2 = Q | 1 << v; F2 = [i for i in F if inrw(c, i, Q2)]; b2 = base(c, Q2); ds = (len(F2) - b2) - s0
            if b2 < b0:
                if size + 1 not in best or ds < best[size + 1][0]: best[size + 1] = (ds, D + [v])
                if ds <= 0 and found[0] is None and size + 1 == lim: found[0] = D + [v]
            if size + 1 < lim: rec(Q2, F2, idx + 1, size + 1, D + [v], lim)
    for lim in range(1, cap + 1):
        rec(Q0, F0, 0, 0, [], lim)
        if found[0] is not None: return lim, found[0], best, s0
    return None, None, best, s0
if __name__ == '__main__':
    import f2_nonlocal_build as B
    kind = sys.argv[1]; cap = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    if kind == 'file': d = json.load(open(sys.argv[2]))
    elif kind == 'match': d = B.match(int(sys.argv[2]), 's', True)
    elif kind == 'matchs': d = B.match(int(sys.argv[2]), 's', False)
    else: raise SystemExit('kind')
    assert sample_correct(d), 'INCORRECT on a sampled input'
    c = load(d); r, D, best, s0 = depth(c, 0, cap)
    print(d.get('name'), 'n', d['n'], 'gates', len(d['gates']), 'base', base(c, 0), 'slack(empty)', s0, 'depth', r if r else '> %d' % cap, 'D', D,
          'least slack change by |D|:', {k: v[0] for k, v in sorted(best.items())}, 'at', {k: v[1] for k, v in sorted(best.items())})
