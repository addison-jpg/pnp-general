"""Bounded local witnesses for F2 (seat L3, see limits_local_witness.md).
Run from repo root:  python3 -I research/one-not/research/open/limits_local_witness.py [FANO_CORPUS.jsonl]
(the Fano corpus is made by: python3 -I research/one-not/tools/fano/fano_corpus.py OUT.jsonl, ~2 min)
For every OR gate g and set R, W[g][R] = bitmask over Z in {0,1}^n of contexts with a witness (Lean F2Wit, Q = empty):
Z = 0 on R, g(Z) = 0, g(Z + u) = g(Z + u') = 1 for two u != u' in R.
Families of bounded contexts tested:
  PT_r : |Z| <= r            (pattern: gate, set, 2 points + r context points)
  UN_r : Z = (union of <= r sets) minus R   (pattern: gate + r + 1 sets)
local_r = #{OR gates with a witness Z in the family};  question: local_r >= base on every circuit?"""
import sys, json, glob, itertools, functools
sys.path.insert(0, 'research/one-not/tools/kill_tests')
from f2_nonlocal_build import twin, match

def tables(n, G):
    N = 1 << n; w = []
    for i in range(n):   # bit x of w[i] is x_i: blocks of 2^i zeros then 2^i ones
        blk = ((1 << (1 << i)) - 1) << (1 << i); t = blk; L = 1 << (i + 1)
        while L < N: t |= t << L; L <<= 1
        w.append(t)
    M = (1 << N) - 1
    for g in G: w.append(M ^ w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w, M

_cache = {}
def masks(n):
    if n not in _cache:
        N = 1 << n
        off = [((1 << N) - 1) & ~tables(n, [])[0][u] for u in range(n)]
        pc = [0] * (n + 1)
        for x in range(N): pc[bin(x).count('1')] |= 1 << x
        _cache[n] = (off, pc)
    return _cache[n]

def correct(c, w):
    return all(w[o] == functools.reduce(lambda a, b: a | b, [w[u] for u in S]) for S, o in zip(c['sets'], c['outs']))

def analyse(c, R_PT=6, R_UN=3):
    n = c['n']; w, M = tables(n, c['gates']); off, pc = masks(n)
    assert correct(c, w), 'incorrect circuit'
    Rm = [sum(1 << u for u in R) for R in c['sets']]
    W = {}
    for k, g in enumerate(c['gates']):
        if g[0] != 'or': continue
        t = w[n + k]; Wg = []
        for R in c['sets']:
            avail = M & ~t
            for u in R: avail &= off[u]
            ones = twos = 0
            for u in R:
                x = (t >> (1 << u)) & avail; twos |= ones & x; ones |= x
            Wg.append(twos)
        W[k] = Wg
    base = sum(len(R) - 1 for R in c['sets'])
    F2 = sum(any(Wg) for Wg in W.values())
    cum = [0] * (n + 1); acc = 0
    for r in range(n + 1): acc |= pc[r]; cum[r] = acc
    PT = [sum(any(x & cum[min(r, n)] for x in Wg) for Wg in W.values()) for r in range(R_PT + 1)]
    # minimal context weight per witnessed gate
    minw = []
    for Wg in W.values():
        if any(Wg): minw.append(min(r for r in range(n + 1) if any(x & cum[r] for x in Wg)))
    UN = []; nb = (1 << n) // 8 + 1
    WB = {k: [x.to_bytes(nb, 'little') for x in Wg] for k, Wg in W.items()}
    bit = lambda b, z: b[z >> 3] >> (z & 7) & 1
    for r in range(R_UN + 1):
        Zs = {functools.reduce(lambda a, b: a | b, [Rm[j] for j in J], 0) for s in range(r + 1) for J in itertools.combinations(range(len(Rm)), s)}
        UN.append(sum(any(bit(B[i], z & ~Rm[i]) for i in range(len(Rm)) if Wg[i] for z in Zs) for Wg, B in zip(W.values(), WB.values())))
    def minr(L): return next((r for r, v in enumerate(L) if v >= base), None)
    return dict(n=n, sets=len(Rm), gates=len(c['gates']), nots=sum(g[0] == 'not' for g in c['gates']), base=base, F2=F2,
                PT=PT, UN=UN, minr_PT=minr(PT), minr_UN=minr(UN), maxminw=max(minw) if minw else None)

def stored():
    for f in sorted(glob.glob('research/one-not/data/witnesses/*.json') + glob.glob('research/one-not/data/witnesses/nonlocal/*.json')):
        c = json.load(open(f))
        if 'gates' in c: yield f.split('witnesses/')[-1], c

def families():
    for v in ('OR2', 'E0', 'AND2', 'MAJ3'):
        for k in (2, 3, 4): yield 'twin(%s,k=%d)' % (v, k), twin(v, k)
    for k in range(3, 9):
        for l in ('f', 'x', 's'): yield 'match(k=%d,%s)' % (k, l), match(k, l)
        yield 'match-C(k=%d)' % k, match(k, 's', True)

if __name__ == '__main__':
    worst = {}
    for name, c in itertools.chain(stored(), families()):
        if sum(g[0] == 'not' for g in c['gates']) > 1: print('skip (', sum(g[0] == 'not' for g in c['gates']), 'NOTs):', name); continue
        try: r = analyse(c)
        except AssertionError as e: print('skip', name, e); continue
        print(json.dumps(dict(name=name, **r)), flush=True)
    if len(sys.argv) > 1:
        hist = {}; bad = {'PT': {}, 'UN': {}}; cnt = 0
        for line in open(sys.argv[1]):
            d = json.loads(line); r = analyse(d, R_PT=7, R_UN=3); cnt += 1
            for fam in ('PT', 'UN'):
                m = r['minr_' + fam]; bad[fam][m] = bad[fam].get(m, 0) + 1
            hist[r['F2'] - r['base']] = hist.get(r['F2'] - r['base'], 0) + 1
        print('Fano corpus', cnt, 'circuits; slack histogram', dict(sorted(hist.items())))
        print('min r with local >= base, PT family:', dict(sorted(bad['PT'].items(), key=str)))
        print('min r with local >= base, UN family:', dict(sorted(bad['UN'].items(), key=str)))
