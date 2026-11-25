"""Seat A4: where the single NOT gate enters the F2 count at a mixed state (Q, D).  Run from the repo root:
   python3 -I one-not/research/open/A4_dd_test.py [--maxn 9] [--nocorpus]
Circuits: every one-NOT correct circuit in one-not/data/**.json, one-not/research/open/*.jsonl, and f2lib.corpus(9)+randgen.
a = the NOT gate's input (monotone).  At (Q, D): P_u = 1_Q + e_u (unit atoms), Z_w = 1 off S_w u D (top zero point of w).
  DD(w)    : w alive (S_w cap Q empty, |S_w - D| >= 2), a(Z_w) = 1 and a(P_u) = 0 for some u in S_w - D   (the NOT-sign pattern)
  outDD(w) : C1(out_w)(Z_w) = 1 and C0(out_w)(P_u) = 0 for some u in S_w - D   (the Two-World DD of the restricted circuit)
  dead     : a constant on the subcube.
Claims tested: (1) no DD at (Q, D) => mslack(Q, D) >= 0  [paper proof in A4_f2_transfer.md];
               (2) no outDD at (Q, D) => mslack >= 0  [stronger, open]; and the DD profile of negative/tight states."""
import sys, os, json, glob, collections, itertools
sys.path.insert(0, 'one-not/tools/search'); sys.path.insert(0, 'one-not/tools/kill_tests')
import numpy as np
import continuous as C, core

def tables(c, D, const=None):
    """bool tables of all wires over the subcube x_D = 0; const: replace the NOT gate by that constant."""
    n = c['n']; fr, idx = C.spread(n, D); w = [((idx >> i) & 1).astype(bool) for i in range(n)]
    for g in c['gates']:
        if g[0] == 'not': w.append(np.full(len(idx), const, bool) if const is not None else ~w[g[1]])
        else: w.append(w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]])
    return fr, w

def analyze(c, out):
    n = c['n']; p = [k for k, g in enumerate(c['gates']) if g[0] == 'not'][0]; ain = c['gates'][p][1]
    for D in range(1 << n):
        fr, w = tables(c, D); _, w0 = tables(c, D, False); _, w1 = tables(c, D, True)
        pos = {v: i for i, v in enumerate(fr)}; M = 1 << len(fr); a = w[ain]
        cnt, base = C.slack_table(c, D, parts=True)
        for j in range(M):
            if j & ~((1 << len(fr)) - 1): continue
            Q = {fr[i] for i in range(len(fr)) if j >> i & 1}
            dd = odd = 0
            for S, o in zip(c['sets'], c['outs']):
                if set(S) & Q: continue
                S2 = [u for u in S if not D >> u & 1]
                if len(S2) < 2: continue
                zw = (M - 1) & ~sum(1 << pos[u] for u in S2)
                if a[zw] and any(not a[j | 1 << pos[u]] for u in S2): dd += 1
                if w1[o][zw] and any(not w0[o][j | 1 << pos[u]] for u in S2): odd += 1
            sl = int(cnt[j] - base[j]); dead = bool(a[j]) or not bool(a[M - 1])
            out['states'] += 1
            if dead: out['dead'] += 1; out['dead_neg'] += sl < 0
            if dd == 0: out['noDD'] += 1; out['noDD_neg'] += sl < 0
            if odd == 0: out['noOutDD'] += 1; out['noOutDD_neg'] += sl < 0
            if sl < 0: out['neg'] += 1
            if sl <= 0 and base[j] > 0: out['tight_or_neg'] += 1; out['tight_DD'] += dd > 0
            if dd == 0 and sl < 0: out.setdefault('ex', (c.get('name'), sorted(Q), D, sl))

def collect(maxn, corpus):
    seen = {}
    def add(name, d):
        if not (isinstance(d, dict) and all(k in d for k in ('n', 'sets', 'gates', 'outs'))): return
        c = {"n": d['n'], "sets": [list(s) for s in d['sets']], "gates": [list(g) for g in d['gates']], "outs": list(d['outs']), "name": name}
        if c['n'] > maxn or core.nots(c) != 1 or not C.is_correct(c): return
        if any(len(set(x) & set(y)) > 1 for x, y in itertools.combinations(c['sets'], 2)): return
        seen.setdefault(json.dumps([c['n'], c['sets'], c['gates'], c['outs']]), c)
    for f in glob.glob('one-not/data/**/*.json', recursive=True):
        try: d = json.load(open(f, encoding='utf-8'))
        except Exception: continue
        for i, x in enumerate(d if isinstance(d, list) else [d]): add('%s:%d' % (f, i), x.get('circuit', x) if isinstance(x, dict) else x)
    for f in glob.glob('one-not/research/open/*.jsonl'):
        if 'findings' in f: continue
        for i, line in enumerate(open(f, encoding='utf-8')):
            try: d = json.loads(line)
            except Exception: continue
            if isinstance(d, dict): d = d.get('c', d.get('circuit', d))
            add('%s:%d' % (f, i), d)
    if corpus:
        import f2lib as L
        for c in L.corpus(9) + L.randgen(1, 3000): add('f2lib:' + c['name'], {"n": c['n'], "sets": c['S'], "gates": c['G'], "outs": c['outs']})
    return list(seen.values())

if __name__ == '__main__':
    maxn = int(sys.argv[sys.argv.index('--maxn') + 1]) if '--maxn' in sys.argv else 9
    cs = collect(maxn, '--nocorpus' not in sys.argv); out = collections.Counter()
    for c in cs: analyze(c, out)
    print('circuits', len(cs), dict(out))
