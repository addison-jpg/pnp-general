"""Seat A5: test the F2-transfer inequality |F2'| >= base' at every restriction (Q, D) of circuits with exactly ONE NOT gate.
Run from the repo root:
  python3 -I research/one-not/research/open/A5_transfer_t1.py [--gen FILE.jsonl ...] [--maxn 10] [--bench-dir DIR]
Instances: every circuit dict found in the repository's json/jsonl files (one correct NOT gate), f2lib.corpus(9) + randgen,
and the --gen files (output of research/one-not/tools/search/irreducible.py: irreducible circuits, every gate read, no gate-saving rewiring).
State (Q, D): x_Q = 1, x_D = 0, Q and D disjoint. F2' = OR gates g with a witness (Z contains Q, Z misses D and an alive set S' = S - D,
S cap Q empty, |S'| >= 2, g(Z) = 0, g = 1 at two atoms Z+u, u in S').  base' = sum of |S'| - 1.  (Same definition as A1_negstates.py,
via continuous.slack_table.)  gates' = AND/OR gates of the circuit that are non-constant on the subcube (constant propagation only).
NOT alive = the NOT gate's output is non-constant on the subcube; killed = constant.
A failure is re-evaluated by an independent pure-Python evaluator (no numpy, no truth tables) and written as .bench."""
import sys, os, json, glob, collections, random, itertools
sys.path.insert(0, 'research/one-not/tools/search'); sys.path.insert(0, 'research/one-not/tools/kill_tests')
import numpy as np
import continuous as C, core

def circuit_key(c): return json.dumps([c['n'], c['sets'], c['gates'], c['outs']])

def collect(maxn, gens):
    """name -> circuit, one-NOT correct circuits only; dedup by content."""
    seen = {}; stats = collections.Counter()
    def add(src, d):
        if not (isinstance(d, dict) and all(k in d for k in ('n', 'sets', 'gates', 'outs'))): return
        c = {"n": d['n'], "sets": [list(s) for s in d['sets']], "gates": [list(g) for g in d['gates']], "outs": list(d['outs'])}
        stats['seen'] += 1
        if c['n'] > maxn or core.nots(c) != 1: stats['skip_n_or_t'] += 1; return
        if not C.is_correct(c): stats['incorrect'] += 1; return
        k = circuit_key(c)
        if k not in seen: seen[k] = (src, c)
    for root in ('research/one-not', 'asteroid', 'research/data', 'research/notes'):
        for dp, dn, fn in os.walk(root):
            if '.lake' in dp or '.git' in dp: continue
            for f in fn:
                p = os.path.join(dp, f)
                if f.endswith('.json') and 'findings' not in f:
                    try: whole = json.load(open(p, encoding='utf-8'))
                    except Exception: continue
                    for i, d in enumerate(whole if isinstance(whole, list) else [whole]):
                        if isinstance(d, dict) and 'circuit' in d: d = d['circuit']
                        add('%s:%d' % (p, i), d)
                elif f.endswith('.jsonl') and f != 'findings.jsonl':
                    try:
                        for i, line in enumerate(open(p, encoding='utf-8')):
                            d = json.loads(line)
                            if isinstance(d, dict) and 'c' in d: d = d['c']
                            if isinstance(d, dict) and 'circuit' in d: d = d['circuit']
                            add('%s:%d' % (p, i), d)
                    except Exception: continue
    n_files = len(seen)
    try:
        import f2lib as L
        for c in L.corpus(9) + L.randgen(1, 3000):
            add('f2lib:' + c['name'], {"n": c['n'], "sets": c['S'], "gates": c['G'], "outs": c['outs']})
    except Exception as e: print('f2lib not loaded:', e)
    n_f2 = len(seen) - n_files
    gen = {}
    for g in gens:
        for i, line in enumerate(open(g)):
            d = json.loads(line); k0 = len(seen); add('gen:%s:%d' % (os.path.basename(g), i), d)
            if len(seen) > k0: gen[circuit_key(d)] = True
    return seen, stats, n_files, n_f2, gen

def intersect_ok(c): return all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(c['sets'], 2))

# ---------- independent evaluator (pure python, no tables) ----------
def ev(c, x):
    n = c['n']; w = [(x >> i) & 1 for i in range(n)]
    for g in c['gates']: w.append(1 - w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w
def f2_indep(c, Q, D, any_gate=False):
    """Q, D: sets of points.  Returns (|F2'|, base')."""
    n = c['n']; alive = [[u for u in S if u not in D] for S in c['sets'] if not (set(S) & Q)]
    alive = [S for S in alive if len(S) >= 2]
    base = sum(len(S) - 1 for S in alive); F = set()
    for S in alive:
        free = [v for v in range(n) if v not in D and v not in Q and v not in S]
        for r in range(len(free) + 1):
            for Zs in itertools.combinations(free, r):
                Z = sum(1 << v for v in Q) | sum(1 << v for v in Zs)
                w0 = ev(c, Z); ones = [ev(c, Z | 1 << u) for u in S]
                for k, g in enumerate(c['gates']):
                    if (not any_gate and g[0] != 'or') or k in F: continue
                    if w0[n + k] == 0 and sum(o[n + k] for o in ones) >= 2: F.add(k)
    return len(F), base

# ---------- main evaluation ----------
def write_bench(c, path, note):
    n = c['n']; L = ['# ' + note] + ['INPUT(x%d)' % i for i in range(n)] + ['OUTPUT(g%d)' % (o - n) for o in c['outs']]
    nm = lambda a: 'x%d' % a if a < n else 'g%d' % (a - n)
    for S, o in zip(c['sets'], c['outs']): L.append('#@ or g%d = %s' % (o - n, ' '.join('x%d' % u for u in S)))
    for k, g in enumerate(c['gates']): L.append('g%d = %s(%s)' % (k, g[0].upper(), ', '.join(nm(a) for a in g[1:])))
    open(path, 'w').write('\n'.join(L) + '\n')

def analyse(name, c, agg, fails, ag=(False, True)):
    n = c['n']; G = c['gates']; notk = [k for k, g in enumerate(G) if g[0] == 'not'][0]
    ao = np.array([g[0] != 'not' for g in G]); res = {}
    for R in range(1 << n):                        # R = D
        fr = C.free_points(n, R); m = len(fr); w = C.np_tables(c, R)
        T = np.array([w[n + k] for k in range(len(G))])
        any1 = C.down_close(T.copy(), m); all1 = ~C.down_close(~T, m); nonc = any1 & ~all1
        gp = nonc[ao].sum(0); alive = nonc[notk]
        for a in ag:
            cnt, base = C.slack_table(c, R, any_gate=a, parts=True)
            sel = base > 0
            if not sel.any(): continue
            d = (gp - cnt)[sel]; sl = (cnt - base)[sel]; al = alive[sel]
            for flag in (True, False):
                mk = al == flag
                if not mk.any(): continue
                A = agg[(a, flag)]; A['states'] += int(mk.sum()); A['minslack'] = min(A['minslack'], int(sl[mk].min()))
                A['fail'] += int((sl[mk] < 0).sum())
                for v, ct in zip(*np.unique(d[mk], return_counts=True)): A['hist'][int(v)] += int(ct)
                for v, ct in zip(*np.unique(sl[mk], return_counts=True)): A['slackhist'][int(v)] += int(ct)
            for j in np.nonzero(sel & (cnt < base))[0]:
                Q = {fr[i] for i in range(m) if j >> i & 1}
                fails.append((name, c, a, Q, {v for v in range(n) if R >> v & 1}, int(cnt[j]), int(base[j]), bool(alive[j])))
    return

def newagg(): return {'states': 0, 'minslack': 0, 'fail': 0, 'hist': collections.Counter(), 'slackhist': collections.Counter()}

def main():
    args = sys.argv[1:]; maxn = 10; gens = []; benchdir = 'research/one-not/research/open'
    while args:
        a = args.pop(0)
        if a == '--gen': gens.append(args.pop(0))
        elif a == '--maxn': maxn = int(args.pop(0))
        elif a == '--bench-dir': benchdir = args.pop(0)
    seen, stats, n_files, n_f2, gen = collect(maxn, gens)
    print('circuits kept (one NOT gate, correct, n <= %d): %d  (files %d, f2lib %d, generated %d); raw seen %d, skipped %d, incorrect %d' %
          (maxn, len(seen), n_files, n_f2, len(gen), stats['seen'], stats['skip_n_or_t'], stats['incorrect']))
    agg = {(a, f): newagg() for a in (False, True) for f in (True, False)}
    fails = []; per_n = collections.Counter(); nint = 0; nstates = 0; tot = len(seen)
    for i, (k, (src, c)) in enumerate(sorted(seen.items(), key=lambda kv: kv[1][1]['n'])):
        per_n[c['n']] += 1; nint += intersect_ok(c); nstates += 3 ** c['n']
        analyse(src, c, agg, fails)
        if i % 200 == 0: print(i, tot, 'fails so far', len(fails), flush=True)
    print('instances by n', dict(sorted(per_n.items())), 'pairwise-intersection<=1:', nint, 'restrictions (Q,D) total', nstates)
    for a in (False, True):
        for f in (True, False):
            A = agg[(a, f)]
            print('F2 =', 'any-gate' if a else 'OR-only', 'NOT', 'alive' if f else 'killed', 'states(base>0)', A['states'], 'failures |F2|<base', A['fail'], 'min slack', A['minslack'])
    # independent evaluation: all failures (up to 50) + 300 random states per instance on the first 400 instances
    rng = random.Random(5); mism = 0; chk = 0
    for (name, c, a, Q, D, cnt, base, alive) in fails[:50]:
        r = f2_indep(c, Q, D, a); chk += 1; mism += r != (cnt, base)
    for k, (src, c) in sorted(seen.items(), key=lambda kv: kv[1][1]["n"])[:400:2]:
        n = c['n']
        if n > 7: continue
        for _ in range(8):
            D = {v for v in range(n) if rng.random() < .25}; Q = {v for v in range(n) if v not in D and rng.random() < .25}
            Rm = sum(1 << v for v in D); cn, b = C.slack_table(c, Rm, parts=True); fr = C.free_points(n, Rm)
            j = sum(1 << i for i, v in enumerate(fr) if v in Q); chk += 1; mism += f2_indep(c, Q, D) != (int(cn[j]), int(b[j]))
    print('independent evaluator: states checked', chk, 'mismatches', mism)
    for i, (name, c, a, Q, D, cnt, base, alive) in enumerate(fails[:5]):
        p = os.path.join(benchdir, 'A5_transfer_fail_%d.bench' % i)
        write_bench(c, p, 'A5 F2-transfer failure: Q=%s D=%s |F2|=%d base=%d any_gate=%s src=%s' % (sorted(Q), sorted(D), cnt, base, a, name)); print('FAIL', name, sorted(Q), sorted(D), cnt, base, a, 'wrote', p)
    print('--- table: gates\' - |F2\'| (OR-only F2) by NOT state; states with base > 0')
    for f in (True, False):
        A = agg[(False, f)]; h = sorted(A['hist'].items()); s = A['states']
        mean = sum(v * c for v, c in h) / max(s, 1)
        print('NOT', 'alive ' if f else 'killed', 'states', s, 'min', h[0][0] if h else None, 'mean %.2f' % mean, 'hist', dict(h))
    print('--- slack hist (|F2| - base), OR-only')
    for f in (True, False):
        print('NOT', 'alive ' if f else 'killed', dict(sorted(agg[(False, f)]['slackhist'].items())))

if __name__ == '__main__': main()
