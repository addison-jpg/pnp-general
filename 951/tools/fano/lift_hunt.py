# lift_hunt.py (scaffold 951, 2026-11-24): mutation hunt for a MUL counterexample (|U liftMenu| < base), 1 or 2 NOTs.
# Needs liftmenu.py and fano_corpus.py (same directory). Random walk over CORRECT circuits with exactly K NOT gates, all of them
# essential if --ess (forcing that NOT's output to 0 breaks some output, and forcing it to 1 breaks some output); moves: rewire a
# slot, insert a random gate, a -> (a&N)|(a&h), bypass a gate, prune dangling; objective = exact MUL margin; accept if <=
# current (5% random uphill). Writes every new best to OUT; prints 'MUL COUNTEREXAMPLE' on a negative margin.
#   python3 lift_hunt.py START.json SECONDS SEED OUT.jsonl [--ess] [--smax N]
#   (START.json: one circuit, or {"selector": [[u,v],...], "nsel": 2} for liftmenu.selector_path)
# Landed by coord (scaffold cannot push).
import sys, json, random, time
from liftmenu import lifted_vectors, menu, selector_path
from fano_corpus import correct, mutate, bypass

def essential_each(c):
    n = c['n']; R = 1 << n; full = (1 << R) - 1; res = []
    def run(force_k=None, f=None):
        T = [sum(((r >> i) & 1) << r for r in range(R)) for i in range(n)]
        for k, g in enumerate(c['gates']):
            a = T[g[1]]
            if k == force_k: T.append(f)
            else: T.append(full & ~a if g[0] == 'not' else (a & T[g[2]] if g[0] == 'and' else a | T[g[2]]))
        return T
    Tr = run()
    for k, g in enumerate(c['gates']):
        if g[0] == 'not':
            res.append(all(any(run(k, f)[o] != Tr[o] for o in c['outs']) for f in (0, full)))
    return res

def margin(c):
    T, vec, R = lifted_vectors(c); U = frozenset()
    for w in range(len(c['sets'])):
        for M in menu(c, w, T, vec, R): U |= M
    return len(U) - sum(len(S) - 1 for S in c['sets'])

if __name__ == '__main__':
    st = json.load(open(sys.argv[1])); secs, rng, out = float(sys.argv[2]), random.Random(int(sys.argv[3])), open(sys.argv[4], 'a')
    ess = '--ess' in sys.argv; smax = int(sys.argv[sys.argv.index('--smax') + 1]) if '--smax' in sys.argv else 160
    cur = selector_path([tuple(e) for e in st['selector']], st['nsel']) if 'selector' in st else {k: st[k] for k in ('n', 'sets', 'gates', 'outs')}
    K = sum(g[0] == 'not' for g in cur['gates']); assert correct(cur)
    m = margin(cur); best = m; t0 = time.time(); ev = 0
    while time.time() - t0 < secs:
        c2 = bypass(cur, rng) if rng.random() < 0.35 else mutate(cur, rng)
        if c2 is None or len(c2['gates']) > smax: continue
        if sum(g[0] == 'not' for g in c2['gates']) != K or not correct(c2): continue
        if ess and not all(essential_each(c2)): continue
        m2 = margin(c2); ev += 1
        if m2 <= m or rng.random() < 0.05: cur, m = c2, m2
        if m2 < best:
            best = m2; out.write(json.dumps({'margin': m2, 's': len(c2['gates']), **c2}) + '\n'); out.flush()
            if m2 < 0: print('MUL COUNTEREXAMPLE', json.dumps(c2), flush=True)
    print(json.dumps({'evals': ev, 'best_margin': best, 'final_s': len(cur['gates'])}), flush=True)
