"""Exact equality of the tensor backend with the slow evaluators on the stored corpus.  From the repository root:
    python3 -I one-not/tools/tensor/test_tensor.py [--f2lib]        (also works under pytest)
Checks, per circuit: truth tables == core.tables (every wire), correct == core.correct, slack at every cube == continuous.slack_table
(count and base, OR-only and any-gate), == core.slack at sampled cubes, the mixed slack at every R (n <= MIXED_N) == continuous.slack_table(c, R),
INVALID exactly where Q meets R, and the DD states == the A7/A14 definition evaluated state by state.
Corpus: all of one-not/data (witnesses, t4/t5/t6, ...) up to n = 9, plus (--f2lib) the 3,155 circuits of f2lib."""
import os, sys, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'search'))
import numpy as np
import bits, corpus, core, continuous as C

MIXED_N = 7        # every R checked up to this n; larger n: a random sample of R
NMAX = 9


def check_tables(c):
    n = c['n']; t = bits.tables(c); w = core.tables(n, c['gates'])
    assert t.shape[0] == len(w)
    for i in range(len(w)): assert bits.to_int(t[i]) == w[i], (c['name'], 'wire', i)
    assert bits.correct(c) == core.correct(c, w), c['name']


def check_cubes(c, rng):
    n = c['n']; w = core.tables(n, c['gates'])
    for ag in (False, True):
        a, b = bits.slack_cubes(c, ag, True), C.slack_table(c, 0, any_gate=ag, parts=True)
        assert (a[0] == b[0]).all() and (a[1] == b[1]).all(), (c['name'], 'cube count/base', ag)
        s = a[0] - a[1]
        for Q in [rng.randrange(1 << n) for _ in range(12)] + [0, (1 << n) - 1]:
            assert core.slack(c, Q, w, ag) == int(s[Q]), (c['name'], 'core.slack', Q, ag)


def check_mixed(c, rng):
    n = c['n']; Rs = list(range(1 << n)) if n <= MIXED_N else rng.sample(range(1 << n), 24)
    for ag in (False, True):
        pa, pb = bits.mixed_slack(c, ag, True, rs=Rs)
        sl = bits.mixed_slack(c, ag, rs=Rs); cm = bits.mixed_slack(c, ag, parts=True, rs=Rs, compact=True)
        for i, R in enumerate(Rs):
            fr, idx = C.spread(n, R); cn, bs = C.slack_table(c, R, any_gate=ag, parts=True)
            assert (pa[i][idx] == cn).all() and (pb[i][idx] == bs).all(), (c['name'], 'mixed', R, ag)
            assert (sl[i][idx] == cn - bs).all() and (cm[i][0] == cn).all() and (cm[i][1] == bs).all()    # compact layout == slack_table
            m = np.ones(1 << n, bool); m[idx] = False
            assert (pa[i][m] == bits.INVALID).all() and (sl[i][m] == bits.INVALID).all(), (c['name'], 'invalid cells', R)


def check_stats(c):
    """Packed reductions (no unpacking) == reductions of the full mixed table."""
    if c['n'] > 8: return
    sl, pb = bits.mixed_slack(c), bits.mixed_slack(c, parts=True)[1]; ok = sl != bits.INVALID; v = sl[ok]
    st = bits.mixed_stats(c)
    u, k = np.unique(v, return_counts=True)
    assert st['states'] == 3 ** c['n'] == int(ok.sum()) and st['neg'] == int((v < 0).sum()), (c['name'], 'stats')
    assert st['base_pos'] == int((pb[ok] > 0).sum()) and st['min_slack'] == min(int(v.min()), 0)
    assert st['hist'] == dict(zip(u.tolist(), k.tolist())), (c['name'], 'hist')


def dd_slow(c):
    """A7_dd_absorb_attack.check_state / A14 analyse, the DD test only, state by state with Python-int truth tables."""
    n, G, S = c['n'], c['gates'], c['sets']; W = core.tables(n, G); ALL = (1 << n) - 1
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]; hits = set(); pairs = 0
    for code in itertools.product(range(3), repeat=n):
        Q = {v for v in range(n) if code[v] == 1}; D = {v for v in range(n) if code[v] == 2}; qpt = sum(1 << v for v in Q)
        for R in S:
            if set(R) & Q: continue
            R2 = [u for u in R if u not in D]
            if len(R2) < 2: continue
            zw = ALL
            for u in R2 + list(D): zw &= ~(1 << u)
            if (a >> zw & 1) and any(not (a >> (qpt | 1 << u) & 1) for u in R2):
                hits.add((sum(1 << v for v in D), qpt)); pairs += 1
    return hits, pairs


def check_dd(c):
    anyd, pairs = bits.dd_states(c)
    hits, pr = dd_slow(c)
    got = {(int(d), int(q)) for d, q in zip(*np.nonzero(anyd))}
    assert got == hits and pairs == pr, (c['name'], 'dd', len(got), len(hits))


def run(f2lib=False, verbose=True):
    rng = random.Random(1); cs = corpus.collect(NMAX, f2lib=f2lib); nm = nd = 0
    for c in cs:
        check_tables(c); check_cubes(c, rng); check_mixed(c, rng); check_stats(c); nm += 1
        if core.nots(c) == 1 and c['n'] <= 7 and any(len(R) >= 2 for R in c['sets']): check_dd(c); nd += 1
    if verbose: print('tensor == slow evaluators on %d circuits (tables, cube slack, mixed slack, %d DD checks)' % (nm, nd))
    return nm


def test_corpus(): assert run() > 50


def test_generators():
    """Padding / word-boundary cases: n = 1..8 on random circuits, including const gates."""
    rng = random.Random(7)
    for n in range(1, 9):
        for _ in range(3):
            G = []; N = n
            for _ in range(rng.randrange(1, 12)):
                op = rng.choice(['and', 'or', 'or', 'not'])
                G.append([op, rng.randrange(N + len(G))] + ([rng.randrange(N + len(G))] if op != 'not' else []))
            G.append(['or', rng.randrange(N + len(G)), rng.randrange(N + len(G))])    # the slow slack_table needs one OR gate
            S = [rng.sample(range(n), min(n, rng.randrange(1, 4))) for _ in range(3)]
            c = {'n': n, 'sets': S, 'gates': G, 'outs': [n + len(G) - 1] * 3, 'name': 'rand%d' % n}
            check_tables(c); check_cubes(c, rng)
            if n <= MIXED_N: check_mixed(c, rng)
            c2 = dict(c, gates=G + [['const', 1], ['const', 0], ['or', N + len(G), 0]])      # const gates: against A7.tables
            sys.path.insert(0, os.path.join(ROOT, 'one-not', 'research', 'open')); import A7_dd_absorb_attack as A7
            W7 = A7.tables(n, c2['gates'])[0]; t2 = bits.tables(c2)
            assert all(bits.to_int(t2[i]) == W7[i] for i in range(len(W7))), 'const'


if __name__ == '__main__':
    run('--f2lib' in sys.argv); test_generators(); print('random n=1..8 circuits ok')
