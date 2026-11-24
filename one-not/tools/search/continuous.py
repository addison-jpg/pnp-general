"""The continuous form of the count (task continuous-mapping). Serves README items L5, L6, C2.

Definition (ext, the multilinear extension of the slack).  For p in [0,1]^n let mu_p put each point v in the cube Q
independently with probability p_v.  ext(p) = E_{mu_p}[slack(Q)].  ext(1_Q) = slack(Q); ext is linear in each p_v;
d ext / d p_v (p) = E_{mu_p}[slack(Q + v) - slack(Q) | v not in Q].
Definition (Phi, the diagonal).  Phi(p) = ext(p, ..., p) = sum_i C(n,i) p^i (1-p)^(n-i) m_i, m_i = mean of slack over the
cubes with i points (Bernstein form).  Phi(0) = slack(empty), Phi(1) = 0.
Definition (lap, the up-Laplacian).  lap f (Q) = sum_{v not in Q} (f(Q+v) - f(Q)).  n (1-p) Phi'(p) ... see fable-continuous.md.

Circuit = the dict of core.py.  Tables are numpy bool arrays over the 2^n inputs (bit v of the index = x_v).
Run from the repository root:
  python3 -I one-not/tools/search/continuous.py phi  [files]   Phi, its Bernstein coefficients, sign pattern of Phi, Phi', Phi''
  python3 -I one-not/tools/search/continuous.py grad [files]   vertices where every direction is uphill; the up-Laplacian test
  python3 -I one-not/tools/search/continuous.py mixed [files]  0-steps and 1-steps at mixed states (Q, R)
  python3 -I one-not/tools/search/continuous.py lp   [files]   LP search for a local potential
  python3 -I one-not/tools/search/continuous.py hunt SECONDS SEED [NMAX]   hill climbing against the mixed step
  python3 -I one-not/tools/search/continuous.py check          compares the fast slack table with core.slack
"""
import sys, os, json, glob, random, itertools
from fractions import Fraction
from math import comb
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core

WIT = 'one-not/data/witnesses/'

def load(f):
    d = json.load(open(f)); return {"n": d['n'], "sets": d['sets'], "gates": d['gates'], "outs": d['outs'], "name": os.path.basename(f)[:-5]}

def circuits(args):
    """Circuits from: F.json | F.jsonl[:COUNT] (one circuit per line) | corpus (the 3,155 circuits of c3_allq.py: f2lib.corpus(9) + f2lib.randgen(1, 3000))."""
    for a in args:
        if a == 'corpus':
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kill_tests')); import f2lib as L
            for c in L.corpus(9) + L.randgen(1, 3000): yield {"n": c['n'], "sets": c['S'], "gates": c['G'], "outs": c['outs'], "name": c['name']}
        elif '.jsonl' in a:
            f, _, lim = a.partition(':'); lim = int(lim) if lim else None
            for i, line in enumerate(open(f)):
                if lim is not None and i >= lim: break
                d = json.loads(line); d.setdefault('name', '%s#%d' % (os.path.basename(f), i)); yield d
        else: yield load(a)

def default_files(nmax=16):
    fs = sorted(glob.glob(WIT + '*.json') + glob.glob(WIT + 'nonlocal/*.json'))
    return [f for f in fs if json.load(open(f))['n'] <= nmax]

def free_points(n, R): return [v for v in range(n) if not R >> v & 1]

def spread(n, R):
    """idx[j] = the input vector whose restriction to the points outside R is j (points of R are 0)."""
    fr = free_points(n, R); j = np.arange(1 << len(fr), dtype=np.int64); idx = np.zeros(1 << len(fr), np.int64)
    for i, v in enumerate(fr): idx |= ((j >> i) & 1) << v
    return fr, idx

def np_tables(c, R=0):
    """Bool tables of all wires over the inputs with x_R = 0 (indexed by the sub-vector on the points outside R)."""
    n = c['n']; fr, idx = spread(n, R); w = []
    for i in range(n): w.append(((idx >> i) & 1).astype(bool))
    for g in c['gates']:
        w.append(~w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w

def is_correct(c):
    w = np_tables(c)
    return all(np.array_equal(w[o], np.logical_or.reduce([w[u] for u in S])) for S, o in zip(c['sets'], c['outs']))

def down_close(U, n):
    """U: bool (G, 2^n). Afterwards U[g, Q] = 1 iff some Z containing Q had U[g, Z] = 1."""
    G = U.shape[0]
    for v in range(n):
        A = U.reshape(G, -1, 2, 1 << v); A[:, :, 0, :] |= A[:, :, 1, :]
    return U

def slack_table(c, R=0, any_gate=False, parts=False):
    """slack(Q, R) for every Q disjoint from R, indexed by the sub-vector of Q on the points outside R (R = 0: index = Q, the slack of D8).
    State (Q, R): x_Q = 1, x_R = 0; the sets S_w - R with at least 2 points left that avoid Q; witnesses with Z disjoint from R."""
    n = c['n']; fr, idx = spread(n, R); pos = {v: i for i, v in enumerate(fr)}; M = len(idx); j = np.arange(M, dtype=np.int64); w = np_tables(c, R)
    gi = [k for k, g in enumerate(c['gates']) if any_gate or g[0] == 'or']
    T = np.array([w[n + k] for k in gi]) if gi else np.zeros((0, M), bool)
    U = np.zeros(T.shape, bool); base = np.zeros(M, np.int64)
    for S in c['sets']:
        S2 = [u for u in S if not R >> u & 1]
        if len(S2) < 2: continue
        sm = sum(1 << u for u in S2)
        zero = (idx & sm) == 0
        base += (len(S2) - 1) * zero
        ones = np.zeros(T.shape, np.int8)
        for u in S2: ones += T[:, j | (1 << pos[u])]
        U |= zero[None, :] & ~T & (ones >= 2)
    down_close(U, len(fr))
    cnt = U.sum(axis=0).astype(np.int64)
    return (cnt, base) if parts else cnt - base

def popcount(n):
    idx = np.arange(1 << n, dtype=np.int64); pc = np.zeros(1 << n, np.int64)
    for v in range(n): pc += (idx >> v) & 1
    return pc

def level_means(sl, n):
    pc = popcount(n)
    return [Fraction(int(sl[pc == i].sum()), comb(n, i)) for i in range(n + 1)]

def bern_eval(m, p):
    n = len(m) - 1; return sum(comb(n, i) * p ** i * (1 - p) ** (n - i) * m[i] for i in range(n + 1))

def diffs(m):
    """Bernstein coefficients of the derivative (up to the factor n)."""
    return [m[i + 1] - m[i] for i in range(len(m) - 1)]

def sign_changes(seq):
    s = [x for x in seq if x != 0]; return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))

def grid_signs(m, K=400):
    """Sign pattern of the polynomial with Bernstein coefficients m on the grid j/K (exact rational evaluation)."""
    out = []
    for j in range(K + 1):
        v = bern_eval(m, Fraction(j, K)); s = '+' if v > 0 else ('-' if v < 0 else '0')
        if not out or out[-1] != s: out.append(s)
    return ''.join(out)

def ext(sl, n, p):
    """The multilinear extension at p (list of n floats)."""
    a = np.asarray(sl, float).copy()
    for v in range(n):
        A = a.reshape(-1, 2, 1 << v); a = ((1 - p[v]) * A[:, 0, :] + p[v] * A[:, 1, :]).reshape(-1)
    return float(a[0])

def lap_data(sl, base, n):
    """Per cube: number of free points v, sum over them of slack(Q+v) - slack(Q), and whether every ALIVE one-point step is strictly uphill."""
    N = 1 << n; idx = np.arange(N, dtype=np.int64); lap = np.zeros(N, np.int64); best = np.full(N, 10 ** 9, np.int64)
    for v in range(n):
        free = (idx >> v & 1) == 0; up = idx | (1 << v)
        d = sl[up] - sl
        lap += np.where(free, d, 0)
        paid = free & (base[up] < base)
        best = np.where(paid, np.minimum(best, d), best)
    return lap, best

def cmd_phi(files):
    print('| circuit | n | slack(∅) | min over cubes | m_1 … (level means) | sign changes of Δm, Δ²m | Φ on grid | Φ′ | Φ″ | ρ = Φ/(1−p)² : Δ signs |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    tot = neg = up = 0
    for f in files:
        c = load(f); n = c['n']
        if not is_correct(c): print('|', c['name'], '| NOT CORRECT |'); continue
        t = core.nots(c); sl = slack_table(c, any_gate=(t != 1 and t != 0))
        m = level_means(sl, n); d1 = diffs(m); d2 = diffs(d1); tot += 1
        neg += int(sl.min()) < 0; up += d1[0] > 0
        # rho(p) = Phi(p) / (1 - p)^2 has Bernstein coefficients (degree n - 2)  r_i = m_i C(n,i) / C(n-2,i)
        r = [m[i] * comb(n, i) / comb(n - 2, i) for i in range(n - 1)]
        print('|', c['name'], '(t=%d)' % t, '|', n, '|', int(sl[0]), '|', int(sl.min()), '|', ' '.join('%.2f' % float(x) for x in m[1:]), '|',
              sign_changes(d1), sign_changes(d2), '|', grid_signs(m), '|', grid_signs(d1), '|', grid_signs(d2), '|', sign_changes(diffs(r)), ('first up' if r[1] > r[0] else 'first down'), '|')
    print('circuits %d; with a cube of negative slack %d; with Φ′(0) > 0 (mean first step uphill) %d' % (tot, neg, up))

def cmd_grad(files):
    print('| circuit | n | cubes with base > 0 | all paying one-point steps strictly uphill (ext has no descent direction that pays) | of these at slack 0 | lap ≤ 0 fails | cubes with slack 0 and lap > 0 | least c with lap slack ≤ c·slack |')
    print('|---|---|---|---|---|---|---|---|')
    T = [0] * 5
    for f in files:
        c = load(f); n = c['n']; t = core.nots(c)
        if t > 1 or not is_correct(c): continue
        cnt, base = slack_table(c, parts=True); sl = cnt - base
        lap, best = lap_data(sl, base, n); pos = base > 0
        uph = pos & (best > 0) & (best < 10 ** 9); lf = pos & (lap > 0); z = pos & (sl == 0) & (lap > 0)
        cs = max([Fraction(int(a), int(b)) for a, b in zip(lap[pos & (sl > 0)], sl[pos & (sl > 0)])] + [Fraction(0)])
        for i, x in enumerate([pos.sum(), uph.sum(), (uph & (sl == 0)).sum(), lf.sum(), z.sum()]): T[i] += int(x)
        print('|', c['name'], '|', n, '|', int(pos.sum()), '|', int(uph.sum()), '|', int((uph & (sl == 0)).sum()), '|', int(lf.sum()), '|', int(z.sum()), '|', '%.3f' % float(cs), '|')
    print('totals: cubes %d, uphill vertices %d, uphill at slack 0: %d, lap > 0: %d, slack 0 and lap > 0: %d' % tuple(T))

def cmd_mixed(files, rmax=3 ** 16):
    """Every mixed state (Q, R).  A 1-step puts a free point in Q, a 0-step puts it in R; a step PAYS if the base drops."""
    quiet = any(not f.endswith('.json') for f in files)
    print('| circuit | n | states with base > 0 | least slack | no paying 1-step with slack no larger | no paying 0-step with slack no larger | neither | slack 0 and some step raises the slack |')
    print('|---|---|---|---|---|---|---|---|'); TT = [0] * 5; nc = 0
    for c in circuits(files):
        n = c['n']
        if core.nots(c) > 1 or not is_correct(c) or 3 ** n > rmax: continue
        tab = {}; nc += 1
        for R in range(1 << n): tab[R] = slack_table(c, R, parts=True)
        st = f1 = f0 = fb = tz = 0; mn = 0
        for R in range(1 << n):
            cnt, base = tab[R]; sl = cnt - base; fr = free_points(n, R); M = len(sl); j = np.arange(M, dtype=np.int64)
            if not (base > 0).any(): continue
            ok1 = np.zeros(M, bool); ok0 = np.zeros(M, bool); up = np.zeros(M, bool)
            for i, v in enumerate(fr):
                free = (j >> i & 1) == 0; a = j | (1 << i)
                ok1 |= free & (base[a] < base) & (sl[a] <= sl); up |= free & (sl[a] > sl)
                c2, b2 = tab[R | 1 << v]; lo = j & ((1 << i) - 1); jj = lo | ((j >> (i + 1)) << i)   # delete bit i
                s2 = (c2 - b2)[jj]; ok0 |= free & (b2[jj] < base) & (s2 <= sl); up |= free & (s2 > sl)
            pos = base > 0
            st += int(pos.sum()); f1 += int((pos & ~ok1).sum()); f0 += int((pos & ~ok0).sum()); fb += int((pos & ~ok1 & ~ok0).sum())
            tz += int((pos & (sl == 0) & up).sum()); mn = min(mn, int(sl.min()))
        for i, x in enumerate([st, f1, f0, fb, tz]): TT[i] += x
        if not quiet or fb or mn < 0: print('|', c['name'], '|', n, '|', st, '|', mn, '|', f1, '|', f0, '|', fb, '|', tz, '|', flush=True)
    print('totals: circuits %d; states %d; no 1-step %d; no 0-step %d; neither %d; slack 0 with a step up %d' % tuple([nc] + TT))

KCAP = 3; BCAP = 2
def features(c, rich=True):
    """x(Q) for every cube: the potential is psi(Q) = theta . x(Q).
    Gate features (OR gates): (min(k, KCAP), min(kb, BCAP), b):  k = number of alive sets the gate witnesses at Q,  kb = number of alive sets it
    witnesses with the zero point Z = Q itself (the bottom point of the cube),  b = value of the gate at the bottom point.  rich=False drops kb.
    Set features: (s, j) = (|S_w|, |S_w meet Q|), with coefficient -1 (a charge)."""
    n = c['n']; N = 1 << n; idx = np.arange(N, dtype=np.int64); w = np_tables(c)
    gi = [k for k, g in enumerate(c['gates']) if g[0] == 'or']
    T = np.array([w[n + k] for k in gi]) if gi else np.zeros((0, N), bool); K = np.zeros(T.shape, np.int8); KB = np.zeros(T.shape, np.int8)
    for S in c['sets']:
        sm = sum(1 << u for u in S); zero = (idx & sm) == 0; ones = np.zeros(T.shape, np.int8)
        for u in S: ones += T[:, idx | (1 << u)]
        U = zero[None, :] & ~T & (ones >= 2)
        if rich: KB += U
        K += down_close(U, n)
    K = np.minimum(K, KCAP); KB = np.minimum(KB, BCAP); X = {}
    for k in range(KCAP + 1):
        for kb in range(min(k, BCAP) + 1 if rich else 1):
            for b in (0, 1): X[('g', k, kb, b)] = ((K == k) & (KB == kb) & (T == bool(b))).sum(axis=0)
    for S in c['sets']:
        j = np.zeros(N, np.int64)
        for u in S: j += (idx >> u) & 1
        for jj in range(len(S) + 1):
            X[('s', len(S), jj)] = X.get(('s', len(S), jj), 0) - (j == jj)
    return X

def cmd_lp(files):
    """LP search for a local potential psi = theta . x with  psi <= slack (by the sign constraints),  psi(full cube) = 0,  and a LOCAL inequality:
    form 'all': psi(Q + v) <= psi(Q) for every free v;  form 'avg': sum over free v of (psi(Q + v) - psi(Q)) <= 0.  Either gives psi >= 0, so slack >= 0."""
    from scipy.optimize import linprog
    rich = 'poor' not in files; files = [f for f in files if f != 'poor']
    rows = {'all': [], 'avg': []}; keys = {}; data = []; nc = 0
    for c in circuits(files):
        if core.nots(c) > 1 or c['n'] > 16 or not is_correct(c): continue
        X = features(c, rich); n = c['n']; nc += 1
        for k in X: keys.setdefault(k, len(keys))
        data.append((n, X))
    D = len(keys)
    for n, X in data:
        N = 1 << n; idx = np.arange(N, dtype=np.int64); M = np.zeros((N, D), np.int64)
        for k, col in X.items(): M[:, keys[k]] = col
        tot = np.zeros((N, D), np.int64); parts = []
        for v in range(n):
            free = (idx >> v & 1) == 0; d = M[idx[free] | (1 << v)] - M[free]; parts.append(d); tot[free] += d
        rows['all'].append(np.unique(np.concatenate(parts), axis=0)); rows['avg'].append(np.unique(tot, axis=0))
    lo = np.full(D, -np.inf); hi = np.full(D, np.inf)
    for k, i in keys.items():
        if k[0] == 'g': hi[i] = 1 if k[1] >= 1 else 0; lo[i] = 0 if k[1] == 0 else -np.inf      # a non-witness gate weighs 0, a witness gate at most 1
        else:
            s, j = k[1], k[2]
            if j == 0: lo[i] = s - 1            # an alive set is charged at least its demand
            elif j == s: lo[i] = hi[i] = 0      # nothing is charged at the full cube
            else: lo[i] = 0                     # a dead set is charged at least 0
    print('circuits %d, parameters %d, gate features %s' % (nc, D, '(k, kb, b)' if rich else '(k, b)'))
    for form in ('all', 'avg'):
        A = np.unique(np.concatenate(rows[form]), axis=0); A = A[np.any(A != 0, axis=1)]
        r = linprog(np.zeros(D), A_ub=A.astype(float), b_ub=np.zeros(len(A)), bounds=list(zip(lo, hi)), method='highs')
        print('form %s: %d distinct inequalities; LP %s' % (form, len(A), 'FEASIBLE' if r.status == 0 else 'INFEASIBLE (status %d)' % r.status))
        if r.status == 0:
            for k, i in sorted(keys.items()): print('   ', k, round(float(r.x[i]), 4))

def mixed_margin(c):
    """(m, count): m = max over the mixed states with base > 0 of (least slack change over the paying 0-steps and 1-steps); m >= 1 refutes the
    mixed step.  count = number of states that attain m."""
    n = c['n']; tab = [slack_table(c, R, parts=True) for R in range(1 << n)]; m = None; k = 0
    for R in range(1 << n):
        cnt, base = tab[R]; sl = cnt - base; fr = free_points(n, R); M = len(sl); j = np.arange(M, dtype=np.int64)
        if not (base > 0).any(): continue
        best = np.full(M, 10 ** 6, np.int64)
        for i, v in enumerate(fr):
            free = (j >> i & 1) == 0; a = j | (1 << i)
            best = np.where(free & (base[a] < base), np.minimum(best, sl[a] - sl), best)
            c2, b2 = tab[R | 1 << v]; lo = j & ((1 << i) - 1); jj = lo | ((j >> (i + 1)) << i)
            best = np.where(free & (b2[jj] < base), np.minimum(best, (c2 - b2)[jj] - sl), best)
        b = best[base > 0]; x = int(b.max())
        if m is None or x > m: m, k = x, int((b == x).sum())
        elif x == m: k += int((b == x).sum())
    return (m if m is not None else -10 ** 6), k

def cmd_hunt(args):
    """Hill climbing against the mixed step: python3 -I one-not/tools/search/continuous.py hunt SECONDS SEED [NMAX].  Finding nothing proves nothing."""
    import time, copy, hunt as H
    secs, seed = float(args[0]), int(args[1]); nmax = int(args[2]) if len(args) > 2 else 6; rng = random.Random(seed)
    starts = [load(f) for f in default_files(nmax)]; starts = [c for c in starts if core.nots(c) <= 1]
    starts += [H.or_tree(c['n'], c['sets']) for c in starts]
    t0 = time.time(); tried = kept = 0; top = None
    while time.time() - t0 < secs:
        cur = copy.deepcopy(rng.choice(starts)); mc = mixed_margin(cur); stall = 0
        while time.time() - t0 < secs and stall < 150:
            new = (H.rewrite if rng.random() < 0.4 else H.mutate)(cur, rng, 1); tried += 1
            if len(new['gates']) > 40 or core.nots(new) > 1 or not is_correct(new): stall += 1; continue
            new = core.prune(new); mn = mixed_margin(new)
            if mn >= mc:
                stall = 0 if mn > mc else stall + 1; cur, mc = new, mn; kept += 1
                if top is None or mc > top[0]: top = (mc, copy.deepcopy(cur))
                if mc[0] >= 1:
                    os.makedirs('one-not/tools/search/found', exist_ok=True); p = 'one-not/tools/search/found/mixed_step_seed%d.json' % seed
                    json.dump(dict(cur, name='hunt mixed step', margin=mc[0]), open(p, 'w')); print('FOUND', p); return
            else: stall += 1
    print('mixed step | seed %d | n <= %d | %d mutations, %d kept | counterexamples 0 | largest (least step change) %s%s' % (seed, nmax, tried, kept, top[0][0] if top else None, ' (%d gates)' % len(top[1]['gates']) if top else ''))

def cmd_check(files, trials=40):
    rng = random.Random(1); bad = tot = 0
    for f in files:
        c = load(f); n = c['n']
        if n > 9: continue
        any_gate = core.nots(c) > 1; sl = slack_table(c, any_gate=any_gate); w = core.tables(n, c['gates'])
        for _ in range(trials):
            Q = rng.randrange(1 << n); tot += 1; bad += core.slack(c, Q, w, any_gate) != int(sl[Q])
    print('fast slack table against core.slack: %d of %d agree' % (tot - bad, tot))

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'phi'; files = sys.argv[2:] or ([] if cmd == 'hunt' else default_files())
    {'phi': cmd_phi, 'grad': cmd_grad, 'check': cmd_check, 'mixed': cmd_mixed, 'lp': cmd_lp, 'hunt': cmd_hunt}[cmd](files)
