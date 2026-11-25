"""Seat REF1: refuter for PHC, checking Lemma D's inequality (F1_phc.md) on generated and stored instances.
Lemma D:  PHC <=> for every payer set J:  sum_w (c_w(J) - 1) <= |E - J|.   slack(J) = |E - J| - sum_w (c_w(J) - 1).
A VIOLATION is an instance with some J of slack < 0.  (J = E always has slack 0, so min slack <= 0; "tightest" below means
the smallest slack over J != E, a nonempty deletion set R = E - J.)
Repo root:
  nice python3 -I one-not/research/open/REF1_phc.py --shard i --of N [--out F.jsonl] [--scale S] [--budget SEC] [--only stored,sys,prog]
  nice python3 -I one-not/research/open/REF1_phc.py --selftest          (checker against U1's matroid partition on random instances)
  nice python3 -I one-not/research/open/REF1_phc.py --recheck F.json     (independent recheck of a saved instance with U1 + A14)
Work units (unit u goes to shard u % N), three families:
  stored : BottomPay instances (F1/A7 setup) from stored one-NOT circuits (n <= 12), DD states at Q=D=0 and sampled states
  sys    : random correct one-NOT switch circuits on linear set systems (Fano, Pasch, grids, K4/C5/C6 edge sets, random),
           DD states sampled (exhaustive when 3^n is small)
  prog   : two-set point programs (B9 encoding via SAT) at K = base, base+1, base+2 lines, PHC@0 (U1 setup)
J search: exhaustive over useful payers when <= EXH of them, else all |R| <= 3 plus hill-climbing restarts (R cutting one set).
Output: one JSON line per unit; violations carry the full instance and its sha256.  Shard prints 'SUMMARY {...}' to stdout.
"""
import sys, os, json, random, time, itertools, collections, hashlib, argparse
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
EXH = 14
NCIRC = 30

# ---------------------------------------------------------------- the Lemma D checker
def comps(classes, edges):
    lab = {c: c for c in classes}
    def fd(c):
        while lab[c] != c: lab[c] = lab[lab[c]]; c = lab[c]
        return c
    k = len(classes)
    for e in edges:
        e = list(e); r = fd(e[0])
        for x in e[1:]:
            s = fd(x)
            if s != r: lab[s] = r; k -= 1
    return k

class Inst:
    """payers E, per set w: classes cls[w], hyperedge hyp[w][g] (frozenset of classes)."""
    def __init__(self, E, cls, hyp):
        self.cls = cls; self.K = len(cls)
        self.useful = [g for g in E if any(len(hyp[w][g]) >= 2 for w in range(self.K))]
        self.m = len(self.useful)
        self.ed = [[[hyp[w][g] for g in self.useful][i] if len(hyp[w][self.useful[i]]) >= 2 else None for i in range(self.m)] for w in range(self.K)]
        self.hyp = hyp; self.E = E
    def slack(self, mask):
        """mask = R (deleted payers, bit i = useful[i] NOT in J)."""
        s = bin(mask).count('1')
        for w in range(self.K):
            s -= comps(self.cls[w], [self.ed[w][i] for i in range(self.m) if not mask >> i & 1 and self.ed[w][i] is not None]) - 1
        return s
    def to_json(self):
        return {'E': list(self.E), 'cls': [list(c) for c in self.cls],
                'hyp': [{str(g): sorted(h, key=str) for g, h in hw.items()} for hw in self.hyp]}

def check(inst, rng, climbs=60):
    """returns dict(min_all, min_nontriv, argmask, tight, exhaustive)"""
    m = inst.m
    if m == 0: s0 = inst.slack(0); return dict(min_all=min(s0, 0), min_nontriv=None, arg=0, tight=0, exh=True)
    best = None; arg = 0; tight = 0; bestall = 0; argall = 0
    def note(mask, s):
        nonlocal best, arg, tight, bestall, argall
        if s < bestall: bestall, argall = s, mask
        if mask and (best is None or s < best): best, arg = s, mask
    if m <= EXH:
        note(0, inst.slack(0))
        for mask in range(1, 1 << m):
            s = inst.slack(mask); note(mask, s); tight += s == 0
        return dict(min_all=bestall, min_nontriv=best, arg=arg if bestall >= 0 else argall, tight=tight, exh=True)
    seen = {}
    def S(mask):
        if mask not in seen: seen[mask] = inst.slack(mask); note(mask, seen[mask]);
        return seen[mask]
    S(0)
    for r in (1, 2, 3):
        for c in itertools.combinations(range(m), r): S(sum(1 << i for i in c))
    full = (1 << m) - 1
    for _ in range(climbs):
        mask = sum(1 << i for i in range(m) if rng.random() < rng.choice([.15, .3, .5, .7]))
        if not mask: mask = 1 << rng.randrange(m)
        cur = S(mask)
        for _ in range(4 * m):
            i = rng.randrange(m); nm = mask ^ (1 << i)
            if not nm: continue
            ns = S(nm)
            if ns <= cur: mask, cur = nm, ns
    tight = sum(1 for s in seen.values() if s == 0)
    return dict(min_all=bestall, min_nontriv=best, arg=argall if bestall < 0 else arg, tight=tight, exh=False)

# ---------------------------------------------------------------- instance builders
def sha(obj): return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

class Stats:
    def __init__(self): self.c = collections.Counter(); self.hist = collections.Counter(); self.tight = []; self.viol = []
    def add(self, inst, r, tag, info, rng_seed=0):
        self.c[tag + '.instances'] += 1; self.c[tag + '.exhaustive' if r['exh'] else tag + '.targeted'] += 1
        mn = r['min_nontriv']
        if mn is not None:
            self.hist[tag + ' ' + str(max(min(mn, 6), -6))] += 1; self.c[tag + '.tight_R_total'] += r['tight']
        else: self.c[tag + '.trivial'] += 1
        if r['min_all'] < 0:
            js = inst.to_json(); js['R'] = [inst.useful[i] for i in range(inst.m) if r['arg'] >> i & 1]; js['tag'] = tag; js['info'] = info
            self.viol.append({'sha256': sha(js), 'instance': js, 'slack': r['min_all']})
        elif mn is not None:
            self.tight.append((mn, tag, inst.m, r['tight'], info, inst.to_json() if mn <= 1 else None))
            if len(self.tight) > 400: self.tight = sorted(self.tight, key=lambda t: (t[0], -t[2]))[:50]

def bottompay_instances(c, W, X, Q, D, rng):
    """yield the BottomPay instance of circuit c at mixed state (Q, D), or None (F1_phc_tight.dd setup)."""
    import A7_dd_absorb_attack as A7, A10_light_attack as A10
    n, G, S = c['n'], c['gates'], c['sets']; ALL = (1 << n) - 1
    p = [i for i, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]
    qpt = sum(1 << v for v in Q); top = set(); dds = []
    for w, R in enumerate(S):
        if set(R) & Q: continue
        R2 = [u for u in R if u not in D]
        if len(R2) < 2: continue
        zw = ALL
        for u in R2 + list(D): zw &= ~(1 << u)
        P = {u: qpt | 1 << u for u in R2}
        if not (a >> zw & 1 and any(not (a >> P[u] & 1) for u in R2)):
            top |= set(A10.uf_run(G, W, n, zw, P)); continue
        U = [u for u in R2 if a >> P[u] & 1]
        if len(U) >= 2: top |= set(A10.uf_run(G, W, n, zw, {u: P[u] for u in U}))
        dds.append((w, R2, P, {u: ('H' if u in U else u) for u in R2}))
    if len(dds) < 2: return None
    ORs = [i for i in range(len(G)) if G[i][0] == 'or' and not W[n + i] >> qpt & 1]
    E = [i for i in ORs if i not in top]
    cls = [sorted(set(d[3].values()), key=str) for d in dds]
    hyp = [{i: frozenset(d[3][u] for u in d[1] if W[n + i] >> d[2][u] & 1) for i in ORs} for d in dds]
    return Inst(E, cls, hyp)

def switch_circuit(rng, sets, n):
    """correct one-NOT switch circuit on the given sets (A7.gen_switch generalised to a fixed set system)."""
    G = []
    def gate(op, *a): G.append([op] + list(a)); return n + len(G) - 1
    def OR(items):
        items = list(items); rng.shuffle(items)
        while len(items) > 1:
            x = items.pop(); y = items.pop(); items.insert(rng.randint(0, len(items)), gate('or', x, y))
        return items[0]
    terms = [gate('and', *rng.sample(range(n), rng.choice([2, 2, 3]))) for _ in range(rng.randint(1, 5))]
    h = OR(terms); g = gate('not', h); outs = []
    for R in sets:
        T = [u for u in R if rng.random() < 0.5]; U = [u for u in R if u not in T]
        if not U: outs.append(OR(R)); continue
        y = OR(U); parts = list(T) + [gate('and', h, y), gate('and', g, y)]
        outs.append(OR(parts))
    return {'n': n, 'sets': [list(s) for s in sets], 'gates': G, 'outs': outs, 'name': 'sw'}

def linear_systems(rng):
    fano = [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]
    pasch = [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]
    g33 = [[3 * r + c for c in range(3)] for r in range(3)] + [[3 * c + r for c in range(3)] for r in range(3)]
    g34 = [[4 * r + c for c in range(4)] for r in range(3)] + [[4 * r + c for r in range(3)] for c in range(4)]
    k4 = [[a, b] for a, b in itertools.combinations(range(4), 2)]
    c5 = [[i, (i + 1) % 5] for i in range(5)]; c6 = [[i, (i + 1) % 6] for i in range(6)]
    petri = [[0, 1, 2], [2, 3, 4], [4, 5, 0], [1, 3, 5]]            # a 4-cycle of triples (hexagon plus one transversal)
    mixed = [[0, 1, 2], [2, 3], [3, 4, 5], [5, 0], [1, 4]]
    return {'fano': (7, fano), 'pasch': (6, pasch), 'grid33': (9, g33), 'grid34': (12, g34), 'k4': (4, k4), 'c5': (5, c5), 'c6': (6, c6),
            'tri4cyc': (6, petri), 'mixed': (6, mixed)}

def random_linear(rng):
    n = rng.randint(6, 11); sets = []
    for _ in range(rng.randint(3, 7)):
        R = sorted(rng.sample(range(n), rng.randint(2, 4)))
        if all(len(set(R) & set(x)) <= 1 for x in sets): sets.append(R)
    return n, sets

def states_for(c, rng, nsamp):
    import A7_dd_absorb_attack as A7
    n = c['n']
    if 3 ** n <= 2200:
        yield from A7.states(n, rng, -1); return
    yield set(), set()
    for v in range(n): yield {v}, set(); yield set(), {v}
    for _ in range(nsamp):
        Q, D = set(), set()
        for v in range(n):
            r = rng.random()
            if r < 0.12: Q.add(v)
            elif r < 0.35: D.add(v)
        yield Q, D

def run_circuit(c, rng, nsamp, S, tag, info, dedupe, deadline):
    import A7_dd_absorb_attack as A7
    W, X, FULL = A7.tables(c['n'], c['gates'])
    if not A7.correct(c, W, X): S.c[tag + '.incorrect_circuit'] += 1; return
    if any(len(set(x) & set(y)) > 1 for x, y in itertools.combinations(c['sets'], 2)): return
    S.c[tag + '.circuits'] += 1
    for Q, D in states_for(c, rng, nsamp):
        if time.time() > deadline: S.c['budget_stop'] += 1; return
        inst = bottompay_instances(c, W, X, Q, D, rng)
        if inst is None: continue
        S.c[tag + '.dd_states'] += 1
        key = (tuple(map(tuple, inst.cls)), tuple(tuple(sorted(map(str, e))) if e is not None else () for row in inst.ed for e in row))
        if key in dedupe: S.c[tag + '.duplicates'] += 1; continue
        dedupe.add(key)
        S.add(inst, check(inst, rng), tag, [c.get('name', '')[-50:], sorted(Q), sorted(D)])

PROG_CFG = [(p, q, sh) for (p, q) in [(3, 3), (3, 4), (4, 4), (3, 5), (4, 5), (5, 5), (2, 4), (2, 6), (3, 6)] for sh in (True, False)]

def run_prog(unit, rng, S, deadline, cap):
    from B9_two_sets import build
    from pysat.solvers import Solver
    p, q, sh, dK, seed = unit
    if sh: Wt = [list(range(p)), [0] + list(range(p, p + q - 1))]; n = p + q - 1
    else: Wt = [list(range(p)), list(range(p, p + q))]; n = p + q
    K = (p - 1) + (q - 1) + dK; tag = 'prog(%d,%d,%s)+%d' % (p, q, 's' if sh else 'd', dK)
    cl, X, meta, new = build(n, Wt, K); nv = new()
    cnt = 0; r2 = random.Random(seed)
    s = Solver(name='g3', bootstrap_with=cl)
    s.set_phases([v if r2.random() < .5 else -v for v in range(1, nv)])
    while cnt < cap and time.time() < deadline and s.solve():
        m = set(v for v in s.get_model() if v > 0); cnt += 1
        vals = [frozenset(u for u in range(n) if X[i][u] in m) for i in range(K)]
        ops = [[k for k in range(4) if meta[i][2][k] in m][0] for i in range(K)]
        hyp = [{i: vals[i] & frozenset(R) for i in range(K)} for R in Wt]
        inst = Inst(list(range(K)), [list(R) for R in Wt], hyp)
        S.add(inst, check(inst, rng), tag, [[sorted(v) for v in vals], ops])
        # random restart of the phases: diversify instead of walking the blocking-clause order
        s.add_clause([-X[i][u] if X[i][u] in m else X[i][u] for i in range(K) for u in range(n)])
        if cnt % 40 == 0: s.set_phases([v if r2.random() < .5 else -v for v in range(1, nv)])
    s.delete()

def units(scale):
    import A7_dd_absorb_attack as A7
    U = []
    stored = A7.collect(12)
    for j in range(len(stored)): U.append(('stored', j))
    for name in sorted(linear_systems(random.Random(0))):
        for seed in range(int(6 * scale)): U.append(('sys', name, seed))
    for seed in range(int(30 * scale)): U.append(('rand', seed))
    for (p, q, sh) in PROG_CFG:
        for dK in (0, 1, 2):
            for seed in range(max(1, int(2 * scale))): U.append(('prog', p, q, sh, dK, seed))
    return U, stored

def recheck(path):
    """independent recheck of a saved instance: U1's matroid partition (PHC proper) and A14's Edmonds partition."""
    import U1_payment_hall as U1, A14_bottom_hall as A14
    d = json.load(open(path)); inst = d['instance'] if 'instance' in d else d
    cls = [[tuple(c) if isinstance(c, list) else c for c in cw] for cw in inst['cls']]
    K = len(cls); E = inst['E']
    def key(x): return x
    hyp = [{int(g): frozenset(h) for g, h in hw.items()} for hw in inst['hyp']]
    sets = [({c: c for c in cls[w]}, {int(g): [hyp[w][int(g)]] for g in E if len(hyp[w].get(int(g), ())) >= 2}) for w in range(K)]
    ranks, ok = U1.partition([int(g) for g in E], sets)
    ok = ok and ranks == [len(c) - 1 for c in cls]; print('U1.partition: ranks', ranks, 'need', [len(c) - 1 for c in cls], 'PHC', ok)
    assign, I, reach = A14.partition([int(g) for g in E], hyp, K)
    print('A14.partition union', sum(len(I[w]) for w in range(K)), 'sum need', sum(len(c) - 1 for c in cls))
    R = set(inst.get('R', [])); J = [g for g in E if g not in R]
    c = [comps(cls[w], [hyp[w][int(g)] for g in J if len(hyp[w][int(g)]) >= 2]) for w in range(K)]
    print('J = E - R, R =', sorted(R), 'c_w(J) =', c, 'sum(c-1) =', sum(x - 1 for x in c), '|E-J| =', len(R))

def selftest():
    import U1_payment_hall as U1
    rng = random.Random(5); bad = viol = tot = 0
    for _ in range(1500):
        K = rng.randint(2, 3); m = rng.randint(2, 7)
        cls = [list(range(rng.randint(2, 4))) for _ in range(K)]
        hyp = [{g: frozenset(x for x in cls[w] if rng.random() < rng.choice([.3, .5, .7])) for g in range(m)} for w in range(K)]
        inst = Inst(list(range(m)), cls, hyp); r = check(inst, rng)
        sets = [({c: c for c in cls[w]}, {g: [hyp[w][g]] for g in range(m) if len(hyp[w][g]) >= 2}) for w in range(K)]
        ranks, ok = U1.partition(list(range(m)), sets); ok = ok and ranks == [len(c) - 1 for c in cls]
        mine = r['min_all'] >= 0; tot += 1; viol += not mine; bad += mine != ok
    print('selftest: instances', tot, 'Lemma-D violations', viol, 'disagreements with U1 partition', bad)
    return bad == 0

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--shard', type=int, default=0); ap.add_argument('--of', type=int, default=1); ap.add_argument('--out', default='/dev/null')
    ap.add_argument('--scale', type=float, default=1.0); ap.add_argument('--budget', type=float, default=1e9)
    ap.add_argument('--only', default='stored,sys,rand,prog'); ap.add_argument('--nsamp', type=int, default=250); ap.add_argument('--cap', type=int, default=400)
    ap.add_argument('--topk', type=int, default=20); ap.add_argument('--seeds'); ap.add_argument('--selftest', action='store_true'); ap.add_argument('--recheck')
    a = ap.parse_args()
    if a.selftest: sys.exit(0 if selftest() else 1)
    if a.recheck: recheck(a.recheck); return
    only = set(a.only.split(',')); t0 = time.time(); deadline = t0 + a.budget
    U, stored = units(a.scale); S = Stats(); dedupe = set(); systems = linear_systems(random.Random(0))
    mine = [(j, u) for j, u in enumerate(U) if j % a.of == a.shard and u[0] in only]
    print('units total', len(U), 'mine', len(mine), flush=True)
    with open(a.out, 'w') as f:
        for j, u in mine:
            if time.time() > deadline: S.c['budget_stop_units'] += 1; continue
            rng = random.Random(1000 * j + 17); before = (sum(S.c[k] for k in S.c if k.endswith('.instances')), len(S.viol))
            if u[0] == 'stored': run_circuit(stored[u[1]], rng, a.nsamp, S, 'stored', None, dedupe, deadline)
            elif u[0] == 'sys':
                n, sets = systems[u[1]]
                for _ in range(NCIRC):
                    c = switch_circuit(rng, sets, n); c['name'] = 'sys:%s:%d' % (u[1], u[2]); run_circuit(c, rng, a.nsamp, S, 'sys:' + u[1], None, dedupe, deadline)
            elif u[0] == 'rand':
                for _ in range(NCIRC):
                    n, sets = random_linear(rng)
                    if len(sets) < 2: continue
                    c = switch_circuit(rng, sets, n); c['name'] = 'rand:%d' % u[1]; run_circuit(c, rng, a.nsamp, S, 'rand', None, dedupe, deadline)
            else: run_prog(u[1:], rng, S, deadline, a.cap)
            after = (sum(S.c[k] for k in S.c if k.endswith('.instances')), len(S.viol))
            f.write(json.dumps({'unit': j, 'u': list(u), 'instances': after[0] - before[0], 'violations': after[1] - before[1]}) + '\n')
        for v in S.viol: f.write(json.dumps({'VIOLATION': v}) + '\n')
        S.tight.sort(key=lambda t: (t[0], -t[2], -t[3]))
        seeds = [{'slack': t[0], 'family': t[1], 'useful_payers': t[2], 'tight_R': t[3], 'info': t[4], 'instance': t[5], 'sha256': sha(t[5])} for t in S.tight[:a.topk] if t[5]]
        for sd in seeds: f.write(json.dumps({'SEED': sd}, default=str) + '\n')
        if a.seeds: json.dump(seeds, open(a.seeds, 'w'), default=str)
    summ = {'shard': a.shard, 'of': a.of, 'seconds': round(time.time() - t0, 1), 'counts': dict(S.c), 'min_slack_hist': dict(S.hist),
            'violations': [{'sha256': v['sha256'], 'slack': v['slack'], 'instance': v['instance']} for v in S.viol],
            'tightest': [list(t[:5]) for t in S.tight[:6]]}
    print('SUMMARY ' + json.dumps(summ, separators=(',', ':'), default=str), flush=True)

if __name__ == '__main__': main()
