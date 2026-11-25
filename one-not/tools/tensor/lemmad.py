"""The refuter loop for Lemma D (F1_phc.md) as three chained jobs; the checker and the BottomPay instance builder are REF1_phc.py's.
Lemma D: PHC holds iff for every payer set J  sum_w (c_w(J) - 1) <= |E - J|.  slack(R) = |R| - sum_w (c_w(E - R) - 1); a VIOLATION has slack < 0.
  sweep    --input fano_slack=F    the --top Fano circuits with the least cube slack (the upstream job's output) at all 3^7 mixed states;
                                   plus (--planes K) K random one-NOT switch circuits
                                   on each of AG(2,2), AG(2,3), PG(2,2), PG(2,3); writes the --topk tightest BottomPay instances as SEED lines
                                   (REF1's format plus circuit, Q, D)
  neigh    --input NAME=F ...      takes the --seeds tightest SEED lines of the upstream jobs.  A seed with a circuit: --steps accepted
                                   mutants (fano_corpus moves; correct, one NOT) at all states within distance 2 of the seed state.
                                   A seed without one (REF1 seeds): a deeper payer-set search on the same instance.
  recheck  --input NAME=F ...      every VIOLATION line again, by other code: tensor correctness, instance rebuilt and compared,
                                   U1's matroid partition, a separate component count.  CONFIRMED lines; the summary lists them.
  recheck  --file WITNESS.json     the same for one saved violation; exit 0 iff confirmed (the runner of its finding)
  selftest                         a planted violating instance must be confirmed, a planted non-violation rejected
All take --shard I --of N --out PATH (compute.yml).  Truth tables go through cache.py (kind `tables`).  One SUMMARY line on stdout."""
import os, sys, json, time, random, argparse, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
for p in (HERE, os.path.join(ROOT, 'one-not', 'tools', 'fano'), os.path.join(ROOT, 'one-not', 'research', 'open')): sys.path.insert(0, p)
import bits, cache
import fano_corpus as F
import REF1_phc as R

def wires(c):
    """(W, X) in A7's format (Python-int truth tables), from the cached tensor tables."""
    T = cache.get('tables', c, lambda: bits.tables(c)); W = [bits.to_int(r) for r in T]
    return W, W[:c['n']]

def circ(c): return {'n': c['n'], 'sets': [list(s) for s in c['sets']], 'gates': [list(g) for g in c['gates']], 'outs': list(c['outs'])}

def fano_corpus():
    allc = [('FANO-FORMULA', F.fano_formula())]; sd = F.seeds(); allc += [('seed%d' % i, c) for i, c in enumerate(sd)]
    for r in (1, 2): allc += F.walk(sd, r)
    seen, out = set(), []
    for src, c in allc:
        key = json.dumps([c['gates'], c['outs']])
        if key not in seen: seen.add(key); out.append((src, c))
    return out                                                       # the order of shard_fano.load: index j matches fano_slack's "j"

def all_states(n):
    for code in itertools.product(range(3), repeat=n):
        yield {v for v in range(n) if code[v] == 1}, {v for v in range(n) if code[v] == 2}

def near_states(n, Q, D, dist=2):
    base = [1 if v in Q else 2 if v in D else 0 for v in range(n)]
    for k in range(dist + 1):
        for pos in itertools.combinations(range(n), k):
            for vals in itertools.product((1, 2), repeat=k):
                code = list(base)
                for p, d in zip(pos, vals): code[p] = (code[p] + d) % 3
                yield {v for v in range(n) if code[v] == 1}, {v for v in range(n) if code[v] == 2}

class Top:
    """the k tightest instances seen: least slack, then most tight deletion sets, then most useful payers."""
    def __init__(self, k): self.k = k; self.rows = []; self.seen = set(); self.viol = []; self.n = 0; self.tight = 0; self.lo = None
    def add(self, inst, r, family, info, c=None, Q=None, D=None):
        self.n += 1; mn = r['min_nontriv']
        if r['min_all'] < 0:
            js = inst.to_json(); js['R'] = [inst.useful[i] for i in range(inst.m) if r['arg'] >> i & 1]
            v = {'sha256': R.sha(js), 'slack': r['min_all'], 'family': family, 'info': info, 'instance': js}
            if c is not None: v.update(circuit=circ(c), Q=sorted(Q), D=sorted(D))
            self.viol.append(v); return
        if mn is None: return
        self.lo = mn if self.lo is None else min(self.lo, mn); self.tight += mn == 0
        key = (mn, -r['tight'], -inst.m)
        if len(self.rows) >= self.k and key >= self.rows[-1][0]: return
        js = inst.to_json(); h = R.sha(js)
        if h in self.seen: return
        self.seen.add(h)
        sd = {'slack': mn, 'family': family, 'useful_payers': inst.m, 'tight_R': r['tight'], 'info': info, 'instance': js, 'sha256': h}
        if c is not None: sd.update(circuit=circ(c), Q=sorted(Q), D=sorted(D))
        self.rows.append((key, h, sd)); self.rows.sort(key=lambda t: t[:2]); del self.rows[self.k:]
    def write(self, f):
        for v in self.viol: f.write(json.dumps({'VIOLATION': v}, default=str) + '\n')
        for _, _, sd in self.rows: f.write(json.dumps({'SEED': sd}, default=str) + '\n')

def check_circuit(c, states, rng, top, family, src):
    W, X = wires(c)
    for Q, D in states:
        inst = R.bottompay_instances(c, W, X, Q, D, rng)
        if inst is not None: top.add(inst, R.check(inst, rng), family, [src, sorted(Q), sorted(D)], c, Q, D)

def tagged(inputs, tag):
    out = []
    for spec in inputs or []:
        name, _, path = spec.partition('=')
        for line in open(path, encoding='utf-8'):
            if not line.startswith('{"%s"' % tag): continue
            d = json.loads(line)[tag]; d['from'] = name; out.append(d)
    return out

def planes():
    """AG(2,q) and PG(2,q) line systems for q = 2, 3 (and AG(2,4)): name -> (n, lines)."""
    out = {}
    for q in (2, 3):
        pts = [(x, y) for x in range(q) for y in range(q)]; ix = {p: i for i, p in enumerate(pts)}
        L = [[ix[(x, (m * x + b) % q)] for x in range(q)] for m in range(q) for b in range(q)] + [[ix[(x, y)] for y in range(q)] for x in range(q)]
        out['AG(2,%d)' % q] = (q * q, L)
        P = [v for v in itertools.product(range(q), repeat=3) if any(v) and next(x for x in v if x) == 1]
        out['PG(2,%d)' % q] = (len(P), [[i for i, p in enumerate(P) if sum(a * b for a, b in zip(l, p)) % q == 0] for l in P])
    return out

def sweep_planes(a, top):
    """--planes K: K random correct one-NOT switch circuits (REF1's generator) per plane, sampled mixed states."""
    n_c = 0
    for name, (n, L) in sorted(planes().items()):
        rng = random.Random('%s/%d' % (name, a.shard))
        for i in range(a.planes):
            c = R.switch_circuit(rng, L, n)
            if not F.correct(c): continue
            st = all_states(n) if 3 ** n <= 2200 else R.states_for(c, rng, a.nsamp)
            check_circuit(c, st, rng, top, name, '%s:%d:%d' % (name, a.shard, i)); n_c += 1
    return n_c

def sweep(a):
    rows = []
    for spec in a.input or []:
        for line in open(spec.partition('=')[2]):
            d = json.loads(line)
            if 'j' in d and 'min' in d: rows.append((d['min'], -d['neg'], d['sum'], d['j']))
    rows.sort(); pick = [r[3] for r in rows[:a.top]]; mine = [j for i, j in enumerate(pick) if i % a.of == a.shard]
    corp = fano_corpus(); print('fano_slack rows', len(rows), 'seeded circuits', len(pick), 'mine', len(mine), 'corpus', len(corp), flush=True)
    top = Top(a.topk); rng = random.Random(7 + a.shard)
    for j in mine:
        src, c = corp[j]; check_circuit(c, all_states(c['n']), rng, top, 'fano', '%s#%d' % (src, j))
    npl = sweep_planes(a, top) if a.planes else 0
    with open(a.out, 'w') as f: top.write(f)
    return {'circuits': len(mine), 'plane_circuits': npl, 'instances': top.n, 'tight_instances': top.tight, 'min_nontrivial_slack': top.lo, 'violations': len(top.viol), 'seeds_out': len(top.rows)}

def inst_of(js):
    fix = lambda x: tuple(x) if isinstance(x, list) else x
    cls = [[fix(x) for x in cw] for cw in js['cls']]
    return R.Inst([int(g) for g in js['E']], cls, [{int(g): frozenset(fix(x) for x in h) for g, h in hw.items()} for hw in js['hyp']])

def neigh(a):
    seeds = {}
    for sd in tagged(a.input, 'SEED'): seeds.setdefault(sd['sha256'], sd)
    order = sorted(seeds.values(), key=lambda s: (s['slack'], -s['tight_R'], -s['useful_payers'], s['sha256']))[:a.seeds]
    mine = [s for i, s in enumerate(order) if i % a.of == a.shard]; print('seeds', len(seeds), 'taken', len(order), 'mine', len(mine), flush=True)
    top = Top(a.topk); mut = deep = 0; t0 = time.time()
    for sd in mine:
        rng = random.Random(int(sd['sha256'][:8], 16))
        if 'circuit' not in sd:                                       # REF1 seed: the instance only; search its payer sets harder
            inst = inst_of(sd['instance']); deep += 1
            top.add(inst, R.check(inst, rng, climbs=a.climbs), sd['family'], sd.get('info')); continue
        c0 = circ(sd['circuit']); Q, D = set(sd['Q']), set(sd['D']); cur = c0; seen = {json.dumps(c0['gates'])}; got = tries = 0
        while got < a.steps and tries < 60 * a.steps and time.time() - t0 < a.budget:
            tries += 1
            if tries % 40 == 0: cur = c0
            c2 = F.bypass(cur, rng) if rng.random() < 0.25 else F.mutate(cur, rng)
            if c2 is None or len(c2['gates']) > len(c0['gates']) + 6 or sum(g[0] == 'not' for g in c2['gates']) != 1: continue
            key = json.dumps(c2['gates'])
            if key in seen or not F.correct(c2): continue
            seen.add(key); cur = c2; got += 1; mut += 1
            check_circuit(c2, near_states(c2['n'], Q, D), rng, top, sd['family'] + '~', str(sd.get('info', [''])[0]) + '~%d' % got)
    with open(a.out, 'w') as f: top.write(f)
    return {'seeds': len(mine), 'mutants': mut, 'deep_searches': deep, 'instances': top.n, 'tight_instances': top.tight, 'min_nontrivial_slack': top.lo, 'violations': len(top.viol)}

def comps2(classes, edges):
    """components by repeated merging of sets (written apart from REF1's union-find)."""
    blocks = [{x} for x in classes]
    for e in edges:
        hit = [b for b in blocks if b & set(e)]; rest = [b for b in blocks if not (b & set(e))]
        blocks = rest + [set().union(*hit)] if hit else rest
    return len(blocks)

def confirm(v):
    """independent recheck of one violation record; returns (ok, notes)."""
    import U1_payment_hall as U1
    notes = {}; js = v['instance']; inst = inst_of(js); K = len(inst.cls)
    if v.get('circuit'):
        c = v['circuit']
        notes['circuit_correct'] = bool(bits.correct(c)) and sum(g[0] == 'not' for g in c['gates']) == 1
        notes['sets_linear'] = all(len(set(x) & set(y)) <= 1 for x, y in itertools.combinations(c['sets'], 2))
        T = bits.tables(c); W = [bits.to_int(r) for r in T]                       # not from the cache
        again = R.bottompay_instances(c, W, W[:c['n']], set(v['Q']), set(v['D']), random.Random(0))
        notes['instance_rebuilt'] = again is not None and again.to_json() == {k: js[k] for k in ('E', 'cls', 'hyp')}
    sets = [({x: x for x in inst.cls[w]}, {g: [inst.hyp[w][g]] for g in inst.E if len(inst.hyp[w].get(g, ())) >= 2}) for w in range(K)]
    ranks, ok = U1.partition(list(inst.E), sets)
    notes['phc_fails_by_partition'] = not (ok and ranks == [len(x) - 1 for x in inst.cls])
    Rset = set(js.get('R', [])); J = [g for g in inst.E if g not in Rset]
    s = len(Rset & set(inst.E)) - sum(comps2(inst.cls[w], [inst.hyp[w][g] for g in J if len(inst.hyp[w].get(g, ())) >= 2]) - 1 for w in range(K))
    notes['slack_recount'] = s; notes['slack_negative'] = s < 0
    return all(x for k, x in notes.items() if k != 'slack_recount'), notes

def recheck(a):
    if a.file:
        ok, notes = confirm(json.load(open(a.file))); print(json.dumps(notes)); print(json.dumps({'states': 1}))
        sys.exit(0 if ok else 1)
    vs = tagged(a.input, 'VIOLATION'); mine = [v for i, v in enumerate(vs) if i % a.of == a.shard]; good = []; bad = 0
    with open(a.out, 'w') as f:
        for v in mine:
            ok, notes = confirm(v); v['recheck'] = notes
            f.write(json.dumps({'CONFIRMED' if ok else 'REJECTED': v}, default=str) + '\n')
            if ok: good.append(v)
            else: bad += 1
    return {'violations_in': len(mine), 'confirmed': good, 'rejected': bad}

def selftest():
    # two sets {0,1,2}, {3,4,5}; one payer joins all of both: deleting nothing leaves c = (1, 1), so R = {} has slack 0, fine;
    # PHC needs rank 2 + 2 = 4 from one payer: Lemma D fails at R = {} only if components stay apart, so plant: no useful payer at all.
    bad = {'E': [0], 'cls': [[0, 1, 2], [3, 4, 5]], 'hyp': [{'0': [0, 1]}, {'0': [3, 4]}], 'R': []}
    good = {'E': [0, 1, 2, 3], 'cls': [[0, 1, 2], [3, 4, 5]], 'hyp': [{'0': [0, 1], '1': [1, 2], '2': [], '3': []}, {'0': [], '1': [], '2': [3, 4], '3': [4, 5]}], 'R': []}
    a, na = confirm({'instance': bad}); b, nb = confirm({'instance': good})
    print('selftest: planted violation confirmed', a, na, '| sound instance rejected', not b, nb)
    return a and not b

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('mode', choices=['sweep', 'neigh', 'recheck', 'selftest'])
    ap.add_argument('--input', action='append'); ap.add_argument('--shard', type=int, default=0); ap.add_argument('--of', type=int, default=1); ap.add_argument('--out', default=os.devnull)
    ap.add_argument('--top', type=int, default=2000); ap.add_argument('--topk', type=int, default=20); ap.add_argument('--seeds', type=int, default=40)
    ap.add_argument('--steps', type=int, default=150); ap.add_argument('--climbs', type=int, default=3000); ap.add_argument('--budget', type=float, default=1200); ap.add_argument('--file'); ap.add_argument('--planes', type=int, default=0); ap.add_argument('--nsamp', type=int, default=200)
    a = ap.parse_args(); t0 = time.time()
    if a.mode == 'selftest': sys.exit(0 if selftest() else 1)
    s = {'sweep': sweep, 'neigh': neigh, 'recheck': recheck}[a.mode](a)
    s['seconds'] = round(time.time() - t0, 1)
    print('SUMMARY ' + json.dumps(s, separators=(',', ':'), default=str), flush=True)

if __name__ == '__main__': main()
