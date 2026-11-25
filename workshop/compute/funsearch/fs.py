#!/usr/bin/env python3
"""FunSearch-style loop (Romera-Paredes et al., Nature 2023) over the exact evaluators of this repository.  Task: model-in-the-loop.
    target   = statement + program skeleton + exact evaluator (targets.py; generated from the repository)
    proposer = Qwen (proposer.py) writes new versions of the skeleton, conditioned on the best programs so far
    sandbox  = every proposal runs in its own process without network (sandbox.py); only its JSON result returns
    evaluator= the tensor backend scores a whole batch of results at once (evalbatch.py) and gives score and verdict
    database = islands of programs clustered by score signature; parents are sampled from good clusters, short programs first;
               the worst half of the islands is reset from the survivors every --reset registered programs
The model supplies guesses.  A verdict is only ever the evaluator's; a board word is only ever given after the independent
evaluator (recheck.py) confirms it in a separate process or job (`fs.py record`), and `checked` only by Lean.

  fs.py targets                                             the registry
  fs.py run --target k1:small --proposer hf --model PATH --minutes 20 --out DIR [--islands 4 --batch 4 --k 2 --seed 0]
  fs.py run --target k1:fano --proposer mutate --samples 200 --out DIR          (no model: tests the loop)
  fs.py record DIR --who SEAT [--dry]     recheck every best / candidate witness of a run in separate processes, copy the confirmed
                                          ones to compute/funsearch/results/ and add findings (boards.py add --runner)
git-compute: entry.py (workshop/compute/funsearch/specs/*.json).  Run from the repository root."""
import os, sys, json, time, math, random, hashlib, argparse, subprocess, concurrent.futures
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..')); sys.path.insert(0, HERE)
import sandbox, targets as T, proposer as P                                   # noqa: E402

def sha(s): return hashlib.sha256(s.encode()).hexdigest()[:16]

class DB:
    """Islands of clusters.  A cluster = the programs with one score signature; its rank is the evaluator's rank."""
    def __init__(self, islands=4, reset=60, T0=0.3, period=40, rng=None):
        self.isl = [dict() for _ in range(islands)]; self.prog = {}; self.reset_every, self.T0, self.period = reset, T0, period
        self.rng = rng or random.Random(0); self.count = [0] * islands; self.since = 0; self.resets = 0
    def register(self, i, src, res):
        h = sha(src)
        if h in self.prog: return False
        self.prog[h] = {'src': src, 'rank': res['rank'], 'score': res['score'], 'verdict': res['verdict'], 'detail': res['detail'], 'island': i}
        sig = json.dumps(res['signature']); c = self.isl[i].setdefault(sig, {'rank': res['rank'], 'progs': []}); c['progs'].append(h)
        self.count[i] += 1; self.since += 1
        if self.since >= self.reset_every: self.reset()
        return True
    def best(self, i=None):
        hs = [h for h, p in self.prog.items() if i is None or p['island'] == i]
        return max(hs, key=lambda h: (self.prog[h]['rank'], -len(self.prog[h]['src']))) if hs else None
    def sample(self, i, k):
        cl = list(self.isl[i].values())
        if not cl: return []
        hi = max(c['rank'] for c in cl); lo = min(c['rank'] for c in cl); span = (hi - lo) or 1.0
        temp = self.T0 * (1 - (self.count[i] % self.period) / self.period) + 1e-3
        w = [math.exp((c['rank'] - hi) / span / temp) for c in cl]; picks = []
        for _ in range(min(k, len(cl))):
            j = self.rng.choices(range(len(cl)), w)[0]; c = cl[j]; w[j] = 0.0
            ln = [len(self.prog[h]['src']) for h in c['progs']]; m = min(ln); sp = (max(ln) - m) or 1
            picks.append(self.rng.choices(c['progs'], [math.exp(-(x - m) / sp) for x in ln])[0])
            if not any(w): break
        return sorted(picks, key=lambda h: self.prog[h]['rank'])
    def reset(self):
        self.since = 0; order = sorted(range(len(self.isl)), key=lambda i: self.prog[self.best(i)]['rank'] if self.best(i) else -1e18)
        half = len(order) // 2
        if not half: return
        for i in order[:half]:
            donor = self.best(self.rng.choice(order[half:]))
            if donor is None: continue
            for h, p in self.prog.items():
                if p['island'] == i: p['island'] = -1                              # kept in the record, out of the islands
            d = self.prog[donor]; self.isl[i] = {'reset:' + donor: {'rank': d['rank'], 'progs': [donor]}}; self.count[i] = 0
        self.resets += 1

def label(p):
    d = p['detail']; bits = []
    for k, v in d.items():
        if isinstance(v, dict): bits.append('%s: %s' % (k, 'score %s' % v['score'] if v.get('verdict') in ('ok', 'VIOLATION-CANDIDATE') else v.get('verdict', '?')) + (', NOT not needed' if v.get('essential') is False and v.get('verdict') == 'ok' else ''))
    return '; '.join(bits)[:160] or 'score %s' % p['score']

def run(a):
    reg = T.registry(); assert a.target in reg, 'unknown target %s (fs.py targets)' % a.target
    tg = reg[a.target]; rng = random.Random(a.seed); os.makedirs(a.out, exist_ok=True)
    for d in ('best', 'candidates'): os.makedirs(os.path.join(a.out, d), exist_ok=True)
    assert sandbox.netns_wrapper() is not None, 'no network namespace: refusing to run model output (sandbox.py)'
    t0 = time.time()
    prop = P.make(a.proposer, a.model, seed=a.seed, **({'threads': a.threads, 'max_new': a.max_new, 'temperature': a.temperature} if a.proposer != 'mutate' else {}),
                  **({'dtype': a.dtype} if a.proposer == 'hf' and a.dtype else {}), **({'pattern': a.gguf_pattern} if a.proposer == 'gguf' else {}))
    load = time.time() - t0
    import evalbatch
    print('target', tg.name, '|', tg.statement); print('proposer', prop.name, '| load %.0f s | evaluator backend %s' % (load, evalbatch.bits._BE[0].name), flush=True)
    db = DB(a.islands, a.reset, rng=rng); log = open(os.path.join(a.out, 'log.jsonl'), 'a'); stat = {'proposed': 0, 'unparsed': 0, 'duplicate': 0, 'ran': 0}
    verd = {}; best = {}; cands = []; pool = concurrent.futures.ThreadPoolExecutor(a.jobs)
    def evaluate(srcs, island, t):
        outs = list(pool.map(lambda s: sandbox.run_program(s, tg.preamble, tg.entry, tg.instances, a.timeout), srcs))
        res = tg.evaluate(outs)
        for s, r in zip(srcs, res):
            stat['ran'] += 1; verd[r['verdict']] = verd.get(r['verdict'], 0) + 1; new = False
            if r['verdict'] != 'invalid': new = db.register(island, s, r)
            for w in r['witnesses']:
                key = w.get('system') or w.get('kind'); val = (w.get('claim', {}).get('score', r['score']), bool(w.get('essential')))
                for tag, ok in (('any', True), ('essential', bool(w.get('essential')))):
                    if ok and (key + '|' + tag not in best or val[0] > best[key + '|' + tag][0]):
                        best[key + '|' + tag] = (val[0], sha(s)); json.dump(w, open(os.path.join(a.out, 'best', '%s.%s.json' % (key.replace('(', '').replace(')', '').replace(',', '_'), tag)), 'w'))
            if r['verdict'] == 'VIOLATION-CANDIDATE':
                for w in r['witnesses']:
                    if w.get('claim', {}).get('score', 1) > 0:
                        p = os.path.join(a.out, 'candidates', sha(json.dumps(w, sort_keys=True)) + '.json'); json.dump(w, open(p, 'w')); cands.append(p)
                        print('CANDIDATE (unconfirmed until recheck.py passes in a separate job, then a second seat):', p, flush=True)
            log.write(json.dumps({'t': round(time.time() - t0, 1), 'island': island, 'hash': sha(s), 'new': new, 'score': r['score'], 'rank': r['rank'], 'verdict': r['verdict'],
                                  'detail': r['detail'], 'error': r['error'], 'src': s,
                                  **({'witnesses': r['witnesses']} if r['verdict'] == 'VIOLATION-CANDIDATE' else {})}) + '\n'); log.flush()
    for i in range(a.islands): evaluate(tg.seeds, i, 0)
    stat['ran'] = 0; verd.clear(); it = 0; deadline = t0 + a.minutes * 60 if a.minutes else None
    while (deadline is None or time.time() < deadline) and (not a.samples or stat['proposed'] < a.samples):
        i = it % a.islands; it += 1
        parents = [(db.prog[h]['src'], label(db.prog[h])) for h in db.sample(i, a.k)]
        got = prop.propose(tg, parents, a.batch); stat['proposed'] += len(got)
        srcs = []
        for s in got:
            if s is None: stat['unparsed'] += 1
            elif sha(s) in db.prog or s in srcs: stat['duplicate'] += 1
            else: srcs.append(s)
        if srcs: evaluate(srcs, i, it)
        b = db.prog[db.best()]
        print('it %d island %d  +%d  proposed %d ran %d  best rank %.4f [%s]  %.0f s' % (it, i, len(srcs), stat['proposed'], stat['ran'], b['rank'], label(b), time.time() - t0), flush=True)
    summ = {'target': tg.name, 'proposer': prop.name, 'backend': evalbatch.bits._BE[0].name, 'seconds': round(time.time() - t0), 'load_seconds': round(load), 'tokens': prop.tokens,
            'islands': a.islands, 'resets': db.resets, 'seed': a.seed, **stat, 'verdicts': verd, 'distinct_programs': len(db.prog),
            'best': {k: v[0] for k, v in sorted(best.items())}, 'candidates': len(cands), 'beat_base': bool(cands)}
    json.dump(summ, open(os.path.join(a.out, 'summary.json'), 'w'), indent=1)
    json.dump({h: p for h, p in sorted(db.prog.items(), key=lambda kv: -kv[1]['rank'])[:20]}, open(os.path.join(a.out, 'top_programs.json'), 'w'), indent=1)
    print('SUMMARY ' + json.dumps(summ), flush=True)
    return summ

def record(a):
    """Separate processes: recheck.py on every witness of the run; only confirmed ones reach the board."""
    summ = json.load(open(os.path.join(a.dir, 'summary.json'))); reg = T.registry(); tg = reg[summ['target']]
    run_id = a.run or os.path.basename(os.path.normpath(a.dir)); dest = os.path.join('compute', 'funsearch', 'results', run_id); ok = []; bad = []
    files = sorted(os.listdir(os.path.join(a.dir, 'best'))) if os.path.isdir(os.path.join(a.dir, 'best')) else []
    cfiles = sorted(os.listdir(os.path.join(a.dir, 'candidates'))) if os.path.isdir(os.path.join(a.dir, 'candidates')) else []
    for sub, fs_ in (('best', files), ('candidates', cfiles)):
        for f in fs_:
            p = os.path.join(a.dir, sub, f); r = subprocess.run(['nice', '-n', '19'] + tg.recheck_cmd(p), capture_output=True, text=True, cwd=ROOT, timeout=3600)
            print(('confirmed ' if r.returncode == 0 else 'REJECTED  ') + p, '|', r.stdout.strip().splitlines()[-1] if r.stdout.strip() else r.stderr[-200:])
            (ok if r.returncode == 0 else bad).append((sub, f))
    if a.dry: return
    os.makedirs(os.path.join(ROOT, dest), exist_ok=True); ev = []
    for sub, f in ok:
        q = os.path.join(dest, ('candidate.' if sub == 'candidates' else '') + f); open(os.path.join(ROOT, q), 'w').write(open(os.path.join(a.dir, sub, f)).read()); ev.append((sub, q))
    json.dump(dict(summ, rejected_by_recheck=[f for _, f in bad]), open(os.path.join(ROOT, dest, 'summary.json'), 'w'), indent=1)
    def add(statement, evidence, runner, confirm):
        rid = hashlib.sha1((statement + 'workshop/compute/funsearch').encode()).hexdigest()[:8]
        subprocess.check_call([sys.executable, '-I', 'boards.py', 'add', 'workshop/compute/funsearch', 'funsearch-' + run_id, 'model-in-the-loop', 'tested', statement] + evidence + ['--runner', runner], cwd=ROOT, stdout=subprocess.DEVNULL)
        if confirm: subprocess.check_call([sys.executable, '-I', 'boards.py', 'confirm', rid, a.who], cwd=ROOT, stdout=subprocess.DEVNULL)
        print('finding', rid, '|', statement)
    b = [q for sub, q in ev if sub == 'best']
    if b:
        st = ('FunSearch session %s on %s (%s; %d proposals, %d ran, %d distinct programs kept, %d s): best score = base - gates of a correct circuit with at most one NOT gate: %s. '
              '%s Every listed circuit passes the independent pointwise evaluator recheck.py; the "none beat base" part covers only the programs of this session.'
              % (run_id, summ['target'], summ['proposer'], summ['proposed'], summ['ran'], summ['distinct_programs'], summ['seconds'],
                 ', '.join('%s %s' % (k.replace('|any', '').replace('|essential', ' (NOT essential)'), v) for k, v in summ['best'].items()),
                 'No candidate beat base.' if not summ['candidates'] else '%d candidate(s) beat base, see the separate findings.' % summ['candidates']))
        add(st, b + [os.path.join(dest, 'summary.json')], 'python3 -I workshop/compute/funsearch/recheck.py --file ' + ' '.join(b), True)
    for sub, q in ev:
        if sub != 'candidates': continue
        w = json.load(open(os.path.join(ROOT, q)))
        st = ('CANDIDATE below base, found by the model-in-the-loop search (%s) and confirmed by the independent evaluator: %s on %s, score %s. A SECOND SEAT must recheck this before any word '
              'on BottomPay / no_minCE changes.' % (run_id, w.get('kind'), w.get('system', w.get('target')), w.get('claim', {}).get('score', w.get('slack'))))
        add(st, [q], ' '.join(tg.recheck_cmd(q)), False)                      # never confirmed by this seat: unverified until someone else reruns it

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('cmd'); ap.add_argument('dir', nargs='?')
    ap.add_argument('--target', default='k1:small'); ap.add_argument('--proposer', default='mutate', choices=['hf', 'gguf', 'mutate']); ap.add_argument('--model')
    ap.add_argument('--gguf-pattern', default='*q4_k_m*'); ap.add_argument('--dtype'); ap.add_argument('--threads', type=int, default=3)
    ap.add_argument('--minutes', type=float, default=0); ap.add_argument('--samples', type=int, default=0); ap.add_argument('--out', default='.pnp/funsearch/run')
    ap.add_argument('--islands', type=int, default=4); ap.add_argument('--batch', type=int, default=4); ap.add_argument('--k', type=int, default=2); ap.add_argument('--reset', type=int, default=60)
    ap.add_argument('--seed', type=int, default=0); ap.add_argument('--jobs', type=int, default=3); ap.add_argument('--timeout', type=float, default=10)
    ap.add_argument('--max-new', type=int, default=260); ap.add_argument('--temperature', type=float, default=0.8)
    ap.add_argument('--who'); ap.add_argument('--run'); ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    if a.cmd == 'targets':
        for name, t in T.registry().items(): print('%-28s %-8s <- %s' % (name, t.kind, t.source))
    elif a.cmd == 'run':
        assert a.minutes or a.samples, 'give --minutes or --samples'; run(a)
    elif a.cmd == 'record':
        assert a.dir and (a.dry or a.who), 'fs.py record DIR --who SEAT'; record(a)
    else: sys.exit(__doc__)

if __name__ == '__main__': main()
