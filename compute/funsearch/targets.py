"""The target registry: where the loop attaches.  A target = (statement, program skeleton, exact evaluator -> score and verdict).
Every target is GENERATED from the repository at call time (registry()), none is listed by hand:
  (a) k1:<system>    the k = 1 flagship (boards/tasks/flagship-payment-hall.md; L_meta_951 / no_minCE): one-NOT circuits on linear
                     set systems.  Systems: AG(2,q), PG(2,q), cycles C_m (built here over GF(q)), plus every system of
                     REF1_phc.linear_systems().  score = base - gates; a positive score is a candidate counterexample to
                     BottomPay / no_minCE.  Evaluator: evalbatch.score (tensor backend, exact over all 2^n inputs).
                     k1:small = one program scored on AG(2,4), PG(2,2), PG(2,3) together.
  (b) phc:<system>   PHC tightness at 1_Q (Lemma D slack): evaluators/phc_eval.py (REF1's checker).  Finds tight payer structures.
  (c) runner:<id>    every `tested` finding with a `runner` whose command names instance files (*.json): the program returns an
                     instance near the stored ones, the finding's own runner is the evaluator; exit 1 = candidate violation.
  (d) open:<file>:<k> every board line that reads  OPEN ... evaluator: `python3 -I PATH [ARGS]`  (optional  skeleton: `PATH`).
"Within reason" is enforced here: a target exists only where an exact evaluator exists.  Nothing attaches to Lean proofs, to
`checked` / `paper` / `premise` findings or to philosophy, and no target lets the model assign a word: verdicts come from evaluators.
  python3 -I compute/funsearch/targets.py          list the registry"""
import os, sys, re, json, glob, shlex, itertools, subprocess, tempfile, concurrent.futures
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))

# ------------------------------------------------------------------ set systems (linear: two sets share at most one point)
_POLY = {4: (2, [1, 1, 1]), 8: (2, [1, 1, 0, 1]), 9: (3, [1, 0, 1]), 16: (2, [1, 1, 0, 0, 1])}          # low coefficient first
def gf(q):
    """(add, mul) tables of GF(q), elements 0..q-1 (digits base p = polynomial coefficients)."""
    if all(q % d for d in range(2, q)): p, mod = q, [0, 1]
    else: p, mod = _POLY[q]
    k = len(mod) - 1
    dig = lambda x: [(x // p ** i) % p for i in range(k)]; num = lambda d: sum(c * p ** i for i, c in enumerate(d))
    def mul(a, b):
        r = [0] * (2 * k)
        for i, x in enumerate(dig(a)):
            for j, y in enumerate(dig(b)): r[i + j] = (r[i + j] + x * y) % p
        for i in range(2 * k - 1, k - 1, -1):
            c = r[i]; r[i] = 0
            for j in range(k): r[i - k + j] = (r[i - k + j] - c * mod[j]) % p
        return num(r[:k])
    add = lambda a, b: num([(x + y) % p for x, y in zip(dig(a), dig(b))])
    return [[add(a, b) for b in range(q)] for a in range(q)], [[mul(a, b) for b in range(q)] for a in range(q)]

def AG(q):
    A, M = gf(q); pt = lambda x, y: x * q + y
    L = [[pt(x, A[M[m][x]][b]) for x in range(q)] for m in range(q) for b in range(q)] + [[pt(c, y) for y in range(q)] for c in range(q)]
    return q * q, [sorted(l) for l in L]

def PG(q):
    A, M = gf(q); P = [(1, y, z) for y in range(q) for z in range(q)] + [(0, 1, z) for z in range(q)] + [(0, 0, 1)]
    dot = lambda u, v: A[A[M[u[0]][v[0]]][M[u[1]][v[1]]]][M[u[2]][v[2]]]
    return len(P), [[i for i, p in enumerate(P) if dot(l, p) == 0] for l in P]

def cycle(m): return m, [[i, (i + 1) % m] for i in range(m)]

def is_linear(sets): return all(len(S) >= 2 for S in sets) and all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(sets, 2))

def systems():
    """name -> (n, sets, where it comes from)."""
    out = {}
    for q in (2, 3, 4, 5): out['AG(2,%d)' % q] = AG(q) + ('targets.AG',)
    for q in (2, 3, 4): out['PG(2,%d)' % q] = PG(q) + ('targets.PG',)
    for m in (5, 6, 8, 12): out['C%d' % m] = cycle(m) + ('targets.cycle',)
    try:
        sys.path.insert(0, os.path.join(ROOT, 'one-not', 'research', 'open')); import REF1_phc
        for k, (n, sets) in REF1_phc.linear_systems(None).items(): out.setdefault(k, (n, sets, 'REF1_phc.linear_systems'))
    except Exception as e: print('targets: REF1 systems not loaded:', e, file=sys.stderr)
    for k, (n, sets, _) in out.items(): assert is_linear(sets) and max(map(max, sets)) < n, k
    return out

# ------------------------------------------------------------------ skeletons
CIRCUIT_PRE = r'''
class Circuit:
    def __init__(self, n): self.n = n; self.gates = []
    def _add(self, op, *a):
        a = [int(x) for x in a]
        if len(self.gates) >= 3000: raise ValueError('too many gates')
        for x in a:
            if not 0 <= x < self.n + len(self.gates): raise ValueError('no such wire')
        self.gates.append([op] + a); return self.n + len(self.gates) - 1
    def _chain(self, op, a):
        a = [x for y in a for x in (y if isinstance(y, (list, tuple, set, frozenset)) else [y])]
        if not a: raise ValueError('gate without inputs')
        t = a[0]
        for u in a[1:]: t = self._add(op, t, u)
        return t
    def AND(self, *a): return self._chain('and', a)          # more than two wires: a chain, one gate per extra wire
    def OR(self, *a): return self._chain('or', a)
    def NOT(self, a): return self._add('not', a)
def _CALL(f, a):
    C = Circuit(a[0]); outs = f(a[0], [list(S) for S in a[1]], C)
    return {'gates': C.gates, 'outs': [int(o) for o in outs]}
'''
JSON_PRE = 'def _CALL(f, a): return f(*a)\n'

K1_API = '''Task: build a Boolean circuit with AND, OR and at most ONE NOT gate.
Inputs are wires 0..n-1.  `sets` is a list of lines (lists of input wires); any two lines share at most one point.
Output i must equal the OR of the inputs in sets[i], on every input.  build(n, sets, C) returns the list of output wires.
C.AND(a, b), C.OR(a, b), C.NOT(a) each add one gate and return its wire (an integer).  C.NOT may be called at most once.
Wires are plain integers: combine them only through C.AND / C.OR / C.NOT, never with Python's &, |, not.
Fewer gates is better: score = sum(len(S) - 1 for S in sets) - (number of gates).  The plain formula scores 0.
A wrong circuit scores very low.  A circuit can only beat 0 if its NOT gate is really needed, so use the NOT gate in an essential way.
Share gates between lines.  Only plain Python; no imports, no printing.'''

K1_SEEDS = ['''def build(n, sets, C):
    # the plain formula: one chain of ORs per line (no NOT gate), score 0
    outs = []
    for S in sets:
        t = S[0]
        for u in S[1:]:
            t = C.OR(t, u)
        outs.append(t)
    return outs
''', '''def build(n, sets, C):
    # NOT on one input b; in the first line through b:  ((a AND NOT b) OR b) = a OR b
    b = sets[0][0]
    N = C.NOT(b)
    outs = []
    for i, S in enumerate(sets):
        if i == 0:
            a = S[1]
            t = C.OR(C.AND(a, N), b)
            for u in S[2:]:
                t = C.OR(t, u)
        else:
            t = S[0]
            for u in S[1:]:
                t = C.OR(t, u)
        outs.append(t)
    return outs
''', '''def build(n, sets, C):
    # switch on h = AND of two points outside line 0:  out0 = (h AND y) OR (NOT h AND (y OR h)), y = OR of line 0
    S0 = sets[0]
    rest = [v for v in range(n) if v not in S0]
    h = C.AND(rest[0], rest[1])
    N = C.NOT(h)
    outs = []
    for i, S in enumerate(sets):
        t = S[0]
        for u in S[1:]:
            t = C.OR(t, u)
        if i == 0:
            t = C.OR(C.AND(h, t), C.AND(N, C.OR(t, h)))
        outs.append(t)
    return outs
''']

class Target:
    kind = '?'
    def __init__(self, name, statement, api, preamble, entry, instances, labels, seeds, source):
        self.name, self.statement, self.api, self.preamble, self.entry = name, statement, api, preamble, entry
        self.instances, self.labels, self.seeds, self.source = instances, labels, seeds, source
    def evaluate(self, outputs): raise NotImplementedError
    def recheck_cmd(self, path): raise NotImplementedError

class K1Target(Target):
    """(a) one-NOT circuits on linear set systems."""
    kind = 'k1'
    def __init__(self, name, sysnames, allsys):
        inst = [[allsys[s][0], allsys[s][1]] for s in sysnames]
        st = 'k = 1 flagship (L_meta_951 / no_minCE, open): on %s, is there a correct circuit with at most one NOT gate and fewer than base = sum(|S| - 1) gates?' % ', '.join(sysnames)
        super().__init__(name, st, K1_API, CIRCUIT_PRE, 'build', inst, list(sysnames), K1_SEEDS, 'boards/tasks/flagship-payment-hall.md + ' + ', '.join(sorted({allsys[s][2] for s in sysnames})))
    def evaluate(self, outputs):
        import evalbatch
        per = []
        for j, (n, sets) in enumerate(self.instances):
            per.append(evalbatch.score([o[j]['value'] if o[j]['ok'] and isinstance(o[j]['value'], dict) else None for o in outputs], n, sets))
        res = []
        for i, o in enumerate(outputs):
            rs = [per[j][i] for j in range(len(self.instances))]; ok = [r['verdict'] in ('ok', 'VIOLATION-CANDIDATE') for r in rs]
            wit = [{'kind': 'k1-circuit', 'target': self.name, 'system': self.labels[j], **r['circuit'],
                    'claim': {'base': r['base'], 'gates': r['gates'], 'score': r['score']}, 'essential': r['essential']} for j, r in enumerate(rs) if ok[j]]
            err = next((x['error'] for x in o if not x['ok']), None)
            res.append({'verdict': 'VIOLATION-CANDIDATE' if any(r['verdict'] == 'VIOLATION-CANDIDATE' for r in rs) else 'ok' if all(ok) else 'partial' if any(ok) else rs[0]['verdict'],
                        'score': max(r['score'] for r in rs), 'rank': sum(r['rank'] / r['base'] for r in rs) / len(rs),
                        'detail': {self.labels[j]: {k: r[k] for k in ('verdict', 'score', 'gates', 'nots', 'essential', 'why') if k in r} for j, r in enumerate(rs)},
                        'error': err, 'witnesses': wit, 'signature': [round(r['rank'], 3) for r in rs]})
        return res
    def recheck_cmd(self, path): return ['python3', '-I', 'compute/funsearch/recheck.py', '--file', path]

def _run_cmd(argv, payload, timeout):
    try:
        r = subprocess.run(['nice', '-n', '19'] + argv, input=json.dumps(payload), capture_output=True, text=True, timeout=timeout, cwd=ROOT)
    except subprocess.TimeoutExpired: return None, 'timeout', ''
    return r.returncode, r.stdout, r.stderr

class CommandTarget(Target):
    """(b), (d): the evaluator is a repository command: candidate JSON on stdin -> last line {"score", "verdict", ...}."""
    kind = 'command'
    def __init__(self, name, statement, api, argv, instances, labels, seeds, source, preamble=JSON_PRE, wrap=None, timeout=120, recheck=None):
        super().__init__(name, statement, api, preamble, 'build', instances, labels, seeds, source)
        self.argv, self.wrap, self.timeout, self._recheck = argv, wrap, timeout, recheck
    def _one(self, o, j):
        if not o['ok']: return {'verdict': 'invalid', 'score': -1e6, 'why': o['error']}
        cand = self.wrap(o['value'], j) if self.wrap else o['value']
        rc, out, err = _run_cmd(self.argv, cand, self.timeout)
        if rc is None: return {'verdict': 'invalid', 'score': -1e6, 'why': 'evaluator timeout'}
        try:
            r = json.loads(out.strip().splitlines()[-1]); float(r['score']); assert r['verdict'] in ('ok', 'invalid', 'VIOLATION-CANDIDATE')
        except Exception: return {'verdict': 'invalid', 'score': -1e6, 'why': 'evaluator gave no verdict (exit %s)' % rc}
        return r
    def evaluate(self, outputs):
        jobs = [(i, j) for i in range(len(outputs)) for j in range(len(self.instances))]
        with concurrent.futures.ThreadPoolExecutor(3) as ex: got = list(ex.map(lambda ij: self._one(outputs[ij[0]][ij[1]], ij[1]), jobs))
        res = []
        for i in range(len(outputs)):
            rs = [got[k] for k, (a, _) in enumerate(jobs) if a == i]
            wit = [dict(r['witness'], target=self.name) for r in rs if r.get('witness')]
            res.append({'verdict': 'VIOLATION-CANDIDATE' if any(r['verdict'] == 'VIOLATION-CANDIDATE' for r in rs) else 'ok' if all(r['verdict'] == 'ok' for r in rs) else 'invalid',
                        'score': max(r['score'] for r in rs), 'rank': sum(r.get('rank', r['score']) for r in rs) / len(rs),
                        'detail': {self.labels[j]: {k: v for k, v in r.items() if k != 'witness'} for j, r in enumerate(rs)}, 'error': None,
                        'witnesses': wit, 'signature': [round(r.get('rank', r['score']), 3) for r in rs]})
        return res
    def recheck_cmd(self, path): return [a.replace('{WITNESS}', path) for a in (self._recheck or ['python3', '-I', 'compute/funsearch/recheck.py', '--rerun', path])]

class RunnerTarget(Target):
    """(c): a `tested` finding's own runner, on an instance near its stored ones."""
    kind = 'runner'
    def __init__(self, rec, d, argv, files):
        self.argv_t = argv; self.rec = rec; near = []
        for p in files[:6]:
            try:
                if os.path.getsize(os.path.join(ROOT, p)) < 100000: near.append(json.load(open(os.path.join(ROOT, p))))
            except Exception: pass
        api = ('Task: a tested claim is checked by a fixed command on instance files.  build(instances) gets a list of stored instances (JSON objects)\n'
               'and must return ONE new JSON object of the same shape, close to them but different (change a few entries).\n'
               'score 1 if the claim FAILS on your instance (that is the goal), 0 if it holds, lower if the instance is malformed.\nOnly plain Python; no imports.')
        seeds = ['def build(instances):\n    # return a stored instance unchanged\n    return instances[0]\n']
        super().__init__('runner:' + rec['id'], 'finding %s (tested, %s): %s' % (rec['id'], d, rec['statement'][:300]), api, JSON_PRE, 'build', [[near]], ['near-stored'], seeds, os.path.join(d, 'findings.jsonl'))
    def _one(self, o):
        if not o['ok'] or not isinstance(o['value'], (dict, list)): return {'verdict': 'invalid', 'score': -2, 'rank': -2, 'why': o.get('error', 'not an instance')}
        with tempfile.TemporaryDirectory() as td:
            p = os.path.join(td, 'instance.json'); json.dump(o['value'], open(p, 'w'))
            try: r = subprocess.run(['nice', '-n', '19'] + [p if a == '{INSTANCE}' else a for a in self.argv_t], capture_output=True, text=True, timeout=300, cwd=ROOT)
            except subprocess.TimeoutExpired: return {'verdict': 'invalid', 'score': -1, 'rank': -1, 'why': 'runner timeout'}
        if r.returncode == 0: return {'verdict': 'ok', 'score': 0, 'rank': 0}
        if r.returncode != 1 or 'Traceback' in r.stderr or 'usage:' in r.stderr: return {'verdict': 'invalid', 'score': -1, 'rank': -1, 'why': 'runner broke (exit %d): malformed instance' % r.returncode}
        return {'verdict': 'VIOLATION-CANDIDATE', 'score': 1, 'rank': 1, 'witness': {'kind': 'command', 'argv': self.argv_t, 'instance': o['value'], 'finding': self.rec['id'], 'tail': r.stdout[-400:]}}
    def evaluate(self, outputs):
        res = []
        for o in outputs:
            r = self._one(o[0]); res.append({'verdict': r['verdict'], 'score': r['score'], 'rank': r['rank'], 'detail': {k: v for k, v in r.items() if k != 'witness'}, 'error': None,
                                             'witnesses': [dict(r['witness'], target=self.name)] if r.get('witness') else [], 'signature': [r['rank'], json.dumps(o[0].get('value'), sort_keys=True)[:60] if o[0]['ok'] else '']})
        return res
    def recheck_cmd(self, path): return ['python3', '-I', 'compute/funsearch/recheck.py', '--rerun', path]

# ------------------------------------------------------------------ generators
SAFE = re.compile(r'^[A-Za-z0-9_./*=,:+-]+$')
def _safe_argv(cmd):
    """A runner / evaluator command we are willing to run without a shell: `python3 -I repo/path.py args`, plain tokens only."""
    try: a = shlex.split(cmd)
    except ValueError: return None
    if len(a) < 3 or a[0] != 'python3' or a[1] != '-I' or not a[2].endswith('.py'): return None
    if any(not SAFE.match(x) or x.startswith(('/', '..')) or '/../' in x for x in a[2:]) or not os.path.isfile(os.path.join(ROOT, a[2])): return None
    return a

def _findings():
    for d, dirs, files in os.walk(ROOT):
        dirs[:] = [x for x in dirs if x not in ('.git', '.lake', '__pycache__', 'node_modules', '.pnp')]
        if 'findings.jsonl' not in files: continue
        last = {}
        for line in open(os.path.join(d, 'findings.jsonl')):
            try: r = json.loads(line)
            except ValueError: continue
            if 'id' in r: last[r['id']] = {**last.get(r['id'], {}), **r}
        for r in last.values(): yield os.path.relpath(d, ROOT), r

def k1_targets(allsys=None):
    allsys = allsys or systems(); out = [K1Target('k1:small', ['AG(2,4)', 'PG(2,2)', 'PG(2,3)'], allsys)]
    return out + [K1Target('k1:' + s, [s], allsys) for s, (n, sets, _) in allsys.items() if n <= 21]

def phc_targets(allsys=None):
    allsys = allsys or systems(); out = []
    for s, (n, sets, src) in allsys.items():
        if n > 13: continue
        api = K1_API.split('Fewer gates')[0] + ('The circuit must be correct and use C.NOT exactly once.\nGoal: make the payment condition of Lemma D TIGHT in as many and as large '
              'states as possible (score 0 = tight somewhere; above 0 = the condition fails).\nCircuits that switch several lines on the NOT gate give richer structures.  Only plain Python; no imports.')
        out.append(CommandTarget('phc:' + s, 'PHC tightness at 1_Q on %s: BottomPay instances of a correct one-NOT circuit, least Lemma D slack over payer sets (F1_phc.md).' % s, api,
                                 ['python3', '-I', 'compute/funsearch/evaluators/phc_eval.py'], [[n, sets]], [s], K1_SEEDS[2:], 'one-not/research/open/REF1_phc.py + ' + src,
                                 preamble=CIRCUIT_PRE, wrap=lambda v, j, n=n, sets=sets: dict(v, n=n, sets=sets) if isinstance(v, dict) else v,
                                 recheck=['python3', '-I', 'one-not/research/open/REF1_phc.py', '--recheck', '{WITNESS}']))
    return out

def runner_targets():
    out = []
    for d, r in _findings():
        if r.get('word') != 'tested' or not r.get('runner'): continue
        a = _safe_argv(r['runner'])
        if not a: continue
        files = [f for x in a[3:] if x.endswith('.json') for f in sorted(glob.glob(os.path.join(ROOT, x)))]
        if not files: continue                                           # nothing to search near: the runner names no instance file
        argv = a[:3] + [x for x in a[3:] if not x.endswith('.json')] + ['{INSTANCE}']
        out.append(RunnerTarget(r, d, argv, [os.path.relpath(f, ROOT) for f in files]))
    return out

OPEN_RE = re.compile(r'\bOPEN\b.*?evaluator:\s*`([^`]+)`(?:.*?skeleton:\s*`([^`]+)`)?')
def open_targets(paths=None):
    out = []
    paths = paths or [os.path.join(ROOT, 'BOARD.md')] + sorted(glob.glob(os.path.join(ROOT, 'boards', '**', '*.md'), recursive=True))
    for p in paths:
        if os.path.basename(p) == 'TREE.md' or not os.path.isfile(p): continue
        for k, line in enumerate(open(p, errors='replace')):
            m = OPEN_RE.search(line)
            if not m: continue
            a = _safe_argv(m.group(1))
            if not a: continue
            sk = m.group(2); api = None
            if sk and SAFE.match(sk) and not sk.startswith(('/', '..')) and os.path.isfile(os.path.join(ROOT, sk)): api = open(os.path.join(ROOT, sk)).read()[:4000]
            api = api or ('Task: ' + line.strip()[:800] + '\nbuild() takes no arguments and returns one JSON object (the candidate).  Higher score is better.  Only plain Python; no imports.')
            out.append(CommandTarget('open:%s:%d' % (os.path.relpath(p, ROOT), k + 1), line.strip()[:400], api, a, [[]], ['cell'], ['def build():\n    return {}\n'], os.path.relpath(p, ROOT)))
    return out

def registry():
    allsys = systems(); out = {}
    for t in k1_targets(allsys) + phc_targets(allsys) + runner_targets() + open_targets(): out[t.name] = t
    return out

if __name__ == '__main__':
    for name, t in registry().items(): print('%-28s %-8s %d instance(s)  <- %s' % (name, t.kind, len(t.instances), t.source))
