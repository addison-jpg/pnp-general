"""PureSDR certificates, Python -> Lean (951/PIPELINE.md item 3: Python finds, Lean checks).

For a one-NOT circuit (NOT gate at position p) and each set S_w, the menu of PURE classes of
951/PROOF_PLAN_SUGGESTIONS.md section 0 (kill_tests/ext.py), as defined in Lean (W951/PureSDR.lean):
  I1(w, Z): union-find merges in C_1 (lift at y = 1), zero point Z, atoms e_u; valid when Z avoids S_w and h(Z) = 0
            (every such Z is offered; maximality is not needed);
  I0(w, m): merges in C_0 (lift at y = 0), zero point top_w, atoms m_u | e_u; valid when m_u ∩ S_w ⊆ {u} and
            h(m_u) = 1 (m_u ranges over the minterms of h; offered for every set, h(top_w) = 1 is not needed).
Then a pairwise disjoint choice by backtracking, and a Lean module with the circuit, the chosen options and their
classes as literals in LIFTED wire numbers (lifted gate j is wire n + 1 + j; real wire i < n + p is lifted wire
i + 1, real wire i > n + p keeps its number). Lean recomputes every class (`decide`), so nothing here is trusted.
`tables` and `merges` are those of kill_tests/canon.py.

Usage (from 951/tools/sdrcert): python3 pure_export.py OUT.lean [name ...]  |  python3 pure_export.py OUT.lean --group fixh16
       python3 pure_export.py OUT.lean --group witness   (every *.json in 951/data/witnesses)
       python3 pure_export.py OUT.lean --group ladder    (scaffold's v-ladder, ladder_instances.json)
"""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..')
sys.path.insert(0, HERE)
from export import load, lean_name  # noqa: E402

INSTANCES = [  # (Lean name, source, loader)
    ('cxT2', 'tools/w951/tests/instances/front-match__fc__cxT2.json', 'json'),
    ('cxe3', 'front/work/notes951/w9/fc/cxe3.json', 'json'),
    ('ce3', 'tools/w951/tests/instances/scaffold-951__payment__ce3.json', 'json'),
    ('hard4s', 'tools/sdrcert/scaffold_certs.json', 'scaffold:HARD4'),
    ('cxr', 'tools/w951/tests/instances/front-match__w8b__cxr.json', 'json'),
    ('cfgI', 'research/front612/cfgI/cfgI.json', 'json'),
    ('adv3', 'research/front612/fable_worlds.md', 'ADV3'),
    ('adv4', 'research/front612/fable_worlds.md', 'ADV4'),
    ('hard4', 'front/work/notes951/w9/A2s/hard4.json', 'json'),
    ('uniq0', 'tools/sdrcert/scaffold_certs.json', 'scaffold:unique_sdr_0'),
    ('uniq2', 'tools/sdrcert/scaffold_certs.json', 'scaffold:unique_sdr_2'),
    ('cxT4', 'tools/w951/tests/instances/front-match__fc__cxT4.json', 'json'),
]
GROUPS = {'fixh16': 'tools/sdrcert/fixh16_forced.json',  # as export.py: `--group fixh16`
          'witness': 'data/witnesses',  # a directory: one circuit per *.json (dict with name, n, sets, gates, outs)
          'ladder': 'tools/sdrcert/ladder_instances.json'}  # scaffold's v-ladder (PG(2,3), AG(2,4)), a JSON list


def camel(s):
    parts = s.split('_')
    return parts[0] + ''.join(q[:1].upper() + q[1:] for q in parts[1:])
CAP = 4000  # per-atom minterm products per set, as kill_tests/ext.py


def tables(n, G, mode):
    P = 1 << n; FULL = (1 << P) - 1; W = []
    for v in range(n):
        W.append(sum(1 << x for x in range(P) if x >> v & 1))
    for g in G:
        if g[0] == 'not': W.append((FULL ^ W[g[1]]) if mode == 'real' else (0 if mode == 0 else FULL))
        elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
        elif g[0] == 'or': W.append(W[g[1]] | W[g[2]])
        else: raise ValueError(g[0])
    return W


def merges(W, n, G, R, Z, P):
    par = {u: u for u in R}
    def find(u):
        while par[u] != u:
            par[u] = par[par[u]]; u = par[u]
        return u
    B = {}
    for v in range(n):
        if not (W[v] >> Z) & 1: B[v] = frozenset(u for u in R if (W[v] >> P[u]) & 1)
    M = []
    for k, g in enumerate(G):
        i = n + k
        if (W[i] >> Z) & 1: continue
        B[i] = frozenset(u for u in R if (W[i] >> P[u]) & 1)
        if g[0] == 'or':
            a = B.get(g[1], frozenset()); b = B.get(g[2], frozenset())
            if a and b:
                ra, rb = find(next(iter(a))), find(next(iter(b)))
                if ra != rb: par[ra] = rb; M.append(i)
    return frozenset(M)


def menus(d):
    n, S = d['n'], [list(s) for s in d['sets']]
    G = [[g[0]] + [int(x) for x in g[1:]] for g in d['gates']]
    p = next(k for k, g in enumerate(G) if g[0] == 'not')
    Wr, W0, W1 = tables(n, G, 'real'), tables(n, G, 0), tables(n, G, 1)
    h = Wr[G[p][1]]; hb = lambda x: (h >> x) & 1
    mint = sorted((x for x in range(1 << n) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)),
                  key=lambda x: (bin(x).count('1'), x))
    out = []
    for R in S:
        Rm = sum(1 << u for u in R); top = ((1 << n) - 1) & ~Rm; rest = [v for v in range(n) if v not in R]
        opts = {}
        for r in range(len(rest) + 1):
            for zz in itertools.combinations(rest, r):
                z = sum(1 << v for v in zz)
                if hb(z): continue
                opts.setdefault(merges(W1, n, G, R, z, {u: 1 << u for u in R}), ('one', z))
        per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
        for ms in itertools.islice(itertools.product(*per), CAP):
            M = merges(W0, n, G, R, top, {u: ms[i] | 1 << u for i, u in enumerate(R)})
            opts.setdefault(M, ('zero', dict(zip(R, ms))))
        out.append(opts)
    return n, S, G, p, out


def sdr(opts):
    order = sorted(range(len(opts)), key=lambda w: len(opts[w])); choice = {}
    def bt(i, used):
        if i == len(order): return True
        w = order[i]
        for M in sorted(opts[w], key=lambda M: (len(M), sorted(M))):
            if not (M & used):
                choice[w] = M
                if bt(i + 1, used | M): return True
        return False
    return [choice[w] for w in range(len(opts))] if bt(0, frozenset()) else None


def lifted(n, p, i):
    return i + 1 if i < n + p else i


def fin_set(n, x):
    return '{%s}' % ', '.join(str(v) for v in range(n) if x >> v & 1)


def emit(name, d, n, S, G, p, opts, ch):
    m = len(S); N = 'p' + lean_name(name)
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (g[0], ', '.join(map(str, g[1:]))) for g in G)
    sets = ', '.join('{%s}' % ', '.join(map(str, R)) for R in S)
    cs, kinds = [], []
    for w in range(m):
        kind, par = opts[w][ch[w]]; kinds.append(kind)
        if kind == 'one':
            cs.append('PureOpt.one (canonPt %s)' % fin_set(n, par))
        else:
            cs.append('PureOpt.zero ![%s]' % ', '.join(fin_set(n, par.get(u, 0)) for u in range(n)))
    Ms = ', '.join('{%s}' % ', '.join(str(lifted(n, p, i)) for i in sorted(ch[w])) for w in range(m))
    return kinds, f'''
/-! ### {name}: n = {n}, {len(G)} gates (NOT gate {p}), {m} sets; worlds {', '.join('I1' if k == 'one' else 'I0' for k in kinds)} -/

def {N}Gates : List Gate := [{gl}]
def {N}S : Fin {m} → Finset (Fin {n}) := ![{sets}]
def {N}C : Fin {m} → PureOpt {n} := ![{', '.join(cs)}]
def {N}M : Fin {m} → Finset ℕ := ![{Ms}]

set_option maxRecDepth 100000 in
theorem {N}_valid : ∀ w, PureValid {N}Gates {p} ({N}S w) ({N}C w) := by decide

set_option maxRecDepth 100000 in
theorem {N}_cls : ∀ w, pureCls {N}Gates {p} ({N}S w) ({N}C w) = {N}M w := by decide

theorem {N} : PureSDR {N}S {N}Gates {p} :=
  pureSDR_of_cert _ _ _ {N}C {N}M {N}_valid {N}_cls (by decide)
'''


if __name__ == '__main__':
    if len(sys.argv) > 3 and sys.argv[2] == '--group':
        src = GROUPS[sys.argv[3]]
        path = os.path.join(ROOT, src)
        if os.path.isdir(path):
            INSTANCES[:] = [(camel(json.load(open(os.path.join(path, f)))['name']), os.path.join(src, f), 'json')
                            for f in sorted(os.listdir(path)) if f.endswith('.json')]
        else:
            pre = (lambda d: 'fixh' + d['name'].split('_')[1]) if sys.argv[3] == 'fixh16' else (lambda d: camel(d['name']))
            INSTANCES[:] = [(pre(d), src, 'scaffold:' + d['name']) for d in json.load(open(path))]
        sys.argv[2:] = []
    only = sys.argv[2:] or [x[0] for x in INSTANCES]
    parts, report = [], []
    for name, src, how in INSTANCES:
        if name not in only: continue
        d = load(src, how)
        n, S, G, p, opts = menus(d)
        ch = sdr([set(o) for o in opts])
        assert ch is not None, name + ': no pure SDR'
        kinds, txt = emit(name, d, n, S, G, p, opts, ch)
        parts.append(txt)
        report.append((name, n, len(G), p, [len(o) for o in opts], kinds, [sorted(M) for M in ch]))
    open(sys.argv[1], 'w').write(''.join(parts))
    for r in report: print(r)
