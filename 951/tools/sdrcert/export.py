"""MergeSDR certificates, Python -> Lean (951/PIPELINE.md item 3: Python finds, Lean checks).
For each circuit: the menu of merge sets M_z(w) over all zero points z of S_w (w951 systems.system + merges, atoms
z + e_u), a disjoint choice z_w by backtracking (smallest menus first, smallest merge sets first), and a Lean module
with the circuit, the chosen points and their merge sets as literals. Lean recomputes every merge set (`decide`), so
nothing here is trusted. Usage: python3 export.py OUT.lean  (run from 951/tools/sdrcert; reads the instances below)."""
import itertools, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from w951 import Circuit, systems

ROOT = os.path.join(HERE, '..', '..')
INSTANCES = [  # (Lean name, source, loader)
    ('cfgI', 'research/front612/cfgI/cfgI.json', 'json'),
    ('adv3', 'research/front612/fable_worlds.md', 'ADV3'),
    ('adv4', 'research/front612/fable_worlds.md', 'ADV4'),
    ('ce3', 'tools/w951/tests/instances/scaffold-951__payment__ce3.json', 'json'),
    ('hard4', 'front/work/notes951/w9/A2s/hard4.json', 'json'),
    ('cxr', 'tools/w951/tests/instances/front-match__w8b__cxr.json', 'json'),
    # scaffold (session_01GmnDhdt8ydm1adQLjCP9we, 09:43): its HARD4 (10 gates, not front's A2s/hard4.json) and the two
    # smallest unique-SDR circuits
    ('hard4s', 'tools/sdrcert/scaffold_certs.json', 'scaffold:HARD4'),
    ('uniq0', 'tools/sdrcert/scaffold_certs.json', 'scaffold:unique_sdr_0'),
    ('uniq2', 'tools/sdrcert/scaffold_certs.json', 'scaffold:unique_sdr_2'),
]


def load(src, how):
    p = os.path.join(ROOT, src)
    if how.startswith('scaffold:'):
        return next(d for d in json.load(open(p)) if d['name'] == how.split(':', 1)[1])
    if how == 'json':
        d = json.load(open(p))
        if isinstance(d, list):
            d = d[0]
        if 'circuit' in d:
            d = d['circuit']
        return d
    lines = open(p).read().split('\n')
    i = next(k for k, l in enumerate(lines) if l.startswith(how + ' ('))
    j = next(k for k in range(i, len(lines)) if lines[k].strip().startswith('{"n"'))
    return json.loads(lines[j].strip())


def menu(c, w):
    S = c.sets[w]; rest = [v for v in range(c.n) if v not in S]; out = {}
    for bits in itertools.product((0, 1), repeat=len(rest)):
        z = sum(1 << v for v, b in zip(rest, bits) if b)
        g, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
        M = frozenset(systems.merges(c, S, B)[0])
        out.setdefault(M, z)
    return out  # merge set -> one zero point


def sdr(menus):
    order = sorted(range(len(menus)), key=lambda w: len(menus[w]))
    choice = {}
    def bt(i, used):
        if i == len(order):
            return True
        w = order[i]
        for M in sorted(menus[w], key=lambda M: (len(M), sorted(M))):
            if not (M & used):
                choice[w] = M
                if bt(i + 1, used | M):
                    return True
        return False
    return [choice[w] for w in range(len(menus))] if bt(0, frozenset()) else None


def lean_name(s):
    return s[0].upper() + s[1:]


def emit(name, d, ms, menus):
    n, m = d['n'], len(d['sets'])
    N = lean_name(name)
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (g[0], ', '.join(map(str, g[1:]))) for g in d['gates'])
    sets = ', '.join('{%s}' % ', '.join(map(str, S)) for S in d['sets'])
    pts = ', '.join('ptOf {%s}' % ', '.join(str(v) for v in range(n) if (menus[w][ms[w]] >> v) & 1) for w in range(m))
    Ms = ', '.join('{%s}' % ', '.join(map(str, sorted(ms[w]))) for w in range(m))
    outs = ', '.join(map(str, d['outs']))
    return f'''
/-! ### {name}: n = {n}, {len(d['gates'])} gates, {m} sets -/

def sdr{N}Gates : List Gate := [{gl}]
def sdr{N}S : Fin {m} → Finset (Fin {n}) := ![{sets}]
def sdr{N}Out : Fin {m} → ℕ := ![{outs}]
def sdr{N}Z : Fin {m} → Fin {n} → Bool := ![{pts}]
def sdr{N}M : Fin {m} → Finset ℕ := ![{Ms}]

set_option maxRecDepth 100000 in
theorem sdr{N}_merge : ∀ w, mergeSet sdr{N}Gates (sdr{N}S w) (sdr{N}Z w) = sdr{N}M w := by decide

theorem sdr{N} : MergeSDR sdr{N}S sdr{N}Gates :=
  mergeSDR_of_cert _ _ sdr{N}Z sdr{N}M (by decide) sdr{N}_merge (by decide)
'''


if __name__ == '__main__':
    only = sys.argv[2:] or [x[0] for x in INSTANCES]
    parts, report = [], []
    for name, src, how in INSTANCES:
        if name not in only:
            continue
        d = load(src, how)
        c = Circuit.from_dict(d)
        assert c.is_correct(), name
        menus = [menu(c, w) for w in range(len(c.sets))]
        ms = sdr([set(mu) for mu in menus])
        assert ms is not None, name + ': no disjoint choice'
        parts.append(emit(name, d, ms, menus))
        report.append((name, d['n'], len(d['gates']), len(d['sets']), [len(mu) for mu in menus], [sorted(M) for M in ms]))
    open(sys.argv[1], 'w').write(''.join(parts))
    for r in report:
        print(r)
