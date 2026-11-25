"""LiftSDR certificates from GP test systems, Python -> Lean (Python finds, Lean checks).

For the barrier suite (circuits with NO pure SDR; coord 64776ce, front C 12:17: GP-SDRs exist on all of them) and any
other one-NOT circuit. A GP test system for a set R with output o (Lean `gpLTS b z A`, PureGP.lean) is a world b, a zero
point z and atoms A_u (u in R), all in the lift at y = b. It is VALID (`gpLTS_valid`) when C_b(o)(z) = 0, C_b(o)(A_u) = 1
and two atoms of distinct points meet only inside z. Its class is the union-find merge set of the run (`ltsCls`).

Enumerated family (as referee_b/lifted_union.py, restricted to one world): every z with C_b(o)(z) = 0, atoms
A_u = B | {u} | P_u with B in {empty, ones(z)} common and P_u the zeros of z outside R assigned to at most one atom
(the first KMAX such zeros). Then a pairwise disjoint choice (backtracking) and a Lean module: circuit, chosen systems,
classes as literals in LIFTED wire numbers; Lean recomputes validity and every class (`decide`).

Usage (from research/one-not/tools/sdrcert): python3 lift_export.py OUT.lean [--kmax K] [file.json ...]
       (default files: the barrier suite in research/one-not/data/witnesses)
"""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..')
sys.path.insert(0, HERE)
from pure_export import BARRIER, camel, fin_set, lifted, merges, sdr, tables  # noqa: E402
from export import lean_name  # noqa: E402


def gp_menu(n, G, R, o, KMAX):
    """Distinct GP classes of R (output wire o): class -> (b, z, A)."""
    opts = {}
    for b in (1, 0):
        W = tables(n, G, b)
        for z in range(1 << n):
            if (W[o] >> z) & 1:
                continue
            extra = [v for v in range(n) if not (z >> v) & 1 and v not in R][:KMAX]
            for Bfull in (False, True):
                B = z if Bfull else 0
                for assign in itertools.product([None] + list(R), repeat=len(extra)):
                    A = {u: B | (1 << u) for u in R}
                    for e, a in zip(extra, assign):
                        if a is not None:
                            A[a] |= 1 << e
                    if not all((W[o] >> A[u]) & 1 for u in R):
                        continue
                    opts.setdefault(merges(W, n, G, R, z, A), (b, z, A))
    return opts


def emit(name, d, n, S, G, p, opts, ch):
    m = len(S); N = 'l' + lean_name(name)
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (g[0], ', '.join(map(str, g[1:]))) for g in G)
    sets = ', '.join('{%s}' % ', '.join(map(str, R)) for R in S)
    outs = ', '.join(str(o) for o in d['outs'])
    ts, worlds = [], []
    for w in range(m):
        b, z, A = opts[w][ch[w]]; worlds.append('C%d' % b)
        ts.append('gpLTS %s (canonPt %s) ![%s]' % ('true' if b else 'false', fin_set(n, z),
                                                 ', '.join(fin_set(n, A.get(u, 0)) for u in range(n))))
    Ms = ', '.join('{%s}' % ', '.join(str(lifted(n, p, i)) for i in sorted(ch[w])) for w in range(m))
    valid = '\n'.join('  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)' for _ in range(m))
    hin = ', '.join(map(str, G[p][1:]))
    return worlds, f'''
/-! ### {name}: n = {n}, {len(G)} gates (NOT gate {p}), {m} sets; GP worlds {', '.join(worlds)} -/

def {N}Gates : List Gate := [{gl}]
def {N}S : Fin {m} → Finset (Fin {n}) := ![{sets}]
def {N}Out : Fin {m} → ℕ := ![{outs}]
def {N}T : Fin {m} → LTS {n} := ![{', '.join(ts)}]
def {N}M : Fin {m} → Finset ℕ := ![{Ms}]

set_option maxRecDepth 100000 in
theorem {N}_valid : ∀ w, LTSValid {N}Gates {p} ({N}S w) ({N}Out w) ({N}T w) := by
  intro w
  fin_cases w
{valid}

set_option maxRecDepth 100000 in
theorem {N}_cls : ∀ w, ltsCls {N}Gates {p} ({N}S w) ({N}T w) = {N}M w := by decide

theorem {N} : LiftSDR {N}S {N}Gates {N}Out {p} :=
  liftSDR_of_cert _ _ _ _ {N}T {N}M {N}_valid {N}_cls (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `{name}`: correct, (1,1)-disjoint sets of size at least 2, one NOT gate (gate {p}), LiftSDR. -/
theorem {N}_correct :
    (∀ (w : Fin {m}) (x : Fin {n} → Bool),
      val {N}Gates x ({N}Out w) = decide (∃ v ∈ {N}S w, x v = true)) ∧
    (∀ w, 2 ≤ ({N}S w).card) ∧
    (∀ a b : Fin {m}, a ≠ b → ({N}S a ∩ {N}S b).card ≤ 1) ∧
    {N}Gates[{p}]? = some ⟨GateOp.not, [{hin}]⟩ ∧
    LiftSDR {N}S {N}Gates {N}Out {p} :=
  ⟨by decide, by decide, by decide, rfl, {N}⟩
'''


if __name__ == '__main__':
    args = sys.argv[1:]
    out = args[0]
    KMAX = int(args[args.index('--kmax') + 1]) if '--kmax' in args else 5
    files = [a for i, a in enumerate(args[1:], 1) if not a.startswith('--') and args[i - 1] != '--kmax']
    if not files:
        wd = os.path.join(ROOT, 'research/data/witnesses')
        files = [os.path.join(wd, f) for f in sorted(os.listdir(wd)) if f.endswith('.json')
                 and json.load(open(os.path.join(wd, f)))['name'] in BARRIER]
    parts = []
    for f in files:
        d = json.load(open(f))
        n, S = d['n'], [list(s) for s in d['sets']]
        G = [[g[0]] + [int(x) for x in g[1:]] for g in d['gates']]
        p = next(k for k, g in enumerate(G) if g[0] == 'not')
        opts = [gp_menu(n, G, R, o, KMAX) for R, o in zip(S, d['outs'])]
        ch = sdr([set(o) for o in opts])
        assert ch is not None, d['name'] + ': no GP SDR in the enumerated family'
        worlds, txt = emit(camel(d['name']), d, n, S, G, p, opts, ch)
        parts.append(txt)
        print((d['name'], n, len(G), p, [len(o) for o in opts], worlds, [sorted(M) for M in ch]))
    open(out, 'w').write(''.join(parts))
