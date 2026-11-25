"""The README conjectures as executable predicates. Each returns (margin, detail); margin < 0 is a counterexample.
Add a conjecture = add a function and a line in REGISTRY. Serves README items C2, C3, C4, L7."""
from core import *
from core import _zeros

def count(c, any_gate=False):
    """|witness(empty cube)| >= base. OR-only family: the count behind the Theorem (one NOT gate)."""
    return slack(c, 0, any_gate=any_gate), "slack at the empty cube"

def count_any_gate(c):
    """C4(t): the general witness family (any gate type) has >= base members, any number of NOT gates."""
    return slack(c, 0, any_gate=True), "general slack at the empty cube"

def gates_ge_base(c):
    """The Theorem itself (and its t-NOT form): #gates >= base."""
    return len(c['gates']) - base(c), "gates - base"

def step(c, k=1, any_gate=False):
    """C3_k at the empty cube: some path of <= k points ends with slack no larger than at the start."""
    w = tables(c['n'], c['gates']); s0 = slack(c, 0, w, any_gate); best = None; frontier = {0}
    for _ in range(k):
        nxt = set()
        for Q in frontier:
            for v in alive_points(c, Q):
                Q2 = Q | 1 << v
                if Q2 in nxt: continue
                nxt.add(Q2); m = s0 - slack(c, Q2, w, any_gate)
                best = m if best is None else max(best, m)
        frontier = nxt
    return (best if best is not None else 0), f"best slack drop over paths of <= {k} points"

def _flip_gates(c, mode):
    """Gates g with, for some set R and zero point Z of R: mode 'flip' g(Z+e_u) != g(Z) at two atoms u of R (either direction of change, same
    direction at both); mode 'split' as flip, or g(Z+e_u) != g(Z+e_u') at two atoms (XOR-like);."""
    n = c['n']; w = tables(n, c['gates']); out = set()
    for k in range(len(c['gates'])):
        t = w[n + k]
        for R in c['sets']:
            hit = False
            for Z in _zeros(n, tuple(R), 0):
                b = t >> Z & 1; vals = [t >> (Z | 1 << u) & 1 for u in R]
                if sum(v != b for v in vals) >= 2 or (mode == 'split' and 0 in vals and 1 in vals): hit = True; break
            if hit: out.add(k); break
    return out, w

def count_flip(c):
    """C4 count (flip): gates whose value changes, in EITHER direction, from a zero point Z to two atoms of a set. Counts the AND-side
    (De Morgan) merges that are 1 at Z and fall."""
    f, _ = _flip_gates(c, 'flip'); return len(f) - base(c), "flip gates - base"

def count_split(c):
    """C4 count (split): flip gates, plus gates taking different values at two atoms Z+e_u, Z+e_u' (XOR-like at Z)."""
    f, _ = _flip_gates(c, 'split'); return len(f) - base(c), "split gates - base"

def count_flip_classes(c):
    """C4 count (flip classes): flip gates counted once per function up to complement (g and NOT g are one class; copies are one class)."""
    f, w = _flip_gates(c, 'flip'); M = (1 << (1 << c['n'])) - 1; n = c['n']
    cl = {min(w[n + k], M ^ w[n + k]) for k in f}
    return len(cl) - base(c), "flip classes - base"

def is_irreducible_read_not(c):
    """Class (b): exactly one NOT gate, every gate read (so the NOT gate is read), no gate-saving rewiring (MinCE.no_rewire)."""
    return nots(c) == 1 and all_read(c) and gate_saving_rewire(c) is None

def irreducible_class(c):
    """NOT gate read and irreducible: margin 1 if the circuit is in the class, else 0 (an indicator, never a counterexample)."""
    return (1, "in class") if is_irreducible_read_not(c) else (0, "not in class")

def step_under_no_rewire(c, nmax=8):
    """C2 under no-rewire: +1 (vacuous) unless is_irreducible_read_not(c) and n <= nmax. Else the minimum over EVERY cube Q with
    base(Q) > 0 of the best slack drop over single points (OR-only witnesses); < 0 = a cube where no point works."""
    if c['n'] > nmax or not is_irreducible_read_not(c): return 1, "vacuous (not irreducible with a read NOT gate, or n > %d)" % nmax
    w = tables(c['n'], c['gates']); worst = None
    for Q in range(1 << c['n']):
        if base(c, Q) <= 0: continue
        s0 = slack(c, Q, w, False)
        best = max(s0 - slack(c, Q | 1 << v, w, False) for v in alive_points(c, Q))
        if worst is None or best < worst[0]: worst = (best, Q)
    return (worst[0] if worst else 1), ("no cube with positive base" if not worst else "worst cube Q=%s" % bin(worst[1]))

REGISTRY = {
    "C2 one-point step": lambda c: step(c, 1),
    "C3 two-point step": lambda c: step(c, 2),
    "count (OR-only witnesses)": count,
    "C4 count (any-gate witnesses)": count_any_gate,
    "C4 count (flip)": count_flip,
    "C4 count (split)": count_split,
    "C4 count (flip classes)": count_flip_classes,
    "C2 one-point step under no-rewire": step_under_no_rewire,
    "NOT gate read and irreducible": irreducible_class,
    "Theorem: gates >= base": gates_ge_base,
}
