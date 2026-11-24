"""The README conjectures as executable predicates. Each returns (margin, detail); margin < 0 is a counterexample.
Add a conjecture = add a function and a line in REGISTRY. Serves README items C2, C3, C4, L7."""
from core import *

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

REGISTRY = {
    "C2 one-point step": lambda c: step(c, 1),
    "C3 two-point step": lambda c: step(c, 2),
    "count (OR-only witnesses)": count,
    "C4 count (any-gate witnesses)": count_any_gate,
    "Theorem: gates >= base": gates_ge_base,
}
