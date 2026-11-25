"""asteroid extension: the continuous form. Φ(p) = E[slack(Q)] when each point is in the cube Q with probability p.
Φ(0) = slack at the empty cube, Φ(1) = 0, and the remaining `sorry` is `0 ≤ Φ(0)` for a minimal counterexample
(one-not/lean/PEqualNP/W951/ContinuousAttach.lean).

  phi(NAME, P)                         a term in a claim: P is a decimal or a fraction a/b in [0, 1]
  claim forall p phi(NAME) >= 0 [by lean]   Φ ≥ 0 on [0,1]. Python: slack ≥ 0 at every cube (which implies it) and the
                                            least value of Φ on a grid. `by lean`: the kernel checks every cube, and the
                                            second module states `0 ≤ Phi … p` for all p in [0,1] in the project's `Phi`.
  claim monotone phi(NAME)                  the level means of slack never increase (so Φ is nonincreasing). Python only.
  levelmeans NAME                           prints the mean slack at each level |Q| = i
"""
import re
from fractions import Fraction
import asteroid.asteroid as A

def _levels(api, name):
    A.need("numpy", "the continuous form (phi, bernstein)"); import continuous as C
    c = api["env"][name]; n = c["n"]
    sl = C.slack_table(c, 0, any_gate=False)
    return n, sl, [Fraction(int(sum(int(sl[Q]) for Q in range(1 << n) if bin(Q).count("1") == i)), max(1, __import__("math").comb(n, i))) for i in range(n + 1)]

def _phi(m, n, p):
    from math import comb
    return sum(comb(n, i) * p ** i * (1 - p) ** (n - i) * m[i] for i in range(n + 1))

def claim_expr(text, lean, api, force=False):
    m = re.fullmatch(r"forall p phi\((\w+)\)\s*>=\s*0", text)
    if m:
        name = m.group(1); n, sl, lv = _levels(api, name); worst = min(int(x) for x in sl)
        grid = min(_phi(lv, n, Fraction(i, 100)) for i in range(101)); ok = worst >= 0
        if lean and (ok or force): api["lean_claims"].append((name, "claim", f"slackNonnegAll {name} = true", text))
        return ok, f"least slack over {1 << n} cubes = {worst}; least Phi on a grid of 101 points = {float(grid):.3f}", text
    m = re.fullmatch(r"monotone phi\((\w+)\)", text)
    if m:
        n, sl, lv = _levels(api, m.group(1)); up = [i for i in range(n) if lv[i + 1] > lv[i]]
        return (not up), "level means " + " ".join(f"{float(x):.2f}" for x in lv[:6]) + (" ..." if n > 5 else "") + (f"; rises at level {up[0]} -> {up[0] + 1}" if up else "; never rises"), text
    m = re.fullmatch(r"phi\((\w+),\s*([\d./]+)\)\s*(=|!=|<=|>=|<|>)\s*(-?[\d./]+)", text)
    if m:
        import operator
        ops = {"=": operator.eq, "!=": operator.ne, "<": operator.lt, "<=": operator.le, ">": operator.gt, ">=": operator.ge}
        n, sl, lv = _levels(api, m.group(1)); p = Fraction(m.group(2)); v = _phi(lv, n, p); k = Fraction(m.group(4))
        return ops[m.group(3)](v, k), f"Phi({m.group(2)}) = {float(v):.4f}" + (" (Python only: exact rational arithmetic, no Lean form)" if lean else ""), text
    return None

def handle(line, api):
    if m := re.fullmatch(r"levelmeans (\w+)", line):
        n, sl, lv = _levels(api, m.group(1)); print(f"{api['ln']}: level means of slack for {m.group(1)}: " + " ".join(f"{float(x):.2f}" for x in lv)); return True
    return False
