"""LPs for FracMatch (L-meta-951): minimum maximum gate load over menus, and its dual prices.

Primal (`min_max_load`): set w mixes its menu items C_{w,j} with weights lam_{w,j} (sum 1); inside
item (w,j) it spreads d_w * lam units over the gates of C_{w,j}, at most lam per gate; minimise
L = max gate load. FracMatch holds for the menus iff L* <= 1.

Dual (`Dual`): L* = max over prices pi >= 0, sum pi = 1, of sum_w min_j cheap_{d_w}(pi, C_{w,j}),
where cheap_d(pi, C) = total price of the d cheapest gates of C.

All LPs are solved with scipy.optimize.linprog(method='highs'). The variable and row order is the
one of the original scripts, so values, weights and marginals agree with them exactly.
"""
from collections import namedtuple

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from .circuit import as_circuit

__all__ = ['LoadLP', 'min_max_load', 'fraclp', 'fixed_load', 'cheap', 'ratio', 'Dual', 'lpdual',
           'resid_lp', 'EPS']

EPS = 1e-9

LoadLP = namedtuple('LoadLP', 'L lam pi mu load status')
LoadLP.__doc__ = """Result of min_max_load.
L      optimal max load (None if the LP is not solved to optimality)
lam    {(w, j): weight > 1e-9} of menu item j of set w
pi     {gate: dual price > 1e-9} = minus the marginal of the gate's load row (sums to 1 with unit caps)
mu     [marginal of the 'sum_j lam_{w,j} = 1' row of set w]
load   {gate: load}
status scipy status (0 = optimal)"""


def _mat(rows, nv):
    A = lil_matrix((len(rows), nv))
    b = np.zeros(len(rows))
    for i, (r, bb) in enumerate(rows):
        for k, a in r.items():
            A[i, k] = a
        b[i] = bb
    return A.tocsr(), b


def min_max_load(M, dem, cap=None, fixed=None, free=None, sort_items=True):
    """min L s.t. every gate g has load <= cap[g] * L (cap default 1).

    M[w]    the menu of set w: an iterable of gate collections (dict keys / frozensets / lists)
    dem[w]  the demand d_w = |S_w| - 1
    cap     {gate: capacity multiplier}
    fixed   {gate: absolute load bound} (those gates do not scale with L)
    free    predicate: gates with free(g) true get no load row at all (resid_lp's dummy gates)
    sort_items  process each item as sorted(C) (fraclp, fb/dual.lp); False keeps the given order (resid_lp)

    Legacy: fraclp (front-match work/notes951/w9/fraclp.py:10-39), lp (w9/fb/dual.py:9-45),
    resid_lp (tractability work/duals/resid.py:62-91). Returns LoadLP.
    """
    var = {'L': 0}

    def v(k):
        if k not in var:
            var[k] = len(var)
        return var[k]
    sysl = [(w, j, sorted(C) if sort_items else list(C)) for w, m in enumerate(M) for j, C in enumerate(m)]
    for w, j, C in sysl:
        v(('lam', w, j))
        for g in C:
            v(('y', w, j, g))
    gates = sorted({g for _, _, C in sysl for g in C if not (free and free(g))})
    eq, ub, grow = [], [], {}
    for w, m in enumerate(M):
        eq.append(({v(('lam', w, j)): 1 for j in range(len(m))}, 1))
    for w, j, C in sysl:
        r = {v(('y', w, j, g)): 1 for g in C}
        r[v(('lam', w, j))] = -dem[w]
        eq.append((r, 0))
        for g in C:
            ub.append(({v(('y', w, j, g)): 1, v(('lam', w, j)): -1}, 0))
    for g in gates:
        r = {v(('y', w, j, g)): 1 for w, j, C in sysl if g in C}
        if fixed and g in fixed:
            ub.append((r, fixed[g]))
        else:
            r[0] = -(1 if cap is None else cap.get(g, 1))
            ub.append((r, 0))
        grow[g] = len(ub) - 1
    Ae, be = _mat(eq, len(var))
    Au, bu = _mat(ub, len(var))
    cost = np.zeros(len(var))
    cost[0] = 1
    res = linprog(cost, A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be, bounds=[(0, None)] * len(var), method='highs')
    if res.status != 0:
        return LoadLP(None, {}, {}, [], {}, res.status)
    mg = res.ineqlin.marginals
    pi = {g: -mg[grow[g]] for g in gates if -mg[grow[g]] > EPS}
    mu = [res.eqlin.marginals[w] for w in range(len(M))]
    lam = {(k[1], k[2]): res.x[i] for k, i in var.items() if k != 'L' and k[0] == 'lam' and res.x[i] > EPS}
    load = {g: sum(res.x[var[('y', w, j, g)]] for w, j, C in sysl if g in C) for g in gates}
    return LoadLP(res.fun, lam, pi, mu, load, res.status)


def fraclp(c, coneonly=False, M=None):
    """(L*, lam, M) for the full menus of circuit c (or the given menus M): fraclp, w9/fraclp.py:10-39.
    FracMatch holds iff L* <= 1 (+ tolerance 1e-7 in the scripts)."""
    if M is None:
        from .systems import menus
        M = menus(c, coneonly)
    dem = as_circuit(c).demands
    r = min_max_load(M, dem)
    return r.L, r.lam, M


def resid_lp(Mr, dem):
    """(L, pi): min L where tuple-valued 'dummy' gates carry no load constraint
    (resid_lp, tractability work/duals/resid.py:62-91). (None, None) if not optimal."""
    r = min_max_load(Mr, dem, free=lambda g: isinstance(g, tuple), sort_items=False)
    return (None, None) if r.status != 0 else (r.L, r.pi)


def fixed_load(Dlist, lams, dem):
    """Fixed-weight rule: set w uses counted set Dlist[w][j] with the FIXED weight lams[w][j]; in each it
    spreads d_w * lam units, at most lam per gate; returns the minimum max gate load (inf if some used
    counted set is shorter than d_w or the LP fails). Legacy: fixedlp (w9/mixrule.py:14-41).
    At weights (1/2, 1/2), `L <= 1` is decided exactly by matching.frac_feasible_half."""
    var = {'L': 0}
    rows_eq, rows_ub = [], []

    def v(k):
        if k not in var:
            var[k] = len(var)
        return var[k]
    for w, (Ds, ls) in enumerate(zip(Dlist, lams)):
        for j, (D, l) in enumerate(zip(Ds, ls)):
            if l == 0:
                continue
            if len(D) < dem[w]:
                return float('inf')
            rows_eq.append(({v(('y', w, j, g)): 1 for g in D}, dem[w] * l))
    gates = sorted({k[3] for k in var if k != 'L'})
    for g in gates:
        r = {i: 1 for k, i in var.items() if k != 'L' and k[3] == g}
        r[0] = -1
        rows_ub.append((r, 0))
    nv = len(var)
    Ae, be = _mat(rows_eq, nv)
    Au, bu = _mat(rows_ub, nv)
    bounds = [(0, None)] + [None] * (nv - 1)
    for k, i in var.items():
        if k != 'L':
            bounds[i] = (0, lams[k[1]][k[2]])
    cst = np.zeros(nv)
    cst[0] = 1
    r = linprog(cst, A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be, bounds=bounds, method='highs')
    return r.fun if r.status == 0 else float('inf')


# ---------------------------------------------------------------- dual prices
def cheap(pi, C, d):
    """Total price of the d cheapest gates of C (dualp.py:16, w9/fb/dual.py:53)."""
    return sum(sorted(pi.get(g, 0) for g in C)[:d])


def ratio(pi, M, dem):
    """sum_w min_j cheap_{d_w}(pi, C_wj) / sum pi: the lower bound on L* certified by prices pi (dualp.py:17-18)."""
    return sum(min(cheap(pi, C, d) for C in m) for m, d in zip(M, dem)) / sum(pi.values())


class Dual:
    """Explicit dual LP of min_max_load (Dual, tractability work/duals/dualp.py:19-72).

    Variables pi_g >= 0 (sum 1), mu_w, and per item tau_{wj}, rho_{wjg} >= 0 with
        mu_w <= d_w * tau_wj - sum_g rho_wjg,   rho_wjg >= tau_wj - pi_g.
    solve() maximises sum mu and returns (L*, pi, mu); flat / sparse pick among the optimal duals.
    """

    def __init__(self, M, dem):
        self.M, self.dem = M, dem
        self.var = {}
        self.gates = sorted({g for m in M for C in m for g in C})
        for g in self.gates:
            self.v(('pi', g))
        for w in range(len(M)):
            self.v(('mu', w))
        self.ub = []
        for w, m in enumerate(M):
            for j, C in enumerate(m):
                t = self.v(('tau', w, j))
                r = {self.v(('mu', w)): 1, t: -dem[w]}
                for g in C:
                    rho = self.v(('rho', w, j, g))
                    r[rho] = 1
                    self.ub.append(({t: 1, rho: -1, self.v(('pi', g)): -1}, 0))
                self.ub.append((r, 0))
        self.nv = len(self.var)

    def v(self, k):
        if k not in self.var:
            self.var[k] = len(self.var)
        return self.var[k]

    def solve(self, obj=None, extra_ub=(), extra_eq=()):
        """Default: max sum mu s.t. sum pi = 1 -> (L*, pi, mu). With obj = {variable key: cost} the
        objective is MINIMISED and its value returned first."""
        cost = np.zeros(self.nv)
        if obj is None:
            for w in range(len(self.M)):
                cost[self.var[('mu', w)]] = -1
        else:
            for k, a in obj.items():
                cost[self.var[k]] = a
        Au, bu = _mat(self.ub + list(extra_ub), self.nv)
        Ae, be = _mat([({self.var[('pi', g)]: 1 for g in self.gates}, 1)] + list(extra_eq), self.nv)
        res = linprog(cost, A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be, bounds=[(0, None)] * self.nv, method='highs')
        assert res.status == 0, res.message
        pi = {g: res.x[self.var[('pi', g)]] for g in self.gates if res.x[self.var[('pi', g)]] > EPS}
        mu = [res.x[self.var[('mu', w)]] for w in range(len(self.M))]
        return (-res.fun if obj is None else res.fun), pi, mu

    def optrow(self, L):
        """The constraint sum mu >= L (up to 1e-9)."""
        return ({self.var[('mu', w)]: -1 for w in range(len(self.M))}, -L + EPS)

    def flat(self, L):
        """Among the optimal duals, one minimising max pi (most spread out): (pi, mu)."""
        k = ('mx',)
        if k not in self.var:
            self.var[k] = len(self.var)
            self.nv = len(self.var)
        ex = [self.optrow(L)] + [({self.var[('pi', g)]: 1, self.var[k]: -1}, 0) for g in self.gates]
        _, pi, mu = self.solve(obj={k: 1}, extra_ub=ex)
        return pi, mu

    def sparse(self, L, rng, tries=20):
        """Heuristic small-support optimal dual: random-weight LPs, keep the smallest support: (pi, mu)."""
        best = None
        for _ in range(tries):
            obj = {('pi', g): rng.random() for g in self.gates}
            _, pi, mu = self.solve(obj=obj, extra_ub=[self.optrow(L)])
            if best is None or len(pi) < len(best[0]):
                best = (pi, mu)
        return best


def lpdual(M, dem):
    """(L*, flat pi, flat mu, Dual): lpdual, tractability work/duals/resid.py:30-32."""
    D = Dual(M, dem)
    L, pi, mu = D.solve()
    pif, muf = D.flat(L)
    return L, pif, muf, D
