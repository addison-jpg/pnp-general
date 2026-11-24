"""Config (I) price brute force (owner: extract LP price vectors in Python, feed them to tractability for Lean).
Circuit: front-match w9/fb/cfgI.json (cx1 variant, set a recomputed via an AND gate). Data/LP, not Lean.
LPs (all: min L, every set w spreads mass 1 over its menu, load(g) <= L; dual: max_pi sum_w min_item pi-cost, pi(gates)=1):
  MF        MergeFrac, menu = merge sets M_z(w) over ALL zero points z of S_w (union-find, Lemma M).
  MF[a]     world assignment a in {0,1,*}^m: set w only uses z with h(z) = a_w ('*' = all). A 'global price contradiction'
            is an assignment with L > 1: a price vector no choice of worlds can pay for.
  FM        FracMatch, w951 lp.fraclp (maximal counted sets, cost = d_w cheapest).
For each LP: L* as an exact fraction, and ALL extreme optimal duals found by re-optimising random objectives on the optimal face."""
import itertools, json, os, random, sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.environ.get('W951_TOOLS', '/home/user/c951/tools'))
from w951 import Circuit, load, systems, lp

def frac(x, d=720): return Fraction(x).limit_denominator(d)

def zero_menu(c, w):
    S = c.sets[w]; rest = [v for v in range(c.n) if v not in S]; out = []
    for bits in itertools.product((0, 1), repeat=len(rest)):
        z = sum(1 << v for v, b in zip(rest, bits) if b)
        good, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
        M, _ = systems.merges(c, S, B)
        out.append((z, wz[c.h_wire], frozenset(M)))
    return out

def solve_items(menus):
    """menus[w] = list of gate frozensets (each item loads all its gates). Returns L*, gates, (A_ub, A_eq) for the dual."""
    gates = sorted({g for m in menus for C in m for g in C}); gi = {g: i for i, g in enumerate(gates)}
    cols = [(w, C) for w, m in enumerate(menus) for C in m]; nv = len(cols) + 1
    A_ub = np.zeros((len(gates), nv)); A_ub[:, -1] = -1
    A_eq = np.zeros((len(menus), nv))
    for j, (w, C) in enumerate(cols):
        A_eq[w, j] = 1
        for g in C: A_ub[gi[g], j] = 1
    cobj = np.zeros(nv); cobj[-1] = 1
    r = linprog(cobj, A_ub=A_ub, b_ub=np.zeros(len(gates)), A_eq=A_eq, b_eq=np.ones(len(menus)), bounds=[(0, None)] * nv, method='highs')
    return r.fun, gates

def dual_vertices(menus, L, tries=400, seed=0):
    """Dual: vars pi_g >= 0 (sum 1), t_w free; t_w <= pi(C) for every item C of w; sum_w t_w = L (optimal face).
    Random objectives over pi give extreme points of the optimal face."""
    gates = sorted({g for m in menus for C in m for g in C}); gi = {g: i for i, g in enumerate(gates)}
    G, m = len(gates), len(menus); nv = G + m
    rows, b = [], []
    for w, items in enumerate(menus):
        for C in set(items):
            r = np.zeros(nv); r[G + w] = 1
            for g in C: r[gi[g]] -= 1
            rows.append(r); b.append(0)
    A_eq = np.zeros((2, nv)); A_eq[0, :G] = 1; A_eq[1, G:] = 1
    rng = random.Random(seed); found = {}
    for k in range(tries):
        obj = np.zeros(nv); obj[:G] = [rng.gauss(0, 1) for _ in range(G)] if k else 0
        r = linprog(obj, A_ub=np.array(rows), b_ub=np.array(b), A_eq=A_eq, b_eq=[1, L - 1e-10],
                    bounds=[(0, None)] * G + [(None, None)] * m, method='highs')
        if r.status != 0: continue
        v = tuple(sorted((gates[i], frac(x)) for i, x in enumerate(r.x[:G]) if x > 1e-9))
        found[v] = found.get(v, 0) + 1
    return found

def show(name, menus, c, verts=True):
    L, gates = solve_items(menus)
    print(f'[{name}] L* = {L:.6f} ~ {frac(L)}')
    if verts:
        V = dual_vertices(menus, L)
        print(f'   {len(V)} distinct extreme optimal price vectors (pi(gates) = 1):')
        for v, cnt in sorted(V.items(), key=lambda t: -t[1])[:12]:
            desc = ', '.join(f'g{g}({c.gates[g - c.n][0]}{"*" if g in down else ""})={p}' for g, p in v)
            print(f'     x{cnt:3d}  {desc}')
    return L

if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else 'cfgI.json'
    c = load(path)[0]
    down = set(c.downstream())
    print(f'circuit {path}: n={c.n} s={c.s} base={c.base} sets={c.sets} NOT wire {c.not_wire} h wire {c.h_wire}; * = downstream of NOT')
    print('verify:', {k: v for k, v in c.verify().items() if k in ('correct', 'clean', 'read', 's', 'base')})
    Z = [zero_menu(c, w) for w in range(len(c.sets))]
    for w, zm in enumerate(Z):
        print(f'   set {w} {c.sets[w]}: {len(zm)} zero points, h=0 at {sum(1 for t in zm if t[1] == 0)}, distinct merge sets {len({t[2] for t in zm})}')
    show('MF  MergeFrac, all worlds', [[t[2] for t in zm] for zm in Z], c)
    # global price contradiction search: every world assignment
    worst = []
    for a in itertools.product((0, 1, None), repeat=len(Z)):
        menus = [[t[2] for t in zm if a[w] is None or t[1] == a[w]] for w, zm in enumerate(Z)]
        if any(not m for m in menus): continue
        L, _ = solve_items(menus)
        worst.append((L, a))
    worst.sort(key=lambda t: -t[0])
    print(f'\n[MF worlds] {len(worst)} feasible world assignments (per set h(z) = 0 / 1 / any); max L = {worst[0][0]:.6f}')
    for L, a in worst[:10]:
        print(f'   L = {L:.6f} ~ {frac(L)}  worlds {["*" if x is None else x for x in a]}  {"CONTRADICTION (L > 1)" if L > 1 + 1e-9 else ""}')
    for L, a in worst[:3]:
        if L > 1 + 1e-9 or L == worst[0][0]:
            menus = [[t[2] for t in zm if a[w] is None or t[1] == a[w]] for w, zm in enumerate(Z)]
            show(f'MF worlds {["*" if x is None else x for x in a]}', menus, c)
    Lf, lam, Mf = lp.fraclp(c)
    print(f'\n[FM FracMatch, w951 lp.fraclp] L* = {Lf:.6f} ~ {frac(Lf)}')
    Ld, pif, muf, D = lp.lpdual(Mf, c.demands)
    print('   one optimal pi (w951 lpdual):', {g: str(frac(p)) for g, p in sorted(pif.items()) if p > 1e-9} if isinstance(pif, dict) else pif)
