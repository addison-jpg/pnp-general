"""Density form of |F2|, base, slack for one-NOT circuits (see limits_density_form.md).
Run: python3 -I research/one-not/research/open/limits_density_form.py   (I = isolated; run from repo root)"""
import sys, json, glob, random, itertools
from fractions import Fraction
from math import comb
sys.path.insert(0, 'research/one-not/tools/search')
import core

def bits(m): return [i for i in range(m.bit_length()) if m >> i & 1]

def witness_Z(c, w):
    """Per OR gate k: set of Z (as masks) that occur in some witness tuple (R, Z, u, u'), Q = empty.
    Also tuples count. Lean F2Wit: Z zero on R, g(Z)=0, g(Z+u)=g(Z+u')=1, u != u' in R."""
    n = c['n']; out = {}
    Rs = [sum(1 << u for u in R) for R in c['sets']]
    for k, g in enumerate(c['gates']):
        if g[0] != 'or': continue
        t = w[n + k]; Zs = set(); ntup = 0
        for R in Rs:
            for Z in range(1 << n):
                if Z & R or t >> Z & 1: continue
                us = [u for u in bits(R) if t >> (Z | 1 << u) & 1]
                if len(us) >= 2: Zs.add(Z); ntup += comb(len(us), 2)
        out[k] = (Zs, ntup)
    return out

def f2_from_family(fam, Q):
    """g in F2(Q) iff Q subset of some witness Z."""
    return sum(any(Q & ~Z == 0 for Z in Zs) for Zs, _ in fam.values())

def wire_values(c):
    """Single-point evaluations V0[g] = g(0), E[g] = {u : g(e_u) = 1}: the relations used by the local form."""
    n = c['n']; V0 = {}; E = {}
    for i in range(n): V0[i] = 0; E[i] = {i}
    for k, g in enumerate(c['gates']):
        x = n + k
        if g[0] == 'not':
            V0[x] = 1 - V0[g[1]]
            # g(e_u) = 1 - a(e_u); a(e_u) = 1 iff (V0[a]==1) or (u in E[a])
            E[x] = {u for u in range(n) if 1 - (1 if (V0[g[1]] or u in E[g[1]]) else 0)}
        else:
            a, b = g[1], g[2]
            val = lambda y, u: V0[y] if V0[y] else (1 if u in E[y] else 0)
            op = (lambda p, q: p | q) if g[0] == 'or' else (lambda p, q: p & q)
            V0[x] = op(V0[a], V0[b]); E[x] = {u for u in range(n) if op(val(a, u), val(b, u))}
    return V0, E

def check(path, verbose=True):
    c = json.load(open(path)); n = c['n']; w = core.tables(n, c['gates'])
    fam = witness_Z(c, w)
    # (1) F2(Q) via the family = core.witness (OR gates only), every Q (sampled if n > 9)
    Qs = range(1 << n) if n <= 9 else [0] + random.sample(range(1 << n), 150)
    ok1 = all(f2_from_family(fam, Q) == len(core.witness(c, Q, w, any_gate=False)) for Q in Qs)
    F2 = f2_from_family(fam, 0)
    # (2) base as a size histogram
    N = {}
    for R in c['sets']: N[len(R)] = N.get(len(R), 0) + 1
    B = sum((k - 1) * v for k, v in N.items()); ok2 = B == core.base(c)
    # (3) local form at Q = empty: relations V0, E
    V0, E = wire_values(c); Rset = [set(R) for R in c['sets']]
    m = {}; 
    for k, g in enumerate(c['gates']):
        if g[0] != 'or': continue
        x = n + k
        m[k] = 0 if V0[x] else sum(len(R & E[x]) >= 2 for R in Rset)   # sets R with two points u : g(e_u)=1
    F2loc = sum(1 for v in m.values() if v >= 1)
    bonf_lo = sum(v - comb(v, 2) for v in m.values()); sum_m = sum(m.values())
    # NOT-dependent gates
    h = [n + k for k, g in enumerate(c['gates']) if g[0] == 'not']
    dep = set(h)
    for k, g in enumerate(c['gates']):
        if any(a in dep for a in g[1:]): dep.add(n + k)
    nonloc = [k for k in m if n + k in dep]
    # (3b) exact witness-set counts: mR[g] = number of sets R having a witness (g, R, Z, u, u') for some Z
    mR = {}
    for k, g in enumerate(c['gates']):
        if g[0] != 'or': continue
        t = w[n + k]; cnt = 0
        for R in c['sets']:
            Rm = sum(1 << u for u in R)
            if any(not (Z & Rm) and not (t >> Z & 1) and sum(t >> (Z | 1 << u) & 1 for u in R) >= 2 for Z in range(1 << n)): cnt += 1
        mR[k] = cnt
    P1 = sum(mR.values()); P2 = sum(comb(v, 2) for v in mR.values()); ge1 = sum(v >= 1 for v in mR.values())
    # (4) Phi(p) exactly at p = 1/3 : E[F2] by definition vs gate-wise union of subcubes; E[base] closed form
    p = Fraction(1, 3)
    ok4 = None
    if n <= 9:
        D = {}
        for k, (Zs, _) in fam.items():
            D[k] = {Q for Q in range(1 << n) if any(Q & ~Z == 0 for Z in Zs)}
        direct = sum(p ** bin(Q).count('1') * (1 - p) ** (n - bin(Q).count('1')) * len(core.witness(c, Q, w, any_gate=False)) for Q in range(1 << n))
        gatewise = sum(sum(p ** bin(Q).count('1') * (1 - p) ** (n - bin(Q).count('1')) for Q in D[k]) for k in D)
        Ebase = sum((len(R) - 1) * (1 - p) ** len(R) for R in c['sets'])
        dirb = sum(p ** bin(Q).count('1') * (1 - p) ** (n - bin(Q).count('1')) * core.base(c, Q) for Q in range(1 << n))
        ok4 = (direct == gatewise and Ebase == dirb)
    row = dict(f=path.split('/')[-1], n=n, sets=len(c['sets']), gates=len(c['gates']), nots=len(h), F2=F2, base=B,
               slack=F2 - B, ok_family=ok1, ok_base=ok2, F2_local=F2loc, F2_nonlocal=F2 - F2loc,
               local_gates_h_dependent=len(nonloc), bonf_lo=bonf_lo, sum_m=sum_m,
               bonf_ok=bonf_lo <= F2loc <= sum_m, P1=P1, P2=P2, exact_ge1=(ge1 == F2), bonf_exact=(P1 - P2 <= F2 <= P1), ok_Phi=ok4)
    return row

if __name__ == '__main__':
    random.seed(1)
    files = sorted(glob.glob('research/one-not/data/witnesses/*.json'))
    for f in files:
        r = check(f); print(json.dumps(r))
