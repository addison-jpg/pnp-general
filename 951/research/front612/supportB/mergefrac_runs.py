"""Runs requested by front (08:06) for support-B.
(1) MergeFrac LP per circuit with a |S|>=4 set: min L s.t. mu_w is a distribution over ALL zero points z of S_w
    (z vanishing on S_w), load(g) = sum_w sum_z mu_w(z) [g in M_z(w)] <= L, M_z(w) = union-find merge gates over the
    wires that are 0 at z with atoms z + e_u (Lemma M; w951 systems.system + systems.merges). All sets w of the circuit
    take part (|S_w| >= 2). MergeFrac holds iff L* <= 1. Dual pi = load-row marginals (normalised to sum 1):
    L* = max_pi sum_w min_z pi(M_z(w)) with pi(gates) = 1. Reports support of pi and whether it is 0/1 up to scale.
(2) For B1-failing circuits: the shared 3rd+ merges (canonical z = z_{S_w}), whether each is downstream of the NOT
    (N-dependent), and every restriction x_v := b (w951 Circuit.restrict, semantic) that removes it.
Usage: python3 mergefrac_runs.py > mergefrac_runs.txt"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
import harness as H
from w951 import systems

def merge_menu(c, w):
    S = c.sets[w]; rest = [v for v in range(c.n) if v not in S]
    menu = {}
    for bits in itertools.product((0, 1), repeat=len(rest)):
        z = sum(1 << v for v, b in zip(rest, bits) if b)
        good, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
        M, _ = systems.merges(c, S, B)
        menu.setdefault(frozenset(M), z)
    return menu

def mergefrac(c):
    menus = [merge_menu(c, w) for w in range(len(c.sets))]
    gates = sorted({g for m in menus for C in m for g in C})
    gi = {g: i for i, g in enumerate(gates)}
    cols = [(w, C) for w, m in enumerate(menus) for C in m]   # mu variables, then L last
    nv = len(cols) + 1
    A_ub = np.zeros((len(gates), nv)); A_ub[:, -1] = -1
    for j, (w, C) in enumerate(cols):
        for g in C: A_ub[gi[g], j] = 1
    A_eq = np.zeros((len(menus), nv))
    for j, (w, C) in enumerate(cols): A_eq[w, j] = 1
    cobj = np.zeros(nv); cobj[-1] = 1
    r = linprog(cobj, A_ub=A_ub, b_ub=np.zeros(len(gates)), A_eq=A_eq, b_eq=np.ones(len(menus)), bounds=[(0, None)] * nv, method='highs')
    L = r.fun
    pi = -r.ineqlin.marginals
    pi = pi / pi.sum() if pi.sum() > 0 else pi
    supp = {gates[i]: round(float(p), 6) for i, p in enumerate(pi) if p > 1e-9}
    vals = sorted(set(round(v / max(supp.values()), 6) for v in supp.values())) if supp else []
    return L, supp, vals == [1.0], [len(m) for m in menus]

def shared_report(c, prof):
    owner = {}
    for p in prof:
        for g in p.get('third') or []:
            owner.setdefault(g, []).append(p['w'])
    down = set(c.downstream())
    out = []
    for g, ws in owner.items():
        if len(ws) < 2: continue
        kills = []
        for v in range(c.n):
            for b in (0, 1):
                d = c.restrict(v, b).detail
                if g in set(d['const']) | set(d['merged']) | set(d['dead']):
                    kills.append(f'x{v}:={b}')
        out.append(dict(gate=g, sets=ws, op=c.gates[g - c.n][0], N_dependent=g in down, killed_by=kills))
    return out

if __name__ == '__main__':
    items = [(t, c) for t, c in H.corpora() if c.n <= 20 and len(c.nots) == 1 and c.is_correct()]
    seen = set(); rows = []; fails = []
    for t, c in items:
        prof = H.profile(c)
        if not prof: continue
        key = str(c.to_dict())
        if key in seen: continue
        seen.add(key)
        if c.n - min(len(S) for S in c.sets) > 16: print('skip big', t); continue
        L, supp, zero_one, msz = mergefrac(c)
        rows.append((L, t, c.n, c.s, c.base, len(supp), zero_one))
        ok, _ = H.third_disjoint(c, prof)
        if not ok: fails.append((t, c, prof))
    rows.sort(reverse=True)
    print(f'(1) MergeFrac LP on {len(rows)} distinct circuits with a |S|>=4 set; L* > 1 on {sum(r[0] > 1 + 1e-9 for r in rows)}')
    print(f'    pi 0/1 (up to scale) on {sum(r[6] for r in rows)} of {len(rows)}')
    print('    L*        tag                                              n   s  base |supp pi| 0/1')
    for r in rows:
        print(f'    {r[0]:.6f}  {r[1]:48s} {r[2]:2d} {r[3]:3d} {r[4]:4d} {r[5]:8d} {r[6]}')
    print(f'\n(2) B1-failing distinct circuits: {len(fails)}')
    for t, c, prof in sorted(fails, key=lambda x: (x[1].s, x[1].n)):
        print(f'  {t} (n={c.n}, s={c.s}, base={c.base}, NOT wire {c.not_wire}, h wire {c.h_wire})')
        for r in shared_report(c, prof):
            print('     ', r)
