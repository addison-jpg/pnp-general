"""front request 08:34: on the 14 adversarial circuits (MergeFrac L* < 1), for every heavy point v (h(e_v) = 1, v in some set):
  split v2 (front-match w9/heavy/split3.py semantics): sets with v in S float over ALL their zero points; B-sets (v not in S)
           only over zero points with z_v = 1.
  R4:      star sets as above; B-sets only over the two zero points {e_v, z_{S_b}} (z_{S_b} = all ones off S_b).
LP = min max load (MergeFrac items M_z(w), union-find). Reports max over v."""
import itertools
import harness as H, mergefrac_runs as R
from w951 import systems

def M(c, w, z):
    S = c.sets[w]; g, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
    return frozenset(systems.merges(c, S, B)[0])

def zeros(c, w):
    S = c.sets[w]; rest = [v for v in range(c.n) if v not in S]
    return [sum(1 << v for v, b in zip(rest, bits) if b) for bits in itertools.product((0, 1), repeat=len(rest))]

def lp(menus): return R.solve_items(menus)[0] if False else _lp(menus)
def _lp(menus):
    import cfgI_prices as P
    return P.solve_items(menus)[0]

import sys; sys.path.insert(0, '../cfgI')
seen = set(); res = []
for t, c in H.corpora():
    if c.n > 20 or len(c.nots) != 1 or not c.is_correct() or not H.profile(c): continue
    k = str(c.to_dict())
    if k in seen or c.n - min(len(S) for S in c.sets) > 16: continue
    seen.add(k)
    L, *_ = R.mergefrac(c)
    if L >= 1 - 1e-9: continue
    Z = [zeros(c, w) for w in range(len(c.sets))]
    full = [sorted({M(c, w, z) for z in Z[w]}, key=sorted) for w in range(len(c.sets))]
    pts = sorted({u for S in c.sets for u in S})
    heavy = [v for v in pts if c.eval(1 << v)[c.h_wire]]
    rows = []
    for v in heavy:
        f2 = []; f4 = []
        for w, S in enumerate(c.sets):
            if v in S:
                f2.append(full[w]); f4.append(full[w])
            else:
                f2.append(sorted({M(c, w, z) for z in Z[w] if z >> v & 1}, key=sorted))
                zS = ((1 << c.n) - 1) & ~sum(1 << u for u in S)
                f4.append(sorted({M(c, w, 1 << v), M(c, w, zS)}, key=sorted))
        rows.append((v, _lp(f2), _lp(f4)))
    m2 = max((r[1] for r in rows), default=None); m4 = max((r[2] for r in rows), default=None)
    res.append((t, c.n, c.s, L, len(heavy), m2, m4))
    print(f'{t:48s} n={c.n:2d} s={c.s:2d} L*={L:.4f} heavy={heavy} split_v2 max={m2 if m2 is None else round(m2,4)} R4 max={m4 if m4 is None else round(m4,4)}'
          + ('  per v: ' + ' '.join(f'v{v}:{a:.3f}/{b:.3f}' for v, a, b in rows)), flush=True)
ok = [r for r in res if r[5] is not None]
print(f'\n{len(res)} circuits; with heavy points: {len(ok)}; max split_v2 = {max(r[5] for r in ok):.4f} (#>1: {sum(r[5] > 1 + 1e-9 for r in ok)}); '
      f'max R4 = {max(r[6] for r in ok):.4f} (#>1: {sum(r[6] > 1 + 1e-9 for r in ok)})')
