"""front request 08:09: for each circuit with MergeFrac L* < 1, the optimal 0/1 dual support K and, per set w, the zero
points z minimising |M_z(w) ∩ K| with h(z) (NOT input value at z): which world each set picks at the optimum."""
import itertools
import harness as H, mergefrac_runs as R
from w951 import systems

def run():
    seen = set()
    for t, c in H.corpora():
        if c.n > 20 or len(c.nots) != 1 or not c.is_correct() or not H.profile(c): continue
        k = str(c.to_dict())
        if k in seen or c.n - min(len(S) for S in c.sets) > 16: continue
        seen.add(k)
        L, supp, z1, _ = R.mergefrac(c)
        if L >= 1 - 1e-9: continue
        K = set(supp)
        print(f'{t}  n={c.n} s={c.s} base={c.base}  L*={L:.6f}  K={sorted(K)} (|K|={len(K)}, pi uniform={z1})')
        tot = 0
        for w, S in enumerate(c.sets):
            rest = [v for v in range(c.n) if v not in S]
            best, arg = None, []
            for bits in itertools.product((0, 1), repeat=len(rest)):
                z = sum(1 << v for v, b in zip(rest, bits) if b)
                good, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
                M, _ = systems.merges(c, S, B)
                m = len(set(M) & K)
                hz = wz[c.h_wire]
                if best is None or m < best: best, arg = m, [(z, hz, sorted(set(M) & K))]
                elif m == best: arg.append((z, hz, sorted(set(M) & K)))
            tot += best
            hs = sorted({a[1] for a in arg})
            ex = ', '.join(f'z={[v for v in range(c.n) if a[0] >> v & 1]} h={a[1]} MK={a[2]}' for a in arg[:3])
            print(f'   w={w} S={S}: min |M_z∩K| = {best}; {len(arg)} argmin z; h(z) in {hs}; e.g. {ex}')
        print(f'   check: sum_w min = {tot}, |K| = {len(K)}, ratio {tot/len(K):.6f}\n')
run()
