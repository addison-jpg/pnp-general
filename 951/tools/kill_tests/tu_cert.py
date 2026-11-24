"""(S) by the real Theorem U (cTAHG, 13:40 UTC; coord: prove (S) of CERT-1c/3c).

REAL THEOREM U: for real points a <= b with h(a) = h(b), every wire of a one-NOT circuit is monotone from a to b
(the lift M is monotone and real = M(x, not h(x))). So the cone merge sets of w (zero point z_w) and w' (zero point
z_w') are disjoint as soon as every two points u != u' of S_w have one, x, with z_w + e_x <= z_w' and
h(z_w + e_x) = h(z_w') (pair condition TU(w -> w')); one direction per pair suffices.

Checks per (circuit, Q non-local, v):
  H3u: zero points z_w ⊇ Q off S_w for the sets through v, every cone merge dying under x_v := 1 (D), and every pair
       of star sets with TU in one direction  (=> (S) is PROVED, not just observed);
  stair: the staircase z_j = Q | union_{i<j} (S_{w_i} minus v) for some order, with (D) and TU;
  c1: CERT-1c itself (z_w = Q, (S) and (D) observed);
  hsee_stair: a HEAVY v whose staircase cone merges are all 1 at Q + e_v (SEE, so (D) by certD_of_heavy_see) and pairwise TU
       (so (S) by certS_of_tu): CERT-3c PROVED at v (CertStair.lean `cert3c_of_heavy_tu`);
  hsee_tu: the same with any zero points z_w ⊇ Q off S_w (search).
Run from 951/:  python3 tools/kill_tests/tu_cert.py FILE_OR_DIR ...  (json circuits or jsonl corpora), one json line per instance.
"""
import json, sys, os, itertools, random, zlib
sys.path.insert(0, 'tools'); sys.path.insert(0, 'tools/kill_tests')
from w951 import Circuit  # noqa: E402
from ucert import merges_at  # noqa: E402


def f2set(c, T, sets, ors, Qm, full):
    res = set()
    for g in ors:
        for i, m in enumerate(sets):
            if m & Qm:
                continue
            free = full & ~(Qm | m)
            sub = free
            hit = False
            while True:
                Z = Qm | sub
                if not (T[g] >> Z & 1) and sum(1 for u in c.sets[i] if T[g] >> (Z | 1 << u) & 1) >= 2:
                    hit = True
                    break
                if sub == 0:
                    break
                sub = (sub - 1) & free
            if hit:
                res.add(g)
                break
    return res


def is_local(c, h, Q, full):
    dep = 0
    for u in range(c.n):
        if Q >> u & 1:
            continue
        rest = full & ~(Q | 1 << u)
        sub = rest
        while True:
            x = Q | sub
            if (h >> x & 1) != (h >> (x | 1 << u) & 1):
                dep += 1
                break
            if sub == 0:
                break
            sub = (sub - 1) & rest
    return dep <= 1


def tu(h, S, z, z2, v=None):
    """pair condition TU(w -> w'): every two points of S have one x with z + e_x <= z2 and h(z + e_x) = h(z2)."""
    good = [x for x in S if ((z | 1 << x) & ~z2) == 0 and (h >> (z | 1 << x) & 1) == (h >> z2 & 1)]
    return len(S) - len(good) <= 1


def instance(c, Q):
    n = c.n
    T = c.tables()
    h = T[c.h_wire]
    full = (1 << n) - 1
    sets = [sum(1 << u for u in S) for S in c.sets]
    ors = [n + k for k, g in enumerate(c.gates) if g[0] == 'or']
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive or is_local(c, h, Q, full):
        return None
    F2Q = f2set(c, T, sets, ors, Q, full)
    apts = sorted({u for i in alive for u in c.sets[i]})
    rec = {}
    for v in apts:
        star = [i for i in alive if sets[i] >> v & 1]
        gain = F2Q - f2set(c, T, sets, ors, Q | 1 << v, full)
        cone = {i: c.cone(c.outs[i]) for i in star}
        # c1
        M1 = [merges_at(c, T, c.sets[i], Q, cone[i]) for i in star]
        c1 = all(M <= gain for M in M1) and all(not (M1[a] & M1[b]) for a in range(len(M1)) for b in range(a + 1, len(M1)))
        # dying zero points per star set
        opts = []
        for i in star:
            free = full & ~(Q | sets[i])
            o = []
            sub = free
            while True:
                z = Q | sub
                if merges_at(c, T, c.sets[i], z, cone[i]) <= gain:
                    o.append(z)
                if sub == 0:
                    break
                sub = (sub - 1) & free
            opts.append(o)

        def pick(j, chosen):
            if j == len(star):
                return True
            for z in opts[j]:
                if all(tu(h, c.sets[star[a]], chosen[a], z) or tu(h, c.sets[star[j]], z, chosen[a])
                       for a in range(j)):
                    if pick(j + 1, chosen + [z]):
                        return True
            return False
        h3u = pick(0, [])
        stair = False
        for order in itertools.permutations(range(len(star))):
            z = Q
            zs = [None] * len(star)
            for j in order:
                zs[j] = z
                z |= sets[star[j]] & ~(1 << v)
            if all(zs[j] in opts[j] for j in range(len(star))) and all(
                    tu(h, c.sets[star[a]], zs[a], zs[b]) or tu(h, c.sets[star[b]], zs[b], zs[a])
                    for a in range(len(star)) for b in range(a + 1, len(star))):
                stair = True
                break
        # heavy v with SEE at TU-compatible staircase points ((D) free by qg-d2's certD_of_heavy_see)
        hsee = False
        if h >> (Q | 1 << v) & 1:
            for order in itertools.permutations(range(len(star))):
                z = Q
                zs = [None] * len(star)
                for j in order:
                    zs[j] = z
                    z |= sets[star[j]] & ~(1 << v)
                see = all(T[g] >> (Q | 1 << v) & 1 for j in range(len(star))
                          for g in merges_at(c, T, c.sets[star[j]], zs[j], cone[star[j]]))
                if see and all(tu(h, c.sets[star[a]], zs[a], zs[b]) or tu(h, c.sets[star[b]], zs[b], zs[a])
                               for a in range(len(star)) for b in range(a + 1, len(star))):
                    hsee = True
                    break
        # heavy v, any zero points with SEE, pairwise TU (search)
        hsee_any = False
        if h >> (Q | 1 << v) & 1:
            sopts = []
            for i in star:
                free = full & ~(Q | sets[i])
                o = []
                sub = free
                while True:
                    z = Q | sub
                    if all(T[g] >> (Q | 1 << v) & 1 for g in merges_at(c, T, c.sets[i], z, cone[i])):
                        o.append(z)
                    if sub == 0:
                        break
                    sub = (sub - 1) & free
                sopts.append(o)

            def spick(j, chosen):
                if j == len(star):
                    return True
                return any(all(tu(h, c.sets[star[a]], chosen[a], z) or tu(h, c.sets[star[j]], z, chosen[a])
                               for a in range(j)) and spick(j + 1, chosen + [z]) for z in sopts[j])
            hsee_any = spick(0, [])
        rec[v] = dict(deg=len(star), heavy=bool(h >> (Q | 1 << v) & 1), c1=c1, h3u=h3u, stair=stair, hsee_stair=hsee,
                      hsee_tu=hsee_any)
    return dict(Q=Q, rec=rec, c1=any(r['c1'] for r in rec.values()), h3u=any(r['h3u'] for r in rec.values()),
                stair=any(r['stair'] for r in rec.values()), hsee_stair=any(r['hsee_stair'] for r in rec.values()),
                hsee_tu=any(r['hsee_tu'] for r in rec.values()),
                has_heavy=any(r['heavy'] for r in rec.values()))


def main(paths):
    for p in paths:
        files = []
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                files += [os.path.join(root, f) for f in sorted(fs) if f.endswith(('.json', '.jsonl'))]
        else:
            files = [p]
        for f in files:
            lines = open(f).read().splitlines() if f.endswith('.jsonl') else [open(f).read()]
            for i, l in enumerate(lines):
                try:
                    c = Circuit.from_dict(json.loads(l))
                except Exception:  # noqa: BLE001
                    continue
                if len(c.nots) != 1 or c.n > 9 or not c.is_correct() or not c.all_read():
                    continue
                name = '%s:%d' % (f, i)
                rng = random.Random(zlib.crc32(name.encode()))
                Qs = sorted(set([0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) & rng.randrange(1 << c.n)
                                       for _ in range(3)]))
                for Q in Qs:
                    r = instance(c, Q)
                    if r is not None:
                        r['name'] = name
                        print(json.dumps(r), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
