"""Which instances of the F2 step are now PROVED in Lean by CERT-3c (qg-d2, 2026-11-24)?
(S): cTAHG's certS_of_tu (pairwise TU of the zero points); (D): qg-d2's certD_of_heavy_see (v heavy, i.e. the NOT gate is 0 at
Q + e_v, and every cone merge of every set through v is 1 at Q + e_v). For each non-local, every-gate-read instance (circuit, Q)
and each alive v: is there a choice of zero points z_w ⊇ Q off S_w for the star of v (any z for degree 1; for degree >= 2 search
over all choices) with pairwise TU in one direction, AND v heavy with SEE at Q + e_v for all those cone merges (then (D) holds by the
lemma, no data needed)? proved0: the unified (D) from F1* (every cone merge is 1 at Q + e_v in the real circuit AND in C_0,
the circuit with the NOT gate forced to 0), heavy or light v.
Run from 951/:  python3 tools/kill_tests/proved_cover.py OUT.jsonl FILE_OR_DIR ...
"""
import json
import os
import random
import sys
import zlib

sys.path.insert(0, 'tools')
sys.path.insert(0, 'tools/kill_tests')
from w951 import Circuit  # noqa: E402
from ucert import merges_at, load  # noqa: E402
from tu_cert import tu, is_local  # noqa: E402


def instance(c, Q):
    n = c.n
    T = c.tables()
    T0 = c.tables(force=0)
    h = T[c.h_wire]
    full = (1 << n) - 1
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive or is_local(c, h, Q, full):
        return None
    apts = sorted({u for i in alive for u in c.sets[i]})
    rec = {}
    for v in apts:
        Qv = Q | 1 << v
        heavy = bool(h >> Qv & 1)
        star = [i for i in alive if sets[i] >> v & 1]
        cone = {i: c.cone(c.outs[i]) for i in star}
        opts, opts0 = [], []
        for i in star:
            free = full & ~(Q | sets[i])
            o, o0 = [], []
            sub = free
            while True:
                z = Q | sub
                M = merges_at(c, T, c.sets[i], z, cone[i])
                if all(T[g] >> Qv & 1 for g in M):
                    o.append(z)
                    if all(T0[g] >> Qv & 1 for g in M):
                        o0.append(z)
                if sub == 0:
                    break
                sub = (sub - 1) & free
            opts.append(o)
            opts0.append(o0)

        def pick(j, chosen, opts=opts):
            if j == len(star):
                return True
            for z in opts[j]:
                if all(tu(h, c.sets[star[a]], chosen[a], z) or tu(h, c.sets[star[j]], z, chosen[a]) for a in range(j)):
                    if pick(j + 1, chosen + [z], opts):
                        return True
            return False
        see_tu = pick(0, [])
        see0_tu = pick(0, [], opts0)
        rec[v] = dict(deg=len(star), heavy=heavy, see_tu=see_tu, proved=heavy and see_tu, proved0=see0_tu)
    return dict(Q=Q, proved=any(r['proved'] for r in rec.values()), proved0=any(r['proved0'] for r in rec.values()), rec=rec)


def work(item):
    name, d = item
    try:
        c = Circuit.from_dict(d)
    except Exception:  # noqa: BLE001
        return []
    if len(c.nots) != 1 or c.n > 9 or not c.is_correct() or not c.all_read():
        return []
    rng = random.Random(zlib.crc32(name.encode()))
    Qs = sorted(set([0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) & rng.randrange(1 << c.n) for _ in range(3)]))
    out = []
    for Q in Qs:
        r = instance(c, Q)
        if r is not None:
            r['name'] = name
            r['n'] = c.n
            r['s'] = c.s
            out.append(r)
    return out


if __name__ == '__main__':
    import multiprocessing as mp
    cs = load(sys.argv[2:])
    with mp.Pool(int(os.environ.get('PROCS', '4'))) as pool, open(sys.argv[1], 'w') as fo:
        for rs in pool.imap_unordered(work, cs, chunksize=16):
            for r in rs:
                fo.write(json.dumps(r) + '\n')
