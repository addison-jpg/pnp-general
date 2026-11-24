"""Lemma (D) of CERT-1c / CERT-3c (qg-d2; cTAHG has (S)): data on WHEN the cone merge set of a set through v dies under x_v := 1.
For each instance (circuit with every gate read, Q, h not a literal or constant on the cube x_Q = 1, i.e. not CubeLocal) and each
alive v, each alive set w through v and each zero point z ⊇ Q avoiding S_w: does the cone merge set M^cone_z(w) lie in
F2(Q) \\ F2(Q+v)? Reported per (instance, v, w): z = Q dies; some z dies; z = top_w dies; and per (instance, v): (D) holds at z = Q
for every w; (D) holds with a per-set choice. For every surviving cone merge gate at z = Q, the features of its survival
witness (w', Z') at Q+v: g(Q+e_v), h(Q+e_v) (v heavy), h(Z'), g N-dependent, |S_w'|.
Run from 951/:  python3 tools/kill_tests/certd.py OUT.jsonl FILE_OR_DIR ...
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


def cube_local(T, hw, n, Q):
    h = T[hw]
    full = (1 << n) - 1
    pts = [x for x in range(1 << n) if x & Q == Q]
    vals = {h >> x & 1 for x in pts}
    if len(vals) == 1:
        return True
    return any(all((h >> x & 1) == (x >> a & 1) for x in pts) for a in range(n) if not Q >> a & 1)


def witnesses(c, T, sets, g, Qm, full):
    res = []
    for i, m in enumerate(sets):
        if m & Qm:
            continue
        free = full & ~(Qm | m)
        sub = free
        while True:
            Z = Qm | sub
            if not (T[g] >> Z & 1):
                us = [u for u in c.sets[i] if T[g] >> (Z | 1 << u) & 1]
                if len(us) >= 2:
                    res.append((i, Z))
            if sub == 0:
                break
            sub = (sub - 1) & free
    return res


def instance(c, Q):
    n = c.n
    full = (1 << n) - 1
    T, T0, T1 = c.tables(), c.tables(force=0), c.tables(force=1)
    h = T[c.h_wire]
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive or cube_local(T, c.h_wire, n, Q):
        return None
    apts = sorted({u for i in alive for u in c.sets[i]})
    ors = [n + k for k, g in enumerate(c.gates) if g[0] == 'or']
    W = {g: witnesses(c, T, sets, g, Q, full) for g in ors}
    F2Q = {g for g in ors if W[g]}
    out = {}
    for v in apts:
        Qv = Q | 1 << v
        dead = {g for g in F2Q if not any(Z >> v & 1 for (_, Z) in W[g])}   # Lemma D
        star = [i for i in alive if sets[i] >> v & 1]
        rec = {'heavy': bool(h >> Qv & 1), 'sets': []}
        for i in star:
            cone = c.cone(c.outs[i])
            free = full & ~(Q | sets[i])
            dz = []
            sub = free
            while True:
                M = merges_at(c, T, c.sets[i], Q | sub, cone)
                if M <= dead:
                    dz.append(Q | sub)
                if sub == 0:
                    break
                sub = (sub - 1) & free
            M0 = merges_at(c, T, c.sets[i], Q, cone)
            surv = []
            for g in sorted(M0 - dead):
                wz = [(j, Z) for (j, Z) in W[g] if Z >> v & 1]
                j, Z = wz[0]
                surv.append(dict(g=g, see=bool(T[g] >> Qv & 1), hZ=bool(h >> Z & 1), ndep=T0[g] != T1[g],
                                 wsize=len(c.sets[j]), g0=bool(T0[g] >> Qv & 1), g1=bool(T1[g] >> Qv & 1)))
            rec['sets'].append(dict(w=i, d=len(c.sets[i]) - 1, q_dies=not surv, some_dies=bool(dz),
                                    all_see=all(T[g] >> Qv & 1 for g in M0),
                                    top_dies=(full & ~sets[i]) in dz, n_dying_z=len(dz), n_z=bin(free).count('1'),
                                    surv=surv))
        out[v] = rec
    return out


def work(item):
    name, d = item
    try:
        c = Circuit.from_dict(d)
    except Exception as e:  # noqa: BLE001
        return dict(name=name, skip='parse: %r' % e)
    if len(c.nots) != 1 or c.n > 9 or not c.is_correct() or not c.all_read():
        return dict(name=name, skip='not an all-read correct one-NOT circuit with n <= 9')
    rng = random.Random(zlib.crc32(name.encode()))
    Qs = [0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) & rng.randrange(1 << c.n) for _ in range(3)]
    inst = []
    for Q in sorted(set(Qs)):
        r = instance(c, Q)
        if r is not None:
            inst.append(dict(Q=Q, v=r))
    return dict(name=name, n=c.n, s=c.s, base=c.base, clean=c.is_clean(), essential=c.is_essential(), inst=inst)


if __name__ == '__main__':
    import multiprocessing as mp
    outf = sys.argv[1]
    cs = load(sys.argv[2:])
    with mp.Pool(int(os.environ.get('PROCS', '4'))) as pool, open(outf, 'w') as fo:
        for r in pool.imap_unordered(work, cs, chunksize=16):
            fo.write(json.dumps(r) + '\n')
            fo.flush()
