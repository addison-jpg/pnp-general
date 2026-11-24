"""Uniform certificates for the F2 step (qg-d2, session_01GmnDhgAdyDijthBgZgJFWn; owner: 'make the circuits generalize
to size n' -> find an explicit, size-independent certificate behind the step, for the proof owners to prove).

F2 step (DECISION 12:46): some alive v has gain(v) = |F2(Q) \\ F2(Q+v)| >= cost(v) = sum_{alive w ∋ v} d_w.
Certificate shape tested here: for each alive w ∋ v a zero point Z_w ⊇ Q avoiding S_w whose Lemma-M merge set M_{Z_w}(w)
(exactly d_w OR gates, union-find in circuit order) lies inside gain(v), the merge sets of the sets through v pairwise
disjoint. Such a family gives gain(v) >= cost(v) at once, so a RULE that always produces one is a proof plan for all n.
  H1: Z_w = Q for every w ∋ v                (one rule, no choice)
  H2: Z_w = top_w = all points outside S_w   (one rule, no choice)
  H3: some choice of Z_w per set, disjoint   (search; the weakest form)
  H1c, H2c, H3c: the same with the union-find run only over the cone of o_w (gates that feed the output of w): a MinCE
  has no unread gates (R4 live), and junk outside the cone is exactly what breaks H1-H3 on star4.
Per instance it records which alive v satisfy each, and how simple v-rules do (every heavy v; some heavy v; the alive
point of largest degree; the smallest alive point), next to the step itself (some v with gain >= cost).
Run from one-not/:  python3 tools/kill_tests/ucert.py OUT.jsonl FILE_OR_DIR ...   (json circuits or jsonl corpora)
"""
import json
import os
import random
import sys
import zlib

sys.path.insert(0, 'tools')
from w951 import Circuit  # noqa: E402


def merges_at(c, T, S, Z, within=None):
    """Lemma-M merge gates of the set S at the zero point Z (union-find over the wires that are 0 at Z, circuit order);
    with `within`, only gate wires in that set take part (the cone of o_w)."""
    par = {u: u for u in S}

    def find(u):
        while par[u] != u:
            par[u] = par[par[u]]
            u = par[u]
        return u
    n = c.n
    B = {u: frozenset([u]) for u in S}
    M = []
    for k, g in enumerate(c.gates):
        i = n + k
        if T[i] >> Z & 1 or (within is not None and i not in within):
            continue
        B[i] = frozenset(u for u in S if T[i] >> (Z | 1 << u) & 1)
        if g[0] == 'or':
            a, b = B.get(g[1]), B.get(g[2])
            if a and b:
                roots = sorted({find(u) for u in a | b})
                if len(roots) > 1:
                    for x in roots[1:]:
                        par[x] = roots[0]
                    M.append(i)
    return frozenset(M)


def instance(c, Q, out):
    n = c.n
    full = (1 << n) - 1
    T = c.tables()
    h = T[c.h_wire]
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive:
        return None
    apts = sorted({u for i in alive for u in c.sets[i]})
    ors = [n + k for k, g in enumerate(c.gates) if g[0] == 'or']

    def F2(Qm):
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
    F2Q = F2(Q)
    deg = {v: sum(1 for i in alive if sets[i] >> v & 1) for v in apts}
    res = {}
    for v in apts:
        gain = F2Q - F2(Q | 1 << v)
        star = [i for i in alive if sets[i] >> v & 1]
        cost = sum(len(c.sets[i]) - 1 for i in star)
        disj = lambda Ms: all(not (Ms[a] & Ms[b]) for a in range(len(Ms)) for b in range(a + 1, len(Ms)))
        flags = {}
        for tag, cone in (('', None), ('c', True)):
            within = lambda i: c.cone(c.outs[i]) if cone else None
            M1 = [merges_at(c, T, c.sets[i], Q, within(i)) for i in star]
            M2 = [merges_at(c, T, c.sets[i], full & ~sets[i], within(i)) for i in star]
            flags['h1' + tag] = all(M <= gain for M in M1) and disj(M1)
            flags['size1' + tag] = all(len(M) == len(c.sets[i]) - 1 for M, i in zip(M1, star))
            flags['die1' + tag] = all(M <= gain for M in M1)
            flags['disj1' + tag] = disj(M1)
            flags['h2' + tag] = all(M <= gain for M in M2) and disj(M2)
        # H3: options per star set = dying merge sets over all zero points Z ⊇ Q avoiding S_w; disjoint choice by search
            opts = []
            for i in star:
                free = full & ~(Q | sets[i])
                o = set()
                sub = free
                while True:
                    M = merges_at(c, T, c.sets[i], Q | sub, within(i))
                    if M <= gain:
                        o.add(M)
                    if sub == 0:
                        break
                    sub = (sub - 1) & free
                opts.append(sorted(o, key=sorted))

            def pick(j, used):
                if j == len(opts):
                    return True
                return any(not (M & used) and pick(j + 1, used | M) for M in opts[j])
            flags['h3' + tag] = pick(0, frozenset())
        res[v] = dict(heavy=bool(h >> (Q | 1 << v) & 1), deg=deg[v], cost=cost, gain=len(gain),
                      step=len(gain) >= cost, **flags)
    out.append(dict(Q=Q, v=res))
    return res


def load(paths):
    seen, cs = set(), []
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
                if not l.strip():
                    continue
                try:
                    d = json.loads(l)
                except ValueError:
                    continue
                if not isinstance(d, dict) or 'gates' not in d:
                    continue
                key = json.dumps([d['n'], d['sets'], d['gates'], d['outs']])
                if key in seen:
                    continue
                seen.add(key)
                cs.append(('%s:%d' % (f, i), d))
    return cs


def work(item):
    name, d = item
    try:
        c = Circuit.from_dict(d)
    except Exception as e:  # noqa: BLE001
        return dict(name=name, skip='parse: %r' % e)
    if len(c.nots) != 1 or c.n > 9 or not c.is_correct():
        return dict(name=name, skip='not a correct one-NOT circuit with n <= 9')
    rng = random.Random(zlib.crc32(name.encode()))
    Qs = [0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) & rng.randrange(1 << c.n) for _ in range(3)]
    out = []
    for Q in sorted(set(Qs)):
        instance(c, Q, out)
    return dict(name=name, n=c.n, s=c.s, base=c.base, clean=c.is_clean(), essential=c.is_essential(),
                allread=c.all_read(), inst=out)


if __name__ == '__main__':
    import multiprocessing as mp
    outf = sys.argv[1]
    cs = load(sys.argv[2:])
    with mp.Pool(int(os.environ.get('PROCS', '4'))) as pool, open(outf, 'w') as fo:
        for r in pool.imap_unordered(work, cs, chunksize=16):
            fo.write(json.dumps(r) + '\n')
            fo.flush()
