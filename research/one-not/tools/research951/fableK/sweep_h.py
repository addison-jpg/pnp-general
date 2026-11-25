"""For a system: for all monotone h (up to automorphisms of the system) compute C0(h), C1(h), L(h) (lifted optimum, h a wire).
Output jsonl: {"h": minterms, "C0":, "C1":, "L":, "hard": [...]}  usage: sweep_h.py name '<sets json>' n [maxL]"""
import sys, json, itertools, time
from multiprocessing import Pool
from worlds import *

def auts(n, sets):
    fs = set(frozenset(S) for S in sets)
    return [p for p in itertools.permutations(range(n)) if set(frozenset(p[v] for v in S) for S in sets) == fs]

def perm_tt(n, h, p):
    out = [0] * (1 << n)
    for x in range(1 << n):
        y = 0
        for i in range(n):
            if x >> i & 1: y |= 1 << p[i]
        out[y] = h[x]
    return tuple(out)

def minterms(n, h):
    return [x for x in range(1 << n) if h[x] and all(not h[x & ~(1 << i)] for i in range(n) if x >> i & 1)]

def job(arg):
    n, sets, h = arg
    b = base(sets)
    full = (1 << n) - 1
    hard = [int(h[full & ~sum(1 << v for v in S)]) for S in sets]
    HS = [S for S, t in zip(sets, hard) if t]; ES = [S for S, t in zip(sets, hard) if not t]
    cap = b + 1
    def o(nn, sp, lo=0):
        r = opt(nn, sp, lo=lo, hi=cap)[0]
        return 99 if r is None else r
    c0 = o(n, specs0(n, sets, h)); c1 = o(n, specs1(n, sets, h))
    c0h = o(n, specs0(n, HS, h, with_h=False)) if HS else 0
    c1h = o(n, specs1(n, HS, h, with_h=False)) if HS else 0
    c0e = o(n, specs0(n, ES, h, with_h=False)) if ES else 0
    L = o(n + 1, specsL(n, sets, h), lo=min(max(c0, c1), cap))
    return dict(h=minterms(n, h), C0=c0, C1=c1, L=L, hard=hard, C0h=c0h, C1h=c1h, C0e=c0e, bh=base(HS), be=base(ES))

if __name__ == '__main__':
    name = sys.argv[1]; sets = json.loads(sys.argv[2]); n = int(sys.argv[3])
    A = auts(n, sets)
    seen = set(); reps = []
    for h in monotone_functions(n):
        if h in seen: continue
        for p in A: seen.add(perm_tt(n, h, p))
        reps.append(h)
    print(name, 'base', base(sets), '|Aut|', len(A), 'h classes', len(reps), file=sys.stderr)
    t = time.time()
    with Pool(4) as P, open(f'sweep_{name}.jsonl', 'w') as f:
        for i, r in enumerate(P.imap_unordered(job, [(n, sets, h) for h in reps], chunksize=4)):
            f.write(json.dumps(r) + '\n'); f.flush()
    print('done', time.time() - t, file=sys.stderr)
