import sys, time, itertools
from synth import synth, xor_ext
sz = {}
for l in open('sizes3.txt'):
    u, w = l.split(); sz[int(u)] = int(w)
def perm(f, pi):
    g = 0
    for row in range(8):
        r2 = sum(((row >> i) & 1) << pi[i] for i in range(3))
        if (f >> row) & 1: g |= 1 << r2
    return g
def dual(f):  # NOT f(NOT y)
    return sum((1 - ((f >> (7 - row)) & 1)) << row for row in range(8))
def canon(f):
    best = None
    for pi in itertools.permutations(range(3)):
        g = perm(f, pi)
        for h in (g, 255 ^ dual(g)):
            best = h if best is None else min(best, h)
    return best
m = int(sys.argv[1]); shape = len(sys.argv) > 2
cls = sorted(set(canon(f) for f in range(1, 255) if sz[f] == m and sz[255 ^ f] == m))
print('m', m, 'classes', cls, flush=True)
for f in cls:
    t = time.time(); c = synth(4, xor_ext(3, f), m + 3, shape)
    print('f', f, 'r', m + 3, 'shape', shape, 'SAT' if c else 'UNSAT', round(time.time() - t, 1), c, flush=True)
