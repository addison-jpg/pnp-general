"""The hairy ball on a model cortex. Each cortical hemisphere's surface is topologically a sphere
(neuroimaging inflates it to one for registration). So any smooth map on it (activation, thickness,
the gradient of any field) has critical points, and their indices sum to the Euler characteristic, 2.
Check (checked-finite): random piecewise-linear functions on subdivided icospheres; Banchoff index
1 - (sign changes in the link)/2 at every vertex; the sum must be 2, every time."""
import math, random, sys

def icosphere(n):
    t = (1 + 5 ** 0.5) / 2
    V = [(-1,t,0),(1,t,0),(-1,-t,0),(1,-t,0),(0,-1,t),(0,1,t),(0,-1,-t),(0,1,-t),(t,0,-1),(t,0,1),(-t,0,-1),(-t,0,1)]
    F = [(0,11,5),(0,5,1),(0,1,7),(0,7,10),(0,10,11),(1,5,9),(5,11,4),(11,10,2),(10,7,6),(7,1,8),
         (3,9,4),(3,4,2),(3,2,6),(3,6,8),(3,8,9),(4,9,5),(2,4,11),(6,2,10),(8,6,7),(9,8,1)]
    for _ in range(n):
        mid, NF = {}, []
        def m(a, b):
            k = (min(a, b), max(a, b))
            if k not in mid:
                mid[k] = len(V); V.append(tuple((V[a][i] + V[b][i]) / 2 for i in range(3)))
            return mid[k]
        for a, b, c in F:
            ab, bc, ca = m(a, b), m(b, c), m(c, a)
            NF += [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)]
        F = NF
    return [tuple(x / math.sqrt(sum(y * y for y in v)) for x in v) for v in V], F

def link_cycle(v, F):
    nxt = {}
    for f in F:
        if v in f:
            i = f.index(v); nxt[f[(i + 1) % 3]] = f[(i + 2) % 3]
    start = next(iter(nxt)); cyc = [start]
    while nxt[cyc[-1]] != start: cyc.append(nxt[cyc[-1]])
    return cyc

def index_sum(V, F, rng):
    w = [rng.gauss(0, 1) for _ in range(3 * 6)]
    h = [sum(w[3*k+i] * math.sin((k + 1) * v[i] + w[k]) for k in range(6) for i in range(3)) + 1e-9 * rng.random() for v in V]
    total, crit = 0, 0
    for v in range(len(V)):
        cyc = link_cycle(v, F)
        s = [h[u] > h[v] for u in cyc]
        changes = sum(s[i] != s[i - 1] for i in range(len(s)))
        idx = 1 - changes // 2 if changes else (1)
        total += idx; crit += idx != 0
    return total, crit

if __name__ == "__main__":
    rng = random.Random(0); runs = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    for n in (1, 2, 3):
        V, F = icosphere(n)
        sums = [index_sum(V, F, rng) for _ in range(runs)]
        assert all(s == 2 for s, _ in sums), "index sum is not 2"
        print(f"subdiv {n}: {len(V)} vertices, {runs} random fields, index sum 2 every time, "
              f"critical points min {min(c for _, c in sums)} max {max(c for _, c in sums)}")
    print("PASS")
