#!/usr/bin/env python3
"""Paths to stability: start from the matching you are in, not from scratch. Exhaustive, n <= 3, k = 1 and k = 2.

The model is the one of check.py (imported, not copied): two sides of size n, complete strict rankings,
capacity k, and a pair blocks when each would take the other.
The move. Pick one blocking pair (a, b) of the current matching m. Then a and b become matched.
If a is at capacity (k partners), a drops its worst current partner first; the same for b.
At k=1 this reads: a and b each leave their current partner, if they have one, and pair up.
The theorem tested here (Roth and Vande Vate 1990, cited from memory): at k=1, from ANY matching, some sequence
of such moves reaches a stable matching. It does not say every sequence does: moves can cycle.
For every profile, one backward search from the stable set finds every matching that can reach it.
Checked on every profile and every starting matching (checked-finite):
 (a) k=1, n = 1..3: every matching reaches the stable set (asserted);
 (b) the longest shortest path to stability, and how many profiles have a cycle of moves (reported, not asserted);
 (c) k=2, n = 1..3: the same numbers are reported. The k=1 theorem is not assumed to carry over.
Speed: each side's "would join" bits and "who I would drop" bits are precomputed per ranking table, as in check.py.
On n <= 2 the fast move is asserted equal to a direct move built from check.blocking_pairs.
Stated rankings only, not feelings. No real people.
Run: python3 -I culture/love/paths.py   (writes paths_fingerprints.json beside it; last line is JSON)
"""
import importlib.util, itertools, json, os, time
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("love_check", os.path.join(HERE, "check.py"))
L = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(L)
NMAX = 3

def move(n, k, ra, rb, m, a, b):
    # direct form of the move, on a frozenset of pairs
    assert (a, b) in L.blocking_pairs(n, k, ra, rb, m), "a move needs a blocking pair"
    m = set(m)
    pa = [y for x, y in m if x == a]
    if len(pa) >= k: m.discard((a, max(pa, key=lambda y: ra[a][y])))
    pb = [x for x, y in m if y == b]
    if len(pb) >= k: m.discard((max(pb, key=lambda x: rb[b][x]), b))
    m.add((a, b))
    return frozenset(m)

def mask(n, m): return sum(1 << (a * n + b) for a, b in m)

def drop_bits(n, k, r, m, side):
    # for each member `me` of this side: the bit of the pair it drops on a move, 0 if it has a free place
    out = []
    for me in range(n):
        ps = [(b if side == 0 else a) for a, b in m if (a if side == 0 else b) == me]
        if len(ps) < k: out.append(0); continue
        w = max(ps, key=lambda o: r[me][o])
        out.append(1 << (me * n + w) if side == 0 else 1 << (w * n + me))
    return out

class Tables:
    # everything that depends on one side's rankings only, for every matching of capacity k
    def __init__(self, n, k):
        self.n, self.k = n, k
        self.M = L.matchings(n, k)
        self.masks = [mask(n, m) for m in self.M]
        self.index = {x: i for i, x in enumerate(self.masks)}
        perms = list(itertools.permutations(range(n)))
        self.sides = list(itertools.product(perms, repeat=n))
        self.R = {p: L.ranks(p) for p in self.sides}
        self.WA = {p: [L.side_bits(n, k, self.R[p], m, 0) for m in self.M] for p in self.sides}
        self.WB = {p: [L.side_bits(n, k, self.R[p], m, 1) for m in self.M] for p in self.sides}
        self.DA = {p: [drop_bits(n, k, self.R[p], m, 0) for m in self.M] for p in self.sides}
        self.DB = {p: [drop_bits(n, k, self.R[p], m, 1) for m in self.M] for p in self.sides}

    def graph(self, pa, pb):
        # successors of each matching under every move; the stable matchings have none
        n = self.n; succ = []
        WA, WB, DA, DB, masks, index = self.WA[pa], self.WB[pb], self.DA[pa], self.DB[pb], self.masks, self.index
        for i, x in enumerate(masks):
            blk = WA[i] & WB[i]; s = []
            while blk:
                bit = blk & -blk; blk ^= bit; q = bit.bit_length() - 1; a, b = divmod(q, n)
                s.append(index[(x & ~DA[i][a] & ~DB[i][b]) | bit])
            succ.append(s)
        return succ

def analyse(succ):
    # backward search from the stable set: distance to stability per matching (None: cannot reach)
    N = len(succ); pred = [[] for _ in range(N)]
    for i, s in enumerate(succ):
        for j in s: pred[j].append(i)
    dist = [None] * N; todo = deque()
    for i, s in enumerate(succ):
        if not s: dist[i] = 0; todo.append(i)
    while todo:
        j = todo.popleft()
        for i in pred[j]:
            if dist[i] is None: dist[i] = dist[j] + 1; todo.append(i)
    # a cycle of moves exists iff Kahn's peeling (remove nodes with no successors left) does not empty the graph
    out = [len(s) for s in succ]; gone = deque(i for i in range(N) if out[i] == 0); left = N
    while gone:
        j = gone.popleft(); left -= 1
        for i in pred[j]:
            out[i] -= 1
            if out[i] == 0: gone.append(i)
    return dist, left   # left = matchings on or leading only into cycles (0 means no cycle)

def find_cycle(succ):
    # one cycle of moves, as a list of matching indices (first == last), or None
    colour = [0] * len(succ)
    for root in range(len(succ)):
        if colour[root]: continue
        stack = [(root, iter(succ[root]))]; path = [root]; colour[root] = 1
        while stack:
            v, it = stack[-1]
            w = next(it, None)
            if w is None:
                stack.pop(); path.pop(); colour[v] = 2; continue
            if colour[w] == 1: return path[path.index(w):] + [w]
            if colour[w] == 0: colour[w] = 1; path.append(w); stack.append((w, iter(succ[w])))
    return None

def main():
    t0 = time.time(); states = 0; res = {}; example = None
    for k in (1, 2):
        for n in range(1, NMAX + 1):
            T = Tables(n, k)
            prof = unreach_pairs = unreach_prof = cyc_prof = 0; longest = 0; hist = {}
            for pa in T.sides:
                for pb in T.sides:
                    prof += 1; succ = T.graph(pa, pb); states += len(succ)
                    if n <= 2:
                        ra, rb = T.R[pa], T.R[pb]
                        for i, m in enumerate(T.M):
                            direct = sorted(T.index[mask(n, move(n, k, ra, rb, m, a, b))]
                                            for a, b in L.blocking_pairs(n, k, ra, rb, m))
                            assert direct == sorted(succ[i]), "fast and direct moves disagree"
                            assert (not succ[i]) == L.stable(n, k, ra, rb, m), "no move exactly when stable"
                    dist, left = analyse(succ)
                    bad = sum(d is None for d in dist)
                    if k == 1: assert bad == 0, "a matching cannot reach stability at k=1 (Roth and Vande Vate)"
                    unreach_pairs += bad; unreach_prof += bad > 0
                    if left:
                        cyc_prof += 1
                        if example is None and k == 1:
                            example = {"n": n, "pa": [list(r) for r in pa], "pb": [list(r) for r in pb],
                                       "cycle": [sorted(T.M[i]) for i in find_cycle(succ)]}
                    d = max(x for x in dist if x is not None); longest = max(longest, d); hist[d] = hist.get(d, 0) + 1
            res[(k, n)] = {"profiles": prof, "matchings": len(T.M), "longest_shortest_path": longest,
                           "profiles_with_cycle": cyc_prof, "unreachable_pairs": unreach_pairs,
                           "profiles_with_unreachable": unreach_prof, "worst_path_histogram": dict(sorted(hist.items()))}
            r = res[(k, n)]
            print(f"k={k} n={n} profiles={prof} matchings={len(T.M)} longest shortest path={longest}"
                  f" profiles with a cycle={cyc_prof} (profile, start) pairs that cannot reach stability={unreach_pairs}"
                  f" on {unreach_prof} profiles | worst path per profile: {r['worst_path_histogram']}")
    assert example is not None, "no k=1 cycle found"
    print(f"first k=1 cycle (n={example['n']}): pa={example['pa']} pb={example['pb']} cycle={example['cycle']}")
    fp = []
    for k in (1, 2):
        ns = range(1, NMAX + 1)
        fp += [{"name": f"longest shortest path to stability k={k}, n=1..3", "seq": [res[(k, n)]["longest_shortest_path"] for n in ns]},
               {"name": f"profiles with a cycle of blocking-pair moves k={k}, n=1..3", "seq": [res[(k, n)]["profiles_with_cycle"] for n in ns]},
               {"name": f"start matchings that cannot reach stability k={k}, n=1..3", "seq": [res[(k, n)]["unreachable_pairs"] for n in ns]}]
    for e in fp: e["runner"] = "python3 -I culture/love/paths.py"
    with open(os.path.join(HERE, "paths_fingerprints.json"), "w", encoding="utf-8") as f:
        f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2),
                      "paths": {f"k{k}_n{n}": {x: v for x, v in r.items() if x != "worst_path_histogram"} for (k, n), r in res.items()},
                      "cycle_example": example}))

if __name__ == "__main__":
    main()
