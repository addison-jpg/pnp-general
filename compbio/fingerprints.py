#!/usr/bin/env python3
"""Computational biology, entered through combinatorics: counting sequences by exhaustive enumeration,
each checked against its closed form. These are fingerprints in the centre's sense: two fields that emit
the same sequence are a candidate connection.

1. Rooted binary phylogenetic trees on n labelled leaves: (2n-3)!! (Schroeder 1870; Felsenstein 1978).
   Enumerated by inserting leaf k into every edge, plus above the root, of each tree on k-1 leaves.
2. RNA secondary structures on n unpaired-labelled bases with hairpin loops of at least 1 base
   (Waterman 1978; Stein-Waterman 1979): enumerated as non-crossing pairings with |i - j| >= 2.
   Compared with the recursion S(n) = S(n-1) + sum_{k=1}^{n-2} S(k-1) S(n-k-1).
3. Motzkin numbers (non-crossing partial pairings, no loop constraint), the minimum-loop-0 case of 2.

Exhaustive and exact for n up to the default bound: checked-finite with this script as runner.
  python3 -I compbio/fingerprints.py [nmax]   default 9
"""
import sys
from functools import lru_cache
from itertools import combinations

def trees(n):
    # a tree is a frozenset of clusters (frozensets of leaves); insert leaf k into each edge or above the root
    ts = {frozenset([frozenset([0])])}
    for k in range(1, n):
        new = set()
        for t in ts:
            full = frozenset(range(k))
            edges = list(t)  # each cluster = the edge above it; the root cluster's edge is "above the root"
            for c in edges:
                # attach k as a sibling of cluster c: new cluster c|{k}; add k's singleton; old clusters containing c gain k
                nt = set()
                for d in t:
                    nt.add(d | {k} if c <= d else d)
                nt.add(c)
                nt.add(frozenset([k]))
                nt.add(full | {k})
                new.add(frozenset(nt))
        ts = new
    return len(ts)

def dfact(m):
    r = 1
    while m > 1:
        r *= m; m -= 2
    return r

def rna_enum(n, minloop=1):
    @lru_cache(None)
    def count(i, j):
        if j - i < 1: return 1
        total = count(i + 1, j)  # base i unpaired
        for k in range(i + minloop + 1, j + 1):  # i pairs with k
            total += count(i + 1, k - 1) * count(k + 1, j)
        return total
    return count(0, n - 1) if n > 0 else 1

def rna_brute(n, minloop=1):
    # brute force over all sets of disjoint pairs: non-crossing and loop length check
    pairs = [(i, j) for i, j in combinations(range(n), 2) if j - i > minloop]
    total = 0
    def rec(idx, used, chosen):
        nonlocal total
        if idx == len(pairs):
            total += 1; return
        rec(idx + 1, used, chosen)
        i, j = pairs[idx]
        if i in used or j in used: return
        if any(a < i < b < j or i < a < j < b for a, b in chosen): return
        rec(idx + 1, used | {i, j}, chosen + [(i, j)])
    rec(0, frozenset(), [])
    return total

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    t = [trees(n) for n in range(2, N + 1)]
    assert t == [dfact(2 * n - 3) for n in range(2, N + 1)], t
    print("phylogenetic trees n=2..%d:" % N, t)
    r = [rna_enum(n) for n in range(0, N + 1)]
    rb = [rna_brute(n) for n in range(0, N + 1)]
    assert r == rb, (r, rb)
    print("RNA secondary structures (min loop 1) n=0..%d:" % N, r)
    m = [rna_enum(n, minloop=0) for n in range(0, N + 1)]
    assert m == [rna_brute(n, minloop=0) for n in range(0, N + 1)]
    print("Motzkin n=0..%d:" % N, m)
    print("checks passed")
