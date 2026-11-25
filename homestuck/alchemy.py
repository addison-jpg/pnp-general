#!/usr/bin/env python3
"""A formal model of an alchemy tree: items are built by combining items, and an item's ancestry is
the set of base items it is made of. This is a MODEL of combination, not the comic's exact recipe:
the comic is the cited source of the idea; its recipes are not reproduced here.

Model: base items B = {0..b-1}. An item is a frozenset of base items (its ancestry). Combining two
items gives their union. An item of depth d is one reachable by d rounds of combination starting
from the base items. Count distinct items reachable within depth d, for each depth.

Exhaustive and exact: checked-finite for each (b, d) computed here.

  python3 -I homestuck/alchemy.py [b] [dmax]   default b = 3, dmax = 3
"""
import sys

def reachable_counts(b, dmax):
    base = frozenset(frozenset([i]) for i in range(b))
    seen = set(base)
    frontier = set(base)
    counts = [len(seen)]
    for _ in range(dmax):
        new = set()
        for x in frontier:
            for y in seen:
                z = x | y
                if z not in seen and z not in new:
                    new.add(z)
        seen |= new
        frontier = new
        counts.append(len(seen))
    return counts

if __name__ == "__main__":
    b = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    counts = reachable_counts(b, dmax)
    print(f"b={b} counts by depth 0..{dmax}: {counts}")
    # independent check: every item is a nonempty subset of base items, so the count is at most 2^b - 1 (+ base)
    assert counts[-1] <= 2 ** b - 1, "a reachable item must be a nonempty subset of the base"
    assert all(counts[i] <= counts[i + 1] for i in range(len(counts) - 1)), "reachable sets only grow"
    print("checks passed")
