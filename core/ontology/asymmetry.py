#!/usr/bin/env python3
"""One primitive under every one-way structure: the 2-chain.

Claim (checked-finite, every preorder on 1..4 worlds, no sampling): a finite reflexive-transitive frame (an S4 frame:
a directed history) is NOT symmetric exactly when it has a surjective p-morphism onto the 2-chain {a -> b}
(a sees b, b does not see a). So every instance of "forward but no way back" reduces to that one frame.

A p-morphism f: W -> V keeps arrows (xRy implies f(x)R'f(y)) and lifts them back (f(x)R'v implies some y with xRy and
f(y)=v). Validity of a modal formula on a frame passes to its p-morphic images, so what holds on every such history
also holds on the 2-chain.

The three readings in this repository that share it (labelled readings, not results):
  Beauvoir: one world reaches another and is not reached back (non-reciprocity, the failure of axiom B).
  Car Seat Headrest, Twin Fantasy: a 2011 version and a 2018 version, one history with no way back.
  Forward-only time: a chain of moments (physics/time).
Run: python3 -I core/ontology/asymmetry.py   (prints PASS, then a JSON line)
"""
import itertools, json, time

def preorders(n):
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        R = {(i, i) for i in range(n)} | {p for p, b in zip(pairs, bits) if b}
        if all((a, d) in R for (a, b) in R for (c, d) in R if b == c): yield R

def symmetric(R): return all((b, a) in R for a, b in R)

def is_pmorphism(R, f):
    two = {(0, 0), (1, 1), (0, 1)}                       # the 2-chain, reflexive: 0 sees 1
    forth = all((f[a], f[b]) in two for a, b in R)
    back = all(any((x, y) in R and f[y] == v for y in f) for x in f for v in (0, 1) if (f[x], v) in two)
    return forth and back

t0 = time.time(); total = nonsym = 0
for n in range(1, 5):
    for R in preorders(n):
        total += 1
        W = list(range(n))
        onto = any(is_pmorphism(R, dict(zip(W, vals))) and set(vals) == {0, 1} for vals in itertools.product((0, 1), repeat=n))
        assert onto == (not symmetric(R)), (n, sorted(R))
        nonsym += not symmetric(R)
print("preorders checked on 1..4 worlds:", total, "; not symmetric:", nonsym)
print("for every one: surjective p-morphism onto the 2-chain exists  <=>  the frame is not symmetric")
for name, R in [("Beauvoir non-reciprocity (0 reaches 1, not back)", {(0, 0), (1, 1), (0, 1)}),
                ("Twin Fantasy 2011 -> 2018", {(0, 0), (1, 1), (0, 1)}),
                ("forward time, 3 moments", {(i, j) for i in range(3) for j in range(3) if i <= j})]:
    W = sorted({x for p in R for x in p})
    assert any(is_pmorphism(R, dict(zip(W, v))) and set(v) == {0, 1} for v in itertools.product((0, 1), repeat=len(W))), name
    print("  maps onto the 2-chain:", name)
print("PASS")
print(json.dumps({"states": total, "seconds": round(time.time() - t0, 2)}))
