#!/usr/bin/env python3
"""Bronfenbrenner's nested systems as a chain (micro, meso, exo, macro, chrono; cited from memory, not read).
Checked fact, structural only: the order "i <= j" on k levels is a preorder, not symmetric, with a least and a greatest element,
and maps onto the 2-chain by a p-morphism (first level to 0, the rest to 1). core/ontology/asymmetry.py runs at import and exposes
no function, so the same p-morphism test is repeated here for the chain. That the five systems ARE such a chain is analogy.
Run: python3 -I culture/social/ecology.py   (last line is JSON)
"""
import itertools, json
for k in range(2, 6):
    R = {(i, j) for i in range(k) for j in range(k) if i <= j}; W = range(k)
    assert all((i, i) in R for i in W) and all((a, d) in R for a, b in R for c, d in R if b == c)
    assert not all((b, a) in R for a, b in R) and all((0, j) in R for j in W) and all((j, k - 1) in R for j in W)
    f = {i: int(i > 0) for i in W}; two = {(0, 0), (1, 1), (0, 1)}
    assert all((f[a], f[b]) in two for a, b in R)
    assert all(any((x, y) in R and f[y] == v for y in W) for x in W for v in (0, 1) if (f[x], v) in two)
print("chains on 2..5 levels: preorder, not symmetric, least and greatest element, onto the 2-chain")
print("PASS"); print(json.dumps({"states": 4}))
