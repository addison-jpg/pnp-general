#!/usr/bin/env python3
"""Propp's functions as ordered slots (Morphology of the Folktale, 1928; cited from memory, not read).
A tale is a subset of m ordered functions, told in the fixed order: 2^m tales. Pairing rule used here (an assumption):
functions 2i and 2i+1 form a pair (lack / lack liquidated); a tale may use the second of a pair only if it uses the first.
Pairs then give 3 choices each (neither, first only, both), and an unpaired last function gives 2: count 3^(m//2) * 2^(m%2).
Counted by exhaustion for m = 0..12 against the formula.
Run: python3 -I culture/social/propp.py   (last line is JSON)
"""
import itertools, json
counts = []
for m in range(13):
    free = constrained = 0
    for s in itertools.product((0, 1), repeat=m):
        free += 1; constrained += all(s[2 * i] >= s[2 * i + 1] for i in range(m // 2))
    assert free == 2 ** m and constrained == 3 ** (m // 2) * 2 ** (m % 2); counts.append(constrained)
print("m = 0..12, free 2^m, with pairs:", counts)
print("PASS"); print(json.dumps({"states": sum(2 ** m for m in range(13)), "paired": counts}))
