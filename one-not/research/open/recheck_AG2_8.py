#!/usr/bin/env python3
"""Second-seat recheck of the AG(2,8) point-lemma witness. Shares no code with LIT2's script.
Reads the program dump (leaves, lines) and the statement from B6 s2; builds W itself.
Ops (B6 s2): X = A op B, op in union / inter / diff (reversed diff = swapped operands, expressible).
"""
import json, sys, os
here = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(here, '..', '..', 'data', 'witnesses', 'point_lemma_AG2_q8.json')
prog = json.load(open(P))
assert prog['q'] == 8
q = 8

def mul(a, b):                       # F_8 = F_2[t]/(t^3+t+1), schoolbook shift-and-reduce
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a & 8: a ^= 0b1011
    return r

# (a) W = 64 non-vertical lines y = a x + b
W = {}
for a in range(q):
    for b in range(q):
        W[(a, b)] = frozenset((x, mul(a, x) ^ b) for x in range(q))
fam = list(W.values())
assert len(fam) == 64 and len(set(fam)) == 64 and all(len(s) == 8 for s in fam)
mx = max(len(fam[i] & fam[j]) for i in range(64) for j in range(i))
assert mx <= 1, mx
print('(a) |W| = 64, |S| = 8, max pairwise intersection', mx)

# (b) leaves are partial transversals
leaves = [frozenset(map(tuple, l)) for l in prog['leaves']]
for l in leaves:
    assert all(len(l & s) <= 1 for s in fam)
    assert all(0 <= x < q and 0 <= y < q for x, y in l)
print('(b) %d leaves, all meet every S_w in <= 1 point' % len(leaves))

# (c) every line is union / inter / diff of earlier leaves or lines (leaf refs used as given; each leaf index valid)
val = []
used = set()
for i, (op, A, B) in enumerate(prog['lines']):
    assert op in ('u', 'i', 'd')
    ops = []
    for k, j in (A, B):
        if k == 'X': assert j < i; ops.append(val[j])
        else: assert k == 'L' and 0 <= j < len(leaves); used.add(j); ops.append(leaves[j])
    a, b = ops
    val.append(a | b if op == 'u' else a & b if op == 'i' else a - b)
assert used == set(range(len(leaves)))
print('(c) %d lines, ops legal, refs backward' % len(val))

# (d) every S_w among the lines
have = set(val)
miss = [k for k, s in W.items() if s not in have]
assert not miss, miss
print('(d) all 64 S_w appear among the lines')

# (e) counts
base = 64 * (q - 1)
n = len(val)
assert n == 261 and base == 448 and n <= base - 1
print('(e) lines = %d, base = %d, lines <= base-1: True' % (n, base))
print('ALL CHECKS PASS: no 447-line bound can hold; point lemma fails for this W')
