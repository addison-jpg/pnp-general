#!/usr/bin/env python3
"""Test evaluator for an OPEN-cell target (d): the toy claim "no list of 3 distinct integers in 0..9 sums to 27" (false: 8 + 9 + 10 is
out of range, but the claim is planted as violated by [9, 9, 9]-free ... the planted violation is any candidate summing to >= 24)."""
import sys, json
c = json.load(sys.stdin)
try:
    xs = c['xs']; assert len(xs) == 3 and len(set(xs)) == 3 and all(type(x) is int and 0 <= x <= 9 for x in xs)
except Exception: print(json.dumps({'score': -1, 'verdict': 'invalid'})); sys.exit(0)
s = sum(xs) - 23
print(json.dumps({'score': s, 'verdict': 'VIOLATION-CANDIDATE' if s > 0 else 'ok', **({'witness': {'kind': 'command', 'argv': ['python3', '-I', 'compute/funsearch/tests/toy_check.py'], 'instance': c}} if s > 0 else {})}))
