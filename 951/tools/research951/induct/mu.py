# Run from the repository root:  ls <circuit .json files> | python3 951/tools/research951/induct/mu.py
"""MU(all): |U(all)| = number of distinct gates lying in some pure class of some set, vs base and s."""
import sys, json
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mtest.py')).read(); exec(src[:src.index("tot = {")])
for path in sys.stdin.read().split():
    d = json.load(open(path)); n, S, G = d['n'], d['sets'], d['gates']
    if n > 13: continue
    Me = menus_of(n, S, G); U = frozenset().union(*[C for M in Me for C in M]); base = sum(len(R) - 1 for R in S)
    print('%-34s s=%3d base=%3d |U(all)|=%3d  s-base=%2d  |U|-base=%2d  gates outside U=%2d' % (path.split('/')[-1], len(G), base, len(U), len(G) - base, len(U) - base, len(G) - len(U)))
