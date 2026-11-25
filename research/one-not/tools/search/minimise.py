"""Minimise a correct circuit that has fewer witness gates than base (C4 counterexample).
Moves: (a) replace wire n+k by any earlier wire (all readers and outputs rewired); (b) rewire one input of one gate to an
earlier wire; (c) core.prune. A move is kept only if the circuit stays correct and witness count < base.
Objective: fewer gates, then fewer NOT gates, then smaller witness-minus-base. Local minimum = no single move improves.
Run from the repo root: python3 -I research/one-not/tools/search/minimise.py OUT.json IN.json [IN.json ...]
Serves README item C4."""
import sys, os, json, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *

def key(c): return (len(c['gates']), nots(c))
def ok(c): return correct(c) and len(witness(c)) < base(c)

def replace(c, k, j):
    n = c['n']; d = copy.deepcopy(c); w = n + k
    for g in d['gates']: g[1:] = [j if x == w else x for x in g[1:]]
    d['outs'] = [j if o == w else o for o in d['outs']]
    return prune(d)

def moves(c):
    n = c['n']
    for k in range(len(c['gates']) - 1, -1, -1):
        for j in range(n + k): yield replace(c, k, j)
    for k, g in enumerate(c['gates']):
        for i in range(1, len(g)):
            for j in range(n + k):
                if j != g[i]:
                    d = copy.deepcopy(c); d['gates'][k][i] = j; yield prune(d)

def minimise(c):
    c = prune(c)
    while True:
        for d in moves(c):
            if key(d) < key(c) and ok(d): c = d; break
        else: return c

if __name__ == '__main__':
    out, best = sys.argv[1], None
    for p in sys.argv[2:]:
        d = json.load(open(p)); c = {"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']}
        assert ok(c); m = minimise(c)
        print(p, "->", len(c['gates']), "gates", nots(c), "NOT  =>", len(m['gates']), "gates", nots(m), "NOT, witnesses", len(witness(m)), "base", base(m))
        if best is None or key(m) < key(best): best = m
    json.dump(dict(best, name="general_count_below_base_min", note="locally minimal under minimise.py"), open(out, 'w'))
