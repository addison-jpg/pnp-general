"""Unit test of asteroid/ext_edges.hyps: one condition fails at a time, including 'one output wire per set' (not scriptable).
Run from the repository root:  python3 -I asteroid/tests/test_edges.py"""
import sys, os
sys.path.insert(0, os.getcwd())
import asteroid.asteroid as A
from asteroid import ext_edges as X
ok = {"n": 3, "sets": [[0, 1], [1, 2]], "gates": [["or", 0, 1], ["or", 1, 2]], "outs": [3, 4]}
def v(**kw): c = {**ok, **kw}; return X.hyps(c)
cases = {"ok": (v(), True), "singleton set": (v(sets=[[0], [1, 2]]), False), "share 2": (v(sets=[[0, 1, 2], [0, 1]], outs=[3, 4]), False),
         "two NOT": (v(gates=ok["gates"] + [["not", 0], ["not", 1]]), False), "no gate": (v(gates=[], outs=[]), False),
         "repeat": (v(sets=[[0, 0], [1, 2]]), False), "element >= n": (v(sets=[[0, 3], [1, 2]]), False), "missing output wire": (v(outs=[3]), False)}
bad = [k for k, (got, want) in cases.items() if got != want]
print("hyps cases:", len(cases), "failures:", bad or "none"); sys.exit(1 if bad else 0)
