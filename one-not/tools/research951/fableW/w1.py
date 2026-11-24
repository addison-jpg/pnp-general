"""Fable W: (a) explicit monotone circuits correct on weight <= 1 (set circuits) for AG(2,q^2): build(q, k=1);
(b) one-NOT circuit correct on R* = {0} + unit vectors + tops comp(S_w):  out_w = (g1_w AND NOT T_2) OR (x_v OR x_v')."""
import sys
import numpy as np
import plane2

def eval_rows(n, gates, X):
    """gates: (op,a,b) op 0 OR, 1 AND, 2 NOT(a). X: bool array (n, rows). returns list of arrays."""
    val = [X[i] for i in range(n)]
    for op, a, b in gates:
        val.append(val[a] | val[b] if op == 0 else val[a] & val[b] if op == 1 else ~val[a])
    return val

q = int(sys.argv[1])
C, lines, out, st = plane2.build(q, 1, 2)
n = C.n
print("weight<=1 monotone circuit:", st, "saving", st['base'] - st['size'])
X = np.zeros((n, n + 1), dtype=bool)
for v in range(n): X[v, v + 1] = True
val = eval_rows(n, C.g, X)
bad = sum(1 for key, node in out.items() if not np.array_equal(val[node], np.any(X[lines[key]], axis=0)))
print("bad outputs on weight<=1:", bad)

# (b) one NOT, test set R* = 0, units, tops
gates = list(C.g)
def add(op, a, b=None):
    gates.append((op, a, b)); return n + len(gates) - 1
pre = 0; t2 = None
for v in range(1, n):
    a = add(1, pre, v)
    t2 = a if t2 is None else add(0, t2, a)
    pre = add(0, pre, v)
nt2 = add(2, t2)
out2 = {}
for key, node in out.items():
    v, v2 = lines[key][0], lines[key][1]
    out2[key] = add(0, add(1, node, nt2), add(0, v, v2))
keys = list(lines)
R = np.zeros((n, 1 + n + len(keys)), dtype=bool)
for v in range(n): R[v, v + 1] = True
for i, key in enumerate(keys):
    R[:, 1 + n + i] = True; R[lines[key], 1 + n + i] = False
val = eval_rows(n, gates, R)
bad = sum(1 for key, node in out2.items() if not np.array_equal(val[node], np.any(R[lines[key]], axis=0)))
print("one-NOT circuit on R* = {0, units, tops}: size", len(gates), "base", st['base'], "bad outputs:", bad,
      "NOT gates:", sum(1 for g in gates if g[0] == 2))
