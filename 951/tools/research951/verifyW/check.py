"""Independent check of Fable W's claim: monotone circuit, outputs = OR(line) on all inputs of weight <= 2.
Uses only the gate list/lines/outputs produced by plane2.build; evaluation and all checks are written here."""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '' + __import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'fableW') + '')
import plane2
q = int(sys.argv[1]); T = int(sys.argv[2]) if len(sys.argv) > 2 else None
C, lines, out, st = plane2.build(q, 2, T)
n = C.n; gates = C.g
L = list(lines.values())
# 1. structure of the set system
assert all(len(x) == q * q for x in L), 'line sizes'
pairs = {}
for li, x in enumerate(L):
    for a, b in itertools.combinations(sorted(x), 2):
        assert (a, b) not in pairs, 'two lines share 2 points'
        pairs[(a, b)] = li
assert len(pairs) == n * (n - 1) // 2, 'every pair covered once (affine plane)'
base = sum(len(x) - 1 for x in L)
# 2. gates are fan-in-2 AND/OR on earlier wires
for k, (op, a, b) in enumerate(gates):
    assert op in (0, 1) and 0 <= a < n + k and 0 <= b < n + k, ('bad gate', k)
assert set(out.keys()) == set(lines.keys())
# 3. evaluate on all rows of weight <= 2: row 0 = zero, rows 1..n = e_v, then all pairs
prs = list(itertools.combinations(range(n), 2)); R = 1 + n + len(prs)
bits = np.zeros((n, R), dtype=bool)
for v in range(n): bits[v, 1 + v] = True
for r, (a, b) in enumerate(prs):
    bits[a, 1 + n + r] = True; bits[b, 1 + n + r] = True
val = [int.from_bytes(np.packbits(bits[v]).tobytes(), 'big') for v in range(n)]
del bits
t = time.time()
for (op, a, b) in gates:
    val.append(val[a] & val[b] if op else val[a] | val[b])
bad = 0
for key, x in lines.items():
    exp = 0
    for v in x: exp |= val[v]
    if val[out[key]] != exp: bad += 1
print(f'q={q} T={T}: n={n} m={len(L)} base={base} gates={len(gates)} (ANDs {sum(op for op,_,_ in gates)}) rows={R} '
      f'wrong_outputs={bad} saving={base-len(gates)} eval {time.time()-t:.1f}s')
