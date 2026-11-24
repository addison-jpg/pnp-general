import sys, random
sys.path.insert(0, '' + __import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'fableW') + '')
import plane2
C, lines, out, st = plane2.build(5, 2, 4); n = C.n
random.seed(7); rows = [random.sample(range(n), 3) for _ in range(4000)]
val = [0] * n
for r, X in enumerate(rows):
    for v in X: val[v] |= 1 << r
for (op, a, b) in C.g: val.append(val[a] & val[b] if op else val[a] | val[b])
wrong = 0; under = 0; witness = None
for key, x in lines.items():
    exp = 0
    for v in x: exp |= val[v]
    got = val[out[key]]
    wrong += bin(got ^ exp).count('1'); under += bin(exp & ~got).count('1')
    if witness is None and got != exp:
        r = ((got ^ exp) & -(got ^ exp)).bit_length() - 1; witness = (key, rows[r])
print('weight-3 sample: wrong output bits', wrong, 'of', len(lines) * len(rows), '| below OR(line):', under, '| witness', witness)
