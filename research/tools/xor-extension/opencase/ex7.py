# Machine check of the 7-gate residual-shape circuit for x XOR (y0 AND NOT y2) (inputs y0, y1, y2, x).
import itertools
ok = True
for y0, y1, y2, x in itertools.product((0, 1), repeat=4):
    G2 = y2 | x; H2 = y0 & G2; n = 1 - H2; h1 = y2 | n; u1 = y0 & n; G1 = x & h1; H1 = G1 | u1
    f = y0 & (1 - y2)
    ok &= (H1 == x ^ f)
    ok &= (f == (y0 & (1 - y2)))            # f = u1(H2 := 0) AND NOT h2, with u1(0, y) = y0, h2 = y2
print('7-gate circuit computes x XOR (y0 AND NOT y2):', ok)
