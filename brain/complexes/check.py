"""Protein complexes as counting: necklaces, bracelets, ceilings, Dscam1 self/non-self.
Standard library only. Run: python3 -I brain/complexes/check.py"""
import itertools, json, time
from fractions import Fraction
from math import comb, gcd
T0 = time.time(); states = 0

def phi(n):
    return sum(1 for i in range(1, n + 1) if gcd(i, n) == 1)

def necklace_burnside(n, k):
    s = sum(k ** gcd(i, n) for i in range(n)); assert s % n == 0; return s // n

def bracelet_formula(n, k):
    N = necklace_burnside(n, k)
    if n % 2: r = k ** ((n + 1) // 2)
    else: r = (k ** (n // 2 + 1) + k ** (n // 2)) // 2
    t = N + r; assert t % 2 == 0; return t // 2

def enumerate_classes(n, k):
    global states
    neck, brace = set(), set()
    for w in itertools.product(range(k), repeat=n):
        states += 1
        rots = [w[i:] + w[:i] for i in range(n)]
        r = min(rots); neck.add(r)
        rev = w[::-1]
        brace.add(min(r, min(rev[i:] + rev[:i] for i in range(n))))
    return len(neck), len(brace)

print("1. Rings counted up to rotation (necklace) and rotation+reflection (bracelet)")
seqs = {}
for n in (4, 5, 6):
    ns = []
    for k in range(1, 8):
        a, b = enumerate_classes(n, k)
        assert a == necklace_burnside(n, k) and b == bracelet_formula(n, k)
        if n in (5,):
            assert a == (k ** n + (n - 1) * k) // n
        ns.append(a)
        print(f"  n={n} k={k}: necklaces {a}  bracelets {b}  bracelets that split in two {a-b}")
    seqs[n] = ns
assert seqs[4] == [1, 6, 24, 70, 165, 336, 616]
assert seqs[5] == [1, 8, 51, 208, 629, 1560, 3367]
assert seqs[6] == [1, 14, 130, 700, 2635, 7826, 19684]
assert [necklace_burnside(n,1) for n in range(1,8)] == [1]*7
print("  exhaustive enumeration agrees with Burnside for n in {4,5,6}, k in 1..7")

print("2. Combinatorial ceilings (formula only; NOT counts of what exists)")
g = necklace_burnside(5, 19); assert g == (19**5 + 4*19)//5 == 495235
print(f"  GABA-A pentamer, 19 subunit genes: {g} rotation classes; bracelets {bracelet_formula(5,19)}")
assert bracelet_formula(5, 19) == 251047
q = necklace_burnside(4, 18); assert q == 26334
print(f"  ionotropic glutamate tetramer, 18 subunit genes: {q}")
c6 = necklace_burnside(6, 21); assert c6 == (21**6 + 21**3 + 2*21**2 + 2*21)//6 == 14296051
print(f"  connexon hexamer, 21 human connexins: {c6} rotation classes")
homo, het = 21, comb(21, 2); assert (homo, het, homo + het) == (21, 210, 231)
print(f"  gap junction from homomeric connexons: homotypic {homo}, heterotypic {het}, total {homo+het}")
allpairs = c6 * (c6 + 1) // 2; assert allpairs == 102188544245326
print(f"  gap junction from any two hexamers (unordered pair): {allpairs}")

print("3. Dscam1 (Drosophila)")
D = 12 * 48 * 33 * 2; assert D == 38016
E = 12 * 48 * 33; assert E == 19008
print(f"  isoforms 12*48*33*2 = {D}; ectodomains 12*48*33 = {E}")
def p_none(N, m):
    return Fraction(comb(N - m, m), comb(N, m))
rows = {}
PIN = {(19008,10):'0.994750',(19008,20):'0.979155',(19008,50):'0.876457',(38016,10):'0.997372',(38016,20):'0.989528',(38016,50):'0.936274'}
for N in (E, D):
    for m in (10, 20, 50):
        p = p_none(N, m); rows[(N, m)] = p
        # independent check: product formula
        q2 = Fraction(1)
        for i in range(m): q2 *= Fraction(N - m - i, N - i)
        assert p == q2 and 0 < p < 1
        assert f"{float(p):.6f}" == PIN[(N, m)]
        print(f"  N={N} m={m}: P(no shared isoform) = {float(p):.6f}  (1 - P = {float(1-p):.6f})")
assert rows[(E, 10)] > Fraction(99, 100) and rows[(E, 50)] > Fraction(87, 100)
print("  reduced diversity: N small")
for N in (12, 24, 48, 576, 19008):
    p = p_none(N, 1); assert p == Fraction(N - 1, N)
    print(f"  N={N} m=1: P(no shared) = {p}")
p4 = p_none(48, 4); assert f"{float(p4):.6f}" == "0.697662"; print(f"  N=48 m=4: P(no shared) = {float(p4):.6f}"); assert Fraction(2,3) < p4 < Fraction(7,10)

print("4. Clustered protocadherins, mouse")
a, b, gm = 14, 22, 22; assert a + b + gm == 58
print(f"  alpha {a} + beta {b} + gamma {gm} = {a+b+gm} variable exons")
print("PASS")
print(json.dumps({"states": states, "seconds": round(time.time() - T0, 3)}))
