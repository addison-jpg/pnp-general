#!/usr/bin/env python3
"""Protein complexes, counted. The 'complexes' level of the bottom-up account in brain/.

One object does most of the work. A complex is
  - a set of positions (the places where a subunit can sit),
  - one subunit type, out of k, at each position,
  - a group of symmetries: moves of the whole complex that put positions onto positions.
Two choices of subunits that a symmetry carries into each other are the same complex. So the number of
complexes is the number of orbits (classes) of the k^n choices under the group. The biology picks the group:
  a ring of n in a membrane        turn it, never flip it (inside and outside differ)   -> necklaces
  the same ring, free in solution  turn it or flip it                                   -> bracelets
  a glutamate receptor             four subunits, but only a half turn is a symmetry
  two docked rings (gap junction)  turn both together, or turn the channel end over end
  Dscam1, a spliced gene           no symmetry at all: a plain product of choices
Every count is done twice: by listing all k^n choices and grouping them, and by Burnside's lemma
(number of orbits = average, over the group, of the number of choices a symmetry leaves fixed).

Second object: two cells that each show m isoforms drawn at random out of N. How many they share is the
hypergeometric distribution. Checked by listing every pair of sets for N <= 10, then evaluated exactly.

Third object: cells joined by channels form a graph. The surface that separates inside from outside
(membranes plus channel walls) is built as a polygon mesh and its Euler characteristic is counted.

Run from the repository root:
  python3 -I brain/complexes/check.py                       about 20 seconds
  python3 -I brain/complexes/check.py --full                also lists all 21^6 hexamers (about a minute more)
  python3 -I brain/complexes/check.py --write-fingerprints  rewrite fingerprints.json from the computed sequences
Every number printed is asserted. Last line: {"states": configurations listed, "seconds": s}.
Standard library only; integers and fractions only (no floating point in any check).
"""
import itertools, json, math, os, sys, time
from fractions import Fraction

T0 = time.time()
STATES = 0                       # configurations listed one by one, over the whole run
HERE = os.path.dirname(os.path.abspath(__file__))

# ------------------------------------------------------------------ groups acting on positions
def cyclic(n):
    """The n turns of a ring: turn j sends position i to i + j."""
    return [[(i + j) % n for i in range(n)] for j in range(n)]

def dihedral(n):
    """The n turns and the n flips of a ring: flip j sends position i to j - i."""
    return cyclic(n) + [[(j - i) % n for i in range(n)] for j in range(n)]

def is_group(perms):
    """Contains the identity and is closed under doing one move after another."""
    have = {tuple(p) for p in perms}
    ident = tuple(range(len(perms[0])))
    return ident in have and len(have) == len(perms) and all(
        tuple(p[q[i]] for i in range(len(p))) in have for p in perms for q in perms)

def cycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            while i not in seen: seen.add(i); i = p[i]
    return c

def orbits(npos, k, perms, keep=False):
    """List all k^npos colourings (as numbers in base k) and group them under the moves in perms.
    Returns (number of classes, {class size: how many classes}, smallest member of each class if keep)."""
    global STATES
    total = k ** npos; STATES += total
    pw = [k ** i for i in range(npos)]
    weights = [[pw[p[i]] for i in range(npos)] for p in perms]      # colour at i moves to p[i]
    seen = bytearray(total); count = 0; sizes = {}; reps = []
    x = seen.find(0)
    while x >= 0:
        d = []; y = x
        for _ in range(npos): d.append(y % k); y //= k
        images = {sum(map(int.__mul__, d, w)) for w in weights}
        for y in images: seen[y] = 1
        count += 1; s = len(images); sizes[s] = sizes.get(s, 0) + 1
        if keep: reps.append(x)
        x = seen.find(0, x + 1)
    return count, sizes, reps

def burnside(k, perms):
    """Average number of colourings fixed by a move. A move with c cycles fixes k^c colourings."""
    s = sum(k ** cycles(p) for p in perms)
    assert s % len(perms) == 0
    return s // len(perms)

def canon(word, perms):
    """The smallest image of a word (tuple) under the moves: one name per class."""
    n = len(word); best = None
    for p in perms:
        w = [None] * n
        for i in range(n): w[p[i]] = word[i]
        w = tuple(w)
        if best is None or w < best: best = w
    return best

# ------------------------------------------------------------------ closed formulas
def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]
def phi(d): return sum(1 for a in range(1, d + 1) if math.gcd(a, d) == 1)
def mobius(n):
    m, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0: return 0
            m = -m
        p += 1
    return -m if n > 1 else m

def necklace_formula(n, k):
    s = sum(phi(d) * k ** (n // d) for d in divisors(n)); assert s % n == 0
    return s // n

def bracelet_formula(n, k):
    s = 2 * necklace_formula(n, k) + ((k + 1) * k ** (n // 2) if n % 2 == 0 else 2 * k ** ((n + 1) // 2))
    assert s % 4 == 0
    return s // 4

def aperiodic(d, k):
    """Rings of length d with no rotational symmetry at all, up to rotation (Lyndon words)."""
    s = sum(mobius(d // e) * k ** e for e in divisors(d)); assert s % d == 0
    return s // d

def extrapolate(vals, K):
    """vals[j] is the value at k = j, j = 0..n. Value at K of the one polynomial of degree <= n through them."""
    diffs, row = [], list(vals)
    while row:
        diffs.append(row[0]); row = [b - a for a, b in zip(row, row[1:])]
    return sum(d * math.comb(K, j) for j, d in enumerate(diffs))

def rotation_classes_fast(n, k):
    """Same count as orbits(n, k, cyclic(n))[0]; one multiply and one divide per turn."""
    global STATES
    total = k ** n; STATES += total; top = k ** (n - 1)
    seen = bytearray(total); count = 0
    x = seen.find(0)
    while x >= 0:
        y = x
        for _ in range(n):
            seen[y] = 1; y = (y % top) * k + y // top
        count += 1
        x = seen.find(0, x + 1)
    return count

def dec(fr, places):
    """A fraction in [0, 1), cut off (not rounded) after `places` decimals. Integer arithmetic only."""
    q = fr.numerator * 10 ** places // fr.denominator
    s = str(q).rjust(places + 1, "0")
    return s[:-places] + "." + s[-places:]

def sci(fr, sig=3):
    """A positive fraction as d.dde-x, cut off after `sig` digits. Integer arithmetic only."""
    e = 0
    while fr >= 10: fr /= 10; e += 1
    while fr < 1: fr *= 10; e -= 1
    s = str(fr.numerator * 10 ** (sig - 1) // fr.denominator)
    return s[0] + "." + s[1:] + "e%d" % e

SEQ = {}                          # the integer sequences that go to fingerprints.json

# ================================================================== 1. rings
def rings():
    print("1. RINGS IN A MEMBRANE: necklaces (turns only) against bracelets (turns and flips)")
    ks = list(range(1, 11))
    for n in (3, 4, 5, 6):
        C, D = cyclic(n), dihedral(n)
        assert is_group(C) and is_group(D) and len(C) == n and len(D) == 2 * n
        for j, p in enumerate(C): assert cycles(p) == math.gcd(n, j)       # turn j has gcd(n, j) cycles
        for d in divisors(n): assert sum(1 for j in range(n) if n // math.gcd(n, j) == d) == phi(d)
        neck, brac = [], []
        for k in ks:
            c, sizes, _ = orbits(n, k, C)
            assert c == burnside(k, C) == necklace_formula(n, k)
            if n in (3, 5): assert (k ** n + (n - 1) * k) % n == 0 and c == (k ** n + (n - 1) * k) // n
            assert set(sizes) <= set(divisors(n))
            for d in divisors(n): assert sizes.get(d, 0) == aperiodic(d, k)   # classes by size of symmetry
            b, _, _ = orbits(n, k, D)
            assert b == burnside(k, D) == bracelet_formula(n, k)
            assert 2 * b - c >= 0 and c - b >= 0
            neck.append(c); brac.append(b)
        # the count is a polynomial in k of degree <= n (proof in BASE.md): n + 1 listed values fix it
        vals = [0] + neck
        row = vals
        for _ in range(n + 1): row = [y - x for x, y in zip(row, row[1:])]
        assert row and not any(row)                                        # (n+1)-th differences vanish
        for K in (18, 19, 21, 40, 58):
            assert extrapolate(vals[:n + 1], K) == necklace_formula(n, K) == burnside(K, C)
        if n >= 4:
            SEQ["necklaces: rings of %d subunits in k types, up to rotation (k>=1)" % n] = neck
            SEQ["bracelets: rings of %d subunits in k types, up to rotation and flip (k>=1)" % n] = brac
            print("   n=%d  necklaces, k=1..10: %s" % (n, neck))
            print("        bracelets, k=1..10: %s" % brac)
            print("        mirror pairs (necklaces - bracelets): %s" % [a - b for a, b in zip(neck, brac)])
    print("   every entry: listing = Burnside = closed formula; n=3 and n=5 also = (k^n + (n-1)k)/n; n = 3..6, k = 1..10")
    # where the membrane starts to matter
    assert SEQ["necklaces: rings of 4 subunits in k types, up to rotation (k>=1)"][1] == 6 == \
           SEQ["bracelets: rings of 4 subunits in k types, up to rotation and flip (k>=1)"][1]
    assert SEQ["necklaces: rings of 5 subunits in k types, up to rotation (k>=1)"][1] == 8 == \
           SEQ["bracelets: rings of 5 subunits in k types, up to rotation and flip (k>=1)"][1]
    C6 = cyclic(6)
    hexes = {canon(w, C6) for w in itertools.product((0, 1), repeat=6)}
    handed = sorted("".join("AB"[c] for c in w) for w in hexes if canon(w[::-1], C6) != w)
    assert len(hexes) == 14 and handed == ["AABABB", "AABBAB"]
    print("   two types: no mirror pairs in rings of 4 or 5 (6 = 6, 8 = 8); the first is in a ring of 6: %s and %s (14 against 13)" % tuple(handed))
    tet = sorted("".join("AB"[c] for c in w) for w in {canon(w, cyclic(4)) for w in itertools.product((0, 1), repeat=4)})
    assert tet == ["AAAA", "AAAB", "AABB", "ABAB", "ABBB", "BBBB"]
    print("   tetramers from two types (a potassium channel from two subunits): %s" % " ".join(tet))

# ================================================================== 2. anchors
def anchors(full):
    print("2. ANCHORS: the ceiling the counting gives, for real gene families")
    # --- GABA-A receptors: pentamers from 19 genes
    genes = ["alpha%d" % i for i in range(1, 7)] + ["beta%d" % i for i in range(1, 4)] + \
            ["gamma%d" % i for i in range(1, 4)] + ["delta", "epsilon", "theta", "pi"] + ["rho%d" % i for i in range(1, 4)]
    assert len(genes) == len(set(genes)) == 19
    C5, D5 = cyclic(5), dihedral(5)
    c, sizes, _ = orbits(5, 19, C5)
    assert c == 495235 == (19 ** 5 + 4 * 19) // 5 == burnside(19, C5) and sizes == {1: 19, 5: 495216}
    b, _, _ = orbits(5, 19, D5)
    assert b == 251047 == burnside(19, D5) == bracelet_formula(5, 19)
    print("   GABA-A, 19 genes, pentamer: all 19^5 = %d arrangements listed; %d classes up to rotation" % (19 ** 5, c))
    print("      = (19^5 + 4*19)/5, the figure printed in Sente et al. 2022. Up to rotation and flip it would be %d." % b)
    print("      %d of the %d are one subunit five times; the other %d have no symmetry" % (sizes[1], c, sizes[5]))
    known, identified = 26, 11                      # Olsen and Sieghart 2008/2009 (cited, not computed)
    assert c // known == 19047 and Fraction(c, known) > 19047
    print("      known to exist: %d on the 2008 list, %d of them classed as identified: about 1 in %d of the ceiling" % (known, identified, c // known))
    wheel = set(itertools.permutations("aabbg")); assert len(wheel) == 30       # 2 alpha, 2 beta, 1 gamma
    neck = {canon(w, C5) for w in wheel}; brac = {canon(w, D5) for w in wheel}
    real, mirror = tuple("gbaba"), tuple("gabab")
    assert len(neck) == 6 and len(brac) == 4
    assert canon(real, C5) != canon(mirror, C5) and canon(real, D5) == canon(mirror, D5)
    handed = [w for w in neck if canon(w[::-1], C5) != w]
    assert len(handed) == 4 and canon(real, C5) in handed
    print("      2 alpha + 2 beta + 1 gamma: %d rings up to rotation, %d up to rotation and flip; %d of the %d come in mirror pairs," % (len(neck), len(brac), len(handed), len(neck)))
    print("      and the measured order gamma-beta-alpha-beta-alpha is one of a pair: its mirror image is a different receptor")
    al = ["a%d" % i for i in range(1, 7)]; be = ["b%d" % i for i in range(1, 4)]; ga = ["g%d" % i for i in range(1, 4)]
    w3 = {canon((g, b1, a1, b2, a2), C5) for g in ga for b1 in be for a1 in al for b2 in be for a2 in al}
    w4 = {canon((g, b1, a1, b2, a2), C5) for g in ga + ["d"] for b1 in be for a1 in al for b2 in be for a2 in al}
    assert len(w3) == 972 == 6 * 6 * 3 * 3 * 3 and len(w4) == 1296 == 6 * 6 * 3 * 3 * 4
    print("      with that order fixed: %d receptors (gamma1-3 in the single place), %d if delta may take it" % (len(w3), len(w4)))

    # --- tetramers: potassium channels (a true 4-fold ring) and glutamate receptors (2-fold only)
    C4 = cyclic(4); C2 = [[0, 1, 2, 3], [2, 3, 0, 1]]; assert is_group(C4) and is_group(C2)
    kv, _, _ = orbits(4, 40, C4)
    assert kv == 640420 == burnside(40, C4) == necklace_formula(4, 40)
    print("   Kv potassium channels, 40 genes, tetramer with a 4-fold axis: %d if every subunit could mix with every other" % kv)
    half = []
    for k in range(1, 11):
        h, _, _ = orbits(4, k, C2)
        assert h == burnside(k, C2) == (k ** 4 + k ** 2) // 2 == k * k * (k * k + 1) // 2
        half.append(h)
    SEQ["tetramers with a half turn as the only symmetry (dimer of dimers), k types (k>=1)"] = half
    classes = {"AMPA": 4, "kainate": 5, "NMDA": 7, "delta": 2}; assert sum(classes.values()) == 18
    g4, _, _ = orbits(4, 18, C4); g2, _, _ = orbits(4, 18, C2)
    assert g4 == 26334 == necklace_formula(4, 18) and g2 == 52650 == burnside(18, C2)
    within = sum(orbits(4, k, C2)[0] for k in classes.values()); assert within == 136 + 325 + 1225 + 10 == 1696
    nmda = {canon(("N1", x, "N1", y), C2) for x in range(6) for y in range(6)}
    assert len(nmda) == 21 == 6 + 15
    h2, _, _ = orbits(4, 2, C2)
    two_two = {canon(w, C2) for w in set(itertools.permutations("AABB"))}; assert len(two_two) == 4 and h2 == 10
    print("   glutamate receptors, 18 genes, tetramer: %d if the ring had a 4-fold axis; it has only a half turn: %d" % (g4, g2))
    print("      half-turn counts, k=1..10: %s  (= k^2(k^2+1)/2; two types give %d, not 6; a 2:2 mix has %d forms, not 2)" % (half, h2, len(two_two)))
    print("      mixing only inside the four classes (4, 5, 7, 2 genes): %d; NMDA rule (GluN1 at two opposite places): %d" % (within, len(nmda)))

    # --- connexins: hexamers, and two hexamers docked
    C6 = cyclic(6); K = 21
    hexamers = necklace_formula(6, K)
    assert hexamers == 14296051 == burnside(K, C6)
    assert [aperiodic(d, K) for d in (1, 2, 3, 6)] == [21, 210, 3080, 14292740] and 21 + 210 + 3080 + 14292740 == hexamers
    for k in range(1, 7): assert rotation_classes_fast(6, k) == necklace_formula(6, k)
    how = "Burnside, and the polynomial through the listed counts for k = 0..6"
    if full:
        assert rotation_classes_fast(6, K) == hexamers
        how = "all 21^6 = %d hexamers listed" % K ** 6
    print("   connexins, 21 human genes, hexamer (connexon): %d up to rotation (%s)" % (hexamers, how))
    print("      by symmetry: 21 of one type, 210 alternating two types, 3080 with a half turn, 14292740 with none")
    pairs = list(itertools.combinations_with_replacement(range(K), 2))
    homo = sum(1 for a, b in pairs if a == b); hetero = len(pairs) - homo
    assert (len(pairs), homo, hetero) == (231, 21, 210) and K * K == 441
    print("      two cells, one-type connexons: %d homotypic + %d heterotypic = %d channel types (%d if the two cells are told apart)" % (homo, hetero, len(pairs), K * K))
    mixed = hexamers * (hexamers + 1) // 2
    assert mixed == 102188544245326 and hexamers * (hexamers - 1) // 2 == mixed - hexamers
    print("      mixed connexons, any pair: %d homotypic + %d heterotypic = %d" % (hexamers, mixed - hexamers, mixed))
    # the whole 12-subunit channel: positions 0-5 in one cell, 6-11 in the other
    D6 = [[(i + j) % 6 if i < 6 else 6 + (i + j) % 6 for i in range(12)] for j in range(6)] + \
         [[6 + (j - i) % 6 if i < 6 else (j - i) % 6 for i in range(12)] for j in range(6)]
    assert is_group(D6) and len(D6) == 12 and sorted(cycles(p) for p in D6) == [2, 2, 4, 4, 6, 6, 6, 6, 6, 6, 6, 12]
    def channel_formula(k): return (k ** 12 + 7 * k ** 6 + 2 * k ** 4 + 2 * k ** 2) // 12
    for k in range(1, 26): assert burnside(k, D6) == channel_formula(k)
    listed = []
    for k in (1, 2, 3):
        c, _, reps = orbits(12, k, D6, keep=True)
        assert c == burnside(k, D6)
        listed.append(c)
        types = set(); same = 0; one_type = 0
        for x in reps:
            d = [(x // k ** i) % k for i in range(12)]
            up = canon(tuple(d[:6]), C6); down = canon(tuple(d[6 + (-i) % 6] for i in range(6)), C6)
            types.add((min(up, down), max(up, down))); same += up == down
            one_type += len(set(d[:6])) == 1 and len(set(d[6:])) == 1
        m = necklace_formula(6, k)
        assert len(types) == m * (m + 1) // 2 and one_type == k * (k + 1) // 2
        if k == 2: assert (m, same, c - same) == (14, 64, 318)
        if k == 3: assert (m, same, c - same) == (130, 729, 43998)
    assert listed == [1, 382, 44727]
    whole = burnside(K, D6); assert whole == channel_formula(K) == 612985676011611
    print("      whole channels, counting which subunit faces which: %s for k = 1, 2, 3 (listed); two types: 64 homotypic + 318 heterotypic" % listed)
    print("      formula (k^12 + 7k^6 + 2k^4 + 2k^2)/12 at k = 21: %d (Burnside; too many to list)" % whole)

# ================================================================== 3. Dscam1
def dscam():
    global STATES
    print("3. DSCAM1: a product of choices, then self against non-self")
    clusters = [("exon 4", 12), ("exon 6", 48), ("exon 9", 33), ("exon 17", 2)]
    iso = set(itertools.product(*(range(c) for _, c in clusters))); STATES += len(iso)
    ecto = {t[:3] for t in iso}
    assert len(iso) == 38016 == 12 * 48 * 33 * 2 and len(ecto) == 19008 == 12 * 48 * 33 and 12 * 47 * 32 == 18048
    assert dec(Fraction(18048, 19008), 3) == "0.949" and dec(Fraction(18496, 19008), 3) == "0.973"
    print("   12 x 48 x 33 x 2 = %d isoforms listed; %d outside parts (12 x 48 x 33); 12 x 47 x 32 = 18048 bind only themselves (0.949);" % (len(iso), len(ecto)))
    print("   18496 of the 19008 were found in RNA (0.973): here the ceiling is nearly reached")

    # the formula, checked by listing every pair of m-subsets of an N-set, N <= 10
    def pmf(N, m, C=math.comb):
        return [Fraction(C(m, j) * C(N - m, m - j), C(N, m)) for j in range(m + 1)]
    pairs = 0
    for N in range(1, 11):
        for m in range(0, N + 1):
            sets = [sum(1 << i for i in c) for c in itertools.combinations(range(N), m)]
            tally = [0] * (m + 1)
            for a in sets:
                for b in sets: tally[bin(a & b).count("1")] += 1
            pairs += len(sets) ** 2
            assert [Fraction(t, len(sets) ** 2) for t in tally] == pmf(N, m)
    assert pairs == sum(math.comb(2 * N, N) for N in range(1, 11)) == 250952
    STATES += pairs
    # three cells, pairwise disjoint: count = C(N,m) C(N-m,m) C(N-2m,m); and the union bound for 'at most one shared'
    triples = 0
    for N in range(1, 9):
        for m in range(1, 4):
            if m > N: continue
            sets = [sum(1 << i for i in c) for c in itertools.combinations(range(N), m)]
            disjoint = loose = 0
            for a in sets:
                for b in sets:
                    ab = bin(a & b).count("1")
                    if ab > 1: continue
                    for c in sets:
                        ac = bin(a & c).count("1"); bc = bin(b & c).count("1")
                        if ac <= 1 and bc <= 1:
                            loose += 1
                            disjoint += ab == 0 and ac == 0 and bc == 0
            triples += len(sets) ** 3
            want = math.comb(N, m) * (math.comb(N - m, m) if N >= m else 0) * (math.comb(N - 2 * m, m) if N >= 2 * m else 0)
            assert disjoint == want
            q = 1 - pmf(N, m)[0] - (pmf(N, m)[1] if m >= 1 else 0)          # one pair shares two or more
            assert Fraction(loose, len(sets) ** 3) >= 1 - 3 * q
    STATES += triples
    assert triples == 264684
    print("   share-count formula C(m,j)C(N-m,m-j)/C(N,m): equal to the tally over all %d pairs of sets, every N <= 10, every m" % pairs)
    print("   three cells: pairwise-disjoint count and the union bound checked on all %d triples (N <= 8, m <= 3)" % triples)
    print("   toy case N=12, m=2: P(share none) = %s" % pmf(12, 2)[0]); assert pmf(12, 2)[0] == Fraction(15, 22)

    # realistic sizes: binomials recounted by Pascal's rule (no factorials), then exact fractions
    Ns, ms, crowd = (1152, 4752, 18048, 19008), (14, 30, 50), 10
    wanted = set(ms) | {N - j * m for N in Ns for m in ms for j in range(crowd)}
    table, row, upto = {}, [1] + [0] * max(ms), max(ms)
    for i in range(1, max(wanted) + 1):
        for j in range(min(i, upto), 0, -1): row[j] += row[j - 1]
        if i in wanted: table[i] = tuple(row)
    STATES += max(wanted) * upto
    def P(n, j): return table[n][j] if 0 <= j <= upto else 0
    for n in wanted:
        for j in range(upto + 1): assert P(n, j) == math.comb(n, j)
    PIN = {  # (N, m): P(share none), mean shared, P(share >= 2), P(share >= 3), P(10 cells pairwise share none)
        (1152, 14): ("0.841843", "0.170138", "1.14e-2", "4.81e-4", "0.000330"),
        (1152, 30): ("0.448486", "0.781250", "1.82e-1", "4.02e-2", "0.000000"),
        (1152, 50): ("0.103482", "2.170138", "6.50e-1", "3.70e-1", "0.000000"),
        (4752, 14): ("0.959480", "0.041245", "7.18e-4", "7.27e-6", "0.153168"),
        (4752, 30): ("0.826481", "0.189393", "1.50e-2", "8.21e-4", "0.000162"),
        (4752, 50): ("0.587639", "0.526094", "9.66e-2", "1.51e-2", "0.000000"),
        (18048, 14): ("0.989190", "0.010859", "5.05e-5", "1.34e-7", "0.612578"),
        (18048, 30): ("0.951278", "0.049867", "1.12e-3", "1.63e-5", "0.104585"),
        (18048, 50): ("0.870314", "0.138519", "8.46e-3", "3.57e-4", "0.001841"),
        (19008, 14): ("0.989734", "0.010311", "4.56e-5", "1.15e-7", "0.627971"),
        (19008, 30): ("0.953684", "0.047348", "1.01e-3", "1.39e-5", "0.117296"),
        (19008, 50): ("0.876457", "0.131523", "7.66e-3", "3.07e-4", "0.002538"),
    }
    print("   uniform draw of m isoforms out of N per cell; exact fractions, shown cut off:")
    print("      N      m   P(share none)  mean shared  P(share>=2)  P(share>=3)  10 cells, every pair shares none")
    got = {}
    for N in Ns:
        for m in ms:
            f = [Fraction(P(m, j) * P(N - m, m - j), P(N, m)) for j in range(m + 1)]
            assert f == pmf(N, m) and sum(f) == 1
            p0 = f[0]
            prod = Fraction(1)
            for i in range(m): prod *= Fraction(N - m - i, N - i)
            sieve = sum(Fraction((-1) ** j * math.comb(m, j) * math.comb(N - j, m - j), math.comb(N, m)) for j in range(m + 1))
            assert p0 == prod == sieve                                     # three routes to the same fraction
            mean = sum(j * x for j, x in enumerate(f)); assert mean == Fraction(m * m, N)
            ge2 = 1 - f[0] - f[1]; ge3 = ge2 - f[2]
            ten = Fraction(1)
            for j in range(crowd): ten *= Fraction(P(N - j * m, m), P(N, m))
            got[(N, m)] = (p0, ge2, ge3, ten)
            line = (dec(p0, 6), dec(mean, 6) if mean < 1 else str(mean.numerator // mean.denominator) + dec(mean % 1, 6)[1:], sci(ge2), sci(ge3), dec(ten, 6))
            assert line == PIN[(N, m)], ((N, m), line)
            print("      %-6d %-3d %-14s %-12s %-12s %-12s %s" % ((N, m) + line))
    p = got[(19008, 30)][0]
    assert p.denominator == math.comb(19008, 30) // math.gcd(math.comb(18978, 30), math.comb(19008, 30))
    assert (len(str(p.numerator)), len(str(p.denominator))) == (88, 88)
    print("      (N=19008, m=30: P(share none) = C(18978,30)/C(19008,30), a fraction of two 88-digit numbers in lowest terms)")
    # 100 cells: expected number of pairs sharing three or more = C(100,2) * P(share >= 3), exact
    exp = {N: 4950 * got[(N, 30)][2] for N in (1152, 4752, 19008)}
    shown = tuple(str(exp[N].numerator // exp[N].denominator) + dec(exp[N] % 1, 2)[1:] for N in (1152, 4752, 19008))
    assert shown == ("199.36", "4.06", "0.06")
    print("      100 cells, m=30: expected number of pairs sharing three or more: %s (N=1152), %s (N=4752), %s (N=19008)" % shown)

# ================================================================== 4. protocadherins
def protocadherins():
    print("4. CLUSTERED PROTOCADHERINS (mouse): few genes, identity by combination")
    alt = {"alpha": 12, "beta": 22, "gamma": 19}; ctype = {"alpha": 2, "beta": 0, "gamma": 3}
    total = {c: alt[c] + ctype[c] for c in alt}
    assert total == {"alpha": 14, "beta": 22, "gamma": 22} and sum(total.values()) == 58
    assert sum(alt.values()) == 53 and sum(ctype.values()) == 5
    N, m = 53, 10
    sets = math.comb(N, m); assert sets == 19499099620
    f = [Fraction(math.comb(m, j) * math.comb(N - m, m - j), sets) for j in range(m + 1)]
    assert sum(f) == 1 and sum(j * x for j, x in enumerate(f)) == Fraction(100, 53)
    assert f[m] == Fraction(1, sets) and f[0] == Fraction(math.comb(43, 10), sets)
    assert (dec(f[0], 4), dec(1 - f[0], 4), sci(f[m]), dec(Fraction(100, 53) % 1, 3)) == ("0.0983", "0.9016", "5.12e-11", "0.886")
    neurons = 70890000                              # Herculano-Houzel et al. 2006, whole mouse brain (cited)
    assert sets // neurons == 275 and dec(Fraction(neurons, sets), 4) == "0.0036"
    print("   14 alpha + 22 beta + 22 gamma = 58 = 53 alternate + 5 C-type")
    print("   model: a cell shows 10 of the 53 alternates (uniform) and all 5 C-types: C(53,10) = %d possible sets" % sets)
    print("   two cells: share no alternate %s, share at least one %s, mean shared 1.886, identical set %s" % (dec(f[0], 4), dec(1 - f[0], 4), sci(f[m])))
    print("   a mouse brain has about 70.89 million neurons: %d possible sets per neuron, so at most 0.0036 of the ceiling is in use" % (sets // neurons))

# ================================================================== 5. cells joined by channels
def joined_surface(ncells, channels):
    """Each cell is a drum (two n-gons and n side squares: a sphere). Each channel removes one side square
    at each end and glues in a tube of four squares. Faces are listed with a consistent sense of rotation."""
    deg = [0] * ncells
    for u, v in channels: deg[u] += 1; deg[v] += 1
    faces, ports, nv = [], [], 0
    for c in range(ncells):
        n = 2 * deg[c] + 3
        top = list(range(nv, nv + n)); bot = list(range(nv + n, nv + 2 * n)); nv += 2 * n
        faces.append(top[::-1]); faces.append(bot); mine = []
        for i in range(n):
            quad = [top[i], top[(i + 1) % n], bot[(i + 1) % n], bot[i]]
            if i % 2 == 0 and i // 2 < deg[c]: mine.append(quad)
            else: faces.append(quad)
        ports.append(mine)
    for u, v in channels:
        p = ports[u].pop(); q = ports[v].pop()
        for j in range(4): faces.append([p[j], p[(j + 1) % 4], q[(-j - 1) % 4], q[(-j) % 4]])
    return nv, faces

def pieces(nv, faces):
    """Check: closed (every edge has two faces), two-sided (the two faces run along it in opposite
    directions), no pinched vertex. Return the Euler characteristic V - E + F of each connected piece."""
    darts = set()
    for face in faces:
        for i, a in enumerate(face):
            d = (a, face[(i + 1) % len(face)]); assert d not in darts; darts.add(d)
    assert all((b, a) in darts for a, b in darts)
    around = [dict() for _ in range(nv)]
    for face in faces:
        for i, v in enumerate(face): around[v][face[i - 1]] = face[(i + 1) % len(face)]
    for nxt in around:
        start = next(iter(nxt)); u = nxt[start]; steps = 1
        while u != start: u = nxt[u]; steps += 1
        assert steps == len(nxt)
    root = list(range(nv))
    def find(a):
        while root[a] != a: root[a] = root[root[a]]; a = root[a]
        return a
    for face in faces:
        for v in face[1:]: root[find(v)] = find(face[0])
    chi = {}
    for v in range(nv): chi[find(v)] = chi.get(find(v), 0) + 1
    for a, b in darts:
        if a < b: chi[find(a)] -= 1
    for face in faces: chi[find(face[0])] += 1
    return sorted(chi.values())

def index_sum(nv, tris, h):
    """Banchoff's index, as in brain/hairy.py: at each vertex, 1 - (sign changes of h around it)/2. Summed."""
    around = [dict() for _ in range(nv)]
    for a, b, c in tris: around[a][b] = c; around[b][c] = a; around[c][a] = b
    total = 0
    for v, nxt in enumerate(around):
        ring = [next(iter(nxt))]
        while nxt[ring[-1]] != ring[0]: ring.append(nxt[ring[-1]])
        assert len(ring) == len(nxt)
        up = [h[u] > h[v] for u in ring]
        total += 1 - sum(up[i] != up[i - 1] for i in range(len(up))) // 2
    return total

def graph_pieces(nv, edges):
    root = list(range(nv))
    def find(a):
        while root[a] != a: root[a] = root[root[a]]; a = root[a]
        return a
    for u, v in edges: root[find(u)] = find(v)
    comp = {}
    for v in range(nv): comp.setdefault(find(v), [0, 0])[0] += 1
    for u, v in edges: comp[find(u)][1] += 1
    return sorted(comp.values())                       # [cells, channels] of each connected piece

def cells_join():
    global STATES
    print("5. CELLS JOINED BY CHANNELS: the surface between inside and outside")
    # the index identity on three small closed surfaces, for every ordering of the vertices
    tetra = [(0, 1, 2), (0, 3, 1), (0, 2, 3), (1, 3, 2)]
    octa = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 1), (5, 2, 1), (5, 3, 2), (5, 4, 3), (5, 1, 4)]
    torus = [(i, (i + 1) % 7, (i + 3) % 7) for i in range(7)] + [(i, (i + 3) % 7, (i + 2) % 7) for i in range(7)]
    orderings = 0
    for name, nv, tris, chi in (("tetrahedron", 4, tetra, 2), ("octahedron", 6, octa, 2), ("7-vertex torus", 7, torus, 0)):
        assert pieces(nv, [list(t) for t in tris]) == [chi] == [nv - len(tris) // 2]
        for h in itertools.permutations(range(nv)):
            assert index_sum(nv, tris, h) == chi
            orderings += 1
    STATES += orderings; assert orderings == 24 + 720 + 5040
    print("   index sum = V - F/2 = Euler characteristic for every ordering of the vertices: tetrahedron 2, octahedron 2, 7-vertex torus 0 (%d orderings)" % orderings)
    # every simple graph on 1..5 cells; every multigraph on 1..3 cells with 0..3 channels per pair and 0..1 per cell to itself
    graphs = []
    for n in range(1, 6):
        prs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(prs)): graphs.append((n, [p for i, p in enumerate(prs) if mask >> i & 1], True))
    for n in range(1, 4):
        prs = list(itertools.combinations(range(n), 2))
        for mult in itertools.product(range(4), repeat=len(prs)):
            for loops in itertools.product(range(2), repeat=n):
                e = [p for p, c in zip(prs, mult) for _ in range(c)] + [(v, v) for v in range(n) if loops[v]]
                graphs.append((n, e, False))
    assert len(graphs) == (1 + 2 + 8 + 64 + 1024) + (2 + 16 + 512) == 1629
    conn, trees, bridgeless = [0] * 5, [0] * 5, [0] * 5; top = 0; tested = 0
    for n, e, simple in graphs:
        nv, faces = joined_surface(n, e)
        chis = pieces(nv, faces)
        gp = graph_pieces(n, e)
        assert chis == sorted(2 * (v - c) for v, c in gp)                    # each piece: V - E + F = 2(cells - channels)
        assert sum(chis) == 2 * (n - len(e)) and all(c % 2 == 0 and c <= 2 for c in chis)
        genus = sum((2 - c) // 2 for c in chis)
        assert genus == len(e) - n + len(gp)                                # handles = channels - cells + pieces
        critical = sum(1 for i in range(len(e)) if len(graph_pieces(n, e[:i] + e[i + 1:])) > len(gp))
        assert (genus == 0) == (critical == len(e))                         # all spheres iff every channel is critical
        top = max(top, genus)
        # the index sum on the joined surface (a cone over each face makes it a triangle mesh)
        tris, nt = [], nv
        for face in faces:
            for i in range(len(face)): tris.append((face[i], face[(i + 1) % len(face)], nt))
            nt += 1
        assert nt - len(tris) // 2 == sum(chis)
        pr = 10007
        for a, b in ((1, 0), (pr - 1, 0), (4001, 17)):
            h = [(a * v + b) % pr for v in range(nt)]; assert len(set(h)) == nt
            assert index_sum(nt, tris, h) == sum(chis); tested += 1
        if simple and len(gp) == 1:
            conn[n - 1] += 1; trees[n - 1] += len(e) == n - 1; bridgeless[n - 1] += critical == 0
    STATES += len(graphs)
    assert conn == [1, 1, 4, 38, 728] and trees == [1, 1, 3, 16, 125] and bridgeless == [1, 0, 1, 10, 253]
    assert top == 10 and tested == 3 * 1629
    print("   %d networks of cells built as closed two-sided polygon meshes (every graph on up to 5 cells; every multigraph on up to 3 cells, up to 3 channels per pair)" % len(graphs))
    print("   in every one: Euler characteristic = 2(cells - channels); handles = channels - cells + pieces (largest here: %d);" % top)
    print("   all spheres exactly when every channel is critical; index sum = Euler characteristic for %d test functions" % tested)
    print("   connected graphs on 1..5 cells: %s; trees: %s; no critical channel: %s  (the numbers of philosophy/rhizome.py)" % (conn, trees, bridgeless))
    one = pieces(*joined_surface(2, [(0, 1)])); two = pieces(*joined_surface(2, [(0, 1), (0, 1)])); self1 = pieces(*joined_surface(1, [(0, 0)]))
    assert (one, two, self1) == ([2], [0], [0])
    print("   two cells, one channel: Euler characteristic 2 (a sphere). Two channels: 0 (a torus). One cell joined to itself: 0.")

# ================================================================== 6. the rotation group itself
def rotation_group():
    print("6. THE GROUP OF A RING: Z/n")
    for a, b in ((2, 3), (4, 3)):
        n = a * b
        assert len({(x % a, x % b) for x in range(n)}) == n
        assert all(((x + y) % n) % a == (x % a + y % a) % a and ((x + y) % n) % b == (x % b + y % b) % b
                   for x in range(n) for y in range(n))
    assert len({(x % 2, x % 2) for x in range(4)}) == 2
    print("   Z/6 = Z/2 x Z/3 (a hexamer: its half turn and its third turns) and Z/12 = Z/4 x Z/3 (zodiac/BASE.md, open item 1): checked on every element")
    print("   Z/4 is not Z/2 x Z/2: a tetramer's quarter turn has no such splitting")

# ================================================================== fingerprints
def fingerprints(write):
    path = os.path.join(HERE, "fingerprints.json")
    data = [{"name": name, "seq": seq, "runner": "python3 -I brain/complexes/check.py"} for name, seq in SEQ.items()]
    assert len(data) == 7 and all(len(e["seq"]) >= 6 for e in data)
    if write:
        with open(path, "w") as f: json.dump(data, f, indent=1); f.write("\n")
        print("fingerprints.json written: %d sequences" % len(data))
    elif os.path.exists(path):
        assert json.load(open(path)) == data, "fingerprints.json does not match the computed sequences"
        print("fingerprints.json matches the computed sequences (%d sequences)" % len(data))
    else:
        print("fingerprints.json not found (run with --write-fingerprints)")

if __name__ == "__main__":
    full = "--full" in sys.argv[1:]
    rings(); anchors(full); dscam(); protocadherins(); cells_join(); rotation_group()
    fingerprints("--write-fingerprints" in sys.argv[1:])
    print("PASS")
    print(json.dumps({"states": STATES, "seconds": round(time.time() - T0, 2)}))
