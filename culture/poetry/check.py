#!/usr/bin/env python3
"""Poetry as finite structure, with a psychoanalytic layer built as operations. Every case is enumerated; nothing is sampled.

A poem is read as a sequence of lines; each line ends in a signifier (an end sound or end word).
FORMAL LAYER (checked-finite)
  F1 rhyme schemes of n lines = restricted growth strings = set partitions of n: Bell(n), n = 1..10.
  F2 block profiles: partitions with a given multiset of block sizes number n!/(prod size! * prod mult!), every profile, n <= 10.
     The sonnet: 14 lines, 7 rhymes used twice each: 135135 schemes (enumerated). 27 keep each pair inside its
     quatrain or the couplet; of those exactly 1 alternates (ABAB CDCD EFEF GG, Shakespeare). 10395 end on a couplet.
     Petrarch's profile (4, 4, 2, 2, 2): all 1576575 schemes enumerated at n = 14, matching the formula.
  F3 the sestina spiral (Arnaut Daniel's form): next stanza takes end words in order last, first, second last, second, ...
     For n = 6 it is a single 6-cycle (order 6) with no fixed point. For n <= 30 the list of n where it is one n-cycle
     is printed and compared with: 2n+1 prime and 2 of order 2n, or of order n with n odd, mod 2n+1.
     It has a fixed point exactly when n = 1 mod 3.
  F4 Queneau, Cent mille milliards de poemes (1961): 10 choices for each of 14 lines. Product rule checked on every
     small case (k choices, m lines, k, m <= 4); 10^14 is then arithmetic. On a toy: every combination keeps the
     scheme when each slot's variants share a rhyme, and some combination breaks it when one slot's do not.
     Whether Queneau's book has that property is not checked here.
PSYCHOANALYTIC LAYER (the operations and their facts are checked-finite; every psychoanalytic reading is analogy)
  P1 condensation (Freud, Die Traumdeutung, 1900): a map from k thoughts to m signifiers that is not injective.
     Its kernel is a set partition, so a rhyme scheme is exactly the condensation pattern of the line -> sound map.
     Maps with a given kernel of b blocks: m(m-1)...(m-b+1); over all kernels of b blocks: S(k,b) m(m-1)...(m-b+1). Non-injective maps: m^k - m!/(m-k)!. k > m: all condense. k, m <= 5.
  P2 displacement (same work): a permutation of emphasis. Intensity (the sum of weights) is kept. Total displacement
     (no element keeps its place) is a derangement: D(n) for n <= 7. The sestina spiral is a total displacement at n = 6.
  P3 metaphor and metonymy (Jakobson 1956; Lacan, L'instance de la lettre, 1957): metaphor = substitution inside a
     paradigm class; metonymy = contiguity in the chain. Over every paradigm partition of an alphabet of <= 4 signifiers
     and every chain of length <= 3: substitution is an equivalence (classes = k^L), contiguity is symmetric and not
     transitive once L >= 3. Paradigm partitions are Bell(n), the same count as rhyme schemes and as the equivalence
     relations on n points (all 2^(n^2) relations enumerated, n <= 4).
  P4 point de capiton (Lacan, Seminaire III, 1955-56; Subversion du sujet, 1960): meaning fixed only after the fact.
     Model: signifiers are codewords, a chain is a bit string, a reading is its parse. Prefix code {0,10,11}: each
     word is fixed when it ends (delay 0). Code {0,01,11}: uniquely decodable (length <= 12, every string), not a
     prefix code, and its reversal is a prefix code: read from the end it is instant. For each length n we count the
     chains whose first signifier is fixed only by the last bit. That delay is measured against chains of the SAME
     length: the reader knows where the chain ends. With any continuation allowed the delay is unbounded: after
     0 1^k the first word is still open, for every k (checked k <= 12).
  P5 repetition compulsion (Freud, Jenseits des Lustprinzips, 1920): every self-map of a finite set is eventually
     periodic: for every point, tail + cycle <= n. All n^n maps, n <= 6. Pure return (no tail) = permutations = n!.
     A refrain is a fixed point: maps with one: n^n - (n-1)^n. Total cyclic points: sum_k n!/(n-k)! n^(n-k).
  P6 the anchor (this project's own definition, proposed; Freud 1923 / Lacan 1955-56 only as a reading): reading frame = forward order plus rhyme echo, closed
     reflexively and transitively. a is an anchor when every line reachable from a sees a back. Over every scheme of
     n <= 8 lines the anchors form a suffix, they are the final cluster, and the number of schemes whose anchor is the
     last k lines is Bell(n-k) * A(k), A = atomic (unsplittable) partitions. Shakespeare: the couplet. Petrarch: the
     sestet. Terza rima: every line.
Run: python3 -I culture/poetry/check.py     (prints PASS, then a JSON line; writes fingerprints.json beside it)
"""
import itertools, json, math, os, time
from collections import Counter

STATES = 0

def rgs(n):
    """All restricted growth strings of length n (rhyme schemes, first line = letter 0)."""
    if n == 0:
        yield (); return
    def go(prefix, mx):
        if len(prefix) == n:
            yield tuple(prefix); return
        for c in range(mx + 2):
            prefix.append(c); yield from go(prefix, max(mx, c)); prefix.pop()
    yield from go([0], 0)

def bell_rec(N):
    row, out = [1], [1]
    for _ in range(N):
        new = [row[-1]]
        for x in row: new.append(new[-1] + x)
        row = new; out.append(row[0])
    return out                                       # Bell(0..N) by the Bell triangle

def profile(s):
    return tuple(sorted(Counter(s).values()))

def profile_formula(n, prof):
    d = 1
    for size in prof: d *= math.factorial(size)
    for m in Counter(prof).values(): d *= math.factorial(m)
    return math.factorial(n) // d

def by_profile(n, prof):
    """Every set partition of range(n) with the given block sizes, each once: the block of the smallest free line first."""
    def go(free, sizes):
        if not free:
            yield (); return
        a, rest = free[0], free[1:]
        for s in sorted(sizes):
            if sizes[s] == 0: continue
            sizes[s] -= 1
            for others in itertools.combinations(rest, s - 1):
                left = tuple(x for x in rest if x not in others)
                for tail in go(left, sizes): yield ((a,) + others,) + tail
            sizes[s] += 1
    yield from go(tuple(range(n)), Counter(prof))

def stirling2(k, b):
    S = [[1]]                                        # S(0,0) = 1, by the recurrence S(n,j) = j S(n-1,j) + S(n-1,j-1)
    for n in range(1, k + 1):
        S.append([(j * S[n - 1][j] if j < n else 0) + (S[n - 1][j - 1] if j >= 1 else 0) for j in range(n + 1)])
    return S[k][b] if b <= k else 0

def falling(m, b):
    r = 1
    for i in range(b): r *= m - i
    return r

# ---------------------------------------------------------------- F1, F2
def formal_schemes():
    global STATES
    bell = bell_rec(10)
    counts = []
    for n in range(1, 11):
        c = 0; profs = Counter()
        for s in rgs(n):
            c += 1; profs[profile(s)] += 1
        STATES += c
        for prof, k in profs.items(): assert k == profile_formula(n, prof), (n, prof)
        counts.append(c)
    assert counts == bell[1:11] == [1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]
    return counts

def matchings(items):
    if not items:
        yield []; return
    a = items[0]
    for i in range(1, len(items)):
        rest = items[1:i] + items[i + 1:]
        for m in matchings(rest): yield [(a, items[i])] + m

def sonnet():
    global STATES
    blocks = [range(0, 4), range(4, 8), range(8, 12), range(12, 14)]
    blk = {i: k for k, b in enumerate(blocks) for i in b}
    total = local = alternating = couplet = 0
    shakespeare = (0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 6)
    found = False
    for m in matchings(list(range(14))):
        total += 1
        s = [None] * 14
        for k, (a, b) in enumerate(sorted(m)): s[a] = s[b] = k
        seen = {}; s = tuple(seen.setdefault(x, len(seen)) for x in s)   # as a restricted growth string
        found |= s == shakespeare
        if (12, 13) in m: couplet += 1
        if all(blk[a] == blk[b] for a, b in m):
            local += 1
            if all(b - a == 2 for a, b in m if blk[a] < 3): alternating += 1; assert s == shakespeare
    STATES += total
    assert total == 135135 == profile_formula(14, (2,) * 7)          # 13!! = 135135
    assert found and local == 27 and alternating == 1 and couplet == 10395
    petrarch = profile_formula(14, (2, 2, 2, 4, 4))                    # ABBAABBA CDECDE: blocks 4, 4, 2, 2, 2
    assert petrarch == 1576575
    pet_scheme = ((0, 3, 4, 7), (1, 2, 5, 6), (8, 11), (9, 12), (10, 13))
    pet_enum = 0; pet_found = False
    for p in by_profile(14, (4, 4, 2, 2, 2)):                         # enumerated, not only the formula
        pet_enum += 1; pet_found |= p == pet_scheme
    STATES += pet_enum
    assert pet_found and pet_enum == petrarch
    # a second route: choose the two 4-blocks, then match the six lines left
    assert math.comb(14, 4) * math.comb(10, 4) // 2 * 15 == petrarch
    return {"sonnet_profile": total, "quatrain_local": local, "shakespeare": alternating, "end_couplet": couplet,
            "petrarch_profile_enumerated": pet_enum}

# ---------------------------------------------------------------- F3
def spiral(n):
    p = []
    lo, hi = 0, n - 1
    while lo <= hi:
        p.append(hi); hi -= 1
        if lo <= hi: p.append(lo); lo += 1
    return p                                         # stanza k+1, position i, holds stanza k's word p[i]

def cycles(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen: continue
        c, j = 0, i
        while j not in seen: seen.add(j); j = p[j]; c += 1
        out.append(c)
    return out

def order_mod(a, q):
    k, x = 1, a % q
    while x != 1: x = x * a % q; k += 1
    return k

def isprime(q): return q > 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))

def sestina():
    global STATES
    p6 = spiral(6)
    assert p6 == [5, 0, 4, 1, 3, 2] and cycles(p6) == [6]
    order = math.lcm(*cycles(p6)); assert order == 6
    assert all(p6[i] != i for i in range(6))                         # total displacement
    words = list(range(6)); stanzas = [words]
    for _ in range(6): stanzas.append([stanzas[-1][j] for j in p6])
    assert stanzas[6] == stanzas[0] and len({tuple(x) for x in stanzas[:6]}) == 6   # six stanzas, then return
    single, fixed = [], []
    for n in range(1, 31):
        p = spiral(n); STATES += n
        if cycles(p) == [n]: single.append(n)
        if any(p[i] == i for i in range(n)): fixed.append(n)
    char = [n for n in range(1, 31) if isprime(2 * n + 1) and
            (order_mod(2, 2 * n + 1) == 2 * n or (order_mod(2, 2 * n + 1) == n and n % 2 == 1))]
    assert single == char, (single, char)
    assert fixed == [n for n in range(1, 31) if n % 3 == 1]
    return single

# ---------------------------------------------------------------- F4
def queneau():
    global STATES
    for k in range(1, 5):
        for m in range(1, 5):
            c = sum(1 for _ in itertools.product(range(k), repeat=m)); STATES += c
            assert c == k ** m
    scheme = (0, 1, 1, 0)                            # a 4-line toy: each slot's variants share the slot's rhyme
    variants = [[(scheme[i], v) for v in range(3)] for i in range(4)]
    for poem in itertools.product(*variants):
        seen = {}; s = tuple(seen.setdefault(r, len(seen)) for r, _ in poem)
        assert s == scheme
    # the converse, so the toy tests something: let slot 2's variants carry different rhymes; some poem leaves the scheme
    for slot in range(4):
        bad = [list(v) for v in variants]
        bad[slot] = [(scheme[slot], 0), (9, 1), (scheme[slot], 2)]    # one variant with a foreign rhyme 9
        broke = False
        for poem in itertools.product(*bad):
            seen = {}; s = tuple(seen.setdefault(r, len(seen)) for r, _ in poem)
            broke |= s != scheme
        assert broke, slot
    assert 10 ** 14 == 100_000 * 1_000_000_000      # cent mille milliards
    return [10 ** m for m in range(1, 15)]

# ---------------------------------------------------------------- P1, P2
def condensation():
    global STATES
    for k in range(1, 6):
        for m in range(1, 6):
            by_kernel = Counter(); noninj = 0
            for f in itertools.product(range(m), repeat=k):
                STATES += 1
                seen = {}; ker = tuple(seen.setdefault(x, len(seen)) for x in f)   # the rhyme scheme of f
                by_kernel[ker] += 1
                noninj += len(set(f)) < k
            by_blocks = Counter()
            for ker in rgs(k):
                assert by_kernel[ker] == falling(m, max(ker) + 1)          # one GIVEN kernel of b blocks
                by_blocks[max(ker) + 1] += by_kernel[ker]
            for b in range(1, k + 1):                                    # all kernels of b blocks together
                assert by_blocks[b] == stirling2(k, b) * falling(m, b), (k, m, b)
            assert noninj == m ** k - falling(m, k)
            if k > m: assert noninj == m ** k                         # pigeonhole: every map condenses
    return True

def displacement():
    global STATES
    D = []
    for n in range(1, 8):
        w = list(range(1, n + 1)); d = 0
        for p in itertools.permutations(range(n)):
            STATES += 1
            assert sum(w[i] for i in p) == sum(w)                     # intensity kept
            d += all(p[i] != i for i in range(n))
        D.append(d)
    assert D == [0, 1, 2, 9, 44, 265, 1854]
    for n in range(3, 8): assert D[n - 1] == (n - 1) * (D[n - 2] + D[n - 3])
    return D

# ---------------------------------------------------------------- P3
def axes():
    global STATES
    for a in range(1, 5):
        for part in rgs(a):
            k = max(part) + 1
            for L in range(1, 4):
                chains = list(itertools.product(range(a), repeat=L)); STATES += len(chains)
                same = lambda x, y: all(part[i] == part[j] for i, j in zip(x, y))
                for x in chains:
                    for y in chains:
                        if same(x, y):
                            assert same(y, x)
                classes = {tuple(part[c] for c in x) for x in chains}
                assert len(classes) == k ** L
                # transitivity of substitution: two chains equivalent to a third are equivalent to each other
                for x in chains:
                    eq = [y for y in chains if same(x, y)]
                    assert all(same(y, z) for y in eq for z in eq)
    # contiguity on the positions of a chain of length L: i ~ j iff |i - j| == 1
    for L in range(1, 7):
        adj = {(i, j) for i in range(L) for j in range(L) if abs(i - j) == 1}
        assert all((j, i) in adj for i, j in adj)
        trans = all((i, k) in adj for i, j in adj for j2, k in adj if j == j2)
        assert trans == (L < 2)                                      # 0~1~0 without 0~0 breaks it
        adjr = adj | {(i, i) for i in range(L)}                      # with the reflexive closure
        transr = all((i, k) in adjr for i, j in adjr for j2, k in adjr if j == j2)
        assert transr == (L <= 2)
    # equivalence relations on n points <-> set partitions (rgs): all 2^(n^2) relations
    eqs = []
    for n in range(1, 5):
        pairs = [(i, j) for i in range(n) for j in range(n)]; c = 0; parts = set()
        for bits in range(1 << len(pairs)):
            STATES += 1
            R = {pairs[t] for t in range(len(pairs)) if bits >> t & 1}
            if all((i, i) in R for i in range(n)) and all((j, i) in R for i, j in R) and \
               all((i, k) in R for i, j in R for j2, k in R if j == j2):
                c += 1
                seen = {}; parts.add(tuple(seen.setdefault(min(j for j in range(n) if (i, j) in R), len(seen)) for i in range(n)))
        assert parts == set(rgs(n)); eqs.append(c)
    assert eqs == [1, 2, 5, 15]
    return eqs

# ---------------------------------------------------------------- P4
def parses(w, code, memo=None):
    if memo is None: memo = {}
    if w in memo: return memo[w]
    if w == "": return [[]]
    out = [[c] + rest for c in code if w.startswith(c) for rest in parses(w[len(c):], code, memo)]
    memo[w] = out
    return out

def capiton():
    global STATES
    prefix_code, quilt_code = ["0", "10", "11"], ["0", "01", "11"]
    is_prefix = lambda C: not any(a != b and b.startswith(a) for a in C for b in C)
    assert is_prefix(prefix_code) and not is_prefix(quilt_code) and is_prefix([c[::-1] for c in quilt_code])
    only_at_end, retro, total, early = [], [], [], []
    for n in range(1, 13):
        msgs = {}
        for bits in itertools.product("01", repeat=n):
            STATES += 2
            w = "".join(bits)
            for C, tag in ((prefix_code, "p"), (quilt_code, "q")):
                ps = parses(w, C)
                assert len(ps) <= 1                                    # uniquely decodable
                if ps: msgs.setdefault(tag, {})[w] = ps[0][0]
        def delay(tag, w):
            first = msgs[tag][w]
            for t in range(1, n + 1):
                if all(f == first for v, f in msgs[tag].items() if v[:t] == w[:t]): return t
        for w, first in msgs.get("p", {}).items(): assert delay("p", w) == len(first)   # fixed when the word ends
        lates = sorted(w for w in msgs.get("q", {}) if delay("q", w) == n)
        if n >= 2: assert lates == sorted(["0" + "1" * (n - 1), "0" + "1" * (n - 2) + "0"])   # 0 1..1 and 0 1..1 0
        only_at_end.append(len(lates))
        retro.append(sum(1 for w, f in msgs.get("q", {}).items() if delay("q", w) > len(f)))
        early.append(sum(1 for w in msgs.get("q", {}) if delay("q", w) < n))
        total.append(len(msgs.get("q", {})))
    # Unbounded delay once the length is not known: 0 1^k extends to a chain read 0 | 11 ... and to one read 01 | 11 ...
    for k in range(13):
        w = "0" + "1" * k
        a, b = w + ("" if k % 2 == 0 else "1"), w + ("1" if k % 2 == 0 else "")
        pa, pb = parses(a, quilt_code), parses(b, quilt_code)
        assert pa and pb and pa[0][0] == "0" and pb[0][0] == "01", k  # the first word is still open after 0 1^k
    assert [t - l for t, l in zip(total, only_at_end)] == early and all(2 * e > t for e, t in zip(early[2:], total[2:]))   # n >= 3: most chains fix it before the end
    return only_at_end, retro, total, early

# ---------------------------------------------------------------- P5
def repetition():
    global STATES
    perms, withfix, cyc_total, idem, connected, maxtail = [], [], [], [], [], []
    for n in range(1, 7):
        P = F = C = I = K = 0; mt = 0
        for f in itertools.product(range(n), repeat=n):
            STATES += 1
            cyc = set()
            for x in range(n):
                seen = {}; y, t = x, 0
                while y not in seen: seen[y] = t; y = f[y]; t += 1
                tail, c = seen[y], t - seen[y]
                assert tail + c <= n                                   # eventually periodic within n steps
                mt = max(mt, tail)
                cyc.add(y)
                z = f[y]
                while z != y: cyc.add(z); z = f[z]
            P += len(cyc) == n
            F += any(f[x] == x for x in range(n))
            C += len(cyc)
            I += all(f[f[x]] == f[x] for x in range(n))
            # connected functional graph: one component
            par = list(range(n))
            def find(a):
                while par[a] != a: par[a] = par[par[a]]; a = par[a]
                return a
            for x in range(n): par[find(x)] = find(f[x])
            K += len({find(x) for x in range(n)}) == 1
        perms.append(P); withfix.append(F); cyc_total.append(C); idem.append(I); connected.append(K); maxtail.append(mt)
        assert P == math.factorial(n) and F == n ** n - (n - 1) ** n
        assert C == sum(falling(n, k) * n ** (n - k) for k in range(1, n + 1))
        assert I == sum(math.comb(n, k) * k ** (n - k) for k in range(1, n + 1))
        assert mt == n - 1
    assert connected == [1, 3, 17, 142, 1569, 21576]
    return {"permutations": perms, "with_fixed_point": withfix, "cyclic_points_total": cyc_total,
            "idempotent": idem, "connected": connected, "max_tail": maxtail}

# ---------------------------------------------------------------- P6
def frame(s):
    n = len(s)
    R = {(i, j) for i in range(n) for j in range(n) if i <= j}            # forward reading order
    R |= {(i, j) for i in range(n) for j in range(n) if s[i] == s[j]}     # rhyme echo, both ways
    changed = True
    while changed:
        new = {(a, d) for (a, b) in R for (c, d) in R if b == c} - R
        changed = bool(new); R |= new
    return R

def anchors(s):
    R = frame(s); n = len(s)
    return [a for a in range(n) if all((b, a) in R for b in range(n) if (a, b) in R)]

def atomic(n):
    return sum(1 for s in rgs(n) if not any(set(s[:m]).isdisjoint(s[m:]) for m in range(1, n)))

def anchor_layer():
    global STATES
    A = [atomic(n) for n in range(1, 9)]
    assert A == [1, 1, 2, 6, 22, 92, 426, 2146]
    bell = bell_rec(8)
    for n in range(1, 9):
        dist = Counter()
        for s in rgs(n):
            STATES += 1
            an = anchors(s); R = frame(s)
            assert an == list(range(n - len(an), n))                         # a suffix
            final = [i for i in range(n) if (n - 1, i) in R]                 # the cluster of the last line
            assert an == final
            dist[len(an)] += 1
        for k in range(1, n + 1): assert dist[k] == bell[n - k] * A[k - 1]
    shakespeare = (0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 6)
    petrarch = (0, 1, 1, 0, 0, 1, 1, 0, 2, 3, 4, 2, 3, 4)
    terza = (0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 4)                       # ABA BCB CDC DED E
    free = tuple(range(10))
    assert anchors(shakespeare) == [12, 13]
    assert anchors(petrarch) == list(range(8, 14))
    assert anchors(terza) == list(range(13))
    assert anchors(free) == [9]
    return A

def main():
    t0 = time.time()
    bell = formal_schemes();             print("F1 rhyme schemes of n = 1..10 lines (Bell):", bell)
    son = sonnet();                      print("F2 sonnet profile (7 rhymes x 2):", son)
    single = sestina();                  print("F3 sestina spiral is one n-cycle for n <= 30:", single, "(= the 2n+1 prime characterisation in range)")
    qn = queneau();                      print("F4 Queneau: 10^14 =", qn[-1])
    condensation();                      print("P1 condensation: kernel counts and non-injective counts hold for k, m <= 5")
    D = displacement();                  print("P2 total displacements (derangements) n = 1..7:", D)
    eqs = axes();                        print("P3 equivalence relations = paradigm partitions, n = 1..4:", eqs)
    late, retro, qtotal, early = capiton()
    print("P4 chains of {0,01,11}, n = 1..12 (length known): total", qtotal, "; first signifier fixed after it ends", retro,
          "; fixed only by the last bit", late, "; fixed before the last bit", early, "; length unknown: delay unbounded (k <= 12)")
    rep = repetition();                  print("P5 self-maps n = 1..6:", rep)
    A = anchor_layer();                  print("P6 schemes whose anchor is the whole poem (atomic partitions) n = 1..8:", A)
    print("PASS")
    fp = [
        {"name": "rhyme schemes of n lines (Bell numbers)", "seq": bell},
        {"name": "Queneau sonnets with m lines, 10 choices each", "seq": qn},
        {"name": "sestina spiral single cycle n <= 30", "seq": single},
        {"name": "total displacements (derangements)", "seq": D},
        {"name": "self-maps with a refrain (a fixed point)", "seq": rep["with_fixed_point"]},
        {"name": "idempotent self-maps", "seq": rep["idempotent"]},
        {"name": "connected self-maps", "seq": rep["connected"]},
        {"name": "capiton chains fixed only at the end", "seq": late},
        {"name": "capiton chains of {0,01,11}", "seq": qtotal},
        {"name": "capiton chains fixed after the signifier ends", "seq": retro},
        {"name": "poems anchored as a whole (atomic partitions)", "seq": A},
    ]
    for e in fp: e["runner"] = "python3 -I culture/poetry/check.py"
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fingerprints.json"), "w") as fh:
        json.dump(fp, fh, indent=1); fh.write("\n")
    print(json.dumps({"states": STATES, "seconds": round(time.time() - t0, 2), "sonnet": son, "sestina_single_cycle": single,
                      "capiton_late": late, "capiton_retro": retro, "atomic": A}))

if __name__ == "__main__":
    main()
