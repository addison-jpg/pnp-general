#!/usr/bin/env python3
"""Who to pursue: stable matching on two finite sides, one-to-one (k=1) and with capacity k (k=2), exhaustive.

Two sides A and B of size n. Each member ranks every member of the other side strictly (a preference profile).
A matching is a set of A-B pairs; with capacity k each member holds at most k partners. k=1 is one-to-one.
A pair (a, b) outside the matching blocks it when each would take the other: a has a free place or ranks b above
its worst current partner, and the same for b. A matching is stable when no pair blocks it.
Checked on every profile for n = 0..3, no sampling (n=3 has 6^6 = 46656 profiles; n=4 has 24^8, about 1.1e11,
so n=4 is not run: the bound is n <= 3):
 (a) brute force over every matching agrees with deferred acceptance (Gale and Shapley 1962; the capacity
     version is a known many-to-many generalisation, cited from memory): a stable matching exists, and the
     deferred-acceptance result is one of the stable ones;
 (b) the mirror: with k=1 the capacity model gives exactly the stable matchings of a separate one-to-one model;
 (c) the pursuit rule "pursue what deferred acceptance keeps" never leaves a member a blocking pair it could join;
 (d) refusals (a negative edge, kismesis-like) with the matched pairs (positive) form a signed graph; its
     structural balance is checked with the functions of culture/homestuck/quadrants/check.py, imported.
Speed: on n=3 each side's "would join" pairs are precomputed as bits, so a matching is stable when two bit
sets do not meet. On n <= 2 the bit form is asserted equal to the direct pair-by-pair check.
This models stated rankings, not feelings. It cannot say who is good for anyone. No real people.
Run: python3 -I culture/love/check.py   (writes fingerprints.json beside it; last line is JSON)
"""
import importlib.util, itertools, json, os, time

HERE = os.path.dirname(os.path.abspath(__file__))
NMAX = 3

def validate(n, pa, pb):
    # every member of each side ranks all n members of the other side, each once
    want = list(range(n))
    if len(pa) != n or len(pb) != n: raise ValueError("each side needs one ranking per member")
    for r in list(pa) + list(pb):
        if sorted(r) != want: raise ValueError(f"a ranking must list each of 0..{n-1} once, got {r}")

def ranks(prefs):
    # prefs[i] = list of j, best first  ->  rank[i][j] (0 = best)
    out = []
    for p in prefs:
        r = [0] * len(p)
        for pos, j in enumerate(p): r[j] = pos
        out.append(r)
    return out

def matchings(n, k):
    # every set of A-B pairs in which each member has at most k partners
    pairs = [(a, b) for a in range(n) for b in range(n)]
    out = []
    for mask in range(1 << len(pairs)):
        m = frozenset(p for i, p in enumerate(pairs) if mask >> i & 1)
        da = [0] * n; db = [0] * n
        for a, b in m: da[a] += 1; db[b] += 1
        if max(da + db, default=0) <= k: out.append(m)
    return out

def wants(r, me, other, partners, k):
    # would `me` take `other`? yes if a place is free or other beats my worst current partner
    if len(partners) < k: return True
    return r[me][other] < max(r[me][p] for p in partners)

def blocking_pairs(n, k, ra, rb, m):
    pa = {a: [b for x, b in m if x == a] for a in range(n)}
    pb = {b: [a for a, y in m if y == b] for b in range(n)}
    return [(a, b) for a in range(n) for b in range(n)
            if (a, b) not in m and wants(ra, a, b, pa[a], k) and wants(rb, b, a, pb[b], k)]

def stable(n, k, ra, rb, m): return not blocking_pairs(n, k, ra, rb, m)

def deferred_acceptance(n, k, ra, rb):
    # A proposes. Each a keeps proposing down its list while it holds fewer than k; each b keeps its best k offers.
    pref_a = [sorted(range(n), key=lambda b: ra[a][b]) for a in range(n)]
    nxt = [0] * n; held = {b: [] for b in range(n)}; holds = [0] * n
    while True:
        moved = False
        for a in range(n):
            while holds[a] < k and nxt[a] < n:
                b = pref_a[a][nxt[a]]; nxt[a] += 1; moved = True
                held[b].append(a); held[b].sort(key=lambda x: rb[b][x]); holds[a] += 1
                if len(held[b]) > k:
                    out = held[b].pop(); holds[out] -= 1
        if not moved: break
    return frozenset((a, b) for b in range(n) for a in held[b])

# a separate one-to-one model: a matching is a partial injection A -> B; written apart from the capacity code
def injections(n):
    out = []
    for size in range(n + 1):
        for As in itertools.combinations(range(n), size):
            for Bs in itertools.permutations(range(n), size): out.append(dict(zip(As, Bs)))
    return out

def one_to_one_side(n, r, mate):
    # bit a*n+b set when `a` (this side, mate: a -> b) is unmatched or ranks b above its mate
    bits = 0
    for a in range(n):
        for b in range(n):
            if mate.get(a) != b and (a not in mate or r[a][b] < r[a][mate[a]]): bits |= 1 << (a * n + b)
    return bits

def one_to_one_stable(n, ra, rb, inj=None):
    out = set()
    for mate_a in inj if inj is not None else injections(n):
        mate_b = {b: a for a, b in mate_a.items()}
        xa = one_to_one_side(n, ra, mate_a)
        xb = one_to_one_side(n, rb, mate_b)   # indexed b*n+a: transpose before comparing
        xbt = sum(1 << (a * n + b) for a in range(n) for b in range(n) if xb >> (b * n + a) & 1)
        if not xa & xbt: out.add(frozenset(mate_a.items()))
    return out

# fast form of the capacity check: one side's "would join" bits per matching, so stability is one AND
def side_bits(n, k, r, m, side):
    bits = 0
    for me in range(n):
        partners = [b if side == 0 else a for a, b in m if (a if side == 0 else b) == me]
        for other in range(n):
            pair = (me, other) if side == 0 else (other, me)
            if pair not in m and wants(r, me, other, partners, k): bits |= 1 << (pair[0] * n + pair[1])
    return bits

def profiles(n):
    perms = list(itertools.permutations(range(n)))
    for pa in itertools.product(perms, repeat=n):
        for pb in itertools.product(perms, repeat=n):
            yield pa, pb

def load_quadrants():
    path = os.path.join(HERE, "..", "homestuck", "quadrants", "check.py")
    spec = importlib.util.spec_from_file_location("quadrants_check", path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod

def signed(n, m, refuse):
    # vertices: A members 0..n-1, B members n..2n-1. matched pair -> matesprit (+), refusal -> kismesis (-)
    lab = {}
    for a, b in m: lab[(a, n + b)] = "matesprit"
    for a, b in refuse: lab[(a, n + b)] = "kismesis"
    return lab

def main():
    t0 = time.time(); states = 0; out = {}
    for n in range(0, NMAX + 1):
        M = {k: matchings(n, k) for k in (1, 2)}
        prof = 0; uniq = {1: 0, 2: 0}; mx = {1: 0, 2: 0}; total = {1: 0, 2: 0}; more = fewer = same = 0
        perms = list(itertools.permutations(range(n))); sides = list(itertools.product(perms, repeat=n))
        R = {p: ranks(p) for p in sides}
        BA = {k: {p: [side_bits(n, k, R[p], m, 0) for m in M[k]] for p in sides} for k in (1, 2)}
        BB = {k: {p: [side_bits(n, k, R[p], m, 1) for m in M[k]] for p in sides} for k in (1, 2)}
        inj = injections(n)
        O2A = {p: [one_to_one_side(n, R[p], d) for d in inj] for p in sides}
        O2B = {p: [one_to_one_side(n, R[p], {b: a for a, b in d.items()}) for d in inj] for p in sides}
        T = [sum(1 << (a * n + b) for a in range(n) for b in range(n) if x >> (b * n + a) & 1) for x in range(1 << (n * n))]
        for pa, pb in profiles(n):
            validate(n, pa, pb); ra, rb = R[pa], R[pb]; prof += 1
            S = {}
            for k in (1, 2):
                S[k] = [m for m, x, y in zip(M[k], BA[k][pa], BB[k][pb]) if not x & y]; states += len(M[k])
                if n <= 2: assert S[k] == [m for m in M[k] if stable(n, k, ra, rb, m)], "fast and direct checks disagree"
                da = deferred_acceptance(n, k, ra, rb)
                assert S[k], "no stable matching found by brute force"
                assert da in S[k], "deferred acceptance gave an unstable matching"
                # pursuit rule: in the matching deferred acceptance keeps, no member has a pair it would join
                # that the other side would also join (each a and each b checked; this is stability, per member)
                assert not blocking_pairs(n, k, ra, rb, da), "the pursuit rule left a joinable blocking pair"
                total[k] += len(S[k]); mx[k] = max(mx[k], len(S[k])); uniq[k] += len(S[k]) == 1
            # mirror: capacity model at k=1 equals the one-to-one model, as sets of matchings
            o2o = {frozenset(d.items()) for d, x, y in zip(inj, O2A[pa], O2B[pb]) if not x & T[y]}
            if n <= 2: assert o2o == one_to_one_stable(n, ra, rb), "one-to-one fast and direct disagree"
            assert set(S[1]) == o2o, "k=1 capacity model differs from one-to-one"
            # A-proposing deferred acceptance at k=1 gives each a its best partner over all stable matchings
            da1 = dict(deferred_acceptance(n, 1, ra, rb))
            for m in S[1]:
                for a, b in m: assert ra[a][da1[a]] <= ra[a][b], "deferred acceptance not A-optimal at k=1"
            c1, c2 = len(S[1]), len(S[2])
            more += c2 > c1; fewer += c2 < c1; same += c2 == c1
        out[n] = {"profiles": prof, "matchings_k1": len(M[1]), "matchings_k2": len(M[2]),
                  "unique_k1": uniq[1], "unique_k2": uniq[2], "max_k1": mx[1], "max_k2": mx[2],
                  "stable_total_k1": total[1], "stable_total_k2": total[2],
                  "k2_more": more, "k2_fewer": fewer, "k2_same": same}
        print(f"n={n} profiles={prof} matchings k1={len(M[1])} k2={len(M[2])} | unique stable: k1={uniq[1]} k2={uniq[2]}"
              f" | max stable: k1={mx[1]} k2={mx[2]} | total stable: k1={total[1]} k2={total[2]}"
              f" | k2 vs k1 count: more={more} fewer={fewer} same={same}")
    # capacity k >= n: every member can hold the whole other side; the complete matching is the only stable one
    for n in range(1, 3):
        full = frozenset((a, b) for a in range(n) for b in range(n))
        for pa, pb in profiles(n):
            ra, rb = ranks(pa), ranks(pb)
            assert [m for m in matchings(n, 2) if stable(n, 2, ra, rb, m)] == [full]
    print("capacity k >= n (n=1,2, k=2): the complete matching is the only stable one, on every profile")
    # refusals: signed graph of matched pairs (+) and refusals (-), every matching and every refusal set, n <= 3
    Q = load_quadrants(); sig = {}
    for n in range(1, NMAX + 1):
        cross = [(a, b) for a in range(n) for b in range(n)]
        for k in (1, 2):
            tot = bal = 0
            for m in matchings(n, k):
                rest = [p for p in cross if p not in m]
                for r in range(len(rest) + 1):
                    for ref in itertools.combinations(rest, r):
                        lab = signed(n, m, ref); tot += 1; states += 1
                        b = Q.balanced_parity(2 * n, lab)
                        if 2 * n <= 4: assert b == Q.balanced_brute(2 * n, lab), "parity and brute force disagree"
                        bal += b
            sig[f"n{n}_k{k}"] = {"signed graphs": tot, "balanced": bal}
            print(f"refusals n={n} k={k}: signed graphs={tot} balanced={bal}" + (" (parity = brute force)" if 2 * n <= 4 else ""))
    # three one-to-one couples who each refuse every member of the other couples: not balanced (three camps needed)
    m3 = frozenset((i, i) for i in range(3)); ref3 = [(a, b) for a in range(3) for b in range(3) if a != b]
    assert not Q.balanced_parity(6, signed(3, m3, ref3))
    print("three couples, all cross refusals: not balanced (they need three camps, balance allows two)")
    ns = range(1, NMAX + 1)
    fp = [
        {"name": "preference profiles, n=1..3", "seq": [out[n]["profiles"] for n in ns]},
        {"name": "one-to-one matchings (capacity 1), n=1..3", "seq": [out[n]["matchings_k1"] for n in ns]},
        {"name": "capacity-2 matchings, n=1..3", "seq": [out[n]["matchings_k2"] for n in ns]},
        {"name": "profiles with a unique stable matching k=1, n=1..3", "seq": [out[n]["unique_k1"] for n in ns]},
        {"name": "profiles with a unique stable matching k=2, n=1..3", "seq": [out[n]["unique_k2"] for n in ns]},
        {"name": "most stable matchings on one profile k=1, n=1..3", "seq": [out[n]["max_k1"] for n in ns]},
        {"name": "most stable matchings on one profile k=2, n=1..3", "seq": [out[n]["max_k2"] for n in ns]},
    ]
    for e in fp: e["runner"] = "python3 -I culture/love/check.py"
    with open(os.path.join(HERE, "fingerprints.json"), "w", encoding="utf-8") as f:
        f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2),
                      "stable": {str(n): {k: out[n][k] for k in ("unique_k1", "max_k1", "unique_k2", "max_k2")} for n in out},
                      "refusals": sig}))

if __name__ == "__main__":
    main()
