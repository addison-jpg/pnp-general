#!/usr/bin/env python3
"""Roommates: stable matching with the two sides removed. Exhaustive for n = 2, 3, 4 people.

n people. Each strictly ranks all n-1 others (a profile). A matching pairs people; some may be unmatched.
A pair blocks a matching when each of the two prefers the other to their current partner, where being
unmatched is worse than any partner (everyone ranks everyone). A matching is stable when nothing blocks it.
Two sides are the special case where everyone on one side ranks the other side first: the love model.
Checked on every profile (nothing sampled): n=2 (1 profile), n=3 (8), n=4 (1296).
n=5 has 24^5 = 7.96e6 profiles and n=6 has 120^6 = 2.99e12: neither is run here (n=6 is far over 20 s).
Facts asserted: the two-sided model always has a stable matching (the functions of culture/love/check.py,
imported, on all 46656 profiles at n=3 sides, deferred acceptance); the roommates model does not.
Gale and Shapley 1962 gave a roommates instance with no stable matching; Irving 1985 gave an algorithm that
finds one or says there is none (both cited from memory). This models stated rankings, not people.
Run: python3 -I culture/queer/roommates.py   (last line is JSON)
"""
import importlib.util, itertools, json, os, time

HERE = os.path.dirname(os.path.abspath(__file__))

def matchings(n):
    # every set of disjoint pairs on 0..n-1 (unmatched allowed)
    def rec(free):
        if not free: yield (); return
        a, rest = free[0], free[1:]
        yield from rec(rest)                       # a unmatched
        for i, b in enumerate(rest):
            for m in rec(rest[:i] + rest[i + 1:]): yield ((a, b),) + m
    return [frozenset(m) for m in rec(tuple(range(n)))]

def blocking(n, rank, m):
    mate = {}
    for a, b in m: mate[a] = b; mate[b] = a
    def better(x, y):   # does x prefer y to x's current state?
        return x not in mate or rank[x][y] < rank[x][mate[x]]
    return [(a, b) for a in range(n) for b in range(a + 1, n)
            if mate.get(a) != b and better(a, b) and better(b, a)]

def stable_set(n, rank, M): return [m for m in M if not blocking(n, rank, m)]

def profiles(n):
    perms = [list(p) for p in itertools.permutations(range(n - 1))]
    for combo in itertools.product(perms, repeat=n):
        # combo[i] ranks the others of i, best first
        yield [[j for j in range(n) if j != i] for i in range(n)], combo

def rank_of(n, combo):
    prefs = [[ [j for j in range(n) if j != i][k] for k in combo[i]] for i in range(n)]
    rank = []
    for i, p in enumerate(prefs):
        r = [0] * n
        for pos, j in enumerate(p): r[j] = pos
        rank.append(r)
    return prefs, rank

def load_love():
    spec = importlib.util.spec_from_file_location("love_check", os.path.join(HERE, "..", "love", "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def main():
    t0 = time.time(); states = 0; out = {}; smallest = None
    for n in (2, 3, 4):
        M = matchings(n); none = uniq = 0; mx = 0; tot = 0; count = 0
        for _, combo in profiles(n):
            prefs, rank = rank_of(n, combo); count += 1; states += len(M)
            S = stable_set(n, rank, M); c = len(S)
            if c == 0:
                none += 1
                if smallest is None: smallest = (n, prefs)
            uniq += c == 1; mx = max(mx, c); tot += c
        out[n] = {"profiles": count, "matchings": len(M), "none": none, "unique": uniq, "max": mx, "total": tot}
        print(f"n={n}: profiles={count} matchings={len(M)} | no stable matching={none} | unique={uniq} | most on one profile={mx} | total stable={tot}")
    assert out[2]["none"] == 0, "n=2 always has the pair"
    assert out[3]["none"] > 0 and out[4]["none"] > 0, "roommates can fail"
    n, prefs = smallest
    print(f"smallest profile with no stable matching (n={n}, first found; each row best first): " + "; ".join(f"{i}:{p}" for i, p in enumerate(prefs)))
    r = [[0] * n for _ in range(n)]
    for i, p in enumerate(prefs):
        for pos, j in enumerate(p): r[i][j] = pos
    for m in matchings(n):
        b = blocking(n, r, m); assert b, "the smallest profile has a stable matching"
        print(f"  matching {sorted(m) or 'nobody'}: blocked by {b[0]}")
    # two sides: stable matching always exists (love/check.py functions, imported); n=3 sides, every profile
    L = load_love(); per = list(itertools.permutations(range(3))); sides = list(itertools.product(per, repeat=3)); seen = 0
    R = {p: L.ranks(p) for p in sides}
    for pa in sides:
        for pb in sides:
            ra, rb = R[pa], R[pb]; da = L.deferred_acceptance(3, 1, ra, rb)
            assert L.stable(3, 1, ra, rb, da), "two-sided model: deferred acceptance unstable"; seen += 1
    print(f"two sides (love/check.py functions): a stable matching on all {seen} profiles at n=3 per side; roommates: fails on {out[3]['none']} of {out[3]['profiles']} (n=3), {out[4]['none']} of {out[4]['profiles']} (n=4)")
    print("PASS")
    print(json.dumps({"states": states + seen, "seconds": round(time.time() - t0, 2),
                      "no_stable": [out[n]["none"] for n in out], "profiles": [out[n]["profiles"] for n in out],
                      "unique": [out[n]["unique"] for n in out], "most": [out[n]["max"] for n in out]}))

if __name__ == "__main__":
    main()
