"""History-independent claims in the measure toy. Standard library only.

Transport rule: a claim crosses to another branch or ordering only if its hypotheses hold there.
A claim that holds in every ordering is the kind that crosses.

1. Exhaustive, n = 1..7: over every ordering (permutation) of n universes and every
   property P (a subset), the frequency of P among the first N is the same in all
   orderings for every cutoff N iff P holds everywhere or nowhere.
   At the full cutoff N = n every property has one frequency in all orderings.
2. Example on the toy: "n*n mod 4 is 0 or 1" holds for every universe, so its frequency
   is 1 at the cutoffs N = 1, 2, 3, 10, 999, 3000 in ordering A and ordering B
   (and so at every cutoff, since it holds for each element). Evenness is not: 1/2 vs 1/3.
All checked-finite.
"""
from fractions import Fraction
from itertools import permutations

ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name)
    ok = ok and cond

good = True
for n in range(1, 8):
    perms = list(permutations(range(n)))
    for mask in range(1 << n):
        prof = set()
        for p in perms:
            c, row = 0, []
            for x in p:
                c += (mask >> x) & 1
                row.append(c)
            prof.add(tuple(row))
        invariant = len(prof) == 1
        constant = mask in (0, (1 << n) - 1)
        full = {r[-1] for r in prof}
        good &= (invariant == constant) and len(full) == 1
want("n <= 7: frequency is ordering-independent at every cutoff iff the property is constant; full cutoff always agrees", good)

def orderB(N):
    out, k = [], 1
    while len(out) < N:
        out += [4 * k - 3, 4 * k - 1, 2 * k]; k += 1
    return out[:N]
A = list(range(1, 3001)); B = orderB(3000)
sq = lambda m: (m * m) % 4 in (0, 1)
want("n*n mod 4 in {0,1}: frequency 1 at cutoffs 1, 2, 3, 10, 999, 3000 in both orderings",
     all(all(sq(m) for m in A[:N]) and all(sq(m) for m in B[:N]) for N in (1, 2, 3, 10, 999, 3000)) and all(map(sq, A + B)))
want("evenness is ordering-dependent: 1/2 vs 1/3 at N = 3000",
     Fraction(sum(m % 2 == 0 for m in A), 3000) == Fraction(1, 2) and Fraction(sum(m % 2 == 0 for m in B), 3000) == Fraction(1, 3))
print("PASS" if ok else "FAIL")
raise SystemExit(0 if ok else 1)
