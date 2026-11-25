"""Car Seat Headrest level: the checks. Standard library only.

1. Dated records (years confirmed by web search, 2026-11-25; search result only):
   1 (2010), 2 (2010), Twin Fantasy original, later called Mirror to Mirror (2011),
   Twin Fantasy (Face to Face) (2018). Other works have no confirmed year and are left out.
   Fact checked here: listed in release order the years never decrease, and the two
   versions of Twin Fantasy are 7 years apart.
2. A check run both ways (reading of "tybee island horse ghosts"): the verdict
   "every escape route computes OR(people, ground)" over all 4 inputs is the same
   when the inputs are enumerated forward and in reverse, and a refuter searching
   for a counterexample finds none exactly when the prover says TRUE.
   This is checked-finite only in a trivial sense: route and spec are the same
   function here, and order cannot change all() over 4 inputs. It holds by
   construction and tests no real prover/refuter pair from asteroid. The gap stays open.
   That a drone means this is a reading.
"""
from itertools import product

ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name)
    ok = ok and cond

records = [("1", 2010), ("2", 2010), ("Twin Fantasy (Mirror to Mirror)", 2011),
           ("Twin Fantasy (Face to Face)", 2018)]
years = [y for _, y in records]
want("dated records form a time-ordered list (years never decrease)",
     all(a <= b for a, b in zip(years, years[1:])))
want("Twin Fantasy: the two versions are 7 years apart", 2018 - 2011 == 7)

def route(people, ground):          # an escape route, as in gravity.ath
    return people or ground
def spec(people, ground):
    return people or ground
inputs = list(product([False, True], repeat=2))
forward = all(route(*x) == spec(*x) for x in inputs)
backward = all(route(*x) == spec(*x) for x in reversed(inputs))
refuter = [x for x in reversed(inputs) if route(*x) != spec(*x)]
want("prover verdict is the same forward and reversed", forward == backward)
want("refuter finds no counterexample exactly when prover says TRUE", forward == (refuter == []))
# a broken route: both directions must agree it fails
bad = lambda p, g: p
fb = all(bad(*x) == spec(*x) for x in inputs)
bb = all(bad(*x) == spec(*x) for x in reversed(inputs))
want("a broken route fails in both directions", fb is False and bb is False)
print("PASS" if ok else "FAIL")
raise SystemExit(0 if ok else 1)
