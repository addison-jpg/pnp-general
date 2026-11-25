#!/usr/bin/env python3
"""Frank's three illness narratives as exact types of a finite story. Standard library only.

Arthur Frank, The Wounded Storyteller (1995), names restitution, chaos and quest narratives (cited from memory).
Here a story is a sequence of states over S = {W, I, C} (well, ill, changed), one state per time step, length 1..8.
The individuals are constructed: every story is synthetic. No real person's data is used.
  departure    the first step whose state differs from the first state. No departure: the story is "steady".
  restitution  it departs and ends in the state it began in (back to well).
  quest        it departs and ends in a state never held before the departure (transformed, not restored).
  chaos        no state persists two steps running, and the story has at least 3 steps (it never settles).
Restitution and quest split every departing story. Chaos overlaps both. A disjoint reading gives chaos priority
(Frank: chaos is the story that cannot yet be told as either; cited from memory).
Checked (checked-finite, all 9840 stories of length 1..8, two routes): each count equals its closed form:
  restitution 3^(n-1) - 3, quest 2*3^(n-1), chaos 3*2^(n-1), chaos and restitution 2^(n-1) + 2(-1)^(n-1).
Propagating up: a universe is a multiset of stories. Its type counts are the sum of its members' counts (checked on
every 2-multiset of stories of length <= 3). But the type of a joined life (story s, then story t) is NOT a function
of the two types: on every pair of stories of length <= 4, all 16 type pairs occur and none fixes the joined type.
Readings (Kleinman 1988, Charon 2006, Frank 1995; all cited from memory) are analogy, in culture/narrative/DIARIES.md.
Run: python3 -I culture/narrative/narrative.py      (last line is JSON)
"""
import itertools, json, time
S = "WIC"
def types(s):
    t = set()
    dep = next((i for i, x in enumerate(s) if x != s[0]), None)
    if dep is None: t.add("steady")
    elif s[-1] == s[0]: t.add("restitution")
    else: t.add("quest")                                    # every state before dep is s[0], so s[-1] was never held
    if len(s) >= 3 and all(a != b for a, b in zip(s, s[1:])): t.add("chaos")
    return t
def disjoint(s): t = types(s); return "chaos" if "chaos" in t else t.pop()
def stories(n): return ["".join(p) for p in itertools.product(S, repeat=n)]

t0 = time.time(); states = 0; table = {}
for n in range(1, 9):
    c = {k: 0 for k in ("steady", "restitution", "quest", "chaos", "chaos&restitution", "chaos&quest")}
    for s in stories(n):
        states += 1; t = types(s)
        for k in t: c[k] += 1
        c["chaos&restitution"] += {"chaos", "restitution"} <= t; c["chaos&quest"] += {"chaos", "quest"} <= t
    if n >= 2: assert (c["restitution"], c["quest"]) == (3 ** (n - 1) - 3, 2 * 3 ** (n - 1)), n
    if n >= 3: assert c["chaos"] == 3 * 2 ** (n - 1) and c["chaos&restitution"] == 2 ** (n - 1) + 2 * (-1) ** (n - 1), n
    assert c["steady"] + c["restitution"] + c["quest"] == 3 ** n
    table[n] = c; print(f"n={n}: " + ", ".join(f"{k} {v}" for k, v in c.items()))
# propagating up 1: a universe's counts are additive over its members
small = [s for n in (1, 2, 3) for s in stories(n)]
for a, b in itertools.combinations_with_replacement(small, 2):
    states += 1; u = [a, b]
    assert {k: sum(disjoint(s) == k for s in u) for k in ("steady", "restitution", "quest", "chaos")} == \
           {k: (disjoint(a) == k) + (disjoint(b) == k) for k in ("steady", "restitution", "quest", "chaos")}
# propagating up 2: the type of a joined life is not determined by the parts' types
seen = {}
for a, b in itertools.product([s for n in range(1, 5) for s in stories(n)], repeat=2):
    states += 1; seen.setdefault((disjoint(a), disjoint(b)), set()).add(disjoint(a + b))
clash = sorted(k for k, v in seen.items() if len(v) > 1)
assert len(clash) == len(seen) == 16, (len(clash), len(seen))
print(f"universe: counts add over every 2-multiset of {len(small)} stories; a joined life's type is fixed by its parts' types for {len(seen) - len(clash)} of {len(seen)} type pairs")
total = {k: sum(table[n][k] for n in table) for k in table[1]}
print(f"all {sum(3 ** n for n in range(1, 9))} stories of length 1..8: " + ", ".join(f"{k} {v}" for k, v in total.items()))
print("PASS")
print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "length8": table[8], "total": total, "type_pairs_undetermined": len(clash)}))
