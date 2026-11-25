#!/usr/bin/env python3
"""The smallest love: a household as a check, not a template.

A household is a set of people and their bonds (a bond is mutual: a symmetric relation, no self-bonds).
The check asks one thing, Beauvoir's condition read on bonds: no member is left with no one (every member
can go on to someone). It does NOT ask for a shape: two parents, one parent, two mothers, a chosen family
and a nuclear family all pass if no one is alone, and none passes if someone is.
  1. Exhaustive: every labelled household of 1..6 people; the ones that pass are exactly the graphs with no
     isolated vertex: 0, 1, 4, 41, 768, 27449 (an inclusion-exclusion formula, asserted against the count).
  2. Hand-matched households (Addison: "manually match as much as possible"), each written out by hand:
     the check's verdict on each is asserted.
"Environmental since birth" (Bronfenbrenner's microsystem; culture/social/ecology.py): the household is
the first system a person is in; the reading is analogy. Run: python3 -I culture/love/family.py
"""
import itertools, json, math, time

def passes(n, bonds):
    seen = set()
    for a, b in bonds: seen.add(a); seen.add(b)
    return n > 0 and len(seen) == n

def formula(n):   # graphs on n labelled vertices with no isolated vertex
    return sum((-1) ** k * math.comb(n, k) * 2 ** math.comb(n - k, 2) for k in range(n + 1))

def main():
    t0 = time.time(); states = 0; counts = []
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2)); c = 0
        for mask in range(1 << len(pairs)):
            states += 1
            c += passes(n, [p for i, p in enumerate(pairs) if mask >> i & 1])
        assert c == formula(n), "count matches inclusion-exclusion"
        counts.append(c)
    assert counts == [0, 1, 4, 41, 768, 27449]
    print("households of 1..6 where no one is alone:", counts)
    # hand-matched households: (description, people, bonds, expected verdict)
    hand = [
        ("two parents and a child", 3, [(0, 1), (0, 2), (1, 2)], True),
        ("one parent and two children", 3, [(0, 1), (0, 2)], True),
        ("two mothers and a child", 3, [(0, 2), (1, 2), (0, 1)], True),
        ("a chosen family of four friends in a ring", 4, [(0, 1), (1, 2), (2, 3), (3, 0)], True),
        ("a nuclear family with one member cut off", 4, [(0, 1), (0, 2), (1, 2)], False),
        ("a person alone", 1, [], False),
    ]
    for desc, n, bonds, want in hand:
        states += 1
        got = passes(n, bonds); assert got == want, desc
        print(f"  {desc}: {'no one alone' if got else 'someone is alone'}")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "no_one_alone": counts}))

if __name__ == "__main__":
    main()
