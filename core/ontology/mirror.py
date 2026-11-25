#!/usr/bin/env python3
"""The Beauvoir mirror, as a finite check. Standard library only.

A mirror on worlds 0..n-1 is a relation R that is
  (a) reciprocal: x R y implies y R x (I am seen by whom I see), and
  (b) successor-serial, the condition checked in core/ontology/beauvoir.py: every world reached from anywhere
      can itself go on (it reaches some world).
Checked on every relation on 1..3 worlds (2^9 = 512 at n = 3), by two encodings that must agree:
  1. the definition above, on the set of pairs;
  2. the matrix form: R equals its transpose, and every row has a 1 (a reached world can go on).
Counts are printed: how many relations are mirrors. The empty relation counts (vacuously: nothing is reached).
Note (found by the attack subagent): for a reciprocal relation the second condition always holds, since x R y gives
y R x, so y reaches x and can go on. So the mirror count equals the symmetric count; the serial clause adds nothing. Reading (analogy): a mirror is the only kind of
relation in which being reached and being able to go on are the same condition.
Run: python3 -I core/ontology/mirror.py   (last line is JSON)
"""
import itertools, json, time

def is_mirror_pairs(n, R):
    reciprocal = all((y, x) in R for x, y in R)
    reached = {y for _, y in R}
    serial = all(any((w, z) in R for z in range(n)) for w in reached)   # every reached world can go on
    return reciprocal and serial

def is_mirror_matrix(n, R):
    M = [[1 if (i, j) in R else 0 for j in range(n)] for i in range(n)]
    transpose = all(M[i][j] == M[j][i] for i in range(n) for j in range(n))
    rows_ok = all(any(M[i]) for i in range(n) if any(M[k][i] for k in range(n)))
    return transpose and rows_ok

def main():
    t0 = time.time(); states = 0; counts = {}
    for n in (1, 2, 3):
        pairs = [(i, j) for i in range(n) for j in range(n)]; c = 0
        for bits in range(1 << len(pairs)):
            R = {p for k, p in enumerate(pairs) if bits >> k & 1}
            states += 1
            a, b = is_mirror_pairs(n, R), is_mirror_matrix(n, R)
            assert a == b, f"encodings disagree on n={n}, R={sorted(R)}"
            c += a
        counts[n] = c
    print("mirrors on 1, 2, 3 worlds (reciprocal and every reached world can go on):", counts)
    # the empty relation is vacuously a mirror (no world is reached, so none needs to go on); it is counted
    assert counts == {1: 2, 2: 8, 3: 64}, counts
    print("the two encodings agree on every relation checked")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 3), "mirrors": counts}))

if __name__ == "__main__":
    main()
