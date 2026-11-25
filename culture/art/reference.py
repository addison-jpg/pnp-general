#!/usr/bin/env python3
"""'Speaking to me': a broadcast cannot single out a listener; only a lateral link can. Exhaustive.

A broadcast is a hub joined to n listeners (the star of philosophy/cone.py: the cone over n points with
no lateral links, loaded from cone.py itself). A message pattern gives each listener a value. It is
'symmetric' when every symmetry of the graph (every automorphism) leaves it unchanged.
  1. On the star with n = 2..6 listeners, every automorphism fixes the hub and the automorphisms move any
     listener to any other; so every symmetric pattern (k = 1..3 values) is constant: k of k^n.
  2. Add one lateral link between two listeners: now the two linked listeners can receive a different value
     from the rest, symmetrically (for n >= 3: k^2 symmetric patterns, more than k).
  3. And cone.py's fact holds on the same star: the hub is critical (removing it disconnects everyone).
So a broadcast addresses everyone alike; being singled out needs a real link. Reading (analogy): taking a
song 'out of context' as speaking to me reads a symmetric signal as an addressed one. Run: python3 -I culture/art/reference.py
"""
import importlib.util, itertools, json, os, time
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
spec = importlib.util.spec_from_file_location("cone", os.path.join(ROOT, "philosophy", "cone.py"))
cone = importlib.util.module_from_spec(spec); spec.loader.exec_module(cone)

def autos(V, E):
    es = {frozenset(e) for e in E}
    return [p for p in itertools.permutations(range(V)) if {frozenset((p[a], p[b])) for a, b in E} == es]

def symmetric_patterns(n, E, k):
    A = autos(n + 1, E); count = 0
    for pat in itertools.product(range(k), repeat=n):
        if all(pat[p[i]] == pat[i] for p in A for i in range(n)): count += 1
    return count, A

def main():
    t0 = time.time(); states = 0; rows = []
    for n in range(2, 7):
        star = [(v, n) for v in range(n)]                       # hub n, listeners 0..n-1, no lateral link
        assert not cone.connected_without(n + 1, star, drop_vertex=n), "the hub is critical (cone.py fact 1)"
        for k in (1, 2, 3):
            c, A = symmetric_patterns(n, star, k); states += len(A) * k ** n
            assert all(p[n] == n for p in A) and c == k, "a broadcast cannot single anyone out"
        if n >= 3:
            linked = star + [(0, 1)]
            c2, _ = symmetric_patterns(n, linked, 2); states += 2 ** n
            assert c2 == 4 and c2 > 2, "one lateral link lets two listeners differ"
        rows.append(n)
    print("1. on a broadcast star with 2..6 listeners, every symmetric message pattern is constant (k of k^n)")
    print("2. one lateral link between two listeners allows 4 symmetric patterns on 2 values, not 2")
    print("3. on every such star the hub is critical (philosophy/cone.py, loaded, fact 1)")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "listeners": rows}))

if __name__ == "__main__":
    main()
