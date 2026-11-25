"""Tests for matching.py. Run: python3 research/tools/matching/test_matching.py"""
import os, random, sys
from itertools import combinations, combinations_with_replacement, product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from matching import bmatch, simple_bmatch, frac_feasible_half, hall_check, max_matched


def capf(c):
    return (lambda a: 1) if c is None else (lambda a: c) if isinstance(c, int) else (lambda a: c.get(a, 1))


def valid_assignment(T, d, c, A, simple):
    cap = capf(c); use = {}
    assert len(A) == len(T)
    for i, row in enumerate(A):
        assert len(row) == d[i], (row, d[i])
        assert all(a in set(T[i]) for a in row)
        if simple: assert len(set(row)) == len(row), row
        for a in row: use[a] = use.get(a, 0) + 1
    assert all(k <= cap(a) for a, k in use.items()), use
    return True


def valid_violator(T, d, c, s, simple):
    cap = capf(c)
    assert s and all(0 <= i < len(T) for i in s)
    cnt = {}
    for i in s:
        for a in set(T[i]): cnt[a] = cnt.get(a, 0) + 1
    rhs = sum(min(cap(a), k) if simple else cap(a) for a, k in cnt.items())
    assert sum(d[i] for i in s) > rhs, (s, rhs)
    return True


def exists_brute(T, d, c, simple):
    """Independent of Hall: exhaustive search over per-vertex choices."""
    cap = capf(c)
    pick = combinations if simple else combinations_with_replacement
    def rec(i, left):
        if i == len(T): return True
        for ch in pick(sorted(set(T[i])), d[i]):
            l2 = dict(left); ok = True
            for a in ch:
                l2[a] = l2.get(a, cap(a)) - 1
                if l2[a] < 0: ok = False; break
            if ok and rec(i + 1, l2): return True
        return False
    return rec(0, {})


def old_bmatch(Ds, demand):
    """The augmenting-path copy from work/notes951/scripts/w8b/rstar.py:19 (reference)."""
    slots = [(i, k) for i in range(len(Ds)) for k in range(demand[i])]; owner = {}
    def aug(slot, seen):
        for g in Ds[slot[0]]:
            if g in seen: continue
            seen.add(g)
            if g not in owner or aug(owner[g], seen): owner[g] = slot; return True
        return False
    return sum(1 for sl in slots if aug(sl, set()))


def rand_inst(rng):
    n = rng.randint(1, 5); m = rng.randint(1, 6)
    T = [set(rng.sample(range(m), rng.randint(0, m))) for _ in range(n)]
    d = [rng.randint(0, 3) for _ in range(n)]
    mode = rng.randrange(3)
    c = None if mode == 0 else rng.randint(1, 3) if mode == 1 else {a: rng.randint(0, 3) for a in range(m)}
    return T, d, c


def test_counterexample():
    T = [{'a', 'b'}, {'a', 'b'}, {'a', 'c'}]; d = [2, 2, 2]
    assert hall_check(T, d, 2, simple=False) is None          # plain Hall holds for every s
    A, s = bmatch(T, d, 2)
    assert s is None and valid_assignment(T, d, 2, A, False)  # non-simple matching exists
    A, s = simple_bmatch(T, d, 2)
    assert A is None and valid_violator(T, d, 2, s, True)      # ... but no simple one
    assert s == {0, 1, 2} == hall_check(T, d, 2, simple=True)
    assert not exists_brute(T, d, 2, True) and exists_brute(T, d, 2, False)


def test_basic():
    assert bmatch([], []) == ([], None) and simple_bmatch([], []) == ([], None)
    assert bmatch([[]], [0]) == ([[]], None)
    assert bmatch([[]], [1]) == (None, {0})
    assert bmatch([[7]], [3], {7: 3}) == ([[7, 7, 7]], None)
    assert simple_bmatch([[7]], [3], {7: 3}) == (None, {0})
    assert bmatch([['x', 'x', 'y']], [2])[0] in ([['x', 'y']], [['y', 'x']])   # duplicates in T ignored
    A, s = bmatch([[1, 2], [2, 3], [1, 3]], [1, 1, 1])
    assert s is None and sorted(a for r in A for a in r) == [1, 2, 3]
    assert bmatch([[1, 2], [1, 2], [1, 2]], [1, 1, 1]) == (None, {0, 1, 2})
    # failing instance where the violator is a proper subset
    A, s = bmatch([[1], [1], [2, 3]], [1, 1, 1])
    assert A is None and s == {0, 1}


def test_random(N=3000, seed=951):
    rng = random.Random(seed); stats = {}
    for _ in range(N):
        T, d, c = rand_inst(rng)
        for simple, f in ((False, bmatch), (True, simple_bmatch)):
            A, s = f(T, d, c)
            hc = hall_check(T, d, c, simple=simple)
            assert (A is None) == (hc is not None), (T, d, c, simple, A, hc)
            assert (A is None) != (s is None)
            if A is None: valid_violator(T, d, c, s, simple)
            else: valid_assignment(T, d, c, A, simple)
            key = ('simple' if simple else 'bmatch', 'ok' if A is not None else 'fail')
            stats[key] = stats.get(key, 0) + 1
            if sum(d) <= 7:                                   # independent exhaustive search
                assert exists_brute(T, d, c, simple) == (A is not None), (T, d, c, simple)
                stats['exhaustive'] = stats.get('exhaustive', 0) + 1
        if c is None:                                         # unit capacities: all notions agree
            m = old_bmatch([sorted(t) for t in T], d)
            assert max_matched(T, d) == max_matched(T, d, simple=False) == m
            assert (bmatch(T, d)[0] is not None) == (m == sum(d)) == (simple_bmatch(T, d)[0] is not None)
    return stats


def half_brute(T, d):
    """Exhaustive: every system (w,j) picks d[w] distinct gates, each gate used <= 2 times."""
    Ts = [set(D) for pair in T for D in pair]; ds = [d[w] for w in range(len(T)) for _ in (0, 1)]
    return exists_brute(Ts, ds, 2, True)


def test_half(N=600, seed=9):
    rng = random.Random(seed); nok = 0
    for _ in range(N):
        n = rng.randint(1, 3); m = rng.randint(1, 5)
        T = [(set(rng.sample(range(m), rng.randint(0, m))), set(rng.sample(range(m), rng.randint(0, m)))) for _ in range(n)]
        d = [rng.randint(0, 2) for _ in range(n)]
        ok, s = frac_feasible_half(T, d)
        assert ok == half_brute(T, d), (T, d)
        nok += ok
        if ok: assert s is None
        else:
            cnt = {}
            for w, j in s:
                for g in T[w][j]: cnt[g] = cnt.get(g, 0) + 1
            assert sum(d[w] for w, j in s) > sum(min(2, k) for k in cnt.values())
    # one set, same single gate in both worlds: load 1/2 + 1/2 = 1, feasible
    assert frac_feasible_half([([0], [0])], [1]) == (True, None)
    # two such sets on the same gate: load 2, infeasible, violator = all four systems
    assert frac_feasible_half([([0], [0]), ([0], [0])], [1, 1]) == (False, {(0, 0), (0, 1), (1, 0), (1, 1)})
    # mixing two worlds helps: each world alone fails Hall, the 1/2-1/2 mix has load 1
    Tc = [[0], [0]]; Tr = [[1], [1]]
    assert bmatch(Tc, [1, 1])[0] is None and bmatch(Tr, [1, 1])[0] is None
    assert frac_feasible_half(list(zip(Tc, Tr)), [1, 1])[0] is True
    return nok, N


def test_larger(seed=3):
    """Bigger instances: certificate/assignment validity only (no brute force)."""
    rng = random.Random(seed)
    for _ in range(200):
        n = rng.randint(10, 40); m = rng.randint(10, 60)
        T = [rng.sample(range(m), rng.randint(1, min(m, 8))) for _ in range(n)]
        d = [rng.randint(0, 4) for _ in range(n)]
        c = {a: rng.randint(0, 4) for a in range(m)}
        for simple, f in ((False, bmatch), (True, simple_bmatch)):
            A, s = f(T, d, c)
            if A is None: valid_violator(T, d, c, s, simple)
            else: valid_assignment(T, d, c, A, simple)
    # long augmenting chain (deep recursion in the old copies): path 0-1-2-...-n
    n = 3000
    A, s = bmatch([[i, i + 1] for i in range(n)], [1] * n)
    assert s is None and len({r[0] for r in A}) == n


if __name__ == '__main__':
    test_counterexample(); print('counterexample: ok')
    test_basic(); print('basic: ok')
    st = test_random(); print('random cross-check (3000 instances x 2 matchers):', sorted(st.items(), key=str))
    print('frac_feasible_half vs exhaustive: %d feasible of %d' % test_half())
    test_larger(); print('larger instances + 3000-long chain: ok')
    print('ALL TESTS PASSED')
