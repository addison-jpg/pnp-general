"""Referee checks for Lemma K (scaffold, work/notes951/lemmaK on branch scaffold-951).

Lemma K. For a correct circuit with exactly one NOT N = ~h for a linear system F = {S_w}
(|S_w| >= 2, pairwise |S_w ∩ S_j| <= 1), with U = the non-NOT gates that have at most one unit,
    s >= 1 + |U| + sum_{easy w} d_w + sum_{hard w} min(d_w, 2),     d_w = |S_w| - 1,
where w is hard when h(z_{S_w}) = 1. The proof uses the classes
    D_w = {g <= OR(S_w), >= 2 units},  P_w = {g >= OR(S_w), g != 1, g not >= OR(S_j) for j != w},
    Pi_w = D_w ∪ P_w.
This script checks every step separately, on any circuit (the lemma assumes no minimality):
  (a) the Pi_w are pairwise disjoint, (b) |Pi_w| >= min(d_w, 2), with the second member found the way
  the proof finds it (OR-top: an input of o_w; AND-top: a leaf of the AND expansion), (c) for easy w:
  every gate g with g(z_S) = 0 has g <= C1(g) <= OR(S), and the union-find run has >= d_w merging OR
  gates, all in D_w, (d) N is in no Pi_w, (e) U meets no Pi_w, and the final inequality.
  K2 (ii) is checked in the general form its proof needs: if x_v has exactly one reader r and v has
  degree >= 2, then r is not N and r has at most one unit, and different such points have different readers.

It imports tools/w951 (Circuit); run from the one-not/ directory:
    python3 work/notes951/lemmaK_referee/kcheck.py corpus DIR...     # JSON circuits
    python3 work/notes951/lemmaK_referee/kcheck.py random N SEED      # N random one-NOT circuits
"""
import glob
import json
import os
import random
import sys

sys.path.insert(0, 'tools')
from w951 import Circuit  # noqa: E402


def check(c):
    """Return (ok, info) for one circuit; ok is False at the first failed step."""
    n, s = c.n, len(c.gates)
    T, T1, full = c.tables(), c.tables(force=1), c.full
    nots = c.nots
    assert len(nots) == 1, 'Lemma K needs exactly one NOT'
    N = nots[0]
    h = T[c.h_wire]
    gates = range(n, n + s)
    sets = [tuple(S) for S in c.sets]
    O = [c.or_table(S) for S in sets]
    if any(T[o] != O[i] for i, o in enumerate(c.outs)):
        return False, 'not correct'

    def units(g):
        return {u for u in range(n) if T[g] >> (1 << u) & 1}

    def leq(a, b):
        return a & ~b & full == 0

    def z(S):
        return sum(1 << u for u in range(n) if u not in S)

    D = [{g for g in gates if leq(T[g], O[i]) and len(units(g)) >= 2} for i in range(len(sets))]
    P = [{g for g in gates if leq(O[i], T[g]) and T[g] != full
          and all(not leq(O[j], T[g]) for j in range(len(sets)) if j != i)} for i in range(len(sets))]
    Pi = [D[i] | P[i] for i in range(len(sets))]
    U = {g for g in gates if g != N and len(units(g)) <= 1}
    hard = [h >> z(S) & 1 for S in sets]
    # easy <=> h <= OR(S)
    for i in range(len(sets)):
        if (not hard[i]) != leq(h, O[i]):
            return False, 'easy != (h <= OR(S)) at set %d' % i
    # (a)
    for i in range(len(sets)):
        for j in range(i):
            if Pi[i] & Pi[j]:
                return False, '(a) Pi_%d meets Pi_%d' % (i, j)
    # (d), (e)
    if any(N in X for X in Pi):
        return False, '(d) N in a class'
    if any(U & X for X in Pi):
        return False, '(e) U meets a class'
    # (b), with the proof's witness
    for i, S in enumerate(sets):
        o = c.outs[i]
        if o not in Pi[i]:
            return False, '(b) o_w not in Pi_w'
        if len(S) < 3:
            continue
        g = c.gates[o - n]
        if g[0] == 'or':
            A = [a for a in g[1:] if len(units(a)) >= 2]
            if not A or not all(a >= n and a != N and a in D[i] and a != o for a in A):
                return False, '(b) OR-top witness fails at set %d' % i
        elif g[0] == 'and':
            leaves, stack = [], [o]
            while stack:
                w = stack.pop()
                if w >= n and c.gates[w - n][0] == 'and':
                    stack.extend(c.gates[w - n][1:])
                else:
                    leaves.append(w)
            rel = [w for w in leaves if T[w] != full]
            if any(w < n or w == N or not leq(O[i], T[w]) for w in rel):
                return False, '(b) AND-top leaf is an input, N or not >= OR(S) at set %d' % i
            if not any(w in P[i] for w in rel):
                return False, '(b) AND-top: no leaf in P_w at set %d' % i
        else:
            return False, '(b) o_w is the NOT'
        if len(Pi[i]) < 2:
            return False, '(b) |Pi_w| < 2 at set %d' % i
    # (c) Theorem E for easy sets
    for i, S in enumerate(sets):
        if hard[i]:
            continue
        zS = z(S)
        if not (T[N] >> zS & 1):
            return False, '(c) N(z_S) != 1 at easy set %d' % i
        zero = [g for g in range(n + s) if not (T[g] >> zS & 1)]
        for g in zero:
            if g >= n and not (leq(T[g], T1[g]) and leq(T1[g], O[i])):
                return False, '(c) g(z_S) = 0 but not g <= C1(g) <= OR(S): gate %d set %d' % (g, i)
        comp = {u: u for u in S}

        def find(u):
            while comp[u] != u:
                u = comp[u]
            return u
        merges = []
        for g in zero:
            if g < n or c.gates[g - n][0] != 'or':
                continue
            a, b = c.gates[g - n][1:]
            ua, ub = units(a) & set(S), units(b) & set(S)
            if ua and ub:
                ra, rb = find(min(ua)), find(min(ub))
                for blk in (ua, ub):          # invariant: each block lies in one component
                    if len({find(u) for u in blk}) != 1:
                        return False, '(c) union-find invariant fails at gate %d set %d' % (g, i)
                if ra != rb:
                    comp[ra] = rb
                    merges.append(g)
        if len(merges) < len(S) - 1 or not all(g in D[i] for g in merges):
            return False, '(c) union-find: %d merges for d_w = %d at set %d' % (len(merges), len(S) - 1, i)
        if len(D[i]) < len(S) - 1:
            return False, '(c) |D_w| < d_w at set %d' % i
    # K2 (ii), in the general form it needs: correctness, a single reader, degree >= 2, linearity.
    readers = {v: sorted({n + k for k, g in enumerate(c.gates) if v in g[1:]}) for v in range(n)}
    deg = {v: sum(v in S for S in sets) for v in range(n)}
    V1 = [v for v in range(n) if deg[v] >= 2 and len(readers[v]) == 1]
    for v in V1:
        r = readers[v][0]
        if r == N or r not in U:
            return False, 'K2(ii): reader %d of single-reader point %d is N or has >= 2 units' % (r, v)
    if len({readers[v][0] for v in V1}) != len(V1):
        return False, 'K2(ii): two single-reader points share their reader'
    lb = 1 + len(U) + sum((len(S) - 1) if not hard[i] else min(len(S) - 1, 2) for i, S in enumerate(sets))
    tot = 1 + len(U) + sum(map(len, Pi))
    if not (lb <= tot <= s):
        return False, 'final inequality: bound %d, 1+|U|+sum|Pi| %d, s %d' % (lb, tot, s)
    return True, {'s': s, 'lb': lb, 'tot': tot, 'hard3': sum(1 for i, S in enumerate(sets) if hard[i] and len(S) >= 3),
                  'easy3': sum(1 for i, S in enumerate(sets) if not hard[i] and len(S) >= 3), 'm': len(sets),
                  'V1': len(V1)}


def random_circuit(rng, n, s):
    """A random circuit with exactly one NOT; outputs: a random linear family among the OR functions it computes."""
    kN = rng.randrange(s)
    gates = []
    for k in range(s):
        W = n + k
        if k == kN:
            gates.append(('not', rng.randrange(W)))
        else:
            op = rng.choice(('or', 'or', 'and'))
            gates.append((op, rng.randrange(W), rng.randrange(W)))
    c = Circuit(n, gates)
    T, full = c.tables(), c.full
    cand = {}
    for w in range(n + s):
        S = tuple(u for u in range(n) if T[w] >> (1 << u) & 1)
        if len(S) >= 2 and T[w] == c.or_table(S) and S not in cand:
            cand[S] = w
    items = list(cand.items())
    rng.shuffle(items)
    chosen = []
    for S, w in items:
        if all(len(set(S) & set(S2)) <= 1 for S2, _ in chosen):
            chosen.append((S, w))
    if not chosen:
        return None
    return Circuit(n, gates, [S for S, _ in chosen], [w for _, w in chosen])


def main():
    mode = sys.argv[1]
    if mode == 'corpus':
        files = [f for d in sys.argv[2:] for f in sorted(glob.glob(os.path.join(d, '*.json')))]
        bad = 0
        for f in files:
            c = Circuit.from_dict(json.load(open(f)))
            if len(c.nots) != 1:
                print(os.path.basename(f), 'skip: %d NOTs' % len(c.nots))
                continue
            ok, info = check(c)
            bad += not ok
            print(os.path.basename(f), 'OK' if ok else 'FAIL', info)
        print('corpus: %d files, %d failures' % (len(files), bad))
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3])
        rng = random.Random(seed)
        stats = {'checked': 0, 'tight': 0, 'hard3': 0, 'easy3': 0, 'withV1': 0}
        for _ in range(N):
            n = rng.choice((3, 4, 5, 6))
            c = random_circuit(rng, n, rng.randrange(4, 16))
            if c is None:
                continue
            ok, info = check(c)
            if not ok:
                print('COUNTEREXAMPLE', info, json.dumps(c.to_dict()))
                return 1
            stats['checked'] += 1
            stats['tight'] += info['lb'] == info['s']
            stats['hard3'] += info['hard3'] > 0
            stats['easy3'] += info['easy3'] > 0
            stats['withV1'] += info['V1'] > 0
        print('random: no failure;', stats)
    return 0


if __name__ == '__main__':
    sys.exit(main())
