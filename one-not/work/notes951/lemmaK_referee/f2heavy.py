"""Referee tests for front A2's two F2-step lemmas (coord 12:54):
(F1)      v heavy (h(Q + e_v) = 1)  =>  every g in F2(Q ∪ v) has real g(Q + e_v) = 0.
(F2-desc) a real separating triple (g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1, u != u') at any wire descends through AND
          gates (to a child 0 at Z) to an OR gate with the same triple; NOT gates and inputs never separate. Hence every
          output o_w, u != u' in S_w, Z ⊇ Q avoiding S_w gives an F2(Q) gate, and every real merge gate lies in F2(Q).
Random correct one-NOT circuits (kcheck.random_circuit), n = 4-6, random Q. Also: F1 for LIGHT v on a named witness.
Run from one-not/:  python3 work/notes951/lemmaK_referee/f2heavy.py N SEED [witness.json]
"""
import json
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402
from w951 import Circuit  # noqa: E402


def f2(c, T, Qm):
    """F2(Q): OR gates with a real separating triple for an alive set, Z ⊇ Q avoiding the set."""
    n, full = c.n, (1 << c.n) - 1
    res = set()
    sets = [sum(1 << u for u in S) for S in c.sets]
    for k, g in enumerate(c.gates):
        if g[0] != 'or':
            continue
        w_ = c.n + k
        ok = False
        for i, m in enumerate(sets):
            if m & Qm or ok:
                continue
            free = full & ~(Qm | m)
            sub = free
            while True:
                Z = Qm | sub
                if not (T[w_] >> Z & 1) and sum(1 for u in c.sets[i] if T[w_] >> (Z | 1 << u) & 1) >= 2:
                    ok = True
                    break
                if sub == 0:
                    break
                sub = (sub - 1) & free
        if ok:
            res.add(w_)
    return res


def descend(c, T, g, Z, u, u2):
    """Follow AND gates to a child 0 at Z; return the final wire (must be an OR gate with the same triple)."""
    n = c.n
    while True:
        sep = not (T[g] >> Z & 1) and T[g] >> (Z | 1 << u) & 1 and T[g] >> (Z | 1 << u2) & 1
        if not sep:
            return None, 'lost the triple'
        if g < n:
            return None, 'input separates'
        op = c.gates[g - n]
        if op[0] == 'not':
            return None, 'NOT separates'
        if op[0] == 'or':
            return g, None
        a, b = op[1:]
        g = a if not (T[a] >> Z & 1) else b


def main():
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    st = {'F1_heavy_tests': 0, 'F1_light_fail': 0, 'desc_triples': 0, 'out_triples_in_F2': 0}
    for _ in range(N):
        n = rng.choice((4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None:
            continue
        T = c.tables()
        h = T[c.h_wire]
        full = (1 << n) - 1
        Q = rng.randrange(1 << n) & rng.randrange(1 << n)
        F2Q = f2(c, T, Q)
        # F2-desc on every wire and every triple (Z ⊇ Q)
        free = full & ~Q
        sub = free
        while True:
            Z = Q | sub
            for w_ in range(n + len(c.gates)):
                if T[w_] >> Z & 1:
                    continue
                ups = [u for u in range(n) if not (Z >> u & 1) and T[w_] >> (Z | 1 << u) & 1]
                for a in range(len(ups)):
                    for b in range(a + 1, len(ups)):
                        end, err = descend(c, T, w_, Z, ups[a], ups[b])
                        if err:
                            print('F2-desc FAIL', err, json.dumps(c.to_dict()), Q, Z, ups[a], ups[b], w_)
                            return 1
                        st['desc_triples'] += 1
            for i, S in enumerate(c.sets):
                m = sum(1 << u for u in S)
                if Z & m:
                    continue
                o = c.outs[i]
                for a in range(len(S)):
                    for b in range(a + 1, len(S)):
                        end, _ = descend(c, T, o, Z, S[a], S[b])
                        if end not in F2Q:
                            print('F2-desc output FAIL', json.dumps(c.to_dict()), Q, Z, S[a], S[b])
                            return 1
                        st['out_triples_in_F2'] += 1
            if sub == 0:
                break
            sub = (sub - 1) & free
        # F1
        for v in range(n):
            if Q >> v & 1:
                continue
            Qv = Q | 1 << v
            for g in f2(c, T, Qv):
                if h >> Qv & 1:
                    st['F1_heavy_tests'] += 1
                    if T[g] >> Qv & 1:
                        print('F1 FAIL (heavy)', json.dumps(c.to_dict()), Q, v, g)
                        return 1
                elif T[g] >> Qv & 1:
                    st['F1_light_fail'] += 1
    print('no failure:', st)
    if len(sys.argv) > 3:
        c = Circuit.from_dict(json.load(open(sys.argv[3])))
        T = c.tables()
        h = T[c.h_wire]
        v, Q = 2, 0
        bad = [g for g in f2(c, T, Q | 1 << v) if T[g] >> (Q | 1 << v) & 1]
        print(sys.argv[3], 'Q = 0, v = 2: heavy' if h >> (1 << v) & 1 else 'Q = 0, v = 2: light',
              '| F2(Q+v) gates with real g(Q + e_v) = 1:', bad)
    return 0


if __name__ == '__main__':
    sys.exit(main())
