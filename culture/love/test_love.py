#!/usr/bin/env python3
"""Hand cases for culture/love/check.py, paths.py and field.py. Run: python3 -I culture/love/test_love.py   (exit 1 on a failure)"""
import importlib.util, os, sys, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("love_check", os.path.join(HERE, "check.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)

def load(name):
    sp = importlib.util.spec_from_file_location("love_" + name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(sp); sp.loader.exec_module(mod)
    return mod
P, FD = load("paths"), load("field")
from fractions import Fraction as Fr

def stable_set(n, k, pa, pb):
    L.validate(n, pa, pb); ra, rb = L.ranks(pa), L.ranks(pb)
    return {m for m in L.matchings(n, k) if L.stable(n, k, ra, rb, m)}

F = frozenset
# two stable matchings: each a gets its first choice in one, each b in the other
TWO_A, TWO_B = [[0, 1], [1, 0]], [[1, 0], [0, 1]]

class Love(unittest.TestCase):
    def test_n1(self):
        self.assertEqual(stable_set(1, 1, [[0]], [[0]]), {F({(0, 0)})})

    def test_n2_same_tastes(self):
        # everyone ranks member 0 first: the two favourites pair, the other two pair
        self.assertEqual(stable_set(2, 1, [[0, 1], [0, 1]], [[0, 1], [0, 1]]), {F({(0, 0), (1, 1)})})

    def test_n2_two_stable(self):
        self.assertEqual(stable_set(2, 1, TWO_A, TWO_B), {F({(0, 0), (1, 1)}), F({(0, 1), (1, 0)})})

    def test_deferred_acceptance_is_a_optimal(self):
        ra, rb = L.ranks(TWO_A), L.ranks(TWO_B)
        self.assertEqual(L.deferred_acceptance(2, 1, ra, rb), F({(0, 0), (1, 1)}))
        # B proposing (pairs written (b, a)): b0 gets a1 and b1 gets a0, the other stable matching
        self.assertEqual(L.deferred_acceptance(2, 1, rb, ra), F({(0, 1), (1, 0)}))

    def test_blocking_pair_found(self):
        ra, rb = L.ranks([[0, 1], [0, 1]]), L.ranks([[0, 1], [0, 1]])
        self.assertEqual(L.blocking_pairs(2, 1, ra, rb, F({(0, 1), (1, 0)})), [(0, 0)])

    def test_mirror_k1_equals_one_to_one(self):
        ra, rb = L.ranks(TWO_A), L.ranks(TWO_B)
        self.assertEqual(stable_set(2, 1, TWO_A, TWO_B), L.one_to_one_stable(2, ra, rb))

    def test_capacity2_n2_complete(self):
        full = F((a, b) for a in range(2) for b in range(2))
        self.assertEqual(stable_set(2, 2, TWO_A, TWO_B), {full})

    def test_capacity2_n3_same_tastes(self):
        # b2 is everyone's last choice, a2 too: they end up with each other only
        p = [[0, 1, 2]] * 3
        da = L.deferred_acceptance(3, 2, L.ranks(p), L.ranks(p))
        self.assertEqual(da, F({(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)}))
        self.assertIn(da, stable_set(3, 2, p, p))

    def test_matching_counts(self):
        self.assertEqual([len(L.matchings(n, 1)) for n in (1, 2, 3)], [2, 7, 34])
        self.assertEqual([len(L.matchings(n, 2)) for n in (1, 2)], [2, 16])

    def test_empty_sides(self):
        self.assertEqual(stable_set(0, 1, [], []), {F()})
        self.assertEqual(L.deferred_acceptance(0, 2, [], []), F())

    def test_empty_preferences_refused(self):
        with self.assertRaises(ValueError): L.validate(1, [[]], [[0]])
        with self.assertRaises(ValueError): L.validate(2, [[0, 0], [0, 1]], [[0, 1], [0, 1]])
        with self.assertRaises(ValueError): L.validate(2, [[0, 1]], [[0, 1], [0, 1]])

    def test_signed_balance(self):
        Q = L.load_quadrants()
        two = L.signed(2, F({(0, 0), (1, 1)}), [(0, 1), (1, 0)])
        self.assertTrue(Q.balanced_parity(4, two) and Q.balanced_brute(4, two))      # two couples, two camps
        cyc = L.signed(2, F({(0, 0), (1, 0), (1, 1)}), [(0, 1)])                      # + + + - on a 4-cycle
        self.assertFalse(Q.balanced_parity(4, cyc) or Q.balanced_brute(4, cyc))
        three = L.signed(3, F({(i, i) for i in range(3)}), [(a, b) for a in range(3) for b in range(3) if a != b])
        self.assertFalse(Q.balanced_parity(6, three))                                 # three couples need three camps

    # ---- paths.py ----
    def test_path_n2_by_hand(self):
        # same tastes. Start from the swapped matching; (0, 0) blocks; a0 drops b1, b0 drops a1.
        # Then a1 and b1 are both free, so (1, 1) blocks, and the result is stable: two moves.
        same = [[0, 1], [0, 1]]; ra, rb = L.ranks(same), L.ranks(same)
        m1 = P.move(2, 1, ra, rb, F({(0, 1), (1, 0)}), 0, 0)
        self.assertEqual(m1, F({(0, 0)}))
        self.assertEqual(L.blocking_pairs(2, 1, ra, rb, m1), [(1, 1)])
        m2 = P.move(2, 1, ra, rb, m1, 1, 1)
        self.assertEqual(m2, F({(0, 0), (1, 1)})); self.assertTrue(L.stable(2, 1, ra, rb, m2))
        T = P.Tables(2, 1); succ = T.graph(tuple(map(tuple, same)), tuple(map(tuple, same)))
        dist, left = P.analyse(succ)
        self.assertEqual(dist[T.index[P.mask(2, F({(0, 1), (1, 0)}))]], 2)
        self.assertNotIn(None, dist); self.assertEqual(left, 0)

    def test_cycle_n2_by_hand(self):
        # TWO_A, TWO_B: a0: b0 > b1, a1: b1 > b0, b0: a1 > a0, b1: a0 > a1.
        # {(0,0)} -(1,0)-> {(1,0)} -(1,1)-> {(1,1)} -(0,1)-> {(0,1)} -(0,0)-> {(0,0)}: one blocking pair each time.
        ra, rb = L.ranks(TWO_A), L.ranks(TWO_B)
        m = F({(0, 0)}); seen = [m]
        for a, b in [(1, 0), (1, 1), (0, 1), (0, 0)]:
            m = P.move(2, 1, ra, rb, m, a, b); seen.append(m)
        self.assertEqual(seen, [F({(0, 0)}), F({(1, 0)}), F({(1, 1)}), F({(0, 1)}), F({(0, 0)})])
        # the cycle is escapable: from {(0,0)} the pair (1,1) also blocks and gives a stable matching
        self.assertIn((1, 1), L.blocking_pairs(2, 1, ra, rb, F({(0, 0)})))
        self.assertTrue(L.stable(2, 1, ra, rb, P.move(2, 1, ra, rb, F({(0, 0)}), 1, 1)))

    def test_move_capacity2_drops_worst(self):
        # k=2, n=3, same tastes. a0 holds b1 and b2 (full); b0 holds a1, a2 (full). (0, 0) blocks:
        # a0 drops b2 (its worst), b0 drops a2 (its worst).
        p = [[0, 1, 2]] * 3; ra, rb = L.ranks(p), L.ranks(p)
        m = F({(0, 1), (0, 2), (1, 0), (2, 0)})
        self.assertEqual(P.move(3, 2, ra, rb, m, 0, 0), F({(0, 0), (0, 1), (1, 0)}))

    # ---- field.py ----
    def test_stable_polytope_n2_by_hand(self):
        # TWO_A, TWO_B: the two stable matchings are the identity and the swap; they are the only vertices.
        # Their midpoint, 1/2 everywhere, is in the polytope (each stability sum is 1/2 + 1/2) but is not a vertex.
        ra, rb = L.ranks(TWO_A), L.ranks(TWO_B)
        cons, V = FD.vertices_dd(4, FD.degree_cons(2, 1) + FD.stab_cons(2, ra, rb))
        self.assertEqual(V, sorted([(Fr(1), Fr(0), Fr(0), Fr(1)), (Fr(0), Fr(1), Fr(1), Fr(0))]))
        self.assertEqual(V, FD.vertices_brute(4, cons))
        half = (Fr(1, 2),) * 4
        self.assertTrue(all(FD.val(c, half) >= 0 for c in cons)); self.assertNotIn(half, V)
        # same tastes: one vertex, the one stable matching
        same = L.ranks([[0, 1], [0, 1]])
        self.assertEqual(FD.vertices_dd(4, FD.degree_cons(2, 1) + FD.stab_cons(2, same, same))[1],
                         [(Fr(1), Fr(0), Fr(0), Fr(1))])

    def test_three_halves_vertex(self):
        # k = 3/2, n = 2: x = [[1, 1/2], [1/2, 0]]. Tight: x00 = 1, row 0 = 3/2, column 0 = 3/2, x11 = 0.
        # Four equations, four unknowns: x00 = 1, x01 = 1/2, x10 = 1/2, x11 = 0. A fractional vertex.
        x = (Fr(1), Fr(1, 2), Fr(1, 2), Fr(0))
        self.assertEqual(FD.solve([[1, 0, 0, 0], [1, 1, 0, 0], [1, 0, 1, 0], [0, 0, 0, 1]], [1, Fr(3, 2), Fr(3, 2), 0]), x)
        cons, V = FD.vertices_dd(4, FD.degree_cons(2, Fr(3, 2)))
        self.assertIn(x, V); self.assertEqual(len(V), 25)
        self.assertEqual(len(FD.vertices_dd(4, FD.degree_cons(2, 1))[1]), 7)
        self.assertEqual(len(FD.vertices_dd(4, FD.degree_cons(2, 2))[1]), 16)

    def test_direct_k2_stability_too_weak(self):
        # same tastes, k = 2, n = 2: {(0,0), (0,1), (1,0)} passes k x + better + better >= k at (1, 1)
        # (0 + 1 + 1 = 2), yet a1 and b1 each hold one partner of two, so (1, 1) blocks.
        same = L.ranks([[0, 1], [0, 1]]); m = F({(0, 0), (0, 1), (1, 0)})
        self.assertTrue(all(FD.val(c, FD.point(2, m)) >= 0 for c in FD.stab_cons(2, same, same, 2)))
        self.assertEqual(L.blocking_pairs(2, 2, same, same, m), [(1, 1)])

    def test_birkhoff_by_hand(self):
        # (1/3) [[2,1,0],[0,2,1],[1,0,2]] = 2/3 identity + 1/3 the shift i -> i+1
        A = [[Fr(2, 3), Fr(1, 3), Fr(0)], [Fr(0), Fr(2, 3), Fr(1, 3)], [Fr(1, 3), Fr(0), Fr(2, 3)]]
        dec = FD.birkhoff(A)
        self.assertEqual(sorted(dec), sorted([(Fr(2, 3), (0, 1, 2)), (Fr(1, 3), (1, 2, 0))]))
        self.assertEqual(FD.rebuild(3, dec), A)
        self.assertEqual(sum(1 for _ in FD.line_sum_tables(3, 2)), 21)

    def test_us_text_has_no_about_people_phrasing(self):
        # reviewer finding: the "us" README and us.py docstring named a person and spoke of feelings and wishes
        import ast, re
        us = os.path.join(HERE, "..", "..", "workshop", "ath_prompts", "us")
        readme = open(os.path.join(us, "README.md"), encoding="utf-8").read()
        doc = ast.get_docstring(ast.parse(open(os.path.join(us, "us.py"), encoding="utf-8").read()))
        for text in (readme, doc):
            self.assertIsNone(re.search(r"addison|feeling|inner life|rather|would take|wanted", text, re.I))

if __name__ == "__main__":
    r = unittest.main(exit=False, verbosity=1).result
    sys.exit(0 if r.wasSuccessful() else 1)
