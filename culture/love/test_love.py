#!/usr/bin/env python3
"""Hand cases for culture/love/check.py. Run: python3 -I culture/love/test_love.py   (exit 1 on a failure)"""
import importlib.util, os, sys, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("love_check", os.path.join(HERE, "check.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)

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

if __name__ == "__main__":
    r = unittest.main(exit=False, verbosity=1).result
    sys.exit(0 if r.wasSuccessful() else 1)
