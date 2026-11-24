# Menu decision check: are GL / G1 gates in UC(∅, Q)? (12:45 UTC, 2026-11-24)

Script: `python3 -I 951/tools/kill_tests/gl_in_uc.py 951 10` (about 1 s). Definitions of G1 / GL taken from
`951/SYNTHESIS_951.md` §6.1 (front-A2-final-1223.md does not define them); UC from `mu_light.py`.
Reading used for GL: zero (Q ∪ N(v) − a, y_a), atoms (Q+e_v, 0), (Q+e_a, t_a), t_a = ¬h(Q+e_a),
y_a = 1 if C_1(o_va) = 0 at the zero point, else 0; "applies" = at most one light neighbour forced to y_a = 0.
For a pair, the class is the first wire that is 0 at the zero point and 1 at both atoms.

CORPUS LIMIT: the repo holds only 29 correct one-NOT graph-system circuits (all n = 4, 5 or 6 edges, mostly
fixh16*). Front's 35,069-instance graph-heavy corpus (chk/c, ess_rand, ...) is not in the repo and was NOT checked.

## 1. GL and G1 gates vs UC (29 circuits, 630 heavy (Q, v) instances)
- GL applies in 630 / 630. Gates checked 913, in UC 905, NOT in UC 8 (8 instances).
  All 8 are the case "a light, y_a = 0" (21 of 29 such gates are in UC); a heavy (786 / 786) and a light with
  y_a = 1 (98 / 98) are always in UC, and that is provable in two lines (face 0 resp. face 1 at Z = Q).
  Smallest: tools/sdrcert/fixh16_forced.json:10 (n = 4, 16 gates), Q = {1}, v = 2, a = 0, gate 10 =
  (x2 ∧ (x0 ∨ x1)) ∨ NOT: C_1(g) ≡ 1 and C_0(g) needs x2, so no one-face witness exists.
- G1 applies in 623 / 630. Gates checked 903, in UC 903 (provable: face 0 at Z = Q for heavy a, at Z = X for light a).
- Overlap: all 8 instances with a GL gate outside UC have G1 applicable; in the 7 instances where G1 does not
  apply, every GL gate is in UC. So "G1, else GL" lands inside UC in 630 / 630, and the UC gain itself,
  |UC(Q) \ UC(Q+v)| ≥ deg(v), holds in 630 / 630. No proof that G1 failing forces the GL gates into UC.

## 2. Exact liftMenu_Q and the light gain
- Exact menu listed ONLY for graph systems (pairs: all (ζ, q, q') with o(ζ) = 0, o(q) = o(q') = 1, q ∧ q' ≤ ζ,
  x-parts ⊇ Q). For sets of size k ≥ 3 the menu needs (2^(n+1−|Q|))^(k+1) systems per set (2^24 at n = 5, k = 3);
  not listed, so no gain test there (a partial menu would be invalid).
- 29 graph circuits, 314 (C, Q) instances, 24 light. Light gain at some v: liftMenu_Q 24 / 24, UC 24 / 24
  (both also at EVERY v). No failure, no separation between the two families.
- Side fact: UC(Q) ⊆ liftMenu_Q in only 176 / 314 instances (UC is a count set, not a merge class), so the
  two families are incomparable, not nested. |liftMenu_Q| ≥ base in 314 / 314.

## Recommendation
Stay with UC: G1 is inside UC outright, GL leaves UC only where G1 already applies (on this small corpus), and
the light test shows no advantage for liftMenu_Q, whose exact form is unlistable beyond pairs. Caveats: n = 4
only; "G1 fails ⇒ GL gates in UC" rests on 7 instances and is unproved; rerun on front's corpus before relying on it.
