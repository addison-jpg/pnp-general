# research: the LIGHT case of the F2 step (coord 12:46; paper, ambition over thoroughness)
F2(Q): OR gates g with a REAL witness: an alive w (S_w ∩ Q = ∅), a zero point Z ⊇ Q with Z ∩ S_w = ∅ and u ≠ u' ∈ S_w with
real g(Z) = 0, real g(Z + e_u) = real g(Z + e_u') = 1. Step x_v := 1 at an alive point v: gain(v) = |F2(Q) \ F2(Q + v)|,
cost(v) = Σ_{alive w ∋ v} d_w. LIGHT: h is not constant on the cube and h(Q + e_u) = 0 for every alive point u.
Words: PROVED (paper proof here), CHECKED (computed), OPEN. One new computation only (coord's check, §1); no other tests.

## 1. Coord's check: is every alive set free at Q in a light instance? NO (CHECKED)
Light instances with D = 0 on the repo corpus (n ≤ 9; mu_light.py's enumeration): 672. Every alive set free at Q
(h(top_w) = 0, top_w = 1 off S_w) in only 47 of them; 968 of the 1,090 alive sets are TYPE A at Q (h(top_w) = 1).
Reason: light forbids heavy single points, not minterms of size ≥ 2, and those avoid most sets. So the light case is mostly
type A. Its one-world system is at the BOTTOM of the cube, not at the top:

## 2. The bottom system (PROVED)
B. In a light instance, for every alive w the test system (zero point Q, atoms Q + e_u, u ∈ S_w) lies in D = {h = 0}
   (h(Q) ≤ h(Q + e_u) = 0), so real = C_1 on it, and Lemma M gives d_w merge gates M_Q(w) ⊆ F2(Q), each with a real witness
   at Z = Q. This mirrors the free sets (research-typeA-increment.md): a free set's system lies in D at its TOP point; in a
   light instance EVERY alive set's system lies in D at the BOTTOM point.
B fails to count by itself: sets through one point v share v, and their bottom classes can coincide. Example: p = x_a ∨ x_b,
g = p ∨ x_v merges {a, v} AND {b, v} at Q. At the top points the star's classes are disjoint (W1), but a type-A set's top
point is outside D.

## 3. Death criteria for x_v := 1 (PROVED, any instance; real = C_{¬h}: C_0 ≤ real ≤ C_1 pointwise, real = C_1 on
##    {h = 0} and real = C_0 on {h = 1}, C_0 and C_1 monotone)
K0. C_0(g)(Q + e_v) = 1 ⇒ g ∉ F2(Q + v). (At any Z' ⊇ Q + v: real g(Z') ≥ C_0(g)(Z') ≥ C_0(g)(Q + e_v) = 1. No zero point.)
K1. C_1(g)(Q + e_v) = 1 ⇒ every witness of g in F2(Q + v) has h(Z') = 1 at its zero point, so it is a world-0 witness
    (C_0 at Z' and at its atoms, h monotone), and its set w' (v ∉ S_w') is TYPE A at Q + v (h(top_{w'}) ≥ h(Z') = 1).
K2. In a light instance real g(Q + e_v) = C_1(g)(Q + e_v), so every merge gate of M_Q(w), w ∋ v, whose block contains v
    satisfies K1: it survives the move only if it is NOT-dependent at Q + e_v (C_1 = 1, C_0 = 0 there) AND serves a world-0
    witness of a type-A set not through v.
K3. A gate whose only witnesses come from sets through v dies (the sets are dead after the move).

## 4. Where the light step sits (big picture) and what is OPEN
- The heavy step is easy for a structural reason: h(Q + e_v) = 1 makes h ≡ 1 after the move, so the NOT is constant and one
  world (C_0) remains (front A2's HEAVY-COUNT, proved for the heavy star in Lean `starSep_heavy`).
- In the light step the NOT survives the move. By K0 / K1 the only gates that can SURVIVE are world-0 servants of type-A
  sets not through v; by B the gates that can be CHARGED to star(v) are bottom merges, which collide inside the star.
  So the light step is the TYPE-A INCREMENT of research-typeA-increment.md localized to one star: the sets through v
  (pairwise meeting only in v) must find Σ_{w ∋ v} d_w gates that (i) are counted for star(v) and (ii) have no world-0
  witness for a type-A set outside the star at a zero point above Q + v.
- OPEN, the lemma that would close the light step: LIGHT-STAR. In a light instance there is an alive v such that the union
  over w ∋ v of the bottom merges M_Q(w), together with the K0 gates, contains cost(v) gates with NO witness at Q + v
  (i.e. outside F2(Q + v)). [Wording corrected 12:55 per referee dwV8p (dwV8p-referee-F2-light.md): the first draft said
  'no world-0 witness', which does not imply leaving F2: a bottom merge whose block misses v can survive through a WORLD-1
  witness (n = 5, sets {1,2,4}, {3,4}, h = x0 ∧ x4, Q = ∅, v = 2, gate 8). The form tested in §5 is the corrected one.
  Referee: B and K0-K3 CORRECT on 58,795 light instances; the repaired form and the step hold on all instances.]
  Choice of v suggested by the data (fable-mu-induction.md: 11,105 of 11,108 light points are good, 'least h-influence'
  picks a good point): v of least h-influence on the cube, i.e. the point whose star meets the fewest minterms of h above
  Q, so that few type-A world-0 witnesses above Q + v exist (K1).
- Not claimed: anything about minimal counterexamples; everything above is about all correct one-NOT circuits.

## 5. LIGHT-STAR TEST RESULT (coord 12:49; 951/tools/kill_tests/f2_lightstar.py, D = 0, real witnesses as in F2)
Tested statement: LIGHT-STAR(v): |(∪_{alive w ∋ v} M_Q(w) ∪ K0(v)) \ F2(Q + v)| ≥ cost(v), K0(v) = {g ∈ F2(Q) : C_0(g)(Q + e_v) = 1};
LIGHT-STAR(v) ⇒ gain(v) ≥ cost(v). RESULT: 0 failures.
- repo 951/ (74 circuits with n ≤ 9, incl. every witness file): 672 light instances; LIGHT-STAR at SOME v 672 / 672, at the
  LEAST h-INFLUENCE v 672 / 672; per point 2,348 / 2,353 (F2 step gain ≥ cost: 2,352 / 2,353 points; some v: 672 / 672).
- pappus_junk_gain.json (n = 9, s = 66): 1 light instance, LIGHT-STAR at all 9 points. fano_formula.json (n = 7, s = 17):
  43 light instances, LIGHT-STAR at all 190 points.
- Sanity: B (bottom merges ⊆ F2(Q) in light instances) 0 violations.
So the Opus can build on: in a light instance, take v of least h-influence; the gates that die are the bottom merges of
star(v) plus the K0 gates.
- CORPUS (19,828 circuits, n ≤ 9, from the pequalnp-work branches front-archive chk/ w6B/ w6C/ w7/, data-fixh16 fixh16_clean,
  workspace sc_n4-6): 16,281 light instances; LIGHT-STAR at SOME v 16,281 / 16,281, at the LEAST h-INFLUENCE v
  16,281 / 16,281; per point 53,671 / 53,673; F2 step gain ≥ cost at EVERY alive point 16,281 / 16,281 instances.
