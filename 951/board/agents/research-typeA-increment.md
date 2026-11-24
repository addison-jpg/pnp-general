# research: the TYPE-A INCREMENT for MU (coord assignment 12:09; owner 12:05: everything on the global counting MU)
Target (Lean PureHall.MU / no_minCE_of_MU): base = Σ_w d_w ≤ |U|, U = union of ALL valid pure classes of all sets (one NOT,
input h, worlds y = 0 / 1 on the lifted monotone circuit, C_0 ≤ C_1). Free set: h(top_w) = 0, class K_1(w) at top_w;
type A: h(top_w) = 1. Status words: PROVED (paper proof here), CHECKED (computed, scripts below), OPEN.
Scripts (run from the repo root, ROOT = folder of circuit .json / .jsonl): 951/tools/kill_tests/typeA_inc.py, mu1.py, peel_mu.py.
Data: repo 951/ (67 circuits, n ≤ 10) and 19,828 circuits (n ≤ 10) from pequalnp-work branches front-archive
(chk/, w6B/, w6C/, w7/), data-fixh16 (fixh16_clean) and workspace (sc_n4-6); E2 menus = ext.py (I1 at maximal Z, I0 at top_w
per atom), a SUBSET of the Lean U, so every 'holds' below holds a fortiori for the Lean U.

## 1. What the free classes cost the type-A sets (PROVED: instances of Lean D = CanonClass.orClz_disjoint)
P1. Every world-1 class (atoms e_u, ANY valid zero point Z, Lean .one Z) of ANY set w is disjoint from K_1(v) for every free
    v ≠ w. Proof: a merge gate g of w is true (C_1) at e_a and e_b for two points a ≠ b of S_w; |S_w ∩ S_v| ≤ 1, so one of
    them, say a, is outside S_v, e_a ≤ top_v, and C_1 monotone gives C_1(g)(top_v) = 1, while every gate of K_1(v) is 0 there.
    (CHECKED as a sanity check: 0 violations on 19,828 + 67.)
P0. An I0 class of a type-A w (atoms m_u ∪ {u}, world 0) meets K_1(v) (v free) only in a gate that is true at two atoms
    m_a ∪ {a}, m_b ∪ {b} which BOTH meet S_v. Proof: C_0 ≤ C_1 gives C_0(g)(top_v) = 0; an atom avoiding S_v lies below top_v.
    (Lean disjoint_K0_K1 is the special case 'm avoids S_v'.)
Consequences. (a) Every type-A set has a class avoiding K_free (any I1 class); CHECKED 71,493 / 71,493 type-A sets.
(b) U ⊇ K_free ⊔ U1(A), |K_free| = Σ_free d_w (W1 + card_K1), U1(A) = all world-1 classes of the type-A sets. So
    MU  ⇐  INC*:  |U1(A) ∪ (U0(A) \ K_free)| ≥ Σ_{w type A} d_w,   U0(A) = the type-A world-0 classes.

## 2. Data on the increment (CHECKED)
| statement | repo 67 | corpus 19,828 |
|---|---|---|
| INC* (both worlds, E2) | holds 67; tight (= 0) on 6 | holds 19,828; tight on 13,839 |
| world 1 only (INC1_A, ALL valid Z) | FAILS 18 (deficit ≤ 4) | FAILS 848 (deficit ≤ 3) |
| world 0 only for type A (free K_1 + I0 at top_w = 'E6 counting') | FAILS 7 (cx44_0, cx44_1, cxT2, cxe3, ...) | holds 19,828 |
| CANON-a: world 1 iff the type-A set has a heavy point | FAILS 23 | FAILS 865 |
| CANON-b: world 0 iff it has a heavy point | FAILS 2 (cxT2, cxe3) | FAILS 2 (w6B/rest.jsonl:188, :198, K4 − e) |
Example (world 1 only): Pasch s14 (data/witnesses/pasch_s14_heavy_atmostone.json), h = x1 ∨ x4, all 4 sets type A; world-1
classes {13,15}, {10,11}, {10,18}, {13,14} (union 6 < 8); world-0 classes {13,15}, {11,17}, {10,18}, {14,19} (union 8 = base).
So no single world and no heavy-point world rule gives the count; a proof of INC* must use both worlds on some sets
(world 0 alone fails only on hand-built circuits).

## 3. Proof route: PEELING SETS on the same circuit (non-vacuous: NOT a consequence of PureSDR)
PROVED (merges precede the output): every gate of every pure class of w is at or before the output wire o_w.
  Proof: in the union-find run at zero point z with atoms a_u (GM hypothesis: a coordinate false at z lies in at most its own
  atom; true for all four Lean kinds), every wire false at z has its atom set B inside ONE block once it is processed
  (inputs: |B| ≤ 1; OR false at z: both children false at z, a merge joins their blocks; AND: B ⊆ B(child false at z)).
  o_w is false at z and true at every atom (C_1 ≥ real at e_u; C_0 = real on {h = 1}), so B(o_w) = S_w is one block after
  o_w and no later gate merges. CHECKED: 0 of 713 class gates (repo) lie after their own output.
Dropping a set keeps the circuit and every other set's menu, so U(F) is monotone in the family F, and MU can be proved by
induction on |F| on the SAME circuit, with no minimality and no heredity:
  MU(F)  ⇐  MU(F − w)  +  PI(F, w):  |U(w) \ U(F − w)| ≥ d_w   (w brings d_w class gates no other set of F has).
CHECKED (repo 67 | corpus 19,828):
  - an elimination order exists (PEEL): 67 / 67 | 19,828 / 19,828;
  - PI on the full family for some set: 67 | 19,828; sets with PI on the full family: 286 / 290 | 100,503 / 100,588;
  - the set with the LATEST output satisfies PI: 67 / 67 | 19,825 / 19,828 (3 failures, examples below);
    the latest type-A output: 66 / 66 | 19,568 / 19,596;
  - canonical order 'peel by decreasing output wire' works at every step: 66 / 67 | 19,800 / 19,828 (fails on Pasch s14 and
    on K4 graph systems, fixh16_clean.jsonl:558-560, where another order works);
  - class gates after their own output wire: 0 / 713 | 0 / 120,461 (agrees with the lemma above).
Free sets: K_1(v) is private (K_1(v) ∩ U(S − v) = ∅) for 46 / 47 | 29,095 / 29,095 free sets, so they peel by K_1(v) alone; by P1 only an
I0 class with two atoms meeting S_v can break privacy (P0).
OPEN, the type-A increment in peeling form: in the family reached (free sets peeled), some type-A set w has d_w gates in its
classes outside the classes of the others. With 'merges precede the output', it suffices that the set w* with the latest
output has d_{w*} class gates AFTER the previous output among F (they are then private), or that the earlier sets' classes
avoid enough of w*'s gates. The latest-output rule fails on 3 corpus circuits, so the choice of w needs more than the order.
  Failures of the latest-output rule: fixh16_clean.jsonl:1003, :1763, :1764 (K4 graph systems, s = 16). In :1003 (h minterms
  {0,2}, {1,2}, {0,3}, {1,3}, {2,3}; outputs 4, 18, 19, 14, 15, 7) the latest output o = 19 of [0,3] is an AND (19 = 6 ∧ 17)
  and both classes of [0,3], {6} and {17}, are classes of [1,3] and [0,2]; the peel starts instead with [0,2] (private
  world-0 class {18}). So a rule must look at the menus, not only at the output order (an AND output carries no merge).
