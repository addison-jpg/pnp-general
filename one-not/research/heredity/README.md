# Heredity of pure menus under x_v := 0 off V(F) (cTAHG, coord 11:08; front's graph lane)

Question: restrict a one-NOT instance to a family F (x_v := 0 for v outside V = ⋃_{w∈F} S_w, NOT gate kept). Is
the restricted pure menu of each w ∈ F inside the original pure menu?

Run from `one-not/`: `python3 research/heredity/menu_restrict.py` (all 63 one-NOT circuits with n ≤ 10 of the repository
corpus, I0 over minterms) and `python3 research/heredity/graph_full.py` (the 26 graph systems, FULL Lean menus: I1 at
every Z avoiding S_w with h(Z) = 0, I0 at top_w with every m_u, h(m_u) = 1, m_u ∩ S_w ⊆ {u}).

* I1 transfers trivially: a restricted I1 zero point vanishes off V and is an original I1 zero point (same class).
* I0 does NOT transfer with top-only options. The restricted top is V \ S_w, not top_w, and the lower zero point lets
  earlier wires merge. Failing restricted I0 classes: 344 of 4,149 on all 63 circuits, and 144 of 671 on the 26 graph
  systems, against the full Lean menu. Smallest witness (`witness.json`, kernel-checked as `heredity_top_fails` in
  `lean/PEqualNP/W951/PureHeredity.lean`): scaffold's fixh16_20 (n = 4, K4 pairs, 16 gates), F = {S_1, S_2},
  V = {0, 2, 3}, w = 2, S_w = {0, 3}, m_0 = {0, 2}, m_3 = {2, 3}. The restricted class is {h}, where h is the wire
  read by the NOT gate (real wire 8, lifted wire 9). The original menu of w is {14}, because C_0(h)(top_w) = 1 and
  C_1(h)(e_0) = C_1(h)(e_3) = 0.
* FIX (in Lean): I0 at a general zero point (`PureOpt.zeroAt z m`: z vanishes on S_w, m_u ⊆ z ∪ {u}, h(m_u) = 1). Its
  classes still have exactly d_w merges (`card_pureI0At`). Every restricted option is then an original option with the
  same class (`restrValid_valid`), so restricted menu ⊆ menu (`restrictedMenu_subset_pureMenu`). Hall deficiency of F
  therefore passes to the restriction (`restricted_deficient`). The extended menus only add options, so PureSDR and the
  Hall data stay true.
