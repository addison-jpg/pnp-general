# A7: DD-absorption: attack, a proved reduction to light absorption, and the exact obstacle

Seat A7, board `boards/tasks/open-one-not.md`, 2026-11-25. Result: no counterexample; a paper reduction of
DD-absorption to a smaller statement about the **light** points of DD sets only; the exact obstacle. No proof
of DD-absorption, no proof of `no_minCE`.

Words: **paper** = argument written here; **tested** = computed (`A7_dd_absorb_attack.py`, `A7_hill.py`);
**checked** = Lean accepted it (nothing new is checked in this seat; the lemmas used from A4 are checked in
`one-not/lean/PEqualNP/W951/Open/F2Transfer.lean`).

Notation as in `A4_f2_transfer.md`. State `(Q, D)`, `Q ∩ D = ∅`. `h` = the wire the NOT gate reads (monotone).
`P_u = 1_Q + e_u` (unit atoms), `Z_w = Zof(S_w ∪ D)` (top zero point). For an alive `w` with
`k_w = |S_w \ D| ≥ 2`: **heavy atoms** `U_w = {u ∈ S_w \ D : h(P_u) = 1}`, **light atoms**
`T_w = {t ∈ S_w \ D : h(P_t) = 0}`. `w` is DD iff `h(Z_w) = 1` and `T_w ≠ ∅`.

## 0. Verdict

1. **Attack: no counterexample (tested).** 0 failures of DD-absorption at 149,861 sampled DD states of 2,393
   stored one-NOT correct circuits with n up to 16 (2,159 of them at n = 13 on the projective plane PG(2,3),
   67 at n = 16), up to **19 DD sets at one state**; and 0 failures at all 1,147,168 DD states (every mixed
   state) of the 360 circuits with n ≤ 11 (stored n ≤ 9 plus 200 random NOT-switch circuits). A hill-climb
   (gate mutations kept when correct and the minimum absorption slack does not rise, 40 starts × 150 steps,
   every mixed state) never went below 0. Tight states: 12,449 (sampled run), 238,722 (full run).
2. **Reduction (paper).** The heavy atoms of a DD set behave like a non-DD set: the unit-form run at `Z_w`
   over the heavy atoms `U_w` alone gives `|U_w| − 1` OR gates (`H_w`), all in `F2Mix(Q, D)`, and the
   **top family** `{M_v : v non-DD} ∪ {H_w : w DD}` is pairwise disjoint. Hence DD-absorption follows from
   **light absorption**:

   > `|F2Mix(Q, D) \ (∪_{v non-DD} M_v ∪ ∪_{w DD} H_w)| ≥ Σ_{w DD} (|T_w| − [U_w = ∅])`.

   Light absorption holds with 0 failures at every DD state above (same tight count as DD-absorption), and the
   three lemmas of the reduction hold with 0 violations there (no top overlap, every top merge an OR gate in
   `F2Mix`).
3. **The exact obstacle.** Each DD set must still pay `|T_w|` gates (`|T_w| − 1` if it has no heavy atom):
   `|T_w| − 1` to join its light atoms and one bridge to its heavy part. All light atoms lie in `H0 = {h = 0}`
   where the circuit is the monotone `C1`, but the top zero point `Z_w` lies in `H1 = {h = 1}`, so the
   monotone disjointness argument has no zero point on the light side. The natural light zero point `1_Q`
   gives F2 merges (§3) but they **overlap between DD sets** (284 states of the stored n ≤ 9 circuits), and
   the bridge merges of the full unit-form run can fail to be F2 (A4: 2,428 such merges). Nothing found
   pays the light atoms injectively.
4. **Strength.** DD-absorption (and light absorption) is not weaker than the theorem: restricting `x_Q = 1`,
   `x_D = 0` turns every state into the root state of a one-NOT circuit with constant inputs, and at the root
   the statement plus A4's no-DD count is `|F2| ≥ base`, i.e. the F2 form of the general one-NOT bound. What
   is smaller is the structure: after A4 and §1, only the light atoms of DD sets are unaccounted for.

## 1. Paper proof of the reduction

Fix `(Q, D)`. All points below are `≥ 1_Q` and `0` on `D`.

**(a) Heavy merges are OR gates in F2Mix.** Let `w` be DD with `|U_w| ≥ 2`. The test system
`(Z_w, P, U_w)` is a unit test system (`unit_testSystem`). It is `GoodT` by `goodT_of_noDD` (right
disjunct: `h(P_u) = 1` for every `u ∈ U_w`), so `unit_count_of_noDD` with `R = U_w` gives `|U_w| − 1`
counted wires (the output of `w` is `0` at `Z_w`, `1` at every `P_u`). Each merge is an OR gate (as in A4 §2;
the NOT gate is `0` at heavy atoms, so it merges nothing). A merging gate `g` has `g(Z_w) = 0` and
`g(P_u) = g(P_{u'}) = 1` for heavy `u ≠ u'`. Since `P_u ≤ Z_w + e_u`, `sign_of_drop` would need
`h(P_u) = 0` for `g(Z_w + e_u) = 0`; so `g(Z_w + e_u) = g(Z_w + e_{u'}) = 1` and `Z = Z_w` is an
`F2WitMix` witness for `w` (`Z_w = 1` on `Q`, `0` on `S_w ∪ D`). This is the heavy branch of
`F2WitMix_of_unit_noDD`, with the hypothesis "not DD" replaced by "both atoms heavy".

**(b) Heavy overlap is impossible.** Let `g` be `0` at `Z_b` and `1` at `P_u`, `P_{u'}` for heavy
`u ≠ u' ∈ S_a \ D`, `a ≠ b`, `|S_a ∩ S_b| ≤ 1`, `Q` disjoint from `S_b ∪ D`. One of `u, u'`, say `u`, is not
in `S_b`, so `P_u ≤ Z_b` (`unit_le_top`) and `sign_of_drop` forces `h(P_u) = 0`: contradiction. (This is
`unit_overlap` with the extra fact, visible in its proof, that the point `t` it returns is `u` or `u'`.)

**(c) The top family is pairwise disjoint.** Every member is a unit merge set at a top zero point.
`M_v ∩ M_{v'}` (both non-DD) is empty by `overlap_needs_DD`. `H_w ∩ X` for any other member `X` at top zero
point `Z_b` is empty by (b) applied to `a = w`. (`H_w ∩ M_v` and `H_w ∩ H_{w'}` both fall under this.)

**(d) Arithmetic.** With `N = ∪_{non-DD} M_v` and `H = ∪_{DD} H_w`: `H ⊆ F2Mix`, `H ∩ N = ∅` and
`|H| = Σ_{DD} |H_w| ≥ Σ_{DD} (|U_w| − 1)⁺`. So
`|F2Mix \ N| = |H| + |F2Mix \ (N ∪ H)| ≥ Σ_{DD} ((|U_w| − 1)⁺ + |T_w| − [U_w = ∅]) = Σ_{DD} (k_w − 1)`,
since `|U_w| + |T_w| = k_w`. That is DD-absorption. ∎

## 2. Attack details

`A7_dd_absorb_attack.py` (truth tables as Python ints over all `2^n` points, so n ≤ 16 is cheap):

| run | circuits | DD states | DD-absorption fails | light fails | top lemma violations | max DD sets |
|---|---|---|---|---|---|---|
| stored n ≤ 16, 60 random states + root + singletons each | 2,393 | 149,861 | 0 | 0 | 0 | 19 |
| stored n ≤ 9 + 200 switch circuits n 6..11, every state | 360 | 1,147,168 | 0 | 0 | 0 | 9 |

The switch circuits (`gen_switch`) are built to make many sets DD: `h` = random OR of 2-ANDs,
`out_w = OR(T) ∨ (h ∧ Y) ∨ (¬h ∧ Y)` with `Y = OR(S_w \ T)`. They are wasteful, so they are an easy test; the
stored PG(2,3) and AG scaffold circuits are the hard ones. `A7_hill.py`: hill-climb from 40 starts (stored
n ≤ 8 and switch circuits), every mixed state scored; minimum absorption slack stayed 0 on all starts.
No negative mixed slack anywhere.

## 3. Why the light side resists (the obstacle, in detail)

- For light atoms the natural zero point is the bottom `1_Q`: `h(1_Q) = 0`, the NOT gate is `1` there and
  merges nothing, every merging gate is an OR gate, and `Z = 1_Q` is itself an `F2WitMix` witness. So the
  light run of each DD set gives `|T_w| − 1` F2 gates. But two DD sets' light runs share gates (284 stored
  states), as unit merges at a low zero point do even in monotone circuits.
- A zero point `y` in `[1_Q, Z_w]` with `h(y) = 0` keeps (a) but blocks the overlap argument only for points
  `u` with `P_u ≤ y`. Since `y ∈ H0` and `h` is monotone, `y` contains no heavy coordinate, so sets meeting
  heavy coordinates off `S_w` can always overlap.
- The bridge (heavy part to light part) is a merge `0` at `Z_w`, `1` at a heavy and a light atom. At `Z_w + e_t`
  (`t` light) it may drop (`h(P_t) = 0`, `h(Z_w + e_t) = 1`), and at `1_Q` it may already be `1`; so it need
  not be F2.

What would close it: an injective choice, for each DD set, of `|T_w| − [U_w = ∅]` F2 gates outside the top
family. Light absorption is exactly that count, and it is the open target.

## 4. Sub-lemmas (on the board as OPEN (Sonnet) lines)

1. `unit_overlap_pt`: `unit_overlap` with the conclusion `t = u ∨ t = u'` added.
2. `heavy_overlap_false`: (b) above.
3. `F2WitMix_of_unit_heavy`: (a) above, the F2 witness part.
4. `top_family_disjoint` + arithmetic (c), (d): DD-absorption from light absorption, as a Lean implication.
