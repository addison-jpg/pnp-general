# A10: light absorption: the bridge is solved at the bottom; the exact obstacle is a disjoint bottom payment

Seat A10, board `boards/tasks/open-one-not.md`, 2026-11-25. Result: no proof of light absorption, no
counterexample. A paper reduction of light absorption to a smaller statement that lives entirely at the bottom
point `1_Q` (where the circuit is the monotone `C1`), and the exact obstacle.

Words: **paper** = argument written here; **tested** = computed (`A10_light_attack.py`, `A10_maxY_test.py`);
**checked** = Lean accepted it (nothing new is checked in this seat).

Notation as in `A7_dd_absorption.md`. State `(Q, D)`, `Q ∩ D = ∅`, `h` = the NOT gate's input (monotone),
`H0 = {h = 0}`, `P_u = 1_Q + e_u`, `Z_w = Zof(S_w ∪ D)`. For a DD set `w`: heavy atoms `U_w`, light atoms
`T_w`, `need_w = |T_w| − [U_w = ∅]`. Top family `top = ∪_{v non-DD} M_v ∪ ∪_{w DD} H_w` (A7). `E` = the OR
gates `g ∉ top` with `g(1_Q) = 0`.

## 0. Verdict

1. **Bottom runs pay every DD set in F2 (paper).** For a DD set `w`, run the unit form at the zero point `1_Q`
   over the atoms `P_u`, `u ∈ S_w \ D`, with the heavy atoms joined before the first gate. It makes exactly
   `need_w` merges, each an OR gate, and **each merge is in `F2Mix(Q, D)` with witness `Z = 1_Q`**. This
   includes the bridge from the heavy class to the light atoms, which A7 §3 named as an obstacle (bridge merges
   at `Z_w` need not be F2; at `1_Q` they always are).
2. **Reduction (paper).** Light absorption follows from **BOTTOM PAY**:

   > there are pairwise disjoint sets `E_w ⊆ E` (`w` DD) with `|E_w| ≥ need_w`, every `g ∈ E_w` being `1` at
   > `P_u` and `P_{u'}` for some `u ≠ u'` in `S_w \ D`.

   (Every such `g` is in `F2Mix` with witness `1_Q`, so `∪ E_w ⊆ F2Mix \ top` has `Σ need_w` elements.)
   The natural form of BOTTOM PAY is a matroid union (§3): each `E_w` a spanning forest of the `w`-classes
   (heavy class plus light singletons), one chosen pair per gate.
3. **The exact obstacle.** The bottom runs of item 1 are never in `top` in the data (0 states), but bottom runs
   of two DD sets share gates (2,775 of 136,843 DD states, n ≤ 9, every state), and **no choice of one zero
   point per DD set in `H0` avoids this** (242 states, `A10_maxY_test.py`; worked example §2). What pays there
   is a re-choice of edges: gates serving two DD sets are split between them (a matching), which no single
   union-find run does. BOTTOM PAY with forests holds at every tested state (below), but no proof.
4. **Tested.** 0 BOTTOM PAY failures (exact backtracking search for the disjoint forests) at all 136,843 DD
   states of the 160 stored circuits with n ≤ 9 (every mixed state), at 119,467 sampled DD states of 2,393
   stored circuits with n ≤ 16 (40 random states + root + singletons each), and at all 1,010,325 DD states of
   200 switch circuits (`--gen 200`, every state). Item 1 checked at the same states: 0 short runs, 0 non-OR
   merges, 0 merges outside F2, 0 bottom-run gates in `top`.
5. **Strength.** At the root of a circuit whose alive sets are all DD with no heavy atom (example §2), `top` is
   empty and BOTTOM PAY says `Σ (|S_w| − 1)` disjoint bottom forests exist, which implies `|F2| ≥ base` there.
   So it is not weaker than the theorem on such circuits (A7 item 4 shows no reformulation can be). What is
   smaller is the setting: one zero point `1_Q`, all relevant points in `H0` where the circuit equals the
   monotone `C1`, no F2-witness question, no heavy or bridge question.

## 1. Paper proof of items 1 and 2

Fix `(Q, D)` and a DD set `w`. `T_w ≠ ∅` gives `h(P_t) = 0`, so `h(1_Q) = 0`: the NOT gate is `1` at `1_Q`.

**Run.** Classes: `U_w` (if non-empty) and the singletons of `T_w`, so `need_w + 1` classes. Process gates in
order, skip a gate that is `1` at `1_Q`, and join the classes of the atoms where it is `1`. Invariant: every
processed wire that is `0` at `1_Q` has its `1`-atoms in one class. Inputs `x_v` (`v ∉ Q`) are `1` at one atom
at most. An AND gate `0` at `1_Q` has an input `0` at `1_Q` whose `1`-atoms contain its own: no merge. The NOT
gate is `1` at `1_Q`: skipped. An OR gate `0` at `1_Q` has both inputs `0` at `1_Q`, so it joins at most two
classes. The output of `w` is `0` at `1_Q` (`Q ∩ S_w = ∅`) and `1` at every atom, so at the end there is one
class. Hence exactly `need_w` merges, all OR gates, each joining two classes (so `1` at `P_u`, `P_{u'}`,
`u ≠ u'`, at least one light).

**F2.** A merging gate `g` is OR, `g(1_Q) = 0`, `g(1_Q + e_u) = g(1_Q + e_{u'}) = 1`, and `Z = 1_Q` is `1` on
`Q`, `0` on `S_w ∪ D`: an `F2WitMix` witness for `w` (alive). No NOT argument is needed for this step.

**Item 2.** Given BOTTOM PAY, each `g ∈ E_w` is an OR gate with the witness `1_Q` for `w`, so
`∪_w E_w ⊆ F2Mix \ top`, and disjointness gives `|F2Mix \ top| ≥ Σ_w |E_w| ≥ Σ_w need_w`. That is light
absorption. ∎

**Any zero point in H0 works for the count.** The run above at any `Y ≥ 1_Q` with `h(Y) = 0` and `Y = 0` on
`S_w ∪ D` also makes `need_w` OR merges, and they are in `E`-form: `g(Y) = 0` gives `g(1_Q) = 0` by
`sign_of_drop` (`1_Q ≤ Y`, `h(Y) = 0`). A higher `Y` blocks overlap partly: if `g` is in the run at `Y_b` and
`1` at `P_t` with `Y_b(t) = 1` and `t` light, then `P_t ≤ Y_b` in `H0` forces `g(Y_b) = 1`. Heavy coordinates
are always `0` in `Y_b`, and for maximal `Y_b` a light `t` is `0` only when `h(Y_b + e_t) = 1`. So runs of two
DD sets `a, b` can share a gate only through atoms of `S_a \ S_b` that are heavy or outside the support of
`Y_b` (and symmetrically).

## 2. Attack first: the overlap states

`A10_light_attack.py` reproduces A7's dead end (light runs at `1_Q` overlap at 282 of the stored n ≤ 9 DD
states; with the bridge included, 2,775) and tests two repairs:

| repair | result |
|---|---|
| line form at `Z_w` over all of `S_w \ D` (all merges are F2 at `Z_w`, since the whole run lies in `H1`), minus `H_w` | count and F2 hold (0 violations), but runs of DD sets overlap at 14,269 states and the union is short at 9,585: dead |
| one maximal `Y_w ∈ H0` per DD set (all choices tried) | 242 of 26,381 states have no disjoint choice: dead |
| re-choose edges (matroid union, BOTTOM PAY) | 0 failures anywhere |

Worked example (`research/one-not/data/witnesses/cx44_1_junk.json`, root state, n = 7): `S_0 = {0,1,2,3}`,
`S_1 = {0,4,5,6}`, `h = x1x2 ∨ x4x5`; every atom is light, both sets are DD, `top = ∅`, need `3 + 3`. The four
wires `x0 ∨ x_i ∨ x_j` (`i ∈ {1,2}`, `j ∈ {4,5}`) each join `{0, i}` for `S_0` and `{0, j}` for `S_1`. Each set
needs two of them plus its own last gate. Maximal `Y` for `S_0` are `{4,6}`, `{5,6}`; each kills one value of
`j`, and then the union-find takes the two surviving cross wires, which the other set's run (with `{1,3}` or
`{2,3}`) also takes. The payment that works is a matching: `S_0` gets `x0∨x1∨x4`, `x0∨x2∨x5`, `S_1` gets
`x0∨x1∨x5`, `x0∨x2∨x4`. That is the kind of choice BOTTOM PAY must make in general.

## 3. The open statement in matroid form

For a DD set `w` let `M_w` be the matroid on `E` induced from the graphic matroid on the `w`-classes: a set
`I ⊆ E` is independent when one can choose, for each `g ∈ I`, two `w`-classes both containing an atom where `g`
is `1`, so that the chosen pairs form a forest. Item 1 says `r_w(E) = need_w`. By the matroid union theorem,
BOTTOM PAY (with forests) holds iff

> for every `A ⊆ E`: `Σ_{w DD} (need_w − r_w(A)) ≤ |E \ A|`.

In words: deleting any `b` gates of `E` costs the DD sets at most `b` units of rank in total. In a monotone
circuit this holds because the top merges `M_w` are disjoint and are bases of the `M_w` (a gate `0` at `Z_w` is
`0` at `1_Q`). Here the light atoms have no top zero point in `H0`, which is the whole obstacle.

## 4. Sub-lemmas (on the board as OPEN (Sonnet) lines)

1. `bottom_F2WitMix`: item 1's F2 step (witness `canonPt Q`), no NOT hypothesis.
2. `bottom_zero_of_H0`: `canonPt Q ≤ Y`, `hval Y = false`, `val Y i = false` ⇒ `val (canonPt Q) i = false`.
3. `lightAbsorb_of_bottomPay`: item 2 as a Lean implication (`BottomPay` as a `Prop`).
4. A search seat: hill-climb for a BOTTOM PAY failure.
