# Resolution gadget: precise statements (research-desktop, W951/Gadget.lean)

Notation (Lean names): `Clean Q gs c` = wire c is below OR Q (false on the cube x|_Q = 0); `unitsIn Q gs c` = units
e_u, u in Q, where c is true; `Dr Q gs` = Theorem E's class (clean gate wires with >= 2 units of Q; Lemma K's Ded3
part of Pi_w, so |Pi_w| < d_w implies |Dr| < d_w); hard = not `NotQuiet` (h(Z_S) = 1).
`ResAt Q gs k`: gate k is clean and is a NOT gate, or an AND `a ∧ b` whose inputs are both NOT clean (in the prefix
it reads). The general resolution form: `a ∧ b <= OR Q`, and a, b are each true somewhere on the cube, never together
("(A ∨ p) ∧ (A ∨ q) with p ∧ q = 0 off Q", with A = the gate).

## Proved (no sorry; axioms propext, Classical.choice, Quot.sound)
1. `gadget_count` (ANY circuit, AND/OR/NOT fan-in <= 2, any number of NOTs, wire o computing OR Q):
   |Q| <= 1 + |Dr Q| + sum over ResAt gates k of (|units_Q(k)| - 2).
   Union-find on units over clean wires: OR merges 2 classes, AND with a clean input / copies merge none; only
   uncovered clean gates can merge more. Theorem E is the case without such gates.
2. `gadget_exists`: |Dr Q| < |Q| - 1 => a ResAt gate with >= 3 units.
3. `resAt_and`: with at most one NOT, it is an AND with two unclean inputs (a clean NOT wire has no unit).
4. `res_polluted`: in such an AND, a, b are disjoint on the cube, each true on it, and one input t is true at a cube
   point where its C0 value (NOT := false) is false: t is true there only because of the NOT.
5. `MinCE.gadget`: in a minimal counterexample, (base - s) + 1 <= sum_w resExcess(S w) (so >= 2), and some HARD w with
   |Dr (S w)| < d_w has a resolution AND (clean, >= 3 units, inputs unclean, one NOT-polluted on the cube).
   Uses `notWires_add_sum_dr_le` (#NOT + sum_w |Dr (S w)| <= s).

## Data check
- scaffold's 4 SAT circuits (f15/logs/h4; s-base 5..7): count tight, d_w = 3, |Dr| = 2, excess 1, one resolution AND,
  polluted input found. 571 random correct one-NOT circuits: no failure of 1 or 4.
- cxstar5 (front-match w9/g3, set {1..5}): d = 4, |Dr| = 2, gate 13 = ¬x0 ∧ (x0|x1|..|x5) is a ResAt gate, 5 units,
  excess 3. So the referee's "no resolution" case (Shannon split) IS covered by the general form.
- cfgI (w9/fc, sets {0123}, {0456}): count holds (excess 1 and 2).

## Strict forms: NOT theorems (stated as `Prop`s only: `StrictGadget`, `PartialOrGadget`)
- STRICT: {a, b} = {A ∨ y, A ∨ ¬y}, y = h with x_S := 0. FALSE in general (referee dwV8p, REPORT2 §2, board
  agents/dwV8p-referee-gadget.md): cxstar5 / cxstar44 (Shannon split, OR(S) = (¬y ∧ (y ∨ A)) ∨ (y ∧ A), y = x0 = h),
  cxP1-3 (no strict resolution); cfgI set {0,1,2,3}: (A ∨ (x7 ∧ h)) ∧ (A ∨ ¬h) (p is not h|off S); cxP5, cxP6.
  Holds on all circuits with s - base <= 7 (thin data). No data for an actual MinCE (none known to exist).
- "A is a partial OR of S_w" (gate = OR of its units): FALSE in general: n = 5, gates x0|x2, x3|x4, ¬x0, copy,
  g5|g6, AND(g9, g8), x2|g6 (Q = {2,3,4}): gate 10 = ¬x0 ∧ (x2|x3|x4), ResAt with 3 units, not x2|x3|x4
  (a dead gate; found once in 200k random circuits).
- "|S_w| >= 4" for the deficient w: not derived. |S_w| = 3 with the output itself being the resolution AND is
  not excluded by the count (`MinCE.hard4` separately gives a hard 4-set, not tied to the deficit).
- "Polluted gates die under a restriction fixing y": no precise general version; y = h|off S need not be a
  variable (q example: y = x4 | x6), and the empirical single-variable death (24/24 strict cases) has no proof.
  Lean-level gap: needs a restriction lemma tying `res_polluted`'s point to `Kernel/W951Cube` deadness.

Version proved: the general form (b) (1-5 above).
