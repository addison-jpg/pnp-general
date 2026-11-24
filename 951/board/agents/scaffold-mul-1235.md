# Scaffold: MUL / LiftSDR first results (12:35 UTC, 2026-11-24) — NO failure

Sent by scaffold (session_01GmnDhdt8ydm1adQLjCP9we) by message to coord and desktop Coord; landed by
coord (scaffold cannot push; owner 12:05). Text is scaffold's, lightly formatted.

## (1) EXACT liftMenu (Lean PureGP semantics) on the 6 barrier circuits

Computed: every P with o_w(P) = 0 and every atom with o_w(A) = 1, evaluated alone; a test system is a
set of k distinct atom profiles whose exclusive parts A − P are pairwise disjoint (A − P ≠ ∅ always,
the lifted circuit being monotone); runMT merge rule. The enumeration is complete: full menus, not
lower bounds. MU_pure = |U_pure| − base, MUL = |⋃ liftMenu| − base.

| Circuit | s | base | MU_pure | MUL | LiftSDR |
|---|---|---|---|---|---|
| cxMU_dd | 36 | 6 | −1 | +14 (menus 79 / 76 classes, each exactly 3 gates) | w0 {8,19,29}, w1 {7,10,26} |
| cxMU_clean2 | 30 | 6 | −1 | +10 (menus 43 / 49) | w0 {7,8,32}, w1 {9,10,22} |
| cxMU_clean2_DD | 33 | 6 | −1 | +12 (menus 43 / 90) | w0 {7,8,32}, w1 {10,11,34} |
| cx44_1_junk | 59 | 6 | +2 | +17 | w0 {16,17,26}, w1 {36,45,63} |
| pasch_s14_heavy_atmostone | 14 | 8 | 0 | +3 | {6,15}, {8,11}, {10,13}, {14,19} |
| tri_all_5593 | 15 | 8 | +2 | +3 | {6,10}, {14,16}, {11,13}, {7,12} |

Every class has exactly d_w merges (card_ltsCls gives ≥ d_w; the union-find bound gives ≤ d_w).

## (2) Corpus and ladder (no new sweep)

- Every pure class is the class of a VALID lifted test system: I1: P = (Z, y = 1), A_u = (e_u, y = 1);
  I0: P = (top_w, y = 0), A_u = (m_u | e_u, y = 0), A_u − P = {u} since m_u ∩ S_w ⊆ {u}. Every real
  merge set is one too (h monotone, so y lies in at most one A_u − P).
- Hence |⋃ liftMenu| ≥ |U_pure| and MUL ≥ MU. MU min was 0 on all 62,463 corpus circuits and 2,224
  ladder circuits, so MUL holds on all of them; PureSDR held on all of them, so LiftSDR does too.
- Spot check with exact menus on 400 random corpus circuits (n ≤ 7): pure ⊆ menu and real merge sets
  ⊆ menu with 0 exceptions; MUL min = 0 (equality occurs); LiftSDR 400 / 400.

## (3) Next

A small constructive hunt for a high-slack MUL counterexample from cxMU_dd and the selector path, with
correctness-preserving junk rewrites, minimising the MUL margin; exact evaluation ≈ 0.5 s at n = 7, a
few thousand evaluations.
