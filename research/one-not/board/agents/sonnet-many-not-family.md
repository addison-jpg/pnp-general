Serves README item C4 (task family-for-many-not-gates)

Author: main's Sonnet A, 2026-11-24. Tested, not proved.

## Counterexample (minimal)

`research/one-not/data/witnesses/nonlocal/general_count_below_base_min.json`, found by `research/one-not/tools/search/minimise.py` from each of `general_count_below_base_t4/_t5/_t6` (67, 52, 65 gates). All three reduce to the same circuit: **10 gates, 4 NOT gates**, n = 7, sets {0,1,2,3} and {0,4,5,6}, base 6, **5 witness gates**. Local minimum under: replace a gate by any earlier wire, rewire one input, prune. Checked with `core.witness`, the independent `witness_any_gate.py` witness function (both give gates 8, 9, 10, 11, 16) and `core.correct`.

Wires (7 = NOT x0 is read only by wire 14):

| wire | gate | function | witness for |
|---|---|---|---|
| 7 | NOT x0 | ¬x0 | no (1 at Z) |
| 8 | x0 ∨ x1 | | set 0 |
| 9 | 8 ∨ x2 | x0∨x1∨x2 | set 0 |
| 10 | 9 ∨ x3 | OR(S0), output 0 | set 0 |
| 11 | x4 ∨ x5 | | set 1 |
| 12 | NOT 11 | ¬(x4∨x5) | no (1 at Z) |
| 13 | NOT x6 | ¬x6 | no (1 at Z) |
| 14 | 13 ∧ 7 | ¬x6 ∧ ¬x0 | no (1 at Z) |
| 15 | 12 ∧ 14 | NOR(x0,x4,x5,x6) | no (1 at Z) |
| 16 | NOT 15 | OR(S1), output 1 | set 1 |

## Mechanism

Set 0 is an ordinary OR chain: 3 gates, 3 witnesses. Set 1 is built by De Morgan as NOT(NOT(x4∨x5) AND (NOT x6 AND NOT x0)): the three merges of its four atoms are x4+x5, x0+x6, and (x4,x5)+(x0,x6). Only the first and the last are made by gates that are 0 at Z = 0 and rise at two atoms (wires 11 and 16). The middle merge x0+x6 is made by wire 14, an AND of two negations, which is 1 at Z and falls at x0 and at x6: it merges two atoms, but in the other direction, so the witness condition (g(Z) = 0) never sees it. Likewise wire 12 and wire 15 are the falling twins of 11 and 16, the same merges seen from the other side. So 3 merges of set 1 are made by 5 gates (11, 12, 14, 15, 16), only 2 of which are witnesses, and the count is 3 + 2 = 5 < 6. The merges are hidden behind a gate that is already 1 at Z. No XOR-like behaviour is used, and the NOT gates are plain complement gates; the only price is that x0 is shared by both sets, which lets the x0+x6 merge be done once by a falling gate. 4 NOT gates (7, 12, 13, 16) are the minimum found.

## Candidate families

Checked on every file of `research/one-not/data/witnesses/*.json` and `nonlocal/*.json` with n <= 9 (19 files, including the minimal counterexample, on which the old count gives 5 < 6). Hunt: `hunt.py "<name>" 240 6 1`, starts are the top-level witness files with n <= 8 and their OR trees. Registered in `research/one-not/tools/search/conjectures.py`.

| name | definition | holds on N of N files | hunt result |
|---|---|---|---|
| C4 count (flip) | gates g with g(Z+e_u) != g(Z) at two atoms u of one set, Z a zero point of that set (change in either direction); count >= base. On the minimal counterexample: 8 >= 6 | 19 of 19 | 240 s, 6 NOT, seed 1: 660648 mutations, 0 counterexamples, least margin 0. Tested |
| C4 count (split) | flip, or g takes two different values at two atoms Z+e_u, Z+e_u' (XOR-like). Weaker than flip (a superset), so it survives whenever flip does; on the minimal counterexample 10 >= 6 | 19 of 19 | 240 s, 6 NOT, seed 1: 1821876 mutations, 0 counterexamples, least margin 0. Tested, but weak |
| C4 count (flip classes) | flip gates counted once per function up to complement (g, NOT g and copies are one class). On the minimal counterexample exactly 6 = base (classes: wires 8, 9, 10, 11/12, 14, 15/16) | 19 of 19 | 240 s, 6 NOT, seed 1: 717294 mutations, 0 counterexamples, least margin 0. Tested; the sharpest of the three because it is tight on the minimal counterexample |

Caveats: the hunter is a local search starting from n <= 8 files, so "no counterexample" is only a test. Note that I accidentally ran the flip and flip-classes hunts partly in parallel (two processes for about 2 minutes); results are unaffected. Margin 0 in the hunts is reached by plain OR trees, so it does not show the families are tight everywhere.
