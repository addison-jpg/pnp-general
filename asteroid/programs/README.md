# asteroid programs: the formal proof as runnable files

One program per group of items of [`notes/front-page-2026-11-24.md`](../../notes/front-page-2026-11-24.md). Run one with `python3 -m asteroid run asteroid/programs/NAME.ast`, all with `python3 -m asteroid test [--no-lean]`.

| Program | README items | What it checks | Python claims / Lean theorems | Time (Lean / no Lean) |
|---|---|---|---|---|
| `programs/theorem.ast` | Theorem, D5, D8, T3, T4 | all 15 witness circuits with n <= 9: correct (kernel), `gates >= base`, the count `slack >= 0` (kernel), 0 tight by gates / how many tight by count; a one-NOT circuit written in the script with `forall cubes slack >= 0` (16 cubes) and the Fano formula (128 cubes) in the kernel | 10 / 33 | 49 s / 1 s |
| `programs/refuted.ast` | section 5: C2 (twin trees, matched twin trees), pointwise 0-step (Pappus), induction on 0 (Fano), pure-class SDR (cxMU), price inequality (star4b), C4w | seven blocks, each with its counterexample file; the C2 step margin is below 0 on twin_tree_f2step and match_c_k7, the any-gate witness count is below base on general_count_below_base_min / t4 (kernel for the 4-NOT circuit); the count and `gates >= base` hold on every one | 28 / 2 | 32 s / 18 s |
| `programs/open.ast` | C1/C2/C4, the open step of `no_minCE` | conjectures `count`, `mixed` (MixedStep at all states), `flip` (C4 flip classes), `c2norewire` over 14 circuits, then `hunt` 8 s each (no counterexample) | 4 / 0 (3 hunts) | 30 s / 30 s |
| `programs/ladder.ast` | T6, C4, C4w, Theorem | rung 0 (circuits with no NOT gate: count >= 0 and `gates >= base`, kernel) against the four many-NOT files (all have `witness < base`, all have `gates >= base`, flip classes >= 0) | 10 / 6 | 15 s / 1 s |
| `programs/pictures.ast` | D8, L5 | plot phi for the twin tree, MATCH-C, Pappus, Fano; histograms of slack and gates over the corpus | 1 / 0 (6 PNGs in `asteroid/out/`) | 2 s / 2 s |

`python3 -m asteroid test` runs them (with Lean 2 min 44 s for examples and programs together; `--no-lean` 68 s).

### What the language cannot yet say (`# WISH:` lines in the programs)

1. Implication / hypothesis in a corpus claim: `forall c in W: nots(c) <= 1 -> gates(c) >= base(c)`, and the Theorem's other hypotheses (`sets_ok(c)`: every set has at least 2 points, two sets share at most one point).
2. Mixed-state quantifiers over single points: `exists v: mslack(c, {}, {v}) < 0`; pointwise gain and cost of a 0-step and 1-step (`gain0`, `cost0`, `gain1`, `cost1`), needed for the Pappus row and the induction-on-0 row.
3. Merge sets, pure classes and a system-of-distinct-representatives test (`sdr(pure_classes(c))`), and the fractional price of a gate (cxMU and star4b rows).
4. A negated claim over a corpus (`forall c in N: not (...)`) instead of two counts.
5. A Lean form for `gates(c) >= base(c)` (the Theorem has no kernel statement; only the OR-only count does) and for `witness` soundness.
6. `C3 two-point step` at k = 2 on the matched twin trees at n >= 16 is too slow in the registry (minutes), so the C3_k refutation is not shown.
7. Kernel claims for n = 14 to 16 (twin trees): tables of 16,384 inputs time out (a `correct` claim on the twin tree took more than 2 minutes).
