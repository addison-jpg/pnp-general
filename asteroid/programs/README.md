# asteroid programs: the formal proof as runnable files

One program per group of items of [`research/notes/front-page-2026-11-24.md`](../../research/notes/front-page-2026-11-24.md). Run one with `python3 -m asteroid run asteroid/programs/NAME.ath`, all with `python3 -m asteroid test [--no-lean]`.

| Program | README items | What it checks | Python claims / Lean theorems | Time (Lean / no Lean) |
|---|---|---|---|---|
| `programs/theorem.ath` | Theorem, D5, D8, T3, T4 | all 15 witness circuits with n <= 9: correct (kernel), `gates >= base`, the count `slack >= 0` (kernel), 0 tight by gates / how many tight by count; a one-NOT circuit written in the script with `forall cubes slack >= 0` (16 cubes) and the Fano formula (128 cubes) in the kernel | 10 / 33 | 49 s / 1 s |
| `programs/refuted.ath` | section 5: C2 (twin trees, matched twin trees), pointwise 0-step (Pappus), induction on 0 (Fano), pure-class SDR (cxMU), price inequality (star4b), C4w | seven blocks, each with its counterexample file; the C2 step margin is below 0 on twin_tree_f2step and match_c_k7, the any-gate witness count is below base on general_count_below_base_min / t4 (kernel for the 4-NOT circuit); the count and `gates >= base` hold on every one | 28 / 2 | 32 s / 18 s |
| `programs/open.ath` | C1/C2/C4, the open step of `no_minCE` | conjectures `count`, `mixed` (MixedStep at all states), `flip` (C4 flip classes), `c2norewire` over 14 circuits, then `hunt` 8 s each (no counterexample) | 4 / 0 (3 hunts) | 30 s / 30 s |
| `programs/ladder.ath` | T6, C4, C4w, Theorem | rung 0 (circuits with no NOT gate: count >= 0 and `gates >= base`, kernel) against the four many-NOT files (all have `witness < base`, all have `gates >= base`, flip classes >= 0) | 10 / 6 | 15 s / 1 s |
| `programs/pictures.ath` | D8, L5 | plot phi for the twin tree, MATCH-C, Pappus, Fano; histograms of slack and gates over the corpus | 1 / 0 (6 PNGs in `asteroid/out/`) | 2 s / 2 s |

`python3 -m asteroid test` runs them (with Lean 2 min 44 s for examples and programs together; `--no-lean` 68 s).

### What the language cannot yet say (`# WISH:` lines in the programs)

1. Implication / hypothesis in a corpus claim: `forall c in W: nots(c) <= 1 -> gates(c) >= base(c)`, and the Theorem's other hypotheses (`sets_ok(c)`: every set has at least 2 points, two sets share at most one point).
2. Mixed-state quantifiers over single points: `exists v: mslack(c, {}, {v}) < 0`; pointwise gain and cost of a 0-step and 1-step (`gain0`, `cost0`, `gain1`, `cost1`), needed for the Pappus row and the induction-on-0 row.
3. Merge sets, pure classes and a system-of-distinct-representatives test (`sdr(pure_classes(c))`), and the fractional price of a gate (cxMU and star4b rows).
4. A negated claim over a corpus (`forall c in N: not (...)`) instead of two counts.
5. A Lean form for `gates(c) >= base(c)` (the Theorem has no kernel statement; only the OR-only count does) and for `witness` soundness.
6. `C3 two-point step` at k = 2 on the matched twin trees at n >= 16 is too slow in the registry (minutes), so the C3_k refutation is not shown.
7. Kernel claims for n = 14 to 16 (twin trees): tables of 16,384 inputs time out (a `correct` claim on the twin tree took more than 2 minutes).

### New in edges (for the docs seat)

Extension `asteroid/ext_edges.py`; program `programs/edges.ath` (Lean 28 s / no Lean 1 s; 26 Python claims, 15 kernel theorems); unit test `tests/test_edges.py`. Core change: `asteroid.py` has `EXTRA_F` (a dict name -> function of a circuit) and two lines at the top of `F` that consult it.

Grammar lines:

    F(NAME) OP RHS           F also in  flip flipclasses flipslack   (Python only; "Python only" is printed under `by lean`)
    claim hyps(NAME) [= true|false] [by lean]
    claim if EXPR1 then EXPR2                       also  claim forall c in W: if EXPR1 then EXPR2
    claim EXPR1 and EXPR2 [and ...] [by lean]       each part is any claim expression; Lean claims of each part are emitted
    claim theorem(NAME) [by lean]
    note (printed, not a claim)                     `note: NAME has k NOT gates; slack counts OR witnesses (the one-NOT count); use flipslack for several NOT gates`
                                                    whenever slack / orwitness / phi / forall cubes slack is used on a circuit with more than one NOT gate

Verb-table rows:

| Form | Meaning |
|---|---|
| `flip(c)` | gates whose value changes (either direction) from a zero point of a set to two of its atoms (`conjectures._flip_gates`, mode flip) |
| `flipclasses(c)` | flip gates counted once per function up to complement |
| `flipslack(c)` | `flipclasses(c) - base(c)`; equals `margin["C4 count (flip classes)"](c)` (checked on every witness file with n <= 9 and the 4 many-NOT files); the repaired count for several NOT gates |
| `hyps(c)` | the Theorem's other hypotheses, identical to `hypsB` (AsteroidCheap.lean): sets nodup and < n, one output wire per set, at least one gate, every set at least 2 points, two sets share at most 1 point, at most one NOT gate. Lean: `hypsB c = true` (or `= false` for `hyps(c) = false`) by `decide +kernel` |
| `if A then B` | true when A is false or B is true; Python only |
| `A and B` | both; with `by lean` each part keeps its own Lean form |
| `theorem(c)` | `if hyps(c) and correct(c) then gates(c) >= base(c)`; Lean (when the hypotheses hold): `hypsB`, `correctB` and `(c.sets.map (fun S => S.length - 1)).sum ≤ c.gates.length`, three kernel theorems. A script `conjecture theorem: ...` shadows the builtin |

Done from the WISH list above: items 1 (implication, hypotheses), 4 (negated claim: `claim not if ...` and `not hyps(c)`), 5 (Lean form for `gates >= base` through `theorem(c)`).
