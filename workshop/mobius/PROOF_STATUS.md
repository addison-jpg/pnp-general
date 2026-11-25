# Mobius tube: proof status

Spec: `workshop/mobius/SPEC.md`. Runs on 2026-11-25 with `bin/asteroid --no-lean FILE.ath`, frames sent to a scratch file. No record lines, so no `findings.jsonl` was written.

## Runs

| file | true | false | exit |
|---|---|---|---|
| `checks/twist.ath` | 10 | 0 | 0 |
| `checks/pipeline.ath` | 5 | 5 | 1 |
| `checks/pipeline_val.ath` | 6 | 0 | 0 |

`checks/pipeline.ath` is kept as it was run. Its five `claim worlds` lines (lines 14, 15, 17, 23, 24) printed FALSE with "P has no valuation" (or "Pin has no valuation"): asteroid refuses `claim worlds` on a frame without `val`. Those five are false in that file, and the result stands. `checks/pipeline_val.ath` is a separate file that states the same five sentences (plus one more) on frames with a valuation. It is reported as its own run, not as a repair of the first.

## Proved (checked-finite)

| statement | check |
|---|---|
| The twist on the end grid x = k/5 is a function, total, symmetric, and its own inverse (an involution) | `twist.ath` T1, T2, T3, T4 |
| The twist swaps the two ends, so no end point is fixed (each orbit is a 2-cycle) | `twist.ath` T5 |
| The twist sends the left half to the right half and back; the untwisted cylinder keeps each half (control) | `twist.ath` T6, T7 |
| x -> 1 - x composed with itself is the identity at all 1001 points of the grid k/1000 | `twist.ath` T8 |
| The number of grid points k/N with 1 - x = x is 1 for even N and 0 for odd N, N = 0..9 | `twist.ath` T9 |
| The bus order 0, 1, 2, 3 is strictly increasing, so no stop repeats | `pipeline.ath` O1 |
| Each stop has at most one output and at most one input | `pipeline.ath` O4 |
| No walk of 4 hand-offs exists, either way (no cycle); the 3-step walk starts only at the coordinator; stops 0..2 have an output and 1..3 an input | `pipeline_val.ath` V1, V2, V3 |
| Walking back 3 hand-offs from the last bus reaches the coordinator | `pipeline_val.ath` V4 |
| For m = 1..8 pushes on integer parameters, the squared gaps sum to 0 and the pushes cover length m | `pipeline.ath` O6, O7 |

Each of these is about the finite model in `SPEC.md`, not about a measured run of the pipeline.

## Reasoning only (not checked)

- The quotient map q is continuous (definition of the quotient topology).
- Each bus map beta_i and the coordinator c are continuous (composition with q; a map from a finite discrete set).
- The hand-offs match: beta_i(1) = beta_(i+1)(0), and one lap lands on the mirror input q(1 - x, 0). The finite shadow of this (T3, T8) is checked; the statement on all of [0,1] is algebra, not run.
- Smoothness of the hot dog across hand-offs.

## Open

- **Continuity of the tube (C1).** "The front-to-main path is continuous" is a topological claim. No Lean statement in the repository backs it, and no checked finite statement can: a finite grid check says nothing about continuity on [0,1]. It is not proved here. It is the pasting lemma for a finite closed cover, a standard theorem, cited and not checked.
- The plain phrase "a path that never leaves the tube is continuous" is not true as written (a map can stay in the strip and jump). `SPEC.md` replaces it with C1.
- The coordinator `baby.ath` does not exist in the repository. Its map c is specified only.
- The pipeline order (coordinator, `bus.ath`, `laws.ath`, `general.ath`) is a design choice, not read from running code.
- Bus laws L3 and L4 remain open in `workshop/bus/laws.ath`, as before.
- Every field row of `SPEC.md` (d) except the finite combinatorics row is analogy or open.
- The ~ATH catch-22 link stays a reading, not checked.
- No earlier Mobius-strip mapping of the pipeline exists in the repository; there is nothing earlier to cite.
