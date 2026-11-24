# 951: one NOT gate saves nothing on (1,1)-disjoint Boolean sums

Rung 1 of the NOT gate ladder on the main board. This directory is a one-to-one copy of the 951 work
from the private repository addison-jpg/pequalnp-work:

| Here | Came from |
|---|---|
| `lean/PEqualNP/{W951,Kernel,Base,Defs}` | branch `coord-951`, head `ee11077`, the import closure of the 951 development (146 modules) |
| `work/`, `tools/`, `notes/`, `research/` | branch `coord-951`, same paths |
| `board/` | branch `board` (the 951 board: BOARD.md, PROTOCOL.md, paper951.md, agents/, research/, data/), frozen state |
| `front/` | branch `front-match` 169cec0, `work/notes951` (front's math notes: SORRY_DISSECTION.md, w9/ incl. RESUME_LANES.md, heavy/) |

`lean/` is a separate Lake project with the same Lean and Mathlib pins as `../lean`. It is kept apart
because its `Kernel/Circuit.lean` and `Defs` differ from `../lean/PEqualNP`, and mixing the two
would mean refactoring.

## State

Mini board of this directory (final pass, 2026-11-24). Up: [`../README.md`](../README.md) (the proof), [`../boards/one-not.md`](../boards/one-not.md) (the board of this directory). Names: [`../NAMES.md`](../NAMES.md).

- The only `sorry` is `no_minCE` in `lean/PEqualNP/W951/MinCE.lean`: there is no minimal counterexample.
- Checked: the statement holds when the certificate game (U-game) on the lifted outputs is won (`W951/UGame.lean`, `no_minCE_of_ugame`); when the NOT gate reads an input (`NotVarF2`); when every cube is local or has a point step (`CubeF2.lean`).
- Open: circuits that lose the certificate game (smallest: sets {0,1,2}, {0,3,4}, NOT input x1 ∨ x3; hard core: three 4-sets in a triangle, `cxT2`); the point step for real-witness gates (F2) among circuits with no gate-saving rewiring (R6).
- Dead: [`DEAD_ENDS.md`](DEAD_ENDS.md), seven families. The price inequality over REAL merge sets (`MergePrice`) is false without minimality (STAR4); the lifted forms are the target.
- Other proved routes to `no_minCE`: `no_minCE_of_liftClassFrac` (LiftFrac), `no_minCE_of_liftedBound` (LiftBound, equivalent to 951), `no_minCE_of_FJ` (LiftFJ), `no_minCE_of_mergePrice` (MergeFrac).
- Findings: [`FINDINGS_2026-11-24.md`](FINDINGS_2026-11-24.md). Notes by part of the route: [`board/agents/INDEX.md`](board/agents/INDEX.md). Witness circuits: `data/witnesses/`.
- Module map: `work/W951.md`. Guide for writing new Lean here: `work/TRACTABILITY.md`.

## Build and check

```bash
cd one-not/lean && lake build
```

```bash
cd 951 && bash work/bin/merge951.sh /tmp/W951_one.lean
```

The `lake build` must finish with exactly one `sorry` warning outside `PayDraft.lean`, which is a parked
draft. The `merge951.sh` script writes the whole development to one file. That file must compile with
0 errors and exactly 1 sorry. `#print axioms PEqualNP.Outside.L_meta_951` must show only propext,
sorryAx, Classical.choice and Quot.sound.

Checked when copied (2026-11-24, coord): full build OK, one-file 0 errors / 1 sorry, axioms as above.
