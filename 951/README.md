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

- The only `sorry` is `no_minCE` in `lean/PEqualNP/W951/MinCE.lean`: there is no minimal counterexample.
- The open target in its sharpest Lean form is `MergePrice` for a minimal counterexample.
  This is the dual load inequality: for all prices pi >= 0, sum_w min_z pi(M_z(w)) <= pi(gates).
  `no_minCE_of_mergePrice` is proved in `MergeFrac.lean`.
- Other proved routes to `no_minCE`:
  - `no_minCE_of_liftClassFrac` (LiftFrac)
  - `no_minCE_of_liftedBound` (LiftBound, equivalent to 951)
  - `no_minCE_of_FJ` (LiftFJ)
- Module map: `work/W951.md`. Guide for writing new Lean here: `work/TRACTABILITY.md`.

## Build and check

```bash
cd 951/lean && lake build
```

```bash
cd 951 && bash work/bin/merge951.sh /tmp/W951_one.lean
```

The `lake build` must finish with exactly one `sorry` warning outside `MiscSmall.lean` (section `PayDraft`), which is a parked
draft. The `merge951.sh` script writes the whole development to one file. That file must compile with
0 errors and exactly 1 sorry. `#print axioms PEqualNP.Outside.L_meta_951` must show only propext,
sorryAx, Classical.choice and Quot.sound.

Checked when copied (2026-11-24, coord): full build OK, one-file 0 errors / 1 sorry, axioms as above.
