# Quantum gravity and P versus NP

The quantum gravity program (gap ids `L-qg-NNN`). Its board is [`BOARD.md`](../../../../BOARD.md) at
the root of the repository.

## Mini board (final pass, 2026-11-24)

- State: 47 rows checked. Open gaps: L-qg-115, 116, 119, 169 (P_CTC inside EXP).
- The physics premises appear in no Lean statement. No row says that P versus NP is settled.
- References: kept in full in [`research/LITERATURE.md`](../../../../research/LITERATURE.md) section I.
- Up: [`BOARD.md`](../../../../BOARD.md), subboard "quantum gravity".

## What the program is for

Several arguments in quantum gravity are arguments about computational complexity: the
"complexity = volume" and "complexity = action" conjectures, the hardness of decoding Hawking
radiation, the hardness of the AdS/CFT dictionary, computers on closed timelike curves, and the
bounds on the number of states of a region. Each argument rests on a classical, finite core: a
counting bound, a fixed point, a reduction. This program states those cores in Lean, against the
definitions in [`Defs/QuantumGravity.lean`](../Defs/QuantumGravity.lean), and checks them.


## What it does not claim

A row of this program is "checked": the checker accepted a proof of the Lean statement. No row
says that P versus NP is settled. No row is a statement about quantum gravity: the physics
premises (the holographic bound, complexity = volume, the existence of closed timelike curves)
are named as premises in the plain-language text and appear in no Lean statement.

## Tracks

| Track | Physics argument | Classical core in Lean | Rows and gaps |
|---|---|---|---|
| A. Complexity growth | complexity = volume, complexity = action, second law of complexity | products of gates from a gate set (`ReachableIn`) | L-qg-001 to L-qg-007, gap L-qg-101 |
| B. Decoding Hawking radiation | Harlow and Hayden; Aaronson; Brakerski; the Python's lunch | one-way functions and P ≠ NP (`InvertibleInPolyTime`) | gap L-qg-103 |
| C. The AdS/CFT dictionary | Bouland, Fefferman and Vazirani | needs quantum definitions | none yet |
| D. Closed timelike curves | Deutsch; Brun; Aaronson and Watrous | Deutsch consistency (`DeutschConsistent`, `ctcSearchMap`); density matrices and channels in Kraus form (`IsDensityMatrix`, `IsKrausFamily`, `krausMap`) | L-qg-008, L-qg-009, L-qg-102, L-qg-120 to L-qg-127 |
| E. Bounds on states and speed | Bekenstein; the holographic bound; Lloyd; Margolus and Levitin | finite-state systems | L-qg-010 |
| F. Holographic codes | Pastawski, Yoshida, Harlow and Preskill | needs stabilizer code definitions | none yet |
| G. Geometry of circuits | Nielsen; Haferkamp et al. | needs Riemannian metrics on unitary groups; bridge to the GCT program | none yet |

## Rows and gaps

The board, [`BOARD.md`](../../../../BOARD.md), lists every row and every open gap with its column.
The open gaps are `Prop` definitions in [`Gaps.lean`](Gaps.lean); a proof of gap `L-qg-1NN` is a
file `L1NN.lean` in this directory that declares
`theorem PEqualNP.QuantumGravity.L1NN : PEqualNP.QuantumGravity.Gap.L1NN`.

## Files

| Path | What it is |
|---|---|
| `proofs/main/PEqualNP/Defs/QuantumGravity.lean`, `QuantumGravityCodes.lean`, `QuantumGravityCtc.lean`, `QuantumGravityChannels.lean` | the definitions every statement of the program is read against (`QuantumGravityChannels.lean`: density matrices on `Fin d`, channels in Kraus form) |
| `proofs/main/PEqualNP/QuantumGravity/LNNN.lean` | one checked row per file, one theorem named after its module |
| `proofs/main/PEqualNP/QuantumGravity/Helpers/` | the proofs the rows import |
| `proofs/main/PEqualNP/QuantumGravity/Gaps.lean` | the open gaps, as `Prop` definitions |

Build one row: `cd lean && lake build PEqualNP.QuantumGravity.L001`.

## References

Kept in full in [`research/LITERATURE.md`](../../../../research/LITERATURE.md) section I.
