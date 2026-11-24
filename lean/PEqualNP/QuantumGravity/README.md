# Quantum gravity and P versus NP

The quantum gravity program (gap ids `L-qg-NNN`). Its board is [`BOARD.md`](../../../BOARD.md) at
the root of the repository.

## Mini board (final pass, 2026-11-24)

- State: 47 rows checked. Open gaps: L-qg-115, 116, 119, 169 (P_CTC inside EXP).
- The physics premises appear in no Lean statement. No row says that P versus NP is settled.
- References: kept in full in [`LITERATURE.md`](../../../LITERATURE.md) section I.
- Up: [`BOARD.md`](../../../BOARD.md), subboard "quantum gravity".

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

## How P versus NP enters

There are two routes, and neither can settle P versus NP.

1. **Assumption route.** A quantum gravity argument that a task is hard assumes a cryptographic
   primitive. When the primitive is a classical one-way function, P ≠ NP follows from it (gap
   L-qg-103). So if P = NP, every hardness argument that rests on classical one-way functions
   fails. Arguments that rest only on quantum primitives (pseudorandom quantum states, EFI pairs)
   are not known to imply P ≠ NP: Kretschmer gives an oracle relative to which pseudorandom
   quantum states exist and BQP = QMA.
2. **Model route.** The physics fixes the model of computation. If closed timelike curves exist,
   one pass of a polynomial-size circuit decides satisfiability (core: L-qg-009). If the
   holographic bound holds, a computer confined to a region is a finite-state system (core:
   L-qg-010). "NP-complete problems are intractable in the physical world" (Aaronson) is a
   statement about which models physics allows, not a statement about P versus NP.

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

The board, [`BOARD.md`](../../../BOARD.md), lists every row and every open gap with its column.
The open gaps are `Prop` definitions in [`Gaps.lean`](Gaps.lean); a proof of gap `L-qg-1NN` is a
file `L1NN.lean` in this directory that declares
`theorem PEqualNP.QuantumGravity.L1NN : PEqualNP.QuantumGravity.Gap.L1NN`.

## Files

| Path | What it is |
|---|---|
| `lean/PEqualNP/Defs/QuantumGravity.lean`, `QuantumGravityCodes.lean`, `QuantumGravityCtc.lean`, `QuantumGravityChannels.lean` | the definitions every statement of the program is read against (`QuantumGravityChannels.lean`: density matrices on `Fin d`, channels in Kraus form) |
| `lean/PEqualNP/QuantumGravity/LNNN.lean` | one checked row per file, one theorem named after its module |
| `lean/PEqualNP/QuantumGravity/Helpers/` | the proofs the rows import |
| `lean/PEqualNP/QuantumGravity/Gaps.lean` | the open gaps, as `Prop` definitions |

Build one row: `cd lean && lake build PEqualNP.QuantumGravity.L001`.

## References

- J. D. Bekenstein, Universal upper bound on the entropy-to-energy ratio for bounded systems,
  Phys. Rev. D 23 (1981) 287.
- K. Kraus, States, Effects, and Operations, Lecture Notes in Physics 190, Springer (1983).
- D. Deutsch, Quantum mechanics near closed timelike lines, Phys. Rev. D 44 (1991) 3197.
- N. Margolus, L. B. Levitin, The maximum speed of dynamical evolution, Physica D 120 (1998) 188.
- S. Lloyd, Ultimate physical limits to computation, Nature 406 (2000) 1047.
- R. Bousso, The holographic principle, Rev. Mod. Phys. 74 (2002) 825, arXiv:hep-th/0203101.
- T. A. Brun, Computers with closed timelike curves can solve hard problems efficiently, Found.
  Phys. Lett. 16 (2003) 245, arXiv:gr-qc/0209061.
- S. Aaronson, NP-complete problems and physical reality, SIGACT News 36 (2005),
  arXiv:quant-ph/0502072.
- M. A. Nielsen, A geometric approach to quantum circuit lower bounds, Quantum Inf. Comput. 6
  (2006) 213, arXiv:quant-ph/0502070.
- S. Aaronson, J. Watrous, Closed timelike curves make quantum and classical computing
  equivalent, Proc. R. Soc. A 465 (2009) 631, arXiv:0808.2669.
- D. Harlow, P. Hayden, Quantum computation vs. firewalls, JHEP 06 (2013) 085, arXiv:1301.4504.
- D. Stanford, L. Susskind, Complexity and shock wave geometries, Phys. Rev. D 90 (2014) 126007,
  arXiv:1406.2678.
- L. Susskind, Computational complexity and black hole horizons, Fortsch. Phys. 64 (2016) 24,
  arXiv:1402.5674.
- F. Pastawski, B. Yoshida, D. Harlow, J. Preskill, Holographic quantum error-correcting codes:
  toy models for the bulk/boundary correspondence, JHEP 06 (2015) 149, arXiv:1503.06237.
- A. R. Brown, D. A. Roberts, L. Susskind, B. Swingle, Y. Zhao, Holographic complexity equals
  bulk action?, Phys. Rev. Lett. 116 (2016) 191301, arXiv:1509.07876.
- S. Aaronson, The complexity of quantum states and transformations: from quantum money to black
  holes, lecture notes (2016), arXiv:1607.05256.
- A. R. Brown, L. Susskind, Second law of quantum complexity, Phys. Rev. D 97 (2018) 086015,
  arXiv:1701.01107.
- Z. Ji, Y.-K. Liu, F. Song, Pseudorandom quantum states, CRYPTO 2018, arXiv:1711.00385.
- A. R. Brown, H. Gharibyan, G. Penington, L. Susskind, The Python's lunch: geometric obstructions
  to decoding Hawking radiation, JHEP 08 (2020) 121, arXiv:1912.00228.
- A. Bouland, B. Fefferman, U. Vazirani, Computational pseudorandomness, the wormhole growth
  paradox, and constraints on the AdS/CFT duality, ITCS 2020, arXiv:1910.14646.
- W. Kretschmer, Quantum pseudorandomness and classical complexity, TQC 2021, arXiv:2103.09320.
- J. Haferkamp, P. Faist, N. B. T. Kothakonda, J. Eisert, N. Yunger Halpern, Linear growth of
  quantum circuit complexity, Nature Physics 18 (2022) 528, arXiv:2106.05305.
- Z. Brakerski, Black-hole radiation decoding is quantum cryptography, CRYPTO 2023,
  arXiv:2211.05491.
