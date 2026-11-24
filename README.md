# pnp-general (by addison mccarl)
disclaimer that a lot of the readmes are vibecoded. 
the higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it. 

P versus NP through general circuits: lower bounds for circuits of AND, OR and NOT gates with
any number of NOT gates, attacked with circuit complexity, quantum gravity and pure mathematics.
Every claim is a Lean 4 statement that the checker accepted against a pinned Mathlib; the word
for that is "checked".

- **The board:** [`BOARD.md`](BOARD.md): targets, the NOT gate ladder, the track pairs
  between the P versus NP tracks and their quantum gravity counterparts, roles, next steps.
- **The targets in Lean:** [`lean/PEqualNP/General/Gaps.lean`](lean/PEqualNP/General/Gaps.lean).
- **Where the problem stands:** the best lower bounds for explicit functions on unrestricted
  circuits are linear in the number of inputs; a superpolynomial bound for an NP language would
  give P ≠ NP. Three checked barrier rows (relativization, algebrization, natural proofs) say
  which kinds of argument cannot work.

| Path | What it is |
|---|---|
| `lean/` | the Lean project: pinned toolchain and Mathlib, definitions under `PEqualNP/Defs/`, one program per directory |
| `lean/PEqualNP/General/` | the general program (ids `L-gen-NNN`) |
| `lean/PEqualNP/QuantumGravity/` | the quantum gravity program (ids `L-qg-NNN`) |
| `tools/` | the build queue and the checker |
| `notes/` | write-ups |

Build one row: `cd lean && lake exe cache get && lake build PEqualNP.General.L001`. Never run
`lake update`.

The Lean project started from `brilliant-hq/pequalnp-proofs` (Apache License 2.0, see
[`LICENSE.md`](LICENSE.md)); earlier work is frozen in `addison-jpg/pequalnp-work`.

## Mini board

Front page: this file, [`BOARD.md`](BOARD.md) (the board), [`SYNTHESIS.md`](SYNTHESIS.md) (one page: how it fits, what is checked, open, refuted), [`NAMES.md`](NAMES.md) (formal names), [`LITERATURE.md`](LITERATURE.md) (everything read). Longer write-ups are leaves under `notes/`.

- State: `L_meta_951` is checked when the certificate game is won; 47 quantum gravity rows and `Fischer.L104` are checked.
- Open: `L_meta_951` for circuits that lose the certificate game; L-gen-101 to 103; L-qg-115, 116, 119, 169.
- Refuted: [`951/DEAD_ENDS.md`](951/DEAD_ENDS.md), seven families.
- Rule: do not ask the owner; write on the board.
