# pnp-general

P versus NP through general circuits: lower bounds for circuits of AND, OR and NOT gates with
any number of NOT gates, attacked with circuit complexity, quantum gravity and pure mathematics.
Every claim is a Lean 4 statement that the checker accepted against a pinned Mathlib; the word
for that is "checked". **Nothing here says that P versus NP is settled.**

- **The board:** [`BOARD.md`](BOARD.md): targets, the NOT gate ladder, the one-to-one table
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
[`LICENSE`](LICENSE)); earlier work is frozen in `addison-jpg/pequalnp-work`.
