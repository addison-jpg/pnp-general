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

## Mini board (final pass, 2026-11-24)

READMEs are mini boards: state, open, dead, names, and the way up. The main board is [`BOARD.md`](BOARD.md).

| | |
|---|---|
| Names | [`NAMES.md`](NAMES.md) / `NAMES.json`: every code has a name; one flat tree, bottom up |
| Literature | [`LITERATURE.md`](LITERATURE.md): everything read, by topic, with read status. Most important file here |
| Findings | [`COLLATION_2026-11-24.md`](COLLATION_2026-11-24.md), [`951/FINDINGS_2026-11-24.md`](951/FINDINGS_2026-11-24.md) |
| Dead | [`951/DEAD_ENDS.md`](951/DEAD_ENDS.md): seven named families |
| Tree | `MST.json`: every leaf file -> its parent |
| State | 951 is checked in Lean when the certificate game is won; general circuits: Markov and Fischer checked, Kannan's uniform half reduced; quantum gravity: 47 rows checked |
| Open | 951 for circuits that lose the certificate game; L-gen-101 to 103; the XOR extension when C(f) = C(¬f); L-qg-115, 116, 119, 169 |
| Rule | do not ask the owner; write on the board |
