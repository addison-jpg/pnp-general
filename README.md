# pnp-general (by addison-jpg)
disclaimer that a lot of the readmes are vibecoded. 
the higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it. 

> readmes are vibecoded slop. do not change font wherever possible. use my original wording.

> the goal is for proofs and readmes to end up concise, and involve as much of my direct prompting as possible, faithful to my wording.

> now consider the current repo to be a minimum spanning tree. combine leaf nodes where they are relevant. meaning lean proofs. then py, then readme. that order. propogate up.

P versus NP through general circuits: lower bounds for circuits of AND, OR and NOT gates with
any number of NOT gates, attacked with circuit complexity, quantum gravity and pure mathematics.
Every claim is a Lean 4 statement that the checker accepted against a pinned Mathlib; the word
for that is "checked".

- **The board:** [`BOARD.md`](BOARD.md): targets, the NOT gate ladder, the track pairs, roles, next steps.
- **The targets in Lean:** [`lean/PEqualNP/General/Gaps.lean`](lean/PEqualNP/General/Gaps.lean).
- Three checked barrier rows (relativization, algebrization, natural proofs) say which kinds of argument cannot work.

| Path | What it is |
|---|---|
| `lean/` | the Lean project: pinned toolchain and Mathlib, definitions under `PEqualNP/Defs/`, one program per directory |
| `lean/PEqualNP/General/` | the general program (ids `L-gen-NNN`) |
| `lean/PEqualNP/QuantumGravity/` | the quantum gravity program (ids `L-qg-NNN`), see its [`README.md`](lean/PEqualNP/QuantumGravity/README.md) |
| `lean/PEqualNP/Outside/` | one file per gap, `L_gct_101.lean`; a pull request adds exactly one such file |
| `951/` | rung 1 of the NOT gate ladder, see [`951/README.md`](951/README.md) |
| `data/612-fast-encoder/` | SAT encoder with symmetry breaking for exact synthesis of f_G (`python3 portfolio.py`; needs `pip install python-sat networkx`); finite computation, not Lean-checked |
| `tools/` | the build queue and the checker |
| `notes/` | write-ups |

Build one row: `cd lean && lake exe cache get && lake build PEqualNP.General.L001`. Never run
`lake update`.

The Lean project started from `brilliant-hq/pequalnp-proofs` (Apache License 2.0, see
[`LICENSE.md`](LICENSE.md)); earlier work is frozen in `addison-jpg/pequalnp-work`.
