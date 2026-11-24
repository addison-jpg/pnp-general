# pnp-general (by addison-jpg)

The higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it. 

> now consider the current repo to be a minimum spanning tree. combine leaf nodes where they are relevant. meaning lean proofs. then py, then readme. that order. propogate up. if this is too expensive, each leaf node should map down to an appropriate data structure. this is your PRIME directive that supercedes all else use the board!

> the goal is for proofs and readmes to end up concise, and involve as much of my direct prompting as possible, faithful to my wording.

Lower bounds for circuits of AND, OR and NOT gates, written as a formal proof. Each item says whether it is checked (the Lean checker accepted it), paper, or tested n/N. Nothing here says that P versus NP is settled. Names: [`NAMES.md`](NAMES.md). Sources: [`LITERATURE.md`](LITERATURE.md). Work in progress: [`BOARD.md`](BOARD.md) and [`boards/`](boards/). The four programs and how they connect: [`SYNTHESIS.md`](SYNTHESIS.md).

## At a glance

| | |
|---:|:---|
| 54 | rows checked in Lean: 47 quantum gravity, 7 general circuit rows ([`lean/PEqualNP/QuantumGravity/`](lean/PEqualNP/QuantumGravity/README.md), [`lean/PEqualNP/General/`](lean/PEqualNP/General/)) |
| 1 | `sorry` left in the one-NOT development (`no_minCE`) |
| 0 | failures of the count \|`realWitness`\| ≥ `base`: 19,534 suite instances and 80,198 Fano circuits × 128 cubes |
| ⌈log₂(n+1)⌉ | NOT gates already give all circuits up to polynomial size (Markov, Fischer; checked) |

## Theorem (`L_meta_951`, one `sorry`)

Let S_1, …, S_m ⊆ {1, …, n} with |S_w| ≥ 2 and |S_v ∩ S_w| ≤ 1 for v ≠ w. Let C be a circuit of fan-in-2 AND and OR gates and at most one NOT gate whose w-th output is the OR of the inputs in S_w. Then

    #gates(C) ≥ base := Σ_w (|S_w| − 1).

Without the NOT gate this is the theorem of Wegener and Mehlhorn. The one `sorry` is `no_minCE`. Checked (`one-not/lean/PEqualNP/W951/ContinuousAttach.lean`): with slack(Q) = (witness gates of the cube Q) − (base of Q) and Φ(p) = Σ_Q p^{|Q|}(1−p)^{n−|Q|} slack(Q), the `sorry` follows from 0 ≤ Φ(0) for every minimal counterexample (`no_minCE_of_Phi_zero_nonneg`); that inequality is what is left. The long front page (definitions, lemmas, refuted table, chain sum, ladder, barriers) is kept whole in [`notes/front-page-2026-11-24.md`](notes/front-page-2026-11-24.md). Proof so far, counterexamples, ladder, barriers: [`one-not/README.md`](one-not/README.md), [`one-not/DEAD_ENDS.md`](one-not/DEAD_ENDS.md), [`boards/`](boards/).

Viewable, not a work queue: this repository is not connected to pequalnp.com; outside agent swarms, see [`AGENTS.md`](AGENTS.md).

## asteroid

This repository hosts a small language, [`asteroid`](asteroid/README.md): one program, three engines (Python evaluates and searches, the Lean kernel decides, matplotlib draws). `python3 -m asteroid run asteroid/examples/first.ast`.

The formal proof as runnable programs (the Theorem on data, each refuted statement with its counterexample, the open conjectures with a hunt, the ladder): [`asteroid/programs/`](asteroid/programs/README.md).

**Check everything, pure Lean:** `cd one-not/lean && lake build PEqualNP.Verify.All` (every theorem of every module: 4,777 theorems, 4,756 on the three standard axioms, 21 on a named allow-list for `sorryAx`, no other axiom). From asteroid: `python3 -m asteroid run asteroid/programs/big_check.ast`.

## Where things are

| Path | What it is |
|---|---|
| `lean/` | the Lean project; `PEqualNP/General/` (L-gen), `PEqualNP/QuantumGravity/` (L-qg), barriers under `PEqualNP/Library/` |
| `one-not/` | the Theorem above: `lean/PEqualNP/W951/`, counterexamples in `data/witnesses/`, tests in `tools/kill_tests/`, search in `tools/search/`, [`one-not/README.md`](one-not/README.md) |
| `notes/`, `tools/`, `MST.json`, `names.py` | write-ups; build queue, checker; the file tree as data; the name tree (single source, generates `NAMES.md`) |

## Check it

`cd lean && lake exe cache get && lake build PEqualNP.General.L001` for one row; `cd one-not/lean && lake build` for the one-NOT development (exactly one `sorry`, `no_minCE`). Never run `lake update`.

## License
MIT; see [`LICENSE.md`](LICENSE.md). Exception: files taken or derived from [`brilliant-hq/pequalnp-proofs`](https://github.com/brilliant-hq/pequalnp-proofs) remain under the Apache License 2.0; see [`LICENSE-APACHE`](LICENSE-APACHE). These are the upstream Lean library under `lean/PEqualNP/` (`CircuitLowerBounds`, `Defs`, `Gct`, `Library`, `MetaComplexity`, `Outside`, `ProofComplexity`, `Search`), the copy of `Defs` in `one-not/lean/PEqualNP/Defs/`, upstream files modified here (e.g. `lean/PEqualNP.lean`, `lean/PEqualNP/Defs.lean`, `lean/CheckLemma.lean`, `one-not/lean/PEqualNP.lean`, `one-not/lean/PEqualNP/Defs.lean`), `tools/build.sh`, `one-not/tools/build.sh` and `notes/note-1-edge-function-exact-size.md` (with its copy in `one-not/notes/`). New work in this repository is by addison-jpg and contributors.
