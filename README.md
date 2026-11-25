<picture><source media="(prefers-color-scheme: dark)" srcset="site/logo-dark.svg"><img alt="4STeroid (asteroid)" src="site/logo-light.svg" height="56"></picture>

[![asteroid language](https://img.shields.io/badge/language-asteroid%20.ath-19B3B3)](asteroid/SPEC.md) [![VS Code](https://img.shields.io/visual-studio-marketplace/v/asteroid.asteroid?label=VS%20Code&color=3D9BD6)](https://marketplace.visualstudio.com/items?itemName=asteroid.asteroid) [![ast](https://img.shields.io/badge/ast-native%20checker%2C%20Windows%20%2B%20Linux-19B3B3)](#download) [![asteroid](https://img.shields.io/badge/asteroid-universal%2C%20one%20file-3D9BD6)](#download) [![proofs](https://img.shields.io/badge/proofs-Lean%204-555)](one-not/lean)

# asteroid: one language, one standard of proof, every field

**asteroid is a programming language and a machine-checked map of mathematics, built by Addison.** Circuit complexity, quantum gravity, cosmology, knot theory, neuroscience, biology, privacy, transit networks, modal metaphysics and philosophy are all written as `.ath` programs that run and check themselves, in one vocabulary, held to one standard.

**127 verified results** (91 Lean proofs, 18 exact exhaustive checks, 12 numerical tests, 6 refutations with counterexamples), each one rerunnable with a single command: [`RESULTS.md`](RESULTS.md).

### What it has done

- **It found a cross-field connection by itself.** The centre's sequence matcher noticed that neuron dendrite growth and evolutionary trees produce the same counts, (2n − 3)!!. The check then proved the models agree exactly: terminal growth is the Yule model and segmental growth the uniform model, for every tree shape up to 9 tips. `python3 -I biology/brain/neuron/check.py`
- **It formalizes physics in Lean:** PSPACE ⊆ P_CTC ⊆ EXP for computers with closed timelike curves, the three-qubit CKW entanglement inequality, and the two-qubit gate count via the KAK decomposition (known theorems, new formal proofs).
- **It checks the universe exactly:** Friedmann solutions for matter, radiation and a cosmological constant; the age of the universe, 13.796 Gyr from Planck 2018; and the multiverse measure problem shown exactly, where the same universes in two orders give probabilities 1/2 and 1/3. `bin/asteroid --no-lean cosmos.ath`
- **It builds the brain from the bottom up:** seven levels from DNA linking numbers through protein complexes, membranes, tissue, single neurons and networks to the cortex, each independently checked. `biology/brain/`
- **It refutes:** the point lemma for general set families fails on AG(2,8), 261 lines against a base of 448, with the counterexample in the repo.
- **It turns ideas into checks.** Every idea enters as a `frame`: where it came from, how it was read, the exact claim, and a label no stronger than its check. Lacan's knot became exact Milnor invariants; Deleuze's rhizome became a theorem about bridges checked on all 33,867 small graphs; Granovetter's weak ties became an exact crossing time, k(k − 1) + 1.

### The language

asteroid states circuits, integer sequences, exact formulas, finite probability, modal logic (Kripke frames) and frames in one syntax, and every claim prints TRUE or FALSE. Its checks always halt, the mirror image of Homestuck's ~ATH, whose loops end only when something dies. Spec: [`asteroid/SPEC.md`](asteroid/SPEC.md). Editor support: VS Code Marketplace.

**Honest limits, stated once:** the Lean results formalize known theorems, and the axiom audit of the `lean/` project is still pending; readings of philosophy and fiction are labelled readings, never results; nothing here claims progress on P versus NP.

> **About the language bar:** GitHub counts asteroid (`.ath`) files as *Ruby*, because GitHub only lists a language once it is in wide use, and asteroid is new. The Ruby share in the bar is asteroid code.

> Found a mistake, or a claim that reads stronger than its evidence? Please open an issue. Corrections are the most useful contribution.

## A small CPU in our gates

Addison's project theme, as a machine: a 4-bit accumulator CPU (PC, ACC, a 16-word ROM, eight instructions) whose next-state logic is one `.bench` circuit in `cpu/`. It has 443 gates, 238 AND, 190 OR and 15 NOT; the straightforward design used 45 NOT gates, and negations pushed to the inputs cut them to 15. The repository checks that logarithmically many NOT gates suffice (Markov and Fischer); see `cpu/README.md`.

    bin/asteroid run-cpu cpu/cpu.bench --steps 24

The same folder has a SIMD variant, `cpu/simd.bench`: 4 lanes with their own ACC and a mask bit, one shared PC and decoder, branching as predication (877 gates, 31 NOT; linear in the lane count). It is the SIMT idea behind GPUs at toy scale, not a GPU.

    bin/asteroid run-cpu cpu/simd.bench --init 3,7,0,12 --steps 14

## Why this is open

This project is aimed at the P versus NP problem, and it is public on purpose.

A result on a question this important should not sit behind a paywall or belong to a fund. If a proof exists, people should be able to read every line of it, run the checker themselves, and build on it without asking anyone's permission. Work on this problem that is done in private, sold by subscription, or held as an asset asks the public to take its claims on trust. Mathematics does not work on trust.

So everything here is in the open: the proofs, the circuits that broke the wrong ideas, the tools, and the working notes, mistakes included. Open work can be checked by anyone. That is the argument, and it is a political one.

## What this is

This repository studies how many gates a Boolean circuit needs. The circuits use AND, OR and NOT gates, and the count depends on how many NOT gates the circuit may use. Without NOT gates the answer is known exactly for one family of functions: the OR of each set in a family of sets that pairwise share at most one point. The count is the sum over the sets of (size − 1) gates. The question here is whether one NOT gate can lower that number. Jukna and Sergeev posed the question in 2013, and Blum posed it again in 2024. No result on it has been published.

All theorems here are checked by the Lean 4 proof checker. Nothing here settles P versus NP.

## What is proved

- One NOT gate does not help when the NOT gate reads an input variable.
- One NOT gate does not help when every set has at most three points.
- The one-NOT claim holds for every circuit that passes the certificate test.
- The general case reduces to one statement that is not proved: there is no smallest counterexample. A smallest counterexample would have no constant gate, no two gates computing the same function, no unused gate, and a NOT gate it cannot do without.
- Logarithmically many NOT gates are enough to simulate any circuit (a theorem of Markov and Fischer, checked here).
- Forty-seven statements from arguments in quantum gravity about computational complexity are checked. For example, if P = NP, then every polynomial-time, length-preserving function can be inverted in polynomial time.

Checked today, each in Lean with the standard axioms only:

- Several NOT gates (`one-not/lean/PEqualNP/W951/Open/`). The OR of n inputs needs n − 1 AND/OR gates with any number of NOT gates (`Or4ManyNot.lean`, `or_needs_gates`). A system of ORs needs at least n − (number of components of the union graph) AND/OR gates with any number of NOT gates; this equals the NOT-free count on acyclic systems, proved here for pairwise disjoint sets and for chains (`OrSystemManyNot.lean`, `system_bound_comp`, `disjoint_bound`, `chain_bound`). The per-set flip lemma holds for any number of NOT gates (`FlipLemma.lean`, `flip_lemma`). For two sets of size at most 3, the function-level core of the flip-class count is checked (`FlipHall.lean`, `no_sole_partner`).
- Quantum gravity (`lean/PEqualNP/QuantumGravity/Open/`). L115: every operator-norm ball of radius ε in U(2^n) has Haar measure at most (4ε)^(4^n) (`L115.lean`, `haar_small_ball`). L116 follows unconditionally (`L116OfL115.lean`). L169: P_CTC is contained in EXP (`L169.lean`, `PCTC_subset_EXP`). The CTC reset cycle, which is the core of PSPACE ⊆ P_CTC: if halting resets to the start, every Deutsch-consistent distribution is supported on the orbit of the start (`CtcReset.lean`, `reset_support_on_start_cycle`). With it, PSPACE ⊆ P_CTC (`PspaceMachine.lean`, `PSPACE_subset_PCTC`, through `PspaceCtc.lean` and `PspaceClock.lean`), so PSPACE ⊆ P_CTC ⊆ EXP. PSPACE is the repository's own definition (`Library/Evasion/SpaceDraft.lean`, on Mathlib's `Turing.FinTM2`); its faithfulness has not been reviewed independently. The other direction, P_CTC ⊆ PSPACE (needed for Aaronson–Watrous's P_CTC = PSPACE), is not in the repository. L119 with 16 real parameters per two-qubit gate (`KnillParam.lean`, `L119_weak`), and with 15k + 1 (`KnillParam15.lean`, `L119_fifteen`). And the exact L119: if 9k + 3n + 1 < 4^n, circuits of k two-qubit gates reach a Haar-null set (`KAKParam.lean`, `L119`), from a KAK decomposition of every 4×4 unitary proved without Lie theory (`KAK.lean`, `kak`). All four open quantum-gravity statements (L115, L116, L119, L169) are now proved. Every unitary on d levels is a product of at most d(d+1)/2 two-level unitaries (`TwoLevel.lean`). Coffman–Kundu–Wootters monogamy for three qubits (`CKW.lean`, `ckw`). Knill's count (`ApproxCount.lean`, `approx_count_twoQubit`): almost every n-qubit unitary needs exponentially many two-qubit gates, even approximately.
- One NOT gate. The general case reduces to one named statement, `BottomPay` (`one-not/lean/PEqualNP/W951/Open/LightAbsorb.lean`), and every link of the reduction is checked in Lean: `BottomPay` → `LightAbsorb` → `DDAbsorb` → the count at every mixed state (`Open/MixedCount.lean`; the no-NOT case in `Open/MixedCountMono.lean`) → `no_minCE` (`no_minCE_of_ddAbsorb`). `BottomPay` itself is OPEN: tested, not proved (no failure in 1.27 million states). Until it is proved, the one-NOT theorem `L_meta_951` keeps its one allow-listed hole (`no_minCE`), and the one-NOT question is not settled.

## What did not work

Several natural ways to prove the general case were tried. Each one was refuted by an explicit circuit, and the circuits are kept in the repository. The strategies were: fixing one input at a time, fixing any bounded number of inputs at a time, averaging over orders of the inputs, and a counting argument that does not use minimality. The inequality the proof needs has not failed on any circuit tried, about 85,000 of them.

## Transfer: when extending a field helps

Extending an open subclass to a proven, larger field can solve it, when the reduction is explicit and the barrier results do not block the method. The general claim, that any large literature can be extended to solve the problem, is false: relativization, natural proofs and algebrization rule out the broad versions. The precise lemma and the checked case are in `core/ontology/TRANSFER.md`.

## The model layer: Qwen tensors

The open-weight Qwen2.5 models are the large tensors this repository can read. Counted from their safetensors headers by `math/qwen/tensors.py` (exact integers; no weights are loaded or stored here):

| model | layers | hidden | tensors | parameters | size |
|---|---|---|---|---|---|
| Qwen2.5 0.5B Instruct | 24 | 896 | 290 | 494,032,768 | 0.99 GB |
| Qwen2.5 1.5B Instruct | 28 | 1536 | 338 | 1,543,714,304 | 3.09 GB |
| Qwen2.5 3B Instruct | 36 | 2048 | 434 | 3,085,938,688 | 6.17 GB (2 files) |

All three are BF16. The 3B model's tensors are split over two files. The largest single tensor here is the embedding, 151,936 tokens by the hidden size.

**How it propagates up.** A model is a memory record like any other: its tensor count, parameter count and file hashes are exact facts that the centre store can hold, and a claim about the model cites those facts. What a model *does* (its answers, its semantic vectors) is a reading, labelled analogy, until a check is written for it. The language model can propose queries (`ask --model`), but its proposals are labelled proposed and never write a record.

## Philosophy (formal)

`lean/PEqualNP/Philosophy/Deleuze.lean` models one cited reading of Deleuze: distinct problems can share actual solutions, and nondegenerate singular points are isolated. `lean/PEqualNP/Philosophy/Fisher.lean` models one cited reading of Fisher's hauntology as branching time. `one-not/lean/PEqualNP/Philosophy/Bridge.lean` sets this project beside the first as a formal analogy. Φ is a function of the slack table (`Phi_eq_PhiT`, by definition), but different tables can give the same Φ (`PhiT_not_injective`, shown for small arbitrary tables, not yet for tables of real circuits), and the corner values do not determine Φ. Further files (`Unify`, `Hegel`, `Camus`, `Beauvoir`) and an independent review of all of them, `philosophy/REVIEW.md`, are in `philosophy/`. The review finds that most of the checked theorems are general facts about orders and sets, and that the link to each philosopher is interpretation. These are models of cited readings. They claim nothing about what the authors meant, and they are not proofs about the texts.

## asteroid

asteroid is a small language written for this project. You describe a circuit, state a fact about it, and the fact is evaluated at once. A fact marked `by lean` is also handed to the Lean proof checker. Circuits are plain ISCAS `.bench` files.

This is `hello.bench`, a circuit with four inputs and two outputs:

```
# hello: two sets sharing the point x2
INPUT(x0)
INPUT(x1)
INPUT(x2)
INPUT(x3)
OUTPUT(b)
OUTPUT(c)
#@ or b = x0 x1 x2
#@ or c = x2 x3
a = OR(x0, x1)
b = OR(a, x2)
c = OR(x2, x3)
```

This is `hello.ath`, a program that checks that circuit:

```
# hello.ath: run with: bin/asteroid hello.ath
let hello = load hello.bench
show hello
claim correct(hello) by lean                  # it computes both ORs on all 16 inputs
claim gates(hello) = base(hello)              # 3 gates, and 3 is the least possible without a NOT gate
claim hyps(hello) by lean                     # the theorem's side conditions hold
claim forall cubes slack(hello) >= 0 by lean  # the count behind the theorem, at every cube
plot phi hello -> asteroid/out/hello.png
```

`alchemy.ath` is the second example: an alchemy tree (items built by union) as a circuit. It reports gates 4 < base 5: one gate is reused, which only works because two of its sets share two points. That is exactly why the one-NOT theorem assumes every two sets share at most one.

```
bin/asteroid alchemy.ath   # gates 4 < base 5: sharing when sets overlap in 2 points
bin/asteroid demo      # start here: a tiny built-in program. Needs only Python 3.9 or newer, no setup
bin/setup              # once, for plots: numpy and matplotlib in a private environment inside this folder (.venv)
bin/asteroid hello.ath # run one program
bin/asteroid test      # run all of them
```

### Download

Two programs, one file each, nothing to install:

| | Windows | Linux (x86-64) | what it is |
|---|---|---|---|
| **ast** | [`ast.exe`](https://github.com/addison-jpg/pnp-general/raw/main/dist/windows/ast.exe) (4.2 MB) | [`ast`](https://github.com/addison-jpg/pnp-general/raw/main/dist/linux/ast) (4.3 MB) | the native checker, written in Lean: small and fast, no Python. Circuits, claims, the prompt, plots (SVG). Proves with Lean when it finds Lean and the repository. [`dist/windows`](dist/windows/README.md), [`dist/linux`](dist/linux/README.md) |
| **asteroid** | [`asteroid.exe`](https://github.com/addison-jpg/pnp-general/raw/main/dist/windows/asteroid.exe) (built by CI) | [`asteroid`](https://github.com/addison-jpg/pnp-general/raw/main/dist/linux/asteroid) (45 MB) | the universal language: the full implementation, every extension (finite, prob, modal, frame, commit, ask, corpus, eureka, ...), with Python inside. Proves with Lean when it finds `lake` and the repository. |

The links point at `main`. Until branch `refactor/pillars` is merged, `main` has no `dist/linux/ast` and no `dist/windows` folder, and its `dist/linux/asteroid` is the old 4.3 MB native checker, not the 45 MB universal program. Until then, take the files from `refactor/pillars`.

Arch: `packaging/arch/PKGBUILD` installs `ast`. Both programs take the same command line: `ast hello.ath`, `asteroid hello.ath`, `--no-proof`, `version`; with no arguments they open the prompt.

VS Code highlighting for `.ath`: search **asteroid** in Extensions ([Marketplace](https://marketplace.visualstudio.com/items?itemName=asteroid.asteroid)), or install `editors/vscode/asteroid-0.1.0.vsix`.

`bin/asteroid` with no arguments opens the interactive prompt, `bin/asteroid idle` the window.

A native binary, written in Lean and needing no Python, is built with `cd one-not/lean && lake exe cache get && lake build asteroid`. It evaluates a program and has Lean check it. Without arguments it opens the prompt, and `plot phi NAME -> FILE.svg` writes an SVG plot. See `asteroid/NATIVE.md`.

Windows: download `ast.exe` or `asteroid.exe` (table above) and double-click it: it opens the asteroid prompt. Or run `ast.exe hello.ath` in a terminal. Windows SmartScreen will warn, because the files are not signed: click "More info", then "Run anyway".

These lines are for Git Bash on Windows, macOS and Linux. In cmd: `bin\asteroid.cmd demo`, `bin\setup.cmd`. In Windows PowerShell: `bin\asteroid.ps1 demo`, `bin\setup.ps1` (or the same `.cmd` names).

Nothing is installed outside this folder. Delete `.venv` to undo the setup. `bin/asteroid doctor` says what your machine has. A first walk through is in `asteroid/GETTING_STARTED.md`.

Without Lean installed, asteroid says so and only evaluates. In that case nothing is proved. The manual is `asteroid/README.md`, and the format of `.bench` files is described in `asteroid/BENCH.md`.

**One centralized store.** `math/qwen/semantic_rows.json` holds the 896-dimensional input-embedding vectors of 19 of the repository's terms, read exactly from the Qwen2.5 0.5B weights by `math/qwen/embeddings.py`. These are static input embeddings: one vector per token, the same in every context. They are not contextual meanings, and treating them as meaning is a reading, not a result. A term that is not a single token ("rhizome") is recorded as absent, not guessed.

**Nearest matches are weak.** `math/qwen/nearest.py` matches each stored term to its nearest recorded terms by exact cosine. The check passes (symmetry, self-match, no ties), but the values are small, about 0.13 to 0.27, and the nearest pairs do not look like meanings ("camp" lands near "ontology"). So the static input embeddings do not carry the repository's semantic structure by themselves. Matching without an exact copy, as in Steinmetz and Gini's opening-book clusters, needs contextual vectors and a benchmark; that is the open part.

## asteroid as a GitHub language

asteroid programs use the extension `.ath`. A TextMate grammar for them is in `editors/vscode/syntaxes/asteroid.tmLanguage.json`, and the VS Code extension (`editors/vscode/`) registers `.ath` files. Those two pieces are what a language needs before GitHub can colour it.

GitHub does not add a language by itself. A language is added to the Linguist project (github-linguist/linguist), which asks for a grammar, sample files and evidence of real use on GitHub. This repository has none of the usage evidence yet, so **the language is not recognised on GitHub today**. The steps still to do: write the Linguist entry, attach samples from `asteroid/examples/`, and show usage. Whether Linguist accepts it is GitHub's decision, not this repository's.

## The model layer, and a question that is open

The Qwen2.5 models above have 0.49B, 1.54B and 3.09B parameters. A question worth asking is whether a smaller continuous model could carry the same semantic work. That is an **open research question**, not a result. Nothing here has trained or measured such a model. A claim would need a benchmark on the same tasks, with the parameter count, the tensor count and the error reported together. Until then it stays a question.

## Checking the proofs yourself

```bash
cd one-not/lean && lake exe cache get && lake build PEqualNP.Verify.All
```

This uses Lean only. It goes through every theorem of the one-NOT part and fails if any of them rests on anything beyond the three standard axioms, apart from a short list of theorems that depend on the one unproved statement. The larger Lean project under `lean/` has not been run through this check yet.

## What is open

- The general case of the one-NOT question: `BottomPay`, the one statement the checked chain reduces it to.
- One NOT gate on Boolean sums (k = 1): `BottomPay`, above. Nothing is claimed for two or more NOT gates: the general point lemma is refuted (AG(2,8), `one-not/data/witnesses/point_lemma_AG2_8.txt`), and at scale NOT gates do help on these sums (Wegener 1987, §6.7).
- The PSPACE encoding, that is, the full inclusion PSPACE ⊆ P_CTC beyond its reset-cycle core.

## Where things are

- `one-not/` holds the one-NOT work: proofs, circuits and tests.
- `lean/` holds the general circuits, the quantum-gravity statements and the inherited library.
- `asteroid/` holds the language.
- `philosophy/` holds the formal philosophy models and their plan.
- `LITERATURE.md` lists the sources read.
- `BOARD.md` holds the working notes.
- [`ath_prompt_method.md`](ath_prompt_method.md) describes the way this project was prompted and coordinated: informal small asks, mirrored sessions, one board per task. It is a conjecture, not a result.
- [`site/LOGO.md`](site/LOGO.md) credits the logo lettering: fan-made fonts in the style of Terezi Pyrope and Vriska Serket, characters of *Homestuck* by Andrew Hussie, with thanks to the *Homestuck: Beyond Canon* team.

## License
MIT; see [`LICENSE.md`](LICENSE.md). Exception: files taken or derived from [`brilliant-hq/pequalnp-proofs`](https://github.com/brilliant-hq/pequalnp-proofs) remain under the Apache License 2.0; see [`LICENSE-APACHE`](LICENSE-APACHE). These are the upstream Lean library under `lean/PEqualNP/` (`CircuitLowerBounds`, `Defs`, `Gct`, `Library`, `MetaComplexity`, `Outside`, `ProofComplexity`, `Search`), the copy of `Defs` in `one-not/lean/PEqualNP/Defs/`, upstream files modified here (e.g. `lean/PEqualNP.lean`, `lean/PEqualNP/Defs.lean`, `lean/CheckLemma.lean`, `one-not/lean/PEqualNP.lean`, `one-not/lean/PEqualNP/Defs.lean`), `tools/build.sh`, `one-not/tools/build.sh` and `workshop/notes/note-1-edge-function-exact-size.md` (with its copy in `one-not/notes/`). New work in this repository is by addison-jpg and contributors.
