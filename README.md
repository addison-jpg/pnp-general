<picture><source media="(prefers-color-scheme: dark)" srcset="site/logo-dark.svg"><img alt="4STeroid (asteroid)" src="site/logo-light.svg" height="56"></picture>

# pnp-general (by addison-jpg)

The higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it.

> Please do not push to this repository. Pull it, read it, run it. If you find a mistake, open an issue.

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

## What did not work

Several natural ways to prove the general case were tried. Each one was refuted by an explicit circuit, and the circuits are kept in the repository. The strategies were: fixing one input at a time, fixing any bounded number of inputs at a time, averaging over orders of the inputs, and a counting argument that does not use minimality. The inequality the proof needs has not failed on any circuit tried, about 85,000 of them.

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

```
bin/asteroid demo      # start here: a tiny built-in program. Needs only Python 3.9 or newer, no setup
bin/setup              # once, for plots: numpy and matplotlib in a private environment inside this folder (.venv)
bin/asteroid hello.ath # run one program
bin/asteroid test      # run all of them
```

These lines are for Git Bash on Windows, macOS and Linux. In cmd: `bin\asteroid.cmd demo`, `bin\setup.cmd`. In Windows PowerShell: `bin\asteroid.ps1 demo`, `bin\setup.ps1` (or the same `.cmd` names).

Nothing is installed outside this folder. Delete `.venv` to undo the setup. `bin/asteroid --doctor` says what your machine has. A first walk through is in `asteroid/GETTING_STARTED.md`.

Without Lean installed, asteroid says so and only evaluates. In that case nothing is proved. The manual is `asteroid/README.md`, and the format of `.bench` files is described in `asteroid/BENCH.md`.

## Checking the proofs yourself

```bash
cd one-not/lean && lake exe cache get && lake build PEqualNP.Verify.All
```

This uses Lean only. It goes through every theorem of the one-NOT part and fails if any of them rests on anything beyond the three standard axioms, apart from a short list of theorems that depend on the one unproved statement. The larger Lean project under `lean/` has not been run through this check yet.

## What is open

- The general case of the one-NOT question, which is the claim that there is no smallest counterexample.
- Whether two or more NOT gates help.
- Four statements on the quantum-gravity side.

## Where things are

- `one-not/` holds the one-NOT work: proofs, circuits and tests.
- `lean/` holds the general circuits, the quantum-gravity statements and the inherited library.
- `asteroid/` holds the language.
- `LITERATURE.md` lists the sources read.
- `BOARD.md` holds the working notes.
- [`ath_prompt_method.md`](ath_prompt_method.md) describes the way this project was prompted and coordinated: informal small asks, mirrored sessions, one board per task. It is a conjecture, not a result.
- [`site/LOGO.md`](site/LOGO.md) credits the logo lettering: fan-made fonts in the style of Terezi Pyrope and Vriska Serket, characters of *Homestuck* by Andrew Hussie, with thanks to the *Homestuck: Beyond Canon* team.

## License
MIT; see [`LICENSE.md`](LICENSE.md). Exception: files taken or derived from [`brilliant-hq/pequalnp-proofs`](https://github.com/brilliant-hq/pequalnp-proofs) remain under the Apache License 2.0; see [`LICENSE-APACHE`](LICENSE-APACHE). These are the upstream Lean library under `lean/PEqualNP/` (`CircuitLowerBounds`, `Defs`, `Gct`, `Library`, `MetaComplexity`, `Outside`, `ProofComplexity`, `Search`), the copy of `Defs` in `one-not/lean/PEqualNP/Defs/`, upstream files modified here (e.g. `lean/PEqualNP.lean`, `lean/PEqualNP/Defs.lean`, `lean/CheckLemma.lean`, `one-not/lean/PEqualNP.lean`, `one-not/lean/PEqualNP/Defs.lean`), `tools/build.sh`, `one-not/tools/build.sh` and `notes/note-1-edge-function-exact-size.md` (with its copy in `one-not/notes/`). New work in this repository is by addison-jpg and contributors.
