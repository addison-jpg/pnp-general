# asteroid in Lean (no Python)

`asteroid` is also one program written in Lean. It reads an asteroid program, loads the circuits
from `.bench` files, evaluates the claims, writes the proof module, and has the Lean kernel decide
it. No Python process is involved. The evaluator it runs is the one proved sound at the end of this
page.

## Build and run

```
cd one-not/lean && lake exe cache get && lake build asteroid
lake exe asteroid ../../hello.ast              # evaluate, then prove
lake exe asteroid ../../hello.ast --no-proof   # evaluate only
```

Exit code 0: every claim true and (unless `--no-proof`) accepted by the proof checker. Exit 1: a claim
is false or the proof checker rejected the module. Exit 2: the program could not be read (parse
error, missing or bad `.bench` file, a claim naming a circuit that is not defined).
`let NAME = load FILE.bench` reads the file relative to the program file.

## Verbs

| Supported | Not in the Lean version yet (skipped with one line `LINE: VERB: not in the Lean version yet`, run does not fail) |
|---|---|
| `circuit … end` blocks, `let NAME = load FILE.bench` (and `.json`), `show` | `plot`, `corpus`, `search`, `prove`, `hunt`, `mixed` and every other verb of `asteroid/SPEC.md` |
| `claim`, `claim!`, `by lean`, `not` | |
| `correct(c)`, `hyps(c)`, `hyps(c) = false`, `forall cubes slack(c) >= 0` | |
| comparisons of `gates nots base witness orwitness slack anyslack` of a circuit, or a whole number | |

## Against the Python version

| | Python | Lean |
|---|---|---|
| `hello.ast` | 4 claims, 3 proved | same 4 claims, same verdicts, 3 proved |
| `asteroid/examples/first.ast` | 7 true, 8 proved | same |
| `asteroid/tests/notgate.ast` | 11 true, 1 false (forced claim, rejected by the checker) | same |
| claims agreed | | 23 of 23 in 3 programs (verdict and detail text) |
| run, evaluate only | 0.1 to 0.6 s | about 0.9 s (`lake exe` start included) |
| run with proofs, hello / first / notgate | 16.8 / 8.8 / 9.4 s | 12.7 / 7.7 / 9.8 s |
| build | none | 23 s for the executable with Mathlib unpacked by `lake exe cache get`; 1 s when nothing changed |
| binary | | 122 MiB (`.lake/build/bin/asteroid`, static) |

Differences in the text: the Python line reads `claim …: python TRUE (…)`, the Lean line `claim …: TRUE
(…)`; a claim without a Lean form says `evaluated only` in Lean and `Python only` in Python.

## Mathlib

`Program`, `Core`, `Eval`, `Emit`, `Main` import only `Std` and `Lean`. `Core.lean` holds the
checkers a second time as functions of plain data (`Nat`, `List`), so the evaluator has no Mathlib.
`CoreEq.lean` and `Semantics.lean` import the project and Mathlib but are not imported by `Main`: they
are proofs only. One import does reach Mathlib: the `.bench` reader (`Bench.lean`) imports
`SearchCheck`, which imports `Mathlib.Tactic.Basic`, and that is linked into the executable (the
cause of the 122 MiB). Removing it means giving the reader its own `Gate` and `Circ`.

## What remains to drop Python, largest first

1. The extensions: `corpus`, `search`/`hunt`, `mixed`, `eureka`, continuous (`ext_*.py`, thousands of lines).
2. `plot` and every picture.
3. The rest of the term language: `flip`, `flipclasses`, quantifiers over points, arithmetic in terms.
4. The test runner `python3 -m asteroid test` (programs and `--no-lean`) in Lean.
5. The Mathlib import of the `.bench` reader (binary size).

## What is proved about asteroid

All in `one-not/lean/PEqualNP/AsteroidLang/Semantics.lean`; none uses `sorry` or `native_decide`, all
rest on `propext`, `Classical.choice`, `Quot.sound` only. `denote` is the meaning of a claim in the
project's own definitions; `eval_sound` is about `Expr.eval`, the function the executable runs.

- `eval_sound`: a claim of a covered form that the evaluator calls true holds in the project's definitions. Covered forms: `correct(c)` (the project's `Circuit.eval` on `C.toGates` computes the OR of every set on every input), `hyps(c)` (the hypotheses of the main theorem), `forall cubes slack(c) >= 0` (`baseDQ C.setFin ∅ Q ≤ |F2 C.toGates C.setFin Q|` for every `Q`), every comparison between whole numbers and `gates`, `base`, `orwitness`, `slack` (about `C.toGates.length`, `∑ (|S| − 1)`, `|F2 … ∅|`), and `not` of such a comparison.
- `correct_bridge`, `slackNonnegAll_bridge`, `hypsB_bridge`, `setsOk_bridge`, `orWitness_bridge`, `base_bridge`: the executable's light checker on a circuit equals the project's checker on the same circuit as a project circuit (`CoreEq.toProject`).
- `tt_map`, `tables_map`, `orTables_map`, `notCount_map`, `hypsB_map`: the light checkers do not see the gate record, only the op code and two wires.
- `func_sem`, `term_sem`, `term_ex`, `cmp_ex`: the value the executable computes for a count is the value of the project's definition.

Without a soundness theorem yet: `witness`, `nots` and `anyslack` as comparison terms (the missing
statements: `witnessCount C = number of gate wires with a witness` and `nots C = |{g ∈ C.toGates | g.op = GateOp.not}|`);
`hyps(c) = false`, `not correct(c)`, `not hyps(c)`, `not forall cubes …` (these need the converse, that a
failing check means the statement fails: the checkers are sound, not shown complete); the
`slack(c) >= 0 by lean` per-cube forms with a cube other than the empty one.
The generated proof modules (`Asteroid_<program>_sound.lean`) restate the same claims per program.
