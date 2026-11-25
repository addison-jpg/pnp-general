# asteroid in Lean (no Python)

`asteroid` is also one program written in Lean. It reads an asteroid program, loads the circuits
from `.bench` files, evaluates the claims, writes the proof module, and has the Lean kernel decide
it. No Python process is involved. The evaluator it runs is the one proved sound at the end of this
page.

## Build and run

```
cd one-not/lean && lake exe cache get && lake build asteroid
lake exe asteroid ../../hello.ath              # evaluate, then prove
lake exe asteroid ../../hello.ath --no-proof   # evaluate only
```

Exit code 0: every claim true and (unless `--no-proof`) accepted by the proof checker. Exit 1: a claim
is false or the proof checker rejected the module. Exit 2: the program could not be read (parse
error, missing or bad `.bench` file, a claim naming a circuit that is not defined).
`let NAME = load FILE.bench` reads the file relative to the program file (see Windows and Git Bash below).

## Windows and Git Bash

The same commands, in Git Bash, from the repository folder. Lean comes from elan
(`~/.elan/bin`, `%USERPROFILE%\.elan\bin`); no Python is needed.

```
cd one-not/lean && lake exe cache get && lake build asteroid && cd ../..
one-not/lean/.lake/build/bin/asteroid.exe hello.ath             # the built binary, run directly
one-not/lean/.lake/build/bin/asteroid.exe hello.ath --no-proof  # evaluate only
one-not/lean/.lake/build/bin/asteroid.exe --doctor hello.ath    # where it looked, what it found
```

`lake build asteroid` puts one binary at `one-not/lean/.lake/build/bin/asteroid` (`asteroid.exe` on
Windows). It can be run from any folder, or put on PATH (`export PATH="$PWD/one-not/lean/.lake/build/bin:$PATH"`, then
`asteroid hello.ath`); `lake exe asteroid` is the same program.

- **The project** (the folder with `lakefile.toml` and `PEqualNP/W951`) is searched upwards from the
  binary's folder, then the program's folder, then the current folder. Not found: the run evaluates
  only and says so in one line.
- **`lake`** is looked for in every folder on PATH (`lake.exe` on Windows), then `~/.elan/bin` and
  `%USERPROFILE%\.elan\bin`, and asked `lake --version` inside the project (elan picks the toolchain
  there). Not found: the run evaluates only, says so in one line, and exits 0 if every claim is true.
- **Paths**: `\` and `/` both separate folders, `C:/…` and `/…` are absolute, a path may hold spaces.
  `let NAME = load PATH` takes the rest of the line as the path, with or without quotes
  (`load "C:/Users/Some Name/x.bench"`). A relative path is read from the PROGRAM's folder (then from
  the repository folder, which `asteroid/examples/first.ath` uses), never from the current folder.
- **Text**: programs and `.bench` files are read as UTF-8; CRLF line ends and a byte-order mark
  (Notepad) are accepted. The generated proof modules are written byte for byte with LF.
- **`--doctor`** prints the binary, the current folder, every place searched for the project and
  for `lake`, what was found, and whether a run will prove or only evaluate. Exit 0.

**Tested here, on Linux only** (2026-11-25; Windows itself cannot be run in this environment, so
nothing below was run on Windows or in Git Bash): `hello.ath`, `asteroid/examples/first.ath`,
`asteroid/tests/notgate.ath` from the repository folder and from other folders, with proofs (3, 8
proved; notgate's forced false claim rejected, exit 1); copies of `hello.ath` and `hello.bench` with
CRLF and a byte-order mark (3 proved); `/tmp/…/a b/hello.ath` (a space in the folder, 3 proved);
`load` with a quoted path holding a space, an unquoted absolute path holding a space, and a `\`
path; a run from a folder holding a broken `hello.bench` (the program's own one was read);
`--no-proof`; `--doctor`; a run with no `lake` on PATH and no `~/.elan` (one line, evaluate only,
exit 0); a missing program (exit 2). Verdicts equal `python3 -m asteroid` on every program; the
Python version (at the time) failed on the CRLF + byte-order-mark copy and on the `\` path.
`lake build PEqualNP.Verify.All` still succeeds. **Not tested**: Windows path handling by the Lean
runtime (drive letters, `\\?\` paths from `realPath`), finding `lake.exe`, Git Bash's own path
conversion, and building the 122 MiB binary with the Windows toolchain.

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
| `hello.ath` | 4 claims, 3 proved | same 4 claims, same verdicts, 3 proved |
| `asteroid/examples/first.ath` | 7 true, 8 proved | same |
| `asteroid/tests/notgate.ath` | 11 true, 1 false (forced claim, rejected by the checker) | same |
| claims agreed | | 23 of 23 in 3 programs (verdict and detail text) |
| run, evaluate only | 0.1 to 0.6 s | about 0.9 s (`lake exe` start included) |
| run with proofs, hello / first / notgate | 16.8 / 8.8 / 9.4 s | 12.7 / 7.7 / 9.8 s |
| build | none | 23 s for the executable with Mathlib unpacked by `lake exe cache get`; 1 s when nothing changed |
| binary | | 6.3 MB (`.lake/build/bin/asteroid`); 4.3 MB stripped (`dist/linux/asteroid`). Was 122 MiB until 2026-11-25 |

Differences in the text: the Python line reads `claim …: python TRUE (…)`, the Lean line `claim …: TRUE
(…)`; a claim without a Lean form says `evaluated only` in Lean and `Python only` in Python.

## Mathlib and size

`Program`, `Core`, `Eval`, `Emit`, `Bench`, `Json`, `Main` import only `Init` and `Std.Data.HashMap`. `Core.lean` holds the
checkers a second time as functions of plain data (`Nat`, `List`), so the evaluator has no Mathlib.
`CoreEq.lean` and `Semantics.lean` import the project and Mathlib but are not imported by `Main`: they
are proofs only. The `.bench` reader uses `Core`'s `Gate` and `Circ` (it used `SearchCheck`'s, which
imports Mathlib), and `.json` circuits are read by `Json.lean`, a small reader that imports nothing.
The 122 MiB binary of before came from `import Lean.Data.Json`, which links the whole Lean compiler
(Meta, Elab); without it the binary is 6.3 MB (4.3 MB stripped).

## What remains to drop Python, largest first

1. The extensions: `corpus`, `search`/`hunt`, `mixed`, `eureka`, continuous (`ext_*.py`, thousands of lines).
2. `plot` and every picture.
3. The rest of the term language: `flip`, `flipclasses`, quantifiers over points, arithmetic in terms.
4. The test runner `python3 -m asteroid test` (programs and `--no-lean`) in Lean.
5. Done 2026-11-25: binary size (no Mathlib, no `Lean.Data.Json`; 6.3 MB).

## What is proved about asteroid

All in `one-not/lean/PEqualNP/AsteroidLang/Semantics.lean`; none uses `sorry` or `native_decide`, all
rest on `propext`, `Classical.choice`, `Quot.sound` only. `denote` is the meaning of a claim in the
project's own definitions; `eval_sound` is about `Expr.eval`, the function the executable runs.

- `eval_sound`: a claim of a covered form that the evaluator calls true holds in the project's definitions. Covered forms: `correct(c)` (the project's `Circuit.eval` on `C.toGates` computes the OR of every set on every input), `hyps(c)` (the hypotheses of the main theorem), `forall cubes slack(c) >= 0` (`baseDQ C.setFin ∅ Q ≤ |F2 C.toGates C.setFin Q|` for every `Q`), every comparison between whole numbers and `gates`, `nots`, `base`, `orwitness`, `slack` (about `C.toGates.length`, the number of NOT gates of `C.toGates`, `∑ (|S| − 1)`, `|F2 … ∅|`), and `not` of such a comparison.
- `correct_bridge`, `slackNonnegAll_bridge`, `hypsB_bridge`, `setsOk_bridge`, `orWitness_bridge`, `base_bridge`, `nots_bridge` (`nots C = |{g ∈ C.toGates | g.op = GateOp.not}|`): the executable's light checker on a circuit equals the project's checker on the same circuit as a project circuit (`CoreEq.toProject`).
- `tt_map`, `tables_map`, `orTables_map`, `notCount_map`, `hypsB_map`: the light checkers do not see the gate record, only the op code and two wires.
- `func_sem`, `term_sem`, `term_ex`, `cmp_ex`: the value the executable computes for a count is the value of the project's definition.

Without a soundness theorem yet: `witness` and `anyslack` as comparison terms (the missing
statement: `witnessCount C = number of gate wires with a witness`);
`hyps(c) = false`, `not correct(c)`, `not hyps(c)`, `not forall cubes …` (these need the converse, that a
failing check means the statement fails: the checkers are sound, not shown complete); the
`slack(c) >= 0 by lean` per-cube forms with a cube other than the empty one.
The generated proof modules (`Asteroid_<program>_sound.lean`) restate the same claims per program.
