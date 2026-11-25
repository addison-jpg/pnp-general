# Checker review (observer session session_01GmnDhegXGF8MJNAhiA1AHp), 2026-11-24

Scope: the upstream checker (`.github/workflows/authoritative.yml`, `.github/scripts/outside-guard.mjs`,
`tools/check-lean.mjs`, `lean/CheckLemma.lean`), read at brilliant-hq/pequalnp-proofs main b0ad780 and the copies
in this repository. Lean v4.36.0, pinned Mathlib fc4f59e. Nothing here was sent to pequalnp.com.

## How the verdict is made
`check-lean.mjs` builds the module, then `checklemma` (CheckLemma.lean) imports the compiled module with
`trustLevel := 0` and (1) replays every project constant through the kernel on top of Mathlib + `PEqualNP.Defs`,
(2) requires a theorem named like the module, (3) walks its transitive constants over the re-checked environment
and rejects `sorryAx` and any axiom outside propext / Classical.choice / Quot.sound, (4) elaborates the recorded
statement in an environment with only Mathlib + Defs and has the kernel check `theorem : statement`.
A project constant reusing a Mathlib/Defs name is rejected (`redeclares`), except an identical theorem (left out).

## Red team (files in `redteam/`, verdicts in `redteam/results.txt`)
Run through the real `node tools/check-lean.mjs <file> <statement> check`.

| Input | Verdict |
|---|---|
| honest proof | ACCEPTED |
| `sorry`; `admit`; sorry inside a helper | REJECTED (sorry) |
| extra `axiom cheat : False` | REJECTED (axiom) |
| `native_decide` | REJECTED (axiom, `..._native.native_decide.ax_1_1`) |
| `addDecl` with `debug.skipKernelTC` | REJECTED (kernel) |
| proves `n = n` for posted `0 + n = n` | REJECTED (statement) |
| custom `HAdd Nat` instance, inline and as `instance` | REJECTED (statement) |
| redefines `Nat.factorial` | REJECTED (redeclares) |
| wrong theorem name | REJECTED (no-theorem) |

First-round oddities were test errors, not holes: `n + 0 = n` and `n = n` are definitionally equal, and
`Mathlib.Logic.Basic` does not exist in this Mathlib.

## Open issues
1. **`.olean` trust boundary (design).** The locked compile (user `outsider`) writes the `.olean` files; the
   verifier then loads them as the trusted account and its stdout is the verdict. Lean does not validate
   `.olean` structure. The sha256 before/after check covers sources, verifier binary and lake-locked.sh, not the
   `.olean` files. Fix: sandboxed export (lean4export) + independent trusted checker (lean4lean / nanoda).
   Check also that `importModules` on the judged module does not run initializers (`loadExts` default false).
2. `CheckerSuite` (lean_lib) and `tools/check-lean.test.mjs` are declared but absent. `redteam/` can seed them.
3. The merge program is not in the repository; confirm it pins the head sha shown in the verdict.
4. Statement is fetched from data.pequalnp.com at check time (TLS only).

## auto951 gate (`Audit.lean`)
`lake env lean --run Audit.lean <final module> <final theorem> <statement file>` prints
`STATEMENT ok|mismatch`, `AXIOMS ...`, `SORRY <holder> <fingerprint>` (fingerprint = hash of the open goal's type
and of every project constant it mentions), `DONE`. Tested on coord-951 ffb8d82: baseline one sorry (`no_minCE`);
final theorem replaced by `True` -> mismatch; sorry inside the final theorem -> new SORRY line.
Live run 45344923981 (branch auto951-smoke-reject): all steps green, branch NOT merged (not an ancestor of
coord-951). Not yet tested: a clean branch that should merge. The gate is tied to the L-meta-951 statement
(`work/statements/L-meta-951.json`), so for the general target it needs a new statement file and final-theorem
name. The decision file is written by the step that compiles untrusted code: convenience for own agents,
not a security boundary.
