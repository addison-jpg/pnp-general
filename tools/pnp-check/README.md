# pnp-check: a Windows .exe checker bound to this fork

Owner request (2026-11-26): "a .exe working that anyone can use, but that is hardened to our local
fork". Reading used here: **a verdict printed by the exe is only ever a verdict of THIS fork's
checker, definitions, toolchain and Mathlib, and the exe says so and refuses otherwise.** Nothing
here says P versus NP is settled; a lemma is "checked" only when the checker accepts it.

## Status: stage 1 of 4

| Stage | What | State |
|---|---|---|
| 1 | The exe knows exactly what it is bound to (SHA-256 of 67 files) and refuses any other tree | **done, tested on Linux; the Windows build is untested on Windows** |
| 2 | `setup`: fetch the pinned tree, install the pinned toolchain, get the Mathlib cache, build the verifier | open |
| 3 | `check FILE STATEMENT`: the checker's orchestration, differential-tested against `tools/check-lean.mjs` | open |
| 4 | Hardening for files you do not trust (Windows) | open, see limits |

Stage 1 numbers (measured on this box, Go 1.24.7):
- `pnp-check.exe`: **2.3 MB**, PE32+ console, no runtime, no Node, no Python. Two builds are
  bit-for-bit identical (reproducible), so anyone can rebuild it and compare the SHA-256.
- Pinned: `tools/check-lean.mjs`, `lean/CheckLemma.lean`, `lean/lakefile.toml`,
  `lean/lake-manifest.json`, `lean/lean-toolchain`, `lean/PEqualNP/Defs.lean` and EVERY file under
  `lean/PEqualNP/Defs/` (61), of any extension. Refused: a changed, missing or extra file, a symlink
  in place of a file, a `lean/lakefile.lean`, any file under `lean/CheckerSuite/`.
- `go test ./...`: 8 tamper tests pass. On a copy of the real tree: pristine OK; a definition
  edited, an extra file in `Defs/`, the verifier edited, the toolchain pin moved, CRLF line
  endings in one file: each REFUSED (exit 1) with the file named.

```
pnp-check version               what this build is bound to (fork, commit, toolchain, digest)
pnp-check verify-tree [DIR]     0 = byte for byte the pinned fork; 1 = REFUSED, every difference listed; 3 = could not run
```

Build and test (from `tools/pnp-check/`, no network needed, no dependencies):

```bash
GOFLAGS=-mod=mod GOPROXY=off CGO_ENABLED=0 go test ./...
GOOS=windows GOARCH=amd64 CGO_ENABLED=0 go build -trimpath -buildvcs=false \
  -ldflags="-s -w -X main.Version=0.1.0-stage1" -o pnp-check.exe ./cmd/pnp-check
# new pins after the fork changes (the exe must be rebuilt with them):
go run ./cmd/mkpins ../.. addison-jpg/pnp-general "$(git rev-parse HEAD)" > cmd/pnp-check/pins.json
```

## What an exe cannot be

Not self-contained. The verdict is made by `lean/CheckLemma.lean`, which loads Mathlib's compiled
modules. Per user, first run needs: the Windows Lean 4.36.0 toolchain (889,655,772 bytes, exists),
elan (2.6 MB, exists), and the Mathlib cache (458 MB cache directory here; 6.8 GB unpacked). So the
exe is a small, pinned front end that sets this up once; it cannot ship the library inside.

## Plan for stages 2 to 4

2. **setup.** Download the tree of the pinned commit as an archive from github.com and verify the
   pins; never `git clone` (no `.gitattributes` rule fixes line endings for Lean files, so Windows
   autocrlf would rewrite them and every hash would differ). Install the toolchain from
   `lean/lean-toolchain` into the exe's own folder; resolve `lean`/`lake` from there, never from
   `PATH`. Then `lake exe cache get`, build `PEqualNP.Defs` and `checklemma`, record the verifier's
   SHA-256.
3. **check.** Keep ONE judge: `CheckLemma.lean` is unchanged and pinned. Port only the orchestration
   of `tools/check-lean.mjs` (about 200 lines: fixed inputs, verifier hashed before and after,
   scrubbed environment, private statement copy). Differential test: run both on
   `notes/checker/redteam/` (15 cheat cases, `results.txt`) and require the same verdict and exit
   code on every case, before anyone relies on the exe.
4. **Hostile files.** See limits.

## Limits, said plainly

- **A Lean file runs code while it compiles** (macros, `#eval`, `initialize`); `tools/check-lean.mjs`
  says to run it on a file you do not trust only inside an isolated environment. On Linux the
  project's workflow isolates it with a locked-down account. **Windows has no equivalent that a
  plain exe can set up.** What stage 4 can add: a Job Object (memory and CPU limits, kill on close),
  a scratch copy of the tree, a scrubbed environment, a low-integrity token. What it cannot add
  without admin rights: blocking the network or file reads. So: the exe is hardened against a WRONG
  VERDICT (pinned fork, pinned toolchain, one judge); it is not a sandbox. For a stranger's file use
  Windows Sandbox, WSL2 or a VM.
- **SmartScreen and Defender** will flag an unsigned exe (the board already knows this from
  `asteroid.exe`). Publish the SHA-256 and a build-provenance attestation. Code signing costs money.
- The pins cover `lean/` only. `one-not/lean` is a separate Lake project with different `Defs`; it
  needs its own pin set.
- Findings while reading the checker: `lean/lakefile.toml` names a `CheckerSuite` library that has no
  directory (the pins forbid files appearing there); `tools/check-lean.mjs` is POSIX only (sh shim
  `tools/bin/lake`, verifier without `.exe`, needs `git`), which is why stage 3 ports the
  orchestration instead of bundling the script.
