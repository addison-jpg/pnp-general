# Task: pnp-check-exe

- **Serves:** the checker (owner, 2026-11-26, typed to checker-checker: "figure out how to get a .exe working that anyone can use, but that is hardened to our local fork").
- **Statement:** A Windows `pnp-check.exe` that anyone can run to check a Lean proof against THIS fork, and that can only ever give a verdict of this fork: pinned checker, verifier, toolchain, Mathlib and definitions. Reading of "hardened to our local fork" used here: a wrong verdict is refused, not a sandbox for hostile files (see the limits in `tools/pnp-check/README.md`).
- **Done when:** on a clean Windows machine, `pnp-check.exe setup` then `pnp-check.exe check FILE STATEMENT` gives the same verdict and exit code as `node tools/check-lean.mjs` on every file of `notes/checker/redteam/`, and `pnp-check.exe verify-tree` refuses a tree that differs by one byte.
- **How:** DECIDED (checker-checker, 2026-11-26): a small native Go program, cross-compiled and reproducible (2.3 MB), not a Node or Python bundle; the judge stays `lean/CheckLemma.lean`, unchanged and pinned; only the orchestration of `tools/check-lean.mjs` is ported, and differential-tested. Code and numbers: `tools/pnp-check/README.md`.
- **Seats:** stage 1 DONE (checker-checker). Stages 2 to 4 OPEN: a Windows machine or the `windows-latest` runner is needed to test them; none of the Windows code has run on Windows yet.

## OPEN / TAKEN

- DONE (checker-checker, 2026-11-26, cite:file:tools/pnp-check/README.md): stage 1, pins and `verify-tree`, 8 Go tests, 6 tamper cases on a copy of the real tree, two identical Windows builds.
- OPEN stage 2 `setup`: archive of the pinned commit (never `git clone`, line endings), pinned toolchain into the exe's own folder, `lake exe cache get`, build `PEqualNP.Defs` and `checklemma`.
- OPEN stage 3 `check`: port of the orchestration, differential test against `notes/checker/redteam/results.txt`.
- OPEN stage 4: Job Object limits, scratch copy, low-integrity token; says plainly that it is not a sandbox.
- ASK Addison: (1) is "hardened" the wrong-verdict reading above, or do you also need it safe on a stranger's file (then: Windows Sandbox or WSL2 only)? (2) Where should the exe live: committed (2.3 MB, like `asteroid.exe`) or a workflow artifact? (3) Code signing costs money; skip it and publish a SHA-256 plus a build attestation?
