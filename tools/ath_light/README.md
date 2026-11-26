# ath_light: prove asteroid's light claims with Lean core only, re-check them with a 1.3 MB checker

Measured 2026-11-26 (pnp-subproblem) on `refactor/pillars`, toolchain leanprover/lean4:v4.36.0. Reproduce with `run.sh`.

1. **No Mathlib needed for light claims.** `W951/SearchCheck.lean` imports only `Mathlib.Tactic.Basic`; with that one line
   removed, `SearchCheck`, `Asteroid`, `AsteroidMixed` and the emitted modules `Asteroid_corpus` (30 claims) and
   `Asteroid_mixed` compile with plain `lean` (Lean core, no Mathlib, no lake): 33 s + 23 s + 4 s. Axioms of a claim:
   `propext` only.
2. **No Lean install needed to RE-CHECK them.** `leanexport` (0.66 MB) exports the 30 claims with their dependency
   closure: 1.3 MB (0.2 MB gzipped), 811 declarations. `nanoda_bin` (1.3 MB, independent Rust kernel) checks them in 14 s,
   no type checker errors, and prints `W_8_claim8 : correctB W_8 = true`. TAMPER TEST: one literal changed in the export
   (9 -> 987654): nanoda rejects (def_eq assertion, exit 101).
3. **Which claims are light.** Of the 284 theorems in the 28 emitted `Asteroid_*.lean`: 132 `decide +kernel` and 42
   `unfold; decide` are light (61%); 94 `_project` claims (tie a computation to a project theorem) and ~16 continuous Φ
   claims need Mathlib (deep).
So the owner's "Lean a very small dependency" is reachable as: run = `ast` binary only; check light claims = `lean`
core (the 12 MB Init oleans + the Lean shared library) or, with no Lean at all, a shipped 0.2 MB certificate + the
1.3 MB nanoda binary; deep claims = Mathlib in CI only.
