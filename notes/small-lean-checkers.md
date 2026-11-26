# Small / independent Lean 4 checkers (research-desktop, 2026-11-26)

For `boards/tasks/ath-small-deps.md`, tier 3: re-check Lean proofs (incl. Mathlib-based ones) without a full Lean + Mathlib install.
Labels: READ = seen on the page; INFERRED = my reading, not stated there. The project toolchain is Lean v4.36.0.

| Tool | What it is | Needs | Nat / `decide` | Status | Label |
|---|---|---|---|---|---|
| `leanchecker` (was lean4checker) | Replays `.olean` declarations through the OFFICIAL kernel (`lake env leanchecker [--fresh] Mod`); detects environment hacking; NOT an external verifier | the Lean toolchain + the project's `.olean`s (Mathlib cache) | same as Lean | built into every toolchain from v4.28.0 (old repo deprecated). In this container's v4.36.0: `leanchecker` and `leanchecker-paranoid` binaries present | READ (README); binaries seen locally |
| `lean4export` (leanprover) | Exports a module plus its transitive dependencies to the "Lean 4 NDJSON export format" (`lake env lean4export Mathlib > out.ndjson`) | the Lean toolchain + Mathlib build, at EXPORT time only | n/a (exporter) | official leanprover repo | READ (README) |
| `nanoda` / `nanoda_lib` (ammkrn) | External type checker in Rust, reads lean4export files (file or stdin); JSON config; axiom allow-list; multithreaded | Rust toolchain to build (`cargo build --release`), then the binary alone; no Lean | `nat_extension` and `string_extension` options (kernel Nat/String extensions), OFF by default, must be turned on for `decide`-heavy proofs | active; listed as a checker on the Lean Kernel Arena (arena.lean-lang.org, entries nanoda and sonanoda) | READ (README, search result). Binary size: not stated |
| `lean4lean` (Carneiro) | The Lean 4 kernel written in Lean, derived from the C++ kernel ("likely shares some implementation bugs"); also a metatheory and verification project | elan + Lean (built with lake, run via `lake env`), so NOT Lean-free | same algorithms as the C++ kernel | checks Lean, Std and Mathlib; 20-50% slower than C++ (TYPES 2025 paper) | READ (README, arXiv 2403.14064) |
| trepplein | Lean 3 checker (Scala) | — | — | Lean 3 only; not applicable | READ (paper mention) |
| LRAT / DRAT certificates (drat-trim, cake_lpr), Lean `bv_decide` | SAT proof certificates checked by a small checker; `bv_decide` produces LRAT that Lean checks in-kernel | for external checking: a C/CakeML binary | replaces a `decide` over a large finite search by a certificate | n/a | INFERRED: applies only to claims that are SAT/UNSAT instances (e.g. "no circuit of size k" style), not to general Mathlib proofs |

## Recommendation for tier 3 (INFERRED from the above)
- Smallest Lean-free re-check: **CI** builds the proofs with Mathlib and runs `lean4export` → NDJSON. **Users** run a prebuilt `nanoda` binary with `nat_extension: true, string_extension: true` and an axiom allow-list of `propext, Classical.choice, Quot.sound`. No Lean or Mathlib on the user machine; only the export file and one Rust binary.
- Caveats:
  - The export file for all of Mathlib is large. Export only the claim modules plus their transitive dependencies (still large). Its size is not stated; measure it.
  - Format compatibility: in a Dec 2025 Zulip thread users disagreed on whether upstream lean4export matches nanoda's expected format; pin versions and test.
  - nanoda binary size is not stated; measure after `cargo build --release`.
  - `leanchecker` is the cheap first step but needs the toolchain + oleans, so it fits tier 2 or CI, not "nothing installed".
  - For `by decide` claims over finite searches, an LRAT certificate + a small checker (cake_lpr is formally verified) is the smallest option, but only where the claim is a SAT instance.

Sources: github.com/leanprover/lean4export, github.com/leanprover/lean4checker, github.com/digama0/lean4lean, github.com/ammkrn/nanoda_lib (READMEs read 2026-11-26); arXiv 2403.14064; LIPIcs TYPES 2025.2; Lean Zulip "Export format" / nanoda threads (search results only); arena.lean-lang.org (search result; page not rendered).
