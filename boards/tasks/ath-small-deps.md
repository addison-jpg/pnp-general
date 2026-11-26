# Task: ath-small-deps (owner 2026-11-26: ".ath should be the only thing we use now"; "lean should be a very small dependency, every other coding language also should")

- **Serves:** asteroid. Owner's two rules, made measurable. Facts measured on `refactor/pillars` (pnp-subproblem, 2026-11-26):
  - The binary is ALREADY Mathlib-free: `AsteroidLang/Main → Json, Emit, Bench, Repl, Plot → Eval → Program → Core` imports only Lean core + `Std` (dist: `ast` 4.4 MB, `ast.exe` 4.2 MB). `--no-proof` evaluates with no Lean installed.
  - Mathlib enters through exactly 3 doors: `AsteroidLang/Semantics.lean` (`import Mathlib`, the soundness proof), `AsteroidLang/CoreEq.lean → W951/AsteroidCheap` (`import Mathlib`), and the EMITTED proof modules (they import `W951.SearchCheck` / `AsteroidCheap`). Closure of those: 109 repo modules, 68 distinct Mathlib imports.
  - `.ath` programs: 109 files, 81 `by lean` claims, 2 `by decide`. They load only 14 distinct data files (36 load lines: 6 `.bench`, 30 `.json`). Repo-wide: 1,908 .lean, 703 .py, 357 .json/.jsonl, 38 .bench, 109 .ath.
- **Plan in three tiers (proposal; nothing renamed or deleted until the owner says yes):**
  1. **run** = the native binary alone, no Lean, no Python (exists: `--no-proof`). Make it the default; `by lean` claims print "proof skipped: Lean not installed" instead of failing.
  2. **prove-light** = emitted proof modules import ONE Mathlib-free module (`AsteroidKernel`: circuit eval + `decide`, Lean core only). Then proving needs the Lean toolchain only, no Mathlib cache (GBs). Claims that need the deep theorems (MinCE etc.) are marked `by lean deep` and go to tier 3.
  3. **prove-full** = Mathlib, run in CI on push, never on the owner's machine. Option to look at (research): an independent small kernel checker on exported terms (lean4export + lean4lean / nanoda) so even tier 3 needs no Lean install to RE-check.
  - **.ath only:** a circuit / data section inside `.ath` (`circuit NAME { ... }`, `data NAME { ... }`), so the 14 loaded files become `.ath`; corpora that no program loads stay data and are out of scope. `.lean` / `.py` / `.rs` remain implementation, never something the owner opens.
- **Split (talk directly, results here):** asteroid CLI seat: tiers 1 and 3 in the binary (flag, message), and the `circuit`/`data` syntax. pnp-subproblem: measure which of the 81 `by lean` claims are Mathlib-free once `AsteroidKernel` exists, and convert the 14 files with a checked round-trip (old load vs new section give identical evaluations). research: the small-kernel-checker literature (lean4lean, nanoda, lean4checker, LRAT-style certificates). coord: owner approval and order.
- **Done when:** the owner runs `ast hello.ath` on Windows with nothing else installed; every user-facing file is `.ath`; proving needs at most the Lean toolchain (tier 2) or nothing local (tier 3).
- **Seats:** TAKEN pnp-subproblem 2026-11-26 (facts + plan + conversion lane). Nobody asks the owner: [ASK] lines here; DECIDED after 15 min.
- 2026-11-26 research-desktop TAKEN: literature on small independent Lean kernel checkers (lean4lean, nanoda/nanoda_lib, lean4checker, lean4export) + certificate formats (LRAT/DRAT): sizes, decide-heavy support. Sonnet agent; results here

## research-desktop: small independent checkers (2026-11-26)
Full table: `notes/small-lean-checkers.md`. Short version:
- `leanchecker` ships with the toolchain (v4.28+; present in v4.36): it re-checks oleans in the official kernel. It needs Lean + oleans, so it fits tier 2 / CI. [READ]
- `nanoda` (Rust) is a real external kernel that reads `lean4export` NDJSON and needs no Lean; enable `nat_extension` + `string_extension` for `decide`; axiom allow-list. [READ]
- `lean4lean` is complete (checks Mathlib, 20-50% slower than C++) but needs elan + Lean, so it is not Lean-free. [READ]
- Tier-3 pipeline (INFERRED): CI runs lean4export on the claim modules; users run a prebuilt nanoda with the std-3 axiom allow-list. Measure: export size, nanoda binary size, format compatibility (Dec 2025 Zulip: disagreement on upstream lean4export vs nanoda; pin versions).
- `by decide` over finite searches: an LRAT certificate + verified checker (cake_lpr) is smallest, but only for SAT-shaped claims. [INFERRED]
- 2026-11-26 research-desktop DONE (the agent hit the Sonnet spend limit; done by the seat directly).

## Lines
- 2026-11-26 pnp-subproblem [CHECKED] tier 2 and a tiny tier 3 work NOW (tools/ath_light/README.md, run.sh): with `import Mathlib.Tactic.Basic` removed from W951/SearchCheck.lean, SearchCheck + Asteroid + AsteroidMixed + emitted Asteroid_corpus (30 claims) + Asteroid_mixed compile with plain Lean core (no Mathlib, no lake); axioms propext only. leanexport + nanoda_bin (1.3 MB Rust kernel, ships in the toolchain) re-check the 30 claims from a 1.3 MB export (0.2 MB gz, 811 declarations) in 14 s; a tampered export is rejected. 174 of the 284 emitted theorems (61%) are light, 94 `_project` + ~16 continuous are deep.
- 2026-11-26 pnp-subproblem [PROPOSE] (for the asteroid seat; owner approval via coord): (1) drop `import Mathlib.Tactic.Basic` from SearchCheck.lean (one line; 17 emitted modules become Mathlib-free); (2) emit light claims and `_project` claims into separate files; (3) `ast prove` = Lean core for light claims; `ast check` = shipped certificate + nanoda, no Lean at all; deep claims in CI.
- 2026-11-26 research-desktop: owner asked for GitHub <-> local sync: bin/sync (bash; tested on 6 scenarios: no change, local edit, behind+new file, .env refused, real conflict aborts cleanly with exit 2 and keeps the local commit, --check), bin/sync.ps1 + bin/sync.cmd (Windows; same logic, NOT run: PowerShell unavailable in the session). Never force-pushes; merges (so union-merge boards stay conflict-free).
