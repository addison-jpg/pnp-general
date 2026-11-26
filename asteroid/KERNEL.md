# asteroid kernel: Lean core only (branch ath-small-deps; owner-approved lane, not merged)

**Change:** one line removed from `one-not/lean/PEqualNP/W951/SearchCheck.lean`: `import Mathlib.Tactic.Basic`.
SearchCheck (`Circ`, `correctB`, slack and witness checkers), `Asteroid` and `AsteroidMixed` are the kernel the
emitter's `build_lean()` targets; with this change the kernel imports nothing outside Lean core.

**Mathlib imports, before → after**
| module set | before | after |
|---|---|---|
| kernel: W951/SearchCheck, W951/Asteroid, W951/AsteroidMixed | `Mathlib.Tactic.Basic` (via SearchCheck) | none |
| 13 emitted light modules (Asteroid_beyond_one_not, _conjecture, _continuous, _corpus, _demo, _first, _ladder, _many_not, _mixed, _refuted, _theorem; + SearchCheck_t4, SearchCheck_tmin) | `Mathlib.Tactic.Basic` (via SearchCheck) | none |
| AsteroidLang/Core, Bench, BenchTest | none / `Mathlib.Tactic.Basic` (BenchTest via SearchCheck) | none |
| deep: AsteroidCheap, AsteroidSound2, emitted `*_sound`, Asteroid_edges / _hello / _little, Semantics, CoreEq | `Mathlib` | `Mathlib` (unchanged) |

**Checked (2026-11-26, toolchain v4.36.0, plain `lean`, no lake, no Mathlib on LEAN_PATH):** all 19 modules that import
the kernel and nothing from Mathlib directly compile: SearchCheck, Asteroid, AsteroidMixed, SearchCheck_t4,
SearchCheck_tmin, AsteroidLang/Core, Bench, BenchTest, and the 11 emitted light Asteroid_* modules listed above
(longest: Asteroid_theorem 34 s). The other importers of the kernel import Mathlib themselves, so they are unaffected.
A light claim's axioms: `propext` only.

**Re-check without Lean:** `leanexport` + `nanoda_bin` (both in the v4.36 toolchain) re-check Asteroid_corpus's 30 claims
from a 1.3 MB export (0.2 MB gz) in 14 s; a tampered export is rejected. Script: `tools/ath_light/run.sh` on main.

**Not in this lane (needs the asteroid.py owner + owner go in that seat):** emitting light claims and `_project` claims into
separate files; `ast prove` / `ast check` commands.
