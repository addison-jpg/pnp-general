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

## .ath only: the 14 loaded circuit files (second lane; branch ath-small-deps)

- **Loaders (additive):** `let NAME = load FILE.ath` reads an .ath circuit file holding exactly one `circuit NAME N ... end`
  block (the same block syntax programs already use). Python: `circ_of_ath` in `asteroid/asteroid.py`. Native:
  `AsteroidLang/Main.lean resolve`, via the existing program parser. `.bench` and `.json` loads still work.
- **Converted (13 files; the 14th load target is hello.bench by another path):** each `X.json` / `X.bench` → `X.circ.ath`
  next to it (`asteroid/to_ath.py`; `.circ.ath` so it never collides with a program `X.ath`). Wire numbering is kept
  exactly (inputs by number, gate k = `g<k>`). Round trip, all 13: old loader's circuit == `circ_of_ath(new file)`, exactly.
  The old files are KEPT until the owner says delete.
- **Programs:** all 36 load lines in 19 `.ath` programs now load `.circ.ath`; none loads `.json` / `.bench` any more.
- **Same results (`--no-lean`):** Python, 19 programs: 15 byte-identical (after path/timing normalization); 3 differ only in
  randomized `hunt` move counts and timestamped log names; `workshop/little/attempt.ath` was FAILING before
  (`load: no file hello`) and now loads. Native (`lean --run` of AsteroidLang/Main, Lean core only): hello, first, mixed,
  refuted give identical claim lines with the old and new loader.
- **Not done:** corpora read by `corpus W = GLOB` (*.json / *.jsonl) are data, not loaded files; out of scope.
