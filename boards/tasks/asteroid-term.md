# Task: asteroid-term (asteroid.exe as a real terminal, native backend)

- **Serves:** the beginner who double-clicks `asteroid.exe` (Addison, 2026-11-25: "make popup terminal beautiful. i dont want a jank widget, this can be nice, like git bash on linux nice. honestly linux backend is probably a really good step rn"; "if linux backend works well we wouldnt need to depend on python as much, prob not matplotlib as much, and very minimal lean").
- **Decided (Addison, 2026-11-25):** the window is **mintty** (Git Bash's terminal) with its MSYS2 runtime, bundled in a zipped folder: double-click opens a real mintty window running the asteroid prompt in the 4STeroid colours (`site/terminal.json`). Replaces the tkinter/IDLE window of `asteroid/idle_exe.py`.
- **Backend direction:** the native Lean `asteroid` executable (`asteroid/NATIVE.md`), not Python. It needs no Lean install to evaluate; Lean (lake) only for `by lean`. Python and matplotlib become optional fallbacks, then go.
- **Not now:** a GitHub Release or tag (QUIET); code signing (owner action, see asteroid-exe NOTE).

## Seats (one Sonnet each, in this order; each writes TAKEN/DECIDED below)

1. **native-small**: drop the Mathlib import from the `.bench` reader (`one-not/lean/PEqualNP/AsteroidLang/Bench.lean` → its own `Gate`/`Circ`, NATIVE.md "What remains" item 5). Done when `lake build asteroid` gives a binary well under 100 MB, verdicts still equal `python3 -m asteroid` on hello/first/notgate, and `lake build PEqualNP.Verify.All` passes.
2. **term-bundle**: `.github/workflows/exe.yml` builds a folder: mintty + msys-2.0.dll (from the runner's MSYS2) + the native `asteroid.exe` + a launcher `asteroid.exe` that opens mintty on the asteroid prompt, themed from `site/terminal.json`, 4STeroid icon. Zip it; commit if < 100 MB (raw link on the front page), else CI artifact. Ship mintty's GPL licence text and source link in the folder. Smoke test on the runner.
3. **native-repl**: the interactive prompt in the native binary (what `bin/asteroid` with nothing typed does in Python: banner, prompt, one line at a time).
4. **native-plot**: `plot phi` in the native binary, writing SVG directly (no matplotlib).
5. Later, one seat each: `corpus`, `hunt`/`search`, `mixed`, the rest of the term language (NATIVE.md "What remains" 1–3).

## Lines (TAKEN / DECIDED only)
- TAKEN (coord Sonnet seat, 2026-11-25): seat 1 native-small.
- DECIDED (coord, 01:29): main takes seat 3 native-repl and seat 4 native-plot (one Sonnet each), plus the Linux test pass on seat 1's binary when it lands (clean clone, lake build asteroid, hello/first/notgate from another folder, a path with a space, CRLF files). Seat 2 term-bundle stays with coord's seat line (asteroid-vscode seat, which scoped this board).
