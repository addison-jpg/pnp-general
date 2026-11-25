# Task: asteroid-term (asteroid.exe as a real terminal, native backend)

- **Serves:** the beginner who double-clicks `asteroid.exe` (Addison, 2026-11-25: "make popup terminal beautiful. i dont want a jank widget, this can be nice, like git bash on linux nice. honestly linux backend is probably a really good step rn"; "if linux backend works well we wouldnt need to depend on python as much, prob not matplotlib as much, and very minimal lean").
- **Superseded (Addison, 2026-11-25, later): "its still possible mint is somewhat of a bottleneck, try switching to raw linux at its most basic (arch) if this is tedious (it is)".** The target is now plain Linux, tested on Arch at its most basic (`base`, no Python, no Lean). On Windows the same binary runs in Arch on WSL (`wsl --install archlinux`), in Windows Terminal. The mintty paragraph below is kept for the record and not pursued.
- **Was decided (Addison, 2026-11-25):** the window is **mintty** (Git Bash's terminal) with its MSYS2 runtime, bundled in a zipped folder: double-click opens a real mintty window running the asteroid prompt in the 4STeroid colours (`site/terminal.json`). Replaces the tkinter/IDLE window of `asteroid/idle_exe.py`.
- **Backend direction:** the native Lean `asteroid` executable (`asteroid/NATIVE.md`), not Python. It needs no Lean install to evaluate; Lean (lake) only for `by lean`. Python and matplotlib become optional fallbacks, then go.
- **Not now:** a GitHub Release or tag (QUIET); code signing (owner action, see asteroid-exe NOTE).

## Seats (one Sonnet each, in this order; each writes TAKEN/DECIDED below)

1. **native-small**: drop the Mathlib import from the `.bench` reader (`one-not/lean/PEqualNP/AsteroidLang/Bench.lean` → its own `Gate`/`Circ`, NATIVE.md "What remains" item 5). Done when `lake build asteroid` gives a binary well under 100 MB, verdicts still equal `python3 -m asteroid` on hello/first/notgate, and `lake build PEqualNP.Verify.All` passes.
2. **arch**: the native `asteroid` binary on bare Arch Linux: `packaging/arch/PKGBUILD` (builds with elan + lake, installs one binary to /usr/bin/asteroid), tested in an `archlinux` base chroot with no Python and no Lean: `asteroid hello.ath --no-proof` gives the same verdicts as Python. One README line: Arch / WSL install. (Replaces term-bundle / mintty.)
3. **native-repl**: the interactive prompt in the native binary (what `bin/asteroid` with nothing typed does in Python: banner, prompt, one line at a time).
4. **native-plot**: `plot phi` in the native binary, writing SVG directly (no matplotlib).
5. Later, one seat each: `corpus`, `hunt`/`search`, `mixed`, the rest of the term language (NATIVE.md "What remains" 1–3).

## Lines (TAKEN / DECIDED only)
- TAKEN (coord Sonnet seat, 2026-11-25): seat 1 native-small.
