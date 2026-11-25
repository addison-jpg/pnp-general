# asteroid for Linux

Two binaries, x86-64, glibc only. Neither needs Python or Lean installed.

- `ast` is the native checker (`asteroid/NATIVE.md`), written in Lean, stripped: 4.3 MB. Small and fast: circuits, claims, the prompt, plots (SVG).
- `asteroid` is the universal language: the full Python implementation with every extension, packed into one file by PyInstaller (`packaging/universal/asteroid.spec`): 45 MB. Python, numpy and matplotlib are inside it. torch and transformers are not, so `propose` lines and `ask.py --model` say the model is missing and go on.

```
curl -LO https://github.com/addison-jpg/pnp-general/raw/main/dist/linux/ast
chmod +x ast
./ast hello.ath --no-proof
```

The same for `asteroid` (`.../dist/linux/asteroid`, then `./asteroid hello.ath --no-proof`).

## ast

Inside a clone of the repository, `ast` finds the Lean project (`one-not/lean`, searched upwards from the binary, the program and the current folder), so `by lean` claims are proved when `lake` is on PATH, and relative `load` paths resolve from the repository. Elsewhere it evaluates only, and says so in one line.

`plot … -> asteroid/out/x.png` in a program outside the repository writes `asteroid/out/x.svg` next to the program (the folder is created).

Arch: `packaging/arch/PKGBUILD` installs `ast` (`makepkg -si`). Windows: install Arch on WSL (`wsl --install archlinux`), then the same, or use `dist/windows/ast.exe`.

Tested on a bare `archlinux:base` root (no Python, no Lean): `hello.ath` and `asteroid/tests/notgate.ath` give the same verdicts as `python3 -m asteroid`.

Rebuild: `cd one-not/lean && lake build asteroid && strip -o ../../dist/linux/ast .lake/build/bin/asteroid` (the Lean target keeps the name `asteroid`; only the shipped file is `ast`).

## asteroid

The code is inside the binary. The data (`.bench` files, findings, `frames.jsonl`, `one-not/lean`) is the repository's: it is searched upwards from the program's folder, the current folder and the binary's folder. Found: the run reads and writes there, as `python3 -m asteroid` does, and `by lean` claims are proved when `lake` is found. Not found: the run evaluates only and says so in one line; `frames.jsonl` then goes to a temporary folder unless `ASTEROID_FRAMES` names a file.

Evidence: `python3 asteroid/tests/test_universal_exe.py` runs the root programs, `asteroid/tests/notgate.ath`, five examples, an `ask` line, a `propose` line, `version`, a missing program and `core/ontology/ask.py --model` through both `python3 -m asteroid --no-lean` and this binary, and checks that the exit codes and the claim lines are identical. Proving with Lean through this binary was not tested (no Lean where it was built).

Rebuild, from the repository root, in a fresh virtual environment outside the repository:

```
python3 -m venv /tmp/v && /tmp/v/bin/pip install pyinstaller numpy matplotlib
/tmp/v/bin/pyinstaller --noconfirm --distpath /tmp/out --workpath /tmp/work packaging/universal/asteroid.spec
cp /tmp/out/asteroid dist/linux/asteroid
```

Both are built by `.github/workflows/exe.yml` (run by hand; it commits them here).
