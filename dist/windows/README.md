# asteroid for Windows

- `ast.exe` is the native checker (`asteroid/NATIVE.md`), written in Lean: 4.2 MB, no Python inside. Circuits, claims, the prompt, plots (SVG).
- `asteroid.exe` is the universal language: the full Python implementation with every extension, packed into one file by PyInstaller (`packaging/universal/asteroid.spec`). It is built by `.github/workflows/exe.yml` on `windows-latest`; until that workflow has run on this branch, the file is not here.

Download either from the front page (README.md) and double-click it: it opens the asteroid prompt. Or, in a terminal:

```
ast.exe hello.ath --no-proof
asteroid.exe hello.ath --no-proof
```

Windows SmartScreen warns, because the files are not signed: click "More info", then "Run anyway".

Inside a clone of the repository both find the Lean project (`one-not/lean`), so `by lean` claims are proved when `lake` is on PATH or in `%USERPROFILE%\.elan\bin`. Elsewhere they evaluate only and say so in one line.

Nothing in this folder was run on Windows by hand: the workflow's smoke test (`version`, `hello.ath --no-proof`, `asteroid\tests\notgate.ath` exits 1) is the only Windows check. Linux builds of both: `dist/linux/README.md`.
