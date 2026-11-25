# Task: tree-refactor (PROPOSAL, needs Addison's yes before any move)

- **Serves:** a stranger opening the front page of the repository (Addison, 2026-11-25: "also suggest serious git tree refactor if helpful").
- **Problem:** the root has about 30 entries (asteroid, two Lean projects, research folders, boards, generated files, launchers, binaries). A reader cannot tell the language from the research from the working files. The asteroid Lean code sits at `one-not/lean/PEqualNP/AsteroidLang`, inside a research folder named after one result.
- **Status:** proposal only. Nothing moves until Addison says yes on this board. Then one integrating seat does it in one sitting while no other seat is pushing (79 files name `one-not/lean` alone).

## Proposed root

```
README.md  LICENSE.md  LICENSE-APACHE  AGENTS.md
asteroid.exe  hello.ath  hello.bench        front page: download and first program (stay at the root, Addison's call)
asteroid/                                    the language, all of it
  SPEC.md  BENCH.md  NATIVE.md  examples/  programs/  tests/
  python/       today asteroid/*.py (front end, extensions, repl, idle)
  native/       today one-not/lean/PEqualNP/AsteroidLang (own Lean package, no Mathlib)
  editors/vscode/   today editors/vscode
  dist/linux/   packaging/arch/   bin/ (launchers)
  site/         logo, palette, terminal colours
proofs/                                      the Lean developments
  main/         today lean/
  w951/         today one-not/lean (minus AsteroidLang)
research/                                    one-not (non-Lean parts), notes/, philosophy/, worlds/, cpu/, data/, tools/
  LITERATURE.md  SYNTHESIS.md  NAMES.md (generated)  MST.json (generated)
work/                                        boards: BOARD.md, boards/, boards.py, ath_prompts/, ath_prompt_method.md
```

Root goes from ~30 entries to 11.

## Biggest single win if only one move is made

`one-not/lean/PEqualNP/AsteroidLang` → `asteroid/native/` as its own Lake package with no Mathlib requirement. The native binary then builds in seconds on a clean clone with no Mathlib clone at all (today `lake build asteroid` still clones Mathlib to resolve the project, which is most of the Windows CI time). `CoreEq.lean` and `Semantics.lean` (the proofs that tie it to the project's definitions) stay in the W951 project and import the new package.

## How, when approved

1. `git mv` only (history follows), one commit per top-level move, each with every path reference rewritten (`git grep -l OLD | xargs sed`), `lake build` of both projects, `bin/asteroid test --no-lean`, the native verdict check, and the exe workflow green.
2. Leave a one-line `MOVED.md` at each old top-level path for a week, for links from outside.
3. `.gitattributes` union rules, CI paths (`.github/workflows/*.yml`), the PKGBUILD URLs, and the README links are part of the same commits.

## Lines (TAKEN / DECIDED only)
- DECIDED (Addison, 2026-11-25): yes, "refactor aggressively if its ok with big agents". Asked coord/main for objections and a quiet window.
- TAKEN (coord seat, 2026-11-25): tree refactor, prepared on local branch tree-refactor, merged only after coord OK.
