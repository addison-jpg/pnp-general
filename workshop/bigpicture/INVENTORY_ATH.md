# .ath and .lean inventory

Scope: /home/user/pnp-general, excluding `.git` and `.venv`. Counts come from `find` and `wc`. Read-only.

## Table by top-level folder

| Top-level folder | .ath files | .lean files | README present |
|---|---|---|---|
| (root) | 20 | 0 | yes (README.md) |
| physics | 3 | 0 | no |
| philosophy | 3 | 0 | yes |
| math | 4 | 0 | no |
| culture | 8 | 0 | no |
| core | 12 | 0 | no |
| biology | 0 | 0 | no |
| workshop | 20 | 18 | no |
| one-not | 0 | 219 | yes |
| lean | 0 | 1669 | no |
| asteroid | 21 | 3 | yes |

## Per-directory .ath counts (README)

- (root) 20 (yes)
- asteroid 1 (no); asteroid/examples 6 (no); asteroid/out 1 (no); asteroid/programs 9 (yes); asteroid/tests 4 (no)
- core 0 (no); core/ontology 2 (no); core/ontology/joins 10 (no)
- culture 0 (no); culture/art 2 (no); culture/homestuck 1 (yes); culture/love 1 (yes); culture/narrative 1 (no); culture/queer 1 (no); culture/race 1 (no); culture/social 1 (yes)
- math 0 (no); math/language 2 (no); math/qwen 2 (no)
- philosophy 2 (yes); philosophy/metaphysics 1 (no)
- physics 0 (no); physics/blackhole 1 (no); physics/curvature 1 (no); physics/time 1 (no)
- workshop 0 (no); workshop/ask 1 (no); workshop/asks 1 (no); workshop/board 1 (yes); workshop/board_formal 2 (no); workshop/board_formal/head 1 (no); workshop/bus 3 (yes); workshop/little 1 (no); workshop/mobius/checks 3 (no); workshop/orchestra 1 (no); workshop/pair 1 (no); workshop/recovery 1 (yes); workshop/route 1 (no); workshop/steinmetz 2 (no); workshop/windows 1 (yes)
- one-not 0 (yes); lean 0 (no); biology 0 (no)

## Totals

.ath: 91 (root 20, asteroid 21, core 12, workshop 20, culture 8, math 4, physics 3, philosophy 3, biology 0, one-not 0, lean 0). .lean: 1909 (lean 1669, one-not 219, workshop 18, asteroid 3).

## Not checked

The .ath files were not run. No asteroid or ast commands were executed, and no .lean file content was read or built. Counts are file counts by name only. No commits, pushes, installs, or model API calls were made.
