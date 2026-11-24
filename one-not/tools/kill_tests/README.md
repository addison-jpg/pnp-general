# Kill tests for the open step of `no_minCE`

CPU-only scripts (plain Python, no dependencies) behind `one-not/PROOF_PLAN_SUGGESTIONS.md`.
Each takes the corpus root as its first argument and reads every `.json` / `.jsonl` circuit
(`n`, `sets`, `gates`, `outs`) below it; `canon.py`, `fam.py`, `match.py` take a second argument,
the largest `n` (default 11).

| Script | What it checks |
|---|---|
| `canon.py` | lemmas W0, W1, X; collisions of the canonical start; whether its options admit an SDR |
| `fam.py` | which option family admits an SDR of merge sets (interval classes, plain zero points) |
| `match.py` | the same with the matching (exact Hall) form on count sets |
| `probe.py` | for circuits listed on stdin: every SDR over plain zero points, by world of each pick |
| `order.py` | whether a fixed order of the sets makes every partial disjoint choice extendable |

Run from the repository root, for example: `python3 one-not/tools/kill_tests/canon.py one-not 10`.
