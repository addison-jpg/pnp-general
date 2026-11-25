# Demo path (tested 2026-11-25, branch refactor/pillars)

Every command below ran from the repository root, exited as shown, and took under 4 seconds. First: `git pull` on `refactor/pillars`.

Set this once, so the `.ath` runs do not add lines to `frames.jsonl` during the demo:

    export ASTEROID_FRAMES=/tmp/demo_frames.jsonl

| step | command | what it shows | time |
|---|---|---|---|
| 1 | `python3 -I core/ontology/ask.py status` | plain-English query over the whole store, every line labelled | 0.1 s |
| 2 | `python3 -I core/ontology/ask.py what connects beauvoir and time` | the ontology answering a cross-field question from recorded checks | 0.1 s |
| 3 | `bin/asteroid --no-lean hello.ath` | the language: claims checked, "claims: 4 true, 0 false" | 0.9 s |
| 4 | `bin/asteroid --no-lean physics/curvature/curvature.ath` | physics from below: curvature from counting, frames labelled checked or open | 3.4 s |
| 5 | `python3 -I philosophy/cone.py` | the cone and the disk, exhaustive over 33,867 graphs, then the repository measured | 1.9 s |
| 6 | `bin/asteroid --no-lean culture/queer/queer.ath` | remove the two sides from the love model: stability fails on 48 of 1296 profiles | 0.8 s |
| 7 | `python3 -I core/ontology/pr_route.py origin/main origin/mst-lean` | a pull request qualified from the memory cache: superseded (exit 1 is the verdict, not a crash) | 0.5 s |

Avoid live in the demo: `big.ath` (about 80 s) and the `--model` path of `ask.py` (the first call loads a model, about 75 s).
