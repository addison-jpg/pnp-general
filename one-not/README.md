# one-not: one NOT gate saves nothing on (1,1)-disjoint Boolean sums

Rung 1 of the NOT gate ladder on the main board. A copy of the one-NOT work from the private repository addison-jpg/pequalnp-work (branches `coord-951`, `board`, `front-match`). `lean/` is a separate Lake project with the same Lean and Mathlib pins as `../lean`; its `Kernel/Circuit.lean` and `Defs` differ from `../lean/PEqualNP`.

## State

Mini board of this directory (final pass, 2026-11-24). Up: [`../README.md`](../README.md) (the proof), [`../boards/one-not.md`](../boards/one-not.md) (the board of this directory). Names: [`../NAMES.md`](../NAMES.md).

- The only `sorry` is `no_minCE` in `lean/PEqualNP/W951/MinCE.lean`: there is no minimal counterexample.
- Checked: the statement holds when the certificate game (U-game) on the lifted outputs is won (`W951/PureMore.lean`, `no_minCE_of_ugame`); when the NOT gate reads an input (`NotVarF2`); when every cube is local or has a point step (`CubeF2.lean`).
- Open: circuits that lose the certificate game (smallest: sets {0,1,2}, {0,3,4}, NOT input x1 ∨ x3; hard core: three 4-sets in a triangle, `cxT2`); the point step for real-witness gates (F2) among circuits with no gate-saving rewiring (R6).
- Dead: [`DEAD_ENDS.md`](DEAD_ENDS.md), seven families. The price inequality over REAL merge sets (`MergePrice`) is false without minimality (STAR4); the lifted forms are the target.
- Other proved routes to `no_minCE`: `no_minCE_of_liftClassFrac` (LiftFrac), `no_minCE_of_liftedBound` (LiftBound, equivalent to 951), `no_minCE_of_FJ` (LiftFJ), `no_minCE_of_mergePrice` (MergeFrac).
- Findings: [`FINDINGS_2026-11-24.md`](FINDINGS_2026-11-24.md). Notes by part of the route: [`board/agents/INDEX.md`](board/agents/INDEX.md). Witness circuits: `data/witnesses/`.
- Module map: `work/W951.md`. Guide for writing new Lean here: `work/TRACTABILITY.md`.

## Build and check

```bash
cd one-not/lean && lake build
```

```bash
cd one-not && bash work/bin/merge951.sh /tmp/W951_one.lean
```

The `lake build` must finish with exactly one `sorry` warning outside the parked `PayDraft` section of `W951/MiscSmall.lean` (a draft with its own placeholders); the one counted is `no_minCE` in `W951/MinCE.lean`. The `merge951.sh` script writes the whole development to one file. That file must compile with 0 errors and exactly 1 sorry. `#print axioms PEqualNP.Outside.L_meta_951` must show only propext, sorryAx, Classical.choice and Quot.sound.

## Folders (one bullet each; run from the repository root)

- `tools/w951/`: one Python toolkit (Circuit, systems, lp, rules, matching, sat) for the experiments. `python3 one-not/tools/w951/tests/test_w951.py` (about 80 s).
- `tools/kill_tests/`: CPU-only scripts for the open step of `no_minCE`, each takes the corpus root. `python3 one-not/tools/kill_tests/canon.py one-not 10`.
- `tools/search/`: the outward search: conjectures as predicates (`conjectures.py`), a mutation hunter. `python3 -I one-not/tools/search/hunt.py "C4 count (any-gate witnesses)" 170 4 34`.
- `tools/fano/`: Fano-plane corpus and exact menus. `python3 one-not/tools/fano/fano_corpus.py OUT.jsonl` (80,198 circuits, about 1 min), then `f2check.py OUT.jsonl`.
- `tools/sdrcert/`: Python finds merge-set certificates, Lean checks them (`W951/SDRWitness.lean`). `cd one-not/tools/sdrcert && python3 export.py /tmp/sdr.lean`.
- `tools/stat_search/`: naive-Bayes-guided upper bounds and SAT search for edge functions (helper tooling, not a proof). `python3 nb_search.py bench`; needs `pip install python-sat`.
- `tools/l951_charging/`: charging scaffold for L-meta-951 (helper tooling, not a proof). Scripts such as `inj951.py`, `exh951.py`; `STATUS.json`, `INBOX.json`.
- `tools/research951/`: research session tools: SAT relaxation, nauty sweeps, citation crawl. `python3 one-not/tools/research951/relax.py '<json sets>' n s mode`; needs python-sat, networkx, nauty.
- `tools/referee_b/`: see its README.
- `research/heredity/`: do restricted pure menus stay inside the original menu? `python3 research/heredity/menu_restrict.py` from `one-not/` (answer: not with top-only options; witness `witness.json`, `heredity_top_fails` in `W951/PureHeredity.lean`).
- `research/support-b/`: no_minCE numerics, Config (I) prices, MergeFrac LP; Python/LP data, `cfgI/CfgIWorld0.lean`. Corpora are not copied (`harness.py` expects `supportB/corpora/`).
- `work/`: the workspace: `work/bin/setup.sh` (one-time), `python3 work/bin/stmt.py L-meta-951 --lean`, `work/bin/check.sh L-meta-1234`; `TASKS.md`, `statements/`, `drafts/`, `done/`.
- `work/notes951/crossworld_ii/`: hypothesis (ii) of `CrossWorldAt.ndep` on merge sets; fails on 60 live essential clean circuits, smallest checked in Lean (`W951/MiscSmall.lean`, `cx3_counterexample`). `NOMIX_ROOT=<root>/ NOMIX_DC=<data-corpora checkout> python3 cw2.py out.jsonl`.
- `data/scaffold/`: the 66 SAT Fano circuits are `../fano_sat66.json`; the size-ladder corpora `pg13.jsonl` (2,159 circuits) and `ag16.jsonl` (65), `FINDINGS_scaffold.md`, `ladder_REPORT.md`.
- `../data/edge-function-encoder/`: faster exact synthesis for f_G (note 1): `fast_synth.py` (exact-k encoder), `portfolio.py` (sym=0 and sym=1 in parallel), `t1.py` (checks P3=2, P4=4, P5=5, C4=3, C5=7). SAT computation, not Lean-checked. `pip install python-sat networkx`.
