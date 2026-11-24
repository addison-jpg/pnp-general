# 951: one NOT gate saves nothing on (1,1)-disjoint Boolean sums

Rung 1 of the NOT gate ladder on the main board. This directory is a one-to-one copy of the 951 work from the private repository addison-jpg/pequalnp-work (branches `coord-951` ee11077, `board`, `front-match` 169cec0). `lean/` is a separate Lake project with the same Lean and Mathlib pins as `../lean`, kept apart because its `Kernel/Circuit.lean` and `Defs` differ.

## State

- The only `sorry` is `no_minCE` in `lean/PEqualNP/W951/MinCE.lean`: there is no minimal counterexample.
- The open target in its sharpest Lean form is `MergePrice` for a minimal counterexample.
  This is the dual load inequality: for all prices pi >= 0, sum_w min_z pi(M_z(w)) <= pi(gates).
  `no_minCE_of_mergePrice` is proved in `MergeFrac.lean`.
- Other proved routes to `no_minCE`:
  - `no_minCE_of_liftClassFrac` (LiftFrac)
  - `no_minCE_of_liftedBound` (LiftBound, equivalent to 951)
  - `no_minCE_of_FJ` (LiftFJ)
- Module map: `work/W951.md`. Guide for writing new Lean here: `work/TRACTABILITY.md`.

## Build and check

```bash
cd 951/lean && lake build
```

```bash
cd 951 && bash work/bin/merge951.sh /tmp/W951_one.lean
```

The `lake build` must finish with exactly one `sorry` warning outside `PayDraft.lean`, which is a parked
draft. The `merge951.sh` script writes the whole development to one file. That file must compile with
0 errors and exactly 1 sorry. `#print axioms PEqualNP.Outside.L_meta_951` must show only propext,
sorryAx, Classical.choice and Quot.sound.

Checked when copied (2026-11-24, coord): full build OK, one-file 0 errors / 1 sorry, axioms as above.

## Folders (paths from this directory)

- `board/`: the 951 board (BOARD.md, PROTOCOL.md, agents/), frozen.
- `work/`: setup and notes. `work/TASKS.md` is the task list. `bash work/bin/setup.sh` (elan, Mathlib cache), `work/bin/check.sh L-meta-1234` (checks a finished proof). `work/notes951/crossworld_ii/`: is hypothesis (ii) of `CrossWorldAt.ndep` true on merge sets; no, it does not follow from clean / live / essential (`W951/CrossWorldCex.lean`, `cx3_counterexample`); run `NOMIX_ROOT=<root>/ NOMIX_DC=<data-corpora checkout> python3 cw2.py out.jsonl`.
- `research/front612/`: no_minCE numerics (support-B), Config (I) prices, MergeFrac LP, `CfgIWorld0.lean`; Python/LP data, research evidence not a 951 row.
- `research/heredity/`: is the restricted pure menu inside the original one; I1 yes, I0 with top-only options no (`heredity_top_fails` in `W951/PureHeredity.lean`). `python3 research/heredity/graph_full.py`
- `tools/w951/`: one Python toolkit for the L-meta-951 experiments (circuit, systems, lp, rules, matching, sat). `python3 tools/w951/tests/test_w951.py`
- `tools/sdrcert/`: Python finds MergeSDR certificates, Lean checks them (`W951/SDRWitness.lean`). `cd tools/sdrcert && python3 export.py /tmp/sdr.lean`
- `tools/kill_tests/`: CPU-only kill tests behind `PROOF_PLAN_SUGGESTIONS.md`. `python3 951/tools/kill_tests/canon.py 951 10` from the repository root.
- `tools/fano/`: the exact corpus of 80,198 correct one-NOT circuits for PG(2,2), base 14, and the F2 test (10,265,344 cases, 0 failures). `python3 tools/fano/fano_corpus.py OUT.jsonl`
- `tools/referee_b/`: Python pre-check of a candidate merge-tree charge (discovery, not proof). `python3 tools/referee_b/check_charge.py CHARGE.json`
- `tools/l951_charging/`: L-meta-951 charging scaffold (helper tooling, not a proof). `python3 tools/l951_charging/inj951.py`
- `tools/research951/`: relaxation SAT, nauty sweeps, citation crawl, weight-bounded barrier plane. `python3 tools/research951/relax.py '<json sets>' n s mode`; needs python-sat, networkx, nauty.
- `tools/stat_search/`: naive-Bayes-guided upper bounds and SAT search for edge functions (helper tooling, not a proof). `python3 tools/stat_search/nb_search.py graph q3`; needs python-sat.
