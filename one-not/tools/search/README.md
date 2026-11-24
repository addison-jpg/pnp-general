# one-not/tools/search: the outward search

A circuit is a dict `{"n","sets","gates","outs"}`. `core.py` (tables, correct, witness, slack, prune, and the no-rewire filter),
`conjectures.py` (REGISTRY of predicates returning `(margin, detail)`, margin < 0 = counterexample), `hunt.py` (hill climbing).
Run from the repo root. Serves C2, C3, C4.

## Added (main's Sonnet B, 2026-11-24)
- `core.py`: `all_read`, `live_gates`, `topo_sort`, `gate_saving_rewirings` / `gate_saving_rewire` (README L2 `MinCE.no_rewire`: move one
  input of one gate to any wire outside the gate's fan-out, later wires allowed; keep if all outputs stay correct and some gate becomes
  unread), `apply_rewire`, `reduce` (prune + rewirings until none; `rng` = random order, `keep_not` = reject rewirings that unread the NOT gate),
  `faces_incorrect`. Unit check: `witnesses/nonlocal/match_c_k7.json` has exactly 3 gate-saving rewirings, one is (gate 41 = NOT, input 1, wire 64).
- `conjectures.py`: `is_irreducible_read_not` (helper), registry entries "C2 one-point step under no-rewire" (vacuous +1 unless exactly one NOT,
  all gates read, no gate-saving rewiring, n <= 8; else min over every cube with positive base of the best slack drop, OR-only witnesses)
  and "NOT gate read and irreducible" (indicator 1/0, never negative).
- `irreducible.py`: generator (witness files + fano_sat66 + w951 instances + cxT2 (fc), junk via rewrite/mutate, random-order `reduce`,
  mode A plain, mode B keep_not; keep correct, one NOT, all read, no rewiring, both faces incorrect), then the step predicate (n <= 9 here).
- `run_all.py` -> `registry_table.md`: every REGISTRY entry x every correct witness file with n <= 9 (19 files). Only negative margins: the
  `general_count_below_base_*` files on the two count predicates (known, t >= 4 NOT gates).
- `hunt.py`: `main()` now guarded by `__name__`, so `mutate`, `rewrite`, `or_tree` can be imported.

## Counts (seed 7, 240 s, one process)
2,196 random-order reductions (650 mode A, 1,546 mode B). Irreducible with the NOT read: 14 (A), 25 (B); with both faces incorrect: 10 (A), 17 (B);
12 DISTINCT circuits (saved `found/irreducible_seed7.jsonl`; n = 7 to 9, 17 to 30 gates; most descend from cxT2 (fc)). One-point step under
no-rewire at every cube with positive base: held on all 12 (min margin 0, no negative). Keeping the NOT alive is the hard part: the
random walk from junk almost never reaches the class; the bias (mode B) roughly doubles the yield per reduction.

## Commands
    python3 -I one-not/tools/search/irreducible.py 240 7     # generator + step on each
    python3 -I one-not/tools/search/run_all.py               # writes registry_table.md
    python3 -I one-not/tools/search/hunt.py "C2 one-point step under no-rewire" 120 1 7
