# A5: F2-transfer tested at exactly one NOT gate

Seat A5, board `boards/tasks/open-one-not.md`, 2026-11-25. Words: **tested** = computed, not proved. No proof of `no_minCE`.

## Result

For every circuit with exactly one NOT gate that I could collect (3,263 distinct correct circuits, n = 4..10), at every restriction
(Q, D) with base' > 0 (x_Q = 1, x_D = 0): **|F2'| >= base'. Zero failures in 1,353,627 restrictions** (637,948 with the NOT gate alive,
715,679 with it killed). Same with the any-gate witness. Control: the same code on A1's 4-NOT circuit
`general_count_below_base_min.json` finds 248 negative restrictions (170 NOT-alive, 78 NOT-killed), the 248 of A1, so the code does see the failure when it exists.

## Region covered

- All 3,612,033 restrictions (Q, D) of the 3,263 instances (those with base' = 0 are trivial). n: 4: 670, 5: 892, 6: 1,226, 7: 390, 8: 9, 9: 75, 10: 1.
  All have pairwise set intersections <= 1.
- Sources: 260 circuit dicts in the repo's json/jsonl files (witnesses, nonlocal, beyond_one_not, referee_b, climb_*.jsonl, found/irreducible_seed7); 3,003 from `f2lib.corpus(9) + randgen(1, 3000)` (the c3_allq corpus,
  one NOT gate); 22 new irreducible read-NOT circuits made by `research/one-not/tools/search/irreducible.py` (seeds 101..104, 240 s each, kept in `A5_irreducible_gen.jsonl`; every gate read, no gate-saving rewiring, both faces incorrect). The circuits with n > 10 or t != 1 were skipped
  (2,274 of 5,809 raw dicts).
- Checked twice: (1) numpy truth tables (`continuous.slack_table`, A1's definition); (2) an independent pure-Python evaluator (`f2_indep`, no tables) on 1,600 states
  (random states of the small instances), 0 mismatches. There was no failure to write as `.bench`; none was written.

## Where the NOT gate is: gates' - |F2'| (OR-only F2; gates' = AND/OR gates non-constant on the subcube)

| NOT gate | states | min | mean | states with gates' = \|F2'\| | states with \|F2'\| = base' (tight) |
|---|---|---|---|---|---|
| alive (output non-constant on the subcube) | 637,948 | 0 | 10.55 | 2,924 (0.46%) | 112,323 (17.6%) |
| killed (constant) | 715,679 | 0 | 7.89 | 12,268 (1.7%) | 195,536 (27.3%) |

Full histograms: `A5_transfer_t1.out`. Reading: the inequality is tight (|F2'| = base') in both regimes, and a killed NOT gate (monotone restricted circuit)
is tighter than an alive one. Nothing in these numbers shows the NOT gate being *used* by the inequality: no instance has a restriction where the inequality needs the NOT gate to be alive.
The only evidence of where one NOT gate matters stays A1's: with 4 NOT gates the inequality fails (a De Morgan block needs >= 2 NOTs).

## What this does and does not say

- It supports that F2-transfer is true at t = 1 on this corpus; it proves nothing. The corpus is mostly small n and generated circuits, and irreducible ones are few (22 new + 12 stored) because the generator is slow.
- It gives no extra lemma: transfer holds in the killed regime too, so the NOT-sensitive part of a proof is not "the NOT gate is alive".
- Gap: no t = 1 circuit of n >= 8 beyond 85 instances was run.

## Files / rerun (from the repo root)

`python3 -I research/one-not/research/open/A5_transfer_t1.py --maxn 10 --gen research/one-not/research/open/A5_irreducible_gen.jsonl --gen research/one-not/tools/search/found/irreducible_seed7.jsonl` (about 4 min).
Output: `research/one-not/research/open/A5_transfer_t1.out`.
