# B3: SAT search for two or more NOT gates beating base

Script: `B3_sat_manynot.py n m [t,..]` (python-sat, Cadical153). No SAT hit; no .bench written.

**Definition reused** (from `research/one-not/tools/beyond_one_not/enum_small.c`): gate count = every fan-in-2 AND/OR plus every NOT.
System = m input sets (antichain, each of size >= 2, covering all n inputs, up to permutation); output = OR of a set.
base = least gate count with no NOT gate, found here by SAT (t = 0, s increasing). Query: s = base - 1 total gates, at most t NOT gates,
all outputs correct on all 2^n inputs, topological order. Sanity: s = base, t = 0 and t = 1 return circuits that the independent evaluator accepts.

**Region covered, t = 2 and t = 3, s = base - 1: UNSAT in every case.**
- n = 4: m = 2..6, all 14 systems.
- n = 5: m = 2..7, all 148 systems; m = 8: 6 of 7 (the system {012,013,014,023,024,123,134,234}, base 11, was stopped at the time limit, no result).
- n = 6: m = 2, 3, all 56 systems. n = 6, m = 4 not run.
Total 224 systems, 448 UNSAT answers. Each run took seconds (n = 5, m = 8 minutes). Any SAT answer would be decoded, re-evaluated by a separate truth-table evaluator (`check`) and written as `.bench`.

What this says: on these systems, 2 or 3 NOT gates do not give fewer than base gates. It says nothing beyond them (larger n, t >= 4, the unfinished systems).
