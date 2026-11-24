# Referee B support survey: independent cross-check (research)

Script: 951/tools/referee_b_xcheck/xcheck.py (output: results.json). Run: `python3 -I xcheck.py`, 0.4 s, 1 core.
Referee code was read only for definitions; none of it is imported or copied.

**Method.** For each circuit I used `Circuit.from_dict`, `c.is_correct()` and `c.cone(out_w)`. For every set S I took z_S = `z_of(n,S)` and atoms z|e_u, then `systems.system` and `systems.merges`.
Demand(w) = len(merges[w][2:]) for |S| >= 4. The four supports are A = own 3rd+ merges, B = own merges, C = own cone gates, D = C minus the first two merges of every set (all sets, not only |S| >= 4).
Feasibility is decided by my own augmenting-path max-flow (source -> set cap demand -> gate cap 1 -> sink). networkx was not used.
Input selection: the 43 hand-built paths are read from the file column of referee_b/data/survey_handbuilt.txt. For the corpora I scanned every .jsonl in ess, tri, q and climb, filtered to circuits with exactly one NOT, a set with |S| >= 4 and a correct output. This gave 296 circuits, with the same (file, index) keys as the referee's list. Hard4 holds only logs and was not used.

| group (n circuits) | A mine / ref | B mine / ref | C mine / ref | D mine / ref |
|---|---|---|---|---|
| hand-built (43) | 28 / 28 | 38 / 38 | 43 / 43 | 43 / 43 |
| corpora (296) | 294 / 294 | 296 / 296 | 296 / 296 | 296 / 296 |

B fails on cxU6, cxU8, cxU_6_4, cxU_8_4 and cxP2, the same five circuits the referee lists. A fails on the same 15 hand-built circuits and the same 2 corpora circuits (climb/relseeds#7, climb/climb_seeds#3) as the referee. The per-circuit demand values and A/B/C/D flags match on all 339 circuits.

**Disagreements: none.** No circuit raised a merge assertion (no 3-way merge, and every S ends connected).

**Two pitfalls hit during the check (my bugs, now fixed).**
- Gate-to-sink capacity was accumulated across sets instead of fixed at 1, which made A and B falsely feasible.
- A leftover n <= 14 filter dropped 6 circuits with n = 15..18. The referee's `correct()` returns None for n > 14 and treats that as not-incorrect, so those circuits are kept unchecked. Here they pass `c.is_correct()`.

**Verdict: AGREE.** I found no bug in either `tools/w951` `systems.system`/`merges` or referee_b's own merge reimplementation on this set. Caveat: the check shares the definitions (z_S, atoms, first-two-merge removal) with the referee, so it tests the implementation, not whether the definitions are the right ones.
