# Hypothesis (ii) of `CrossWorldAt.ndep` on merge sets (tractability's question, 2026-11-24 09:08)

Question: at a MinCE, is (ii) `C0(g)(Zof S_a) = 0` true for every gate `g` of `M_z(a)` at every world-0 zero point `z` of
`S_a`, so that a cross-world gate under (i) alone is N-dependent (`MinCE.crossWorld_ndep`)?

Corpus: gAdyD's `nomixed.corpus()` (branch `nomixed-951`, `work/nomixed951/nomixed.py`; front's allcirc + chist + cxrb, plus
scaffold's `data-corpora` 2aa9856 via `NOMIX_DC`): 34,064 correct one-NOT circuits. Merge sets: front's `mg.merges`.
`live` = every gate wire is read by a gate or is an output; `ess`, `clean` as in front's lib.py (part2.py).

| Check | circuits failing | live + essential + clean failing | smallest s - base among those |
|---|---|---|---|
| (ii) for every merge gate at a world-0 point (`cw.py`) | 1,476 | 155 | 5 |
| cross-world gate under (i) is N-dependent (`cw2.py`) | 174 | 60 | 5 |

Cross-world pairs under (i): 421, of which (ii) fails on 245. No failure among the essential clean circuits with
s - base <= 4 (842 circuits). The 60 live essential clean failures are in `cross_ndep_fail_live_ess_clean.jsonl`
(`bad` = [gate, a, z, b, z', (ii) holds]; points are bitmasks). The smallest, `ess/ess_k4e_clean.jsonl:627`, is checked in
Lean: `W951/CrossWorldCex.lean`, `cx3_counterexample` (live, clean, essential, cross-world under (i), N-independent).
VERDICT: `MinCE.crossWorld_ndep` does not follow from clean / live / essential; it needs near-optimality or more.

Run: `NOMIX_ROOT=<root>/ NOMIX_DC=<data-corpora checkout> python3 cw2.py out.jsonl` with `nomixed.py` beside it
(root as in nomixed951/README.md); about 3 minutes on 4 cores; needs scipy (imported by front's modules).
