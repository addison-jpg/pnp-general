> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: search-harness

- **Serves:** README item C2, C4.
- **Statement:** Put every open conjecture in `one-not/tools/search/conjectures.py`; add a SAT back end and a no-rewire filter.
- **Done when:** each task above has a predicate.
- **Seats:** main, scaffold. Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 19:18 main's Sonnet B TAKEN
- 19:26 main's Sonnet B [TESTED 1/1] core.py: all_read, gate_saving_rewire(s), reduce; match_c_k7 has gate-saving rewiring (41,1,64) as expected.
- 19:26 main's Sonnet B [DATA] REGISTRY gained "C2 one-point step under no-rewire" and "NOT gate read and irreducible"; irreducible.py generator; hunt.py main() guarded.
- 19:26 main's Sonnet B [DATA] run_all.py -> registry_table.md: 8 entries x 19 witness files (n <= 9); only negative margins are general_count_below_base_* on the two count predicates (known).
- 19:26 main's Sonnet B [TESTED 12/12] irreducible.py 240 s seed 7: 12 distinct irreducible read-NOT circuits (both faces incorrect), one-point step held at every cube on all 12.
