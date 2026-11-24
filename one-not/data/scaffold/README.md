# scaffold data (2026-11-24)

- The 66 SAT Fano circuits are at `../fano_sat66.json` (one copy; the duplicate that was here is removed).
- `pg13.jsonl` (2,159 circuits, PG(2,3)) and `ag16.jsonl` (65, AG(2,4)): the size-ladder corpora, one line per circuit with
  its ladder metrics. Not exactly regenerable (`../../tools/scaffold/ladder_gen.py` is time-budgeted). Summary: `ladder_REPORT.md`.
- `FINDINGS_scaffold.md`: scaffold's findings as of the 14:20 pause.
- The 80,198-circuit Fano corpus is regenerated exactly by `../../tools/fano/fano_corpus.py`.

Tools in `../../tools/scaffold/` (gc3.py k=3 global count, nf.py R1-R6, ladder_gen.py) import helpers from scaffold's
scratchpad (mfrac.py, killtests.py, ladder.py) and are kept for reference, not as standalone scripts.
