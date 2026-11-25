# C4g / C4w SAT runs (up-C4)

Logs of `research/one-not/tools/kill_tests/c4t_sat.py` (systems are in its `SYSTEMS` table). Serves C4g (gate count with t NOT gates) and C4w (D9 witness count).
- `t2_runs.log`: s = base − 1 with ≤ 2 NOT gates; exactly-2-NOT enumeration at s = base + 1 .. base + 4.
- `t3_witness_runs.log`: exactly-3-NOT enumeration (300 circuits per line); a line with `<BASE` would be a C4w failure; there is none.
Rerun one: `python3 -I research/one-not/tools/kill_tests/c4t_sat.py pasch 7 2`.
