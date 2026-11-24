# Task: c4g-two-not-gates

- **Serves:** README item C4g.
- **Statement:** SAT: is there a correct circuit with 2 NOT gates and fewer than base gates, on the Fano plane and on small systems?
- **Done when:** UNSAT up to a stated size, or a circuit.
- **Seats:** scaffold (has the SAT encoder). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 17:57 scaffold TAKEN. Encoder: satk.py, exact size s, 1 <= #NOT <= 2, AND/OR/NOT, clean + every gate read (valid for a minimum circuit), all inputs.
- 17:57 scaffold [TESTED] UNSAT (no correct circuit with <= 2 NOT gates below base): K3 edges (base 3, s = 2), star {01,02,03} (base 3, s = 2), C4 edges (base 4, s = 2, 3), two 3-sets {012, 034} (base 4, s = 2, 3). Running: K4 edges (s = 4, 5), three 3-sets, Pasch (s = 7), two 4-sets (s = 4, 5), Fano (s = 13).
- 19:5x coord TAKEN up-C4 (session_01GmnDhe3y5bZxiBqFwv37X4, started 17:44 by coord): SAT on Fano + small systems with s = base − 1 and ≤ 2 NOTs, then the D9 witness count on what it finds. Lines go here.
- TAKEN up-C4 19:5x (coord)
- 17:59 up-C4 [TESTED, serves C4g] one-not/tools/kill_tests/c4t_sat.py (exact synthesis, cadical; fan-in-2 AND/OR + NOT, every gate counted; each SAT circuit re-checked on all 2^n inputs). s = base − 1, ≤ 2 NOT gates: UNSAT on triangle-of-triples (base 6), Pasch (8), star of 3 triples (6), tri4 (6), q4 (7), Fano minus 2 lines (n = 7, base 10, 155 s). ≤ s NOT gates (unbounded): UNSAT on triangle, Pasch, star, tri4, q4. Fano s = 13, K4-triples s = 11, Fano minus 1 line s = 11: running.
- 17:59 up-C4 [TESTED, serves C4w / D9] general witness(∅) ≥ base on 2,400/2,400 SAT-enumerated circuits with EXACTLY 2 NOT gates (no NOT of NOT) on tri3, star3, tri4, q4 at s = base+3, base+4, and on 2,700/2,700 with EXACTLY 3 NOT gates (s = base+3..base+5, same systems). So C4w does not break at t = 2 or 3 on small systems; the t = 4 break (general_count_below_base_t4) needs larger circuits. Weak: enumeration is SAT order, not adversarial.
- 17:59 up-C4 [TESTED] with exactly 2 non-cancelling NOT gates the minimum is base + 3 on tri3, star3, tri4 (UNSAT at base+1, base+2) and > base + 2 on q4, pasch: NOT gates cost, never save, on these systems.
