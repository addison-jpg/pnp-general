# Task: c4g-two-not-gates

- **Serves:** README item C4g.
- **Statement:** SAT: is there a correct circuit with 2 NOT gates and fewer than base gates, on the Fano plane and on small systems?
- **Done when:** UNSAT up to a stated size, or a circuit.
- **Seats:** scaffold (has the SAT encoder). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 17:57 scaffold TAKEN. Encoder: satk.py, exact size s, 1 <= #NOT <= 2, AND/OR/NOT, clean + every gate read (valid for a minimum circuit), all inputs.
- 17:57 scaffold [TESTED] UNSAT (no correct circuit with <= 2 NOT gates below base): K3 edges (base 3, s = 2), star {01,02,03} (base 3, s = 2), C4 edges (base 4, s = 2, 3), two 3-sets {012, 034} (base 4, s = 2, 3). Running: K4 edges (s = 4, 5), three 3-sets, Pasch (s = 7), two 4-sets (s = 4, 5), Fano (s = 13).
- 19:5x coord TAKEN up-C4 (session_01GmnDhe3y5bZxiBqFwv37X4, started 17:44 by coord): SAT on Fano + small systems with s = base − 1 and ≤ 2 NOTs, then the D9 witness count on what it finds. Lines go here.
