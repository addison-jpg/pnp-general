# qg-d2 (session_01GmnDhgAdyDijthBgZgJFWn): xgen runs for front-A (scaffold task, coord GO 08:18) — FINAL 11:42 UTC
Claim tested (front lane A): some optimal MergeFrac dual price vanishes on cross-world gates X (and the |X|/2 inequality).
Tool: scaffold's xgen.py at pequalnp-work scaffold-951 d31a0da (world 1 = h(z + e_u) = 0 for all u in S, the board
definition), imported unchanged through 951/tools/xgen951/xrun.py (adds progress lines and a PARTIAL summary on timeout).
Set 0 is a HARD 4-set; ess = both shadow circuits wrong; s counts the NOT; LIMIT 3000 circuits per size; caps: 2400 s for
base+1..+3, 5400 s for base+4. Logs: 951/tools/xgen951/logs.tgz.

| System | base | base+1 | base+2 | base+3 | base+4 |
|---|---|---|---|---|---|
| A {0123},{0456},{14},{25} | 8 | none (UNSAT) | none | none | 1,126 circuits (cap), X in 0 |
| B {0123},{0456},{14},{25},{36} | 9 | none | none | undecided (no answer in cap) | >= 50 circuits, X in 0 (run cut at 1034 s by a container restart, not resumed) |
| C {0123},{045},{14},{25},{35} | 8 | none | none | none | 3,000 (limit), X in 0 |
| D {0123},{04},{05},{14},{15} | 7 | none | none | none | 3,000 (limit), X in 0 |

- 7,176 essential circuits analysed in all (A 1,126 + B 50 + C 3,000 + D 3,000), all at base+4.
- No COUNTEREXAMPLE: no circuit with min_piX_on_face > 0 or half_viol > 0. In fact no circuit here has a cross-world gate
  at all (withX = 0 in every run), so these systems do not exercise the claim; a test of it needs systems where X occurs.
- No essential circuit below base+4 on A, C, D (and B up to base+2): agrees with the board conjecture that an essential
  NOT costs >= base+4.
- Random systems with a 4-set plus pairs (n <= 7): not run (CPU went to rounds 2-4 of agents/qg-d2-nomixed.md and to
  landing D-qg-2).

## base+5 (11:45-13:03 UTC; stopped at 13:03 by the owner's 12:05 line "refutes can be highly minimized"). Logs: 951/tools/xgen951/logs5.tgz
| System | s = base+5 | circuits | with X | result |
|---|---|---|---|---|
| D {0123},{04},{05},{14},{15} | 12 | 3,000 (limit) | 16, all with L* = 1.0 (tight) | front-A HOLDS on all 16: min pi(X) on the optimal face = 0, half_viol = 0 |
| A | 13 | ~1,000 in 77 min (stopped) | 0 | - |
| B | 14 | ~150 in 70 min (stopped) | 0 | - |
| C | 13 | ~2,100 in 77 min (stopped) | 0 | - |
First real instances of the claim on these systems (X appears at base+5, as on scaffold's B_tri): 16 tight circuits, no counterexample.
