# Faster exact synthesis for f_G (612 / Note 1): encoder with symmetry breaking + portfolio

Status: SAT finite computation, not Lean-checked. Basis: fan-in-2 AND/OR plus NOT, every gate counted.
Needs `python-sat` and `networkx` (`pip install python-sat networkx`).

Files
- `fast_synth.py`: exact-k encoder. Row-by-row CEGAR seeded with informative rows; every non-output gate is
  read; every non-isolated input is read (so k >= #non-isolated vertices - 1); no NOT of NOT.
  `sym=1`: independent consecutive gates are sorted by input pair. `sym=2`: also a type tie-break and no
  repeated (type, inputs) gate. `sym=0`: none.
- `portfolio.py`: runs sym=0 and sym=1 in parallel and takes the first answer (SAT or UNSAT, both sound).
- `t1.py`: check against known values (P3=2, P4=4, P5=5, C4=3, C5=7). All pass for sym=0 and sym=2.
- `bench.py`: timing against `data/pnp-subproblem/exact_edge_fn.py`.

Measured (4 cores, one run each, wall clock)
| graph | original encoder | portfolio |
|---|---|---|
| S_3 (n=7), k=6..8 | 17.2s | 8.5s |
| C6, k=5..8 | 13.7s | 7.5s |
| C7, k=6..8 | not run | 0.4s, 6.5s, 84s |
| C7, k=9 | n/a | not finished in ~23 min (killed at 25 min) |

Per k on S_3: sym=0: k=7 UNSAT 8.7s, k=8 SAT 3.5s. sym=1: 5.8s, 15.5s. sym=2: 5.8s, 36.8s.
So symmetry breaking helps UNSAT (~1.5x) and hurts SAT (4-10x); the portfolio takes the better of both.

What this does NOT do: UNSAT time still grows ~13x per extra gate, so this is a constant-factor gain
and does not unblock the h>=4 grid rows (n>=11, k=14..19). Not tried: automorphism-based symmetry
breaking, incremental SAT across k, other CEGAR seeds. C7's value 10 is already a Lean row (L-meta-106).
