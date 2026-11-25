# research: weight<=1 relaxation (barrier check on small systems)

Status: checked by SAT (CaDiCaL 1.5.3 via python-sat; own encoder, research scratchpad relax.py; sanity: finds the
6-gate OR circuit and rejects 5 on {012},{034},{135}).

Relaxation: circuit of s fan-in-2 AND/OR gates + <= 1 NOT (any position) that is correct ONLY on the n+1 inputs of
weight <= 1 (0 and the unit vectors). UNSAT here => UNSAT for the real problem (fewer constraints), so it is a
cheaper sufficient certificate for s >= base.

Results:
- c11 = {0,1,2},{0,3,4},{1,5,6},{3,5,7},{2,4,6,7} (n=8, base 11): UNSAT at s=10 with weight<=1 rows only (318 s, all 10
  NOT positions). So on this system even unit vectors + 0 force the bound (one complement gate cannot help).
- Wegener's set-circuit question (cobf.pdf p.214, SC = Σ(|H|-1)?), monotone weight<=1 = union/intersection set circuits:
  sweep over ALL (1,1)-disjoint systems with a set of size >= 3: n=4: 3, n=5: 32 systems, none beats base; n=6 running.
Meaning: the 1-slice barrier is asymptotic (Wegener suspects SC < Σ only for large Nechiporuk sums); on small systems the
weight<=1 relaxation is still exact so far. A finite-frontier SAT can use it as a fast certificate.
- Frontier (front's 33 base-15, s=14): relaxation is SLOWER than hoped: rank 0 with the NOT at gate 13 not solved in 9 min at
  weight<=1, nor in 15+ min at weight<=2 (fewer rows = more freedom = harder UNSAT). Not a fast certificate at this size;
  scaffold's full SAT (chan encoding) stays the route. n=6 set-circuit sweep: 394 systems done, none beats base (stopped).
