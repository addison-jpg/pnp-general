# adv16 NOTES — adversary on the 14 base-16 uncovered systems (restart-safe)
Labels: CHECKED / CONJECTURE / REFUTED / PROVED-PAPER.
TOP: (no counterexample so far)

## Setup
- uncovered16.json: the 14 systems (rank, sets, surviving scenarios B) from front-match w9/g1/uncovered_after_round7.json.
- f16_explain.txt: copy of the blocker table (scenario B, class vector over sorted(B), first non-excluded g*).
- enc.py: guided SAT. Own channel encoder, 15 gates, NOT position free, canonical gate order ((A,B) nondecreasing),
  live, h(0)=0, >=2 AND (AND2), N2 reader cap (readers(u) <= d(u)-1), rule p (nonpair(u) <= l(u)-1),
  tight (readers = d-1) => only OR readers (G1.5), FIXED scenario: V1 points exactly one reader of the form x_v o gate, not NOT
  (absorbing lemma), OR-type if l(v)=2 (T2); B points >= 2 readers; class U/S: exactly one non-pair reader (U: x_t | gate),
  >= 1 pair-gate to a B partner; class T: nonpair = l-1; class M: 2..l-2; no pair-gate at a V1 point (P2).
  Run: python3 enc.py RANK SCEN_INDEX CLASSVECTOR   (UNSAT = this scenario/class vector has no 15-gate circuit)
- Sanity (t0.py): encoder finds the known circuits ({01},{12} at 5/6 gates; n=5 base 6 at 9, 10).
