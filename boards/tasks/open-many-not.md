# Task: open-many-not

- **Statement:** Whether two or more NOT gates can save gates on these functions.
- **Seats:**
  - B1 (Opus): the per-set flip lemma in Lean, any number of NOT gates
  - B2 (Sonnet): every circuit for the OR of four inputs needs at least 3 gates, any number of NOT gates, as a Lean theorem by exhaustive check
  - B3 (Sonnet): SAT search for a circuit with two NOT gates and fewer than base gates
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- Proved: single OR (B2), systems of ORs by partition (B4), S3(a) per-set flip lemma (B1), the point-lemma ingredients (B8). Findings: Or4ManyNot, OrSystemManyNot, FlipLemma, FlipHall, PointLemma in `boards/TREE.md`.
- Open: **S3(b)**, flip classes across all sets ≥ base (Hall form). Reduced (B5) to the thin-basis lemma, then (B6) to the **point lemma**; for two sets (B9) to **rule R2**. Fano and two 5-sets are the first unsettled systems at the thin-basis level (two 5-sets settled by SAT, B6).
- Systems of several overlapping ORs with cycles: no bound beyond base-below.

## OPEN / STOPPED

- OPEN (Sonnet): SAT, run `python3 -I one-not/research/open/B6_point_sat.py NAME` for NAME in fano, grid3, ag3, pg3 with long timeouts (one at a time, background), record UNSAT/SAT/unfinished with seconds in one-not/research/open/B6_thin_basis.md s3. UNSAT at base-1 proves the thin-basis lemma for that system; SAT is not a counterexample (relaxation) and then needs a multi-point version (points 0 and e_u) of the same encoding.
- TAKEN O1 (Opus): paper proof of rule R2 (B9 s3.2): in every program with S, T among its lines (|S ∩ T| <= 1, both of size >= 2), removing one private point deletes >= 1 line after cleanup, or removing a private pair a in S, e in T deletes >= 2. Implies the point lemma for two sets. -> one-not/research/open/B9_point_two_sets.md
- STOPPED B7 (container restart; partial B7_thin_sat.py kept; reopen to continue): SAT of the thin-basis problem (B5 section 5) on Fano, two 5-sets, K4-type and next cyclic systems on 5-6 points, long runs plus one-line-more control; one-not/research/open/B7_thin_sat.py, B7_thin_sat.md
- STOPPED B10 (container restart; partial draft B10_point_S3.md kept, 105 lines; reopen to continue) (was OPEN, Sonnet): paper proof of the point lemma for |S| = 3, any T (|S ∩ T| <= 1): no program of |T| lines has S and T among its lines. Use the tight-tree lemma of B9 s2; the open cases are: T's sub-DAG has |T| lines with |T|+1 leaf slots (one leaf slot without a T-point, or one T-point in two leaf slots), or with |T| leaf slots and one line read twice. -> one-not/research/open/B9_point_two_sets.md s2
- STOPPED B11 (container restart; partial B11_r2_sat.py kept, runs lost; reopen to continue) (Sonnet): SAT, rule R2 of B9 s3.2 exactly (not sampled): add to B9_two_sets.py a mode that asks for a program of K lines (no dead line) computing S, T in which no private point and no private pair (a in S, e in T) satisfies R2 after cleanup; run 4 4 d and 3 5 d for K = 10..13. UNSAT = R2 holds there; SAT = R2 false, record the witness. -> one-not/research/open/B9_point_two_sets.md s3.3

- OPEN (Sonnet): SAT/enum, PHC@0 (U1 §2.2: lines split into disjoint spanning forests, one per set, each line paying one pair inside its own value) on point programs for Fano (13 and 14 lines) and two 5-sets (shared and disjoint, 8 and 9 lines): extend `U1_payment_hall.py enum` to a family argument, cap 10^5 tuples, record tuples, exhaustive or capped, failures; a failure at >= base lines refutes PHC@0, not the point lemma. -> one-not/research/open/U1_unify.md s3
- STOPPED S2 (Addison made S8 the priority; reopen later) (Sonnet): paper proof, OR-only PHC@0 for monotone point programs: every program of union/intersection lines over partial transversals of W (pairwise |S cap T| <= 1) with every S_w among its lines has pairwise disjoint sets E_w of union-lines, |E_w| = |S_w| - 1, each E_w a spanning forest of S_w with each line's edge inside its own value. Start with two sets. -> one-not/research/open/U1_phc_monotone.md
- STOPPED S3 (Addison made S8 the priority; reopen later) (Sonnet): PHC@0 under point deletion (U1 §4): on the exhaustive tuples of U1 s3.1, for each program and private point u, take a PHC@0 partition of the cleaned program for (S - u, T) and test whether it extends to a partition for (S, T) by adding lines; record extendable / not, and the smallest non-extendable program. -> one-not/research/open/U1_unify.md s4

## Refuted / dead

- B4's partition bound does not settle the acyclic thin-basis case; it is not a bound for overlapping systems with cycles.
- With XOR as a fifth op the point lemma is false (3,3 shared in 3 lines): any proof must use monotonicity (B9).
- The one-point rule R is false (10-line witness, |S| = 3, |T| = 5) (B9).
- B3 SAT: 224 systems (n <= 6) UNSAT for t = 2, 3 at base-1, no hit: not a refutation, no counterexample either.

## Decided (one line each; the file holds the proof or the note)

- B1: S3(a) per-set flip lemma, any number of NOT gates. -> `one-not/lean/PEqualNP/W951/Open/FlipLemma.lean::flip_lemma`
- B2: OR of n inputs needs n-1 AND/OR gates with any number of free NOT gates; OR4 needs 3 (structural, no enumeration). -> `Open/Or4ManyNot.lean`
- B3: SAT, no hit. -> `one-not/research/open/B3_sat_manynot.md`
- B4: any number of NOT gates, gates >= n - comp(union graph); equals base for disjoint sets and chains (hyperforests). -> `Open/OrSystemManyNot.lean`
- B5: S3(b) not broken (Hall holds on every subfamily of all stored circuits n <= 22, 0 shared classes); proved for every circuit, any NOT count, for systems of <= 2 sets of size <= 3 (core checked); exact SAT: Hall holds for ALL circuits on two3, dis3, two43, dis43, dis44, star44, tri3, star3, tri4, q4, Pasch. Exact missing statement: the thin-basis lemma (base(W)-1 AND/OR lines over W-thin functions cannot compute all OR(S_w)). -> `one-not/research/open/B5_flip_hall.md` s5, `Open/FlipHall.lean::no_sole_partner`
- B6: thin-basis lemma reduced to the point lemma (sens at the all-zero point: lines become A∪B, A∩B, A∖B, B∖A of partial transversals); exact SAT UNSAT at base-1 on two 5-sets (shared point and disjoint) and Pasch, so S3(b) holds on two 5-sets for every circuit; Fano not finished (300 s). -> `one-not/research/open/B6_thin_basis.md`
- B8: `sens_gate`, `sens_thin_card`, `sens_orS`. -> `Open/PointLemma.lean`
- B9: point lemma for two sets not proved in general; proved when min(|S|,|T|) <= 2 (tight-tree lemma, paper); exact SAT UNSAT at |S|+|T|-3 lines for every size pair with |S|+|T| <= 10; gate elimination: rule R2 implies the lemma (paper). Exact obstacle: R2. -> `one-not/research/open/B9_point_two_sets.md`, `B9_two_sets.py`
