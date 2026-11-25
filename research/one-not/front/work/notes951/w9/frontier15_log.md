# frontier15_log.md — closing the base-15 frontier of cover2.py (restart-safe log)
Conventions as in g1_fable.md / pairrule_log.md: minimal counterexample F (all point deletions satisfy the bound, hence by
heredity every F|rho for a restriction rho does), clean minimum one-NOT circuit, sigma = base - s >= 1, l(u) = #lines (|S|>=3)
through u, P(u) = pair-partners, d = l + p.  For any restriction rho: dead(rho) <= loss(rho) - sigma.
Backup of the round-4 checker: cover2_round4_backup.py.

## 0. Status of the two named examples under 245pqr (from uncovered_after_pairs.json)
 #0 {0567},{034},{126},{145},{235},{247}+{01},{02}: only scenario sigma=1, B={0,1,2,4,5}, V1={3,6,7}; every T of every V1
    point has size >= 2 and no T is a TIGHT pair (0 and 2 have degree 4) -> no rule fires.
 #1 {0567},{034},{135},{146},{237},{245}+{01},{02}: sigma=1, B={0..5}, V1={6,7}; T's {1,4} (6) and {2,3} (7) are tight
    pairs, q passes because the pair-partner 0 of 1 (of 2) lies in the other T.
