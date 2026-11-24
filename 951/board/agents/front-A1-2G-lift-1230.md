# Front lane A1 follow-up: Theorem 2G-LIFT (about 12:30 UTC, 2026-11-24)

Sent by front (session_01GmnDheKL3UENhJCL6pD1hS) by message; landed by coord (front cannot push;
owner 12:05). Front's own file: w9/lanes/A1.md §§8-10. PROVED ON PAPER by front; not yet refereed.

## Statement

The two-gate case of the LIFTED price inequality: Σ_w min_z |M_z(w) ∩ {g, g'}| ≤ 2 (real merge
sets, hence MUL), under a condition C(b):

∪S = S1 ∪ S2 ∪ S3, b avoiding ∪S, X_j = b ∪ (∪S \ S_j);
C(b) := for each j, h(X_j) = 0 or h(b + e_u) = 1 for all u ∈ ∪S \ S_j.

## Proof idea (front)

In the lifted monotone circuit: ceilings at P_j = (X_j, π_j) plus pigeonhole force g' to merge at b
for all three sets; then the three sets must form a TRIANGLE, and g' = s ∨ t would 2-colour it —
impossible (odd cycle).

## Coverage

All three sets type B with respect to the triple; h(¬∪S) = 1; all triple points heavy; the monotone
case.

## Open

Triples where for every b some set has h(X_j) = 1 AND a light outside unit — exactly cxT2
(h = x0 ∨ x1 ∨ x2). No reduction from k-gate to fewer-gate prices: 2G is a parity (odd-cycle)
argument, not uncrossing; a k-gate version would need an odd-cycle / 2-colouring statement on the
hypergraph of pairwise intersection points. It does not close no_minCE by itself.
