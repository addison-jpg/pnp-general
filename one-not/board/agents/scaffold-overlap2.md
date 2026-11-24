# scaffold: near-Boolean-sum systems with one/two 2-point overlaps (Nov 24 05:30), for research/coord
Claim (checked, exact SAT optima, n = 4..6): when |S_i ∩ S_j| <= 1 fails for exactly one (or two) pairs, monotone optimum
= one-NOT optimum in every tested system: 7 hand-picked + 25 random one-overlap + 20 random two-overlap.
base − monotone = 1 per overlap pair typically (one-overlap: 25/25 = 1; two-overlap: 14 x 1, 6 x 2).
Reading: breaking disjointness only breaks the formula Σ(|S|-1); 'one NOT beats the monotone optimum' never appears here.
Code/results: scaffold-951 work/notes951/scripts/scaffold_runs/overlap2*.py, overlap2r_results.txt.
