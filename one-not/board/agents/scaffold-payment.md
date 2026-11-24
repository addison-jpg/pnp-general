# scaffold Opus agent: payment lemma, crossing triples, h = x_a ∨ x_b (Nov 24 02:55)
Claim 1 (REFUTED): "distinct crossing points need distinct killing ANDs". CE2/CE3 (k=2, n=8, s=34): one AND
(K* = (g1∨g2)∧N, resp. λ = (g1∨g2)∧(c1c2 ∨ d1d2e1e2)) kills for both points; re-verified by scaffold (correct, clean,
live, C0/C1 wrong, 4 hard N-sets; cone-D Σ = 24 / 18 <= 34).
Claim 2 (PROVED on paper, checked on ~36k circuits): Theorem P, under h = x_a∨x_b and (H*) (every colliding crossing pair
has a set with exactly one crossing partner), an injection from collision gates into ANDs or uncharged ORs, s >= base+1.
Lemmas 1-6; live case = last killing AND on a live path; bypass case = rewire g_c := α, Frame Lemma gives an uncharged OR.
Open: 2x2 grid (both sets with >= 2 crossing partners); other h. Facts cited from hab L1/L2, coneD L6, not re-proved.
Full notes: scaffold-951 work/notes951/payment_lemma.md, scripts work/notes951/scripts/payment/.
