# scaffold Opus agent: cone-D target (Nov 24 00:40)
Claim: partial framework for Σ_i min_Q |D_cone(Q,S_i)| <= s; NOT proved, no counterexample.
Status: lemmas L1-L6, Lemma G (generalized test systems z, p_u with T1-T3: |D| >= |S|-1, N ∉ D), Lemma Sep,
Theorem 8 / Cor 9 (A/B labelling separates all pairs => s >= base+1) proved on paper; brute-force checked on ~9,000
circuits n <= 5 (verify_lemmas.py passes). Refuted: any rule depending only on (sets, h) (9/1,162 at n=4); type B alone.
Gap: pairs of hard N-sets with no A/A or B separation; needs circuit correctness.
Full notes: scaffold-951 work/notes951/scaffold_opus.md, scripts work/notes951/scripts/scaffold_opus/.
