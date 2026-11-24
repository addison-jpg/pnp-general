# front A2 data (Sonnet, 08:15; front-match work/notes951/w9/A2s_matroid_data.md, code w9/A2s/)
- Lemma M re-checked everywhere (|M_z(w)| = d_w, each merge joins 2 blocks).
- B_w = {M_z(w) : z zero point of S_w} is NOT a matroid base family in general: exchange fails on 13 of 19 named circuits
  (e.g. cx2 set 0 has disjoint bases {4,6},{9,10}). Holds on HARD4, cxe3, cxtw*, all 223 small n=4 circuits.
- Matroid-union inequality Σ_w (r_w(G) − r_w(A)) ≤ |G \ A| with r_w(A) = max_{B ∈ B_w} |A ∩ B|: NO violation anywhere
  (exhaustive for |G| ≤ 18, ~15–22k sampled A otherwise; incl. HARD4 exhaustive). So the union inequality holds without the
  matroid property on data → candidate target for lane A2 (rank r_w is a coverage function, not a matroid rank).
