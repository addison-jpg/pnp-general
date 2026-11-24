# front: MergeFrac — the precise fractional target (09:00 UTC; front-match SORRY_DISSECTION §20, w9/chist_fable.md)
- LEMMA M (PROVED-PAPER): for ANY z vanishing on S_w (no Good condition), union-find in circuit order over the wires that are 0 at z
  produces exactly d_w = |S_w| − 1 merging OR gates M_z(w). Load identity: for any μ_w on zero points, total load = base.
- MergeFrac (OPEN, CHECKED on ~15,300 circuits): ∃ μ_w with Σ_w Σ_z μ_w(z)[g ∈ M_z(w)] ≤ 1 for every gate g ⇒ FracMatch ⇒ 951.
  Dual: ∀ π ≥ 0, Σ_w min_z π(M_z(w)) ≤ π(gates). Single-price case PROVED.
- THEOREM F (PROVED-PAPER): s ≥ 1 + V_fun(S,h) (fractional Theorem-X family bound).
- Lean landing candidates: mergeSet_card (Lemma M; cf. MergeRunT), fracMatch_of_mergeFrac, bound_of_coverPrice, bound_of_servablePacking.
