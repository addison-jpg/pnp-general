# Referee of research-concave-dual.md (CU) — P=NP Coord (desktop) session_01GmnDhckSb9NEwzEy2e7UWf, posted by coord 09:50 UTC
Paper check from the quoted core (no compute). Notation: pi = sum_t lam_t 1_{A_t}, A_1 ⊇ A_2 ⊇ ..., lam_t > 0; F_w(A) = min_z |M_z(w) ∩ A|;
F_w^c = same min over zero points of world c; m_w^c(pi) = min_{z in world c} pi(M_z(w)); m_w = min_c m_w^c.

(1) LAYER-CAKE: CORRECT. m_w(pi) >= sum_t lam_t F_w(A_t) (min of a sum >= sum of mins). Direction: a LOWER bound on m_w, so alone useless
    for MergePrice (needs an upper bound on sum_w m_w); it only characterises when 0/1 suffices. 'EXACTLY WHEN' is correct per w and per pi
    (common minimiser at every level), but as a GLOBAL statement it is only SUFFICIENT. Fix wording: 'sufficient', not 'exactly when'.
(2) CU + per-world chain-uniformity => MergePrice: CORRECT. For pi's chain take the CU choice c: sum_w m_w(pi) <= sum_w m_w^{c(w)}(pi)
    [ANY c is an upper bound] = sum_w sum_t lam_t F_w^{c(w)}(A_t) [chain-uniformity in world c(w)] <= sum_t lam_t |A_t| = pi(G) [CU per level].
    c may depend on the chain; it never needs to be optimal. ESSENTIAL: (i) the SAME c at every level; (ii) chain-uniformity only in the
    chosen world; (iii) the worlds must PARTITION all zero points INCLUDING mixed points (e.g. world 1 := h(z) = 0). If mixed points are
    dropped this proves NoMixedPrice (strictly stronger; plain form FALSE on data).
(3) REPAIR TERM: needed exactly: for every pi some c, CU on pi's chain, with sum_w gap_w^{c(w)}(pi) <= sum_t lam_t slack_t(c), where
    gap_w^c(pi) = m_w^c(pi) - sum_t lam_t F_w^c(A_t) >= 0 and slack_t(c) = |A_t| - sum_w F_w^c(A_t) >= 0. Cautions: gap is concave-minus-
    linear in lam (can peak inside the cone): test integer pi with repeated levels (heights >= 2, unequal multiplicities), not only 0/1
    chains; a constant bound cannot hold (gap scales with lam) — the repair must be proportional.
    CLEANEST SUFFICIENT TARGET (linear in lam): ONE fixed z_w in world c(w) per set, used at all levels, with
    sum_w |M_{z_w}(w) ∩ A_t| <= |A_t| for every t ('chain-SDR'). [coord note: this is the chain-wise weakening of P=NP Front's MergeSDR
    (pairwise disjoint merge sets), which implies MergePrice for all pi at once.]
Summary: (1) CORRECT (wording fix); (2) CORRECT; (3) needs a proportional, same-c, same-z bound, tested on weighted chains.
