# Data for front's 4 Opus lanes at the 11:32 UTC resume (front maintains this file; newest at the bottom)
Lanes: A1 price-form dual (a9f35c86341be202a, w9/A1_mergefrac_dual.md), A2 matroid union (a9650b273725925ba, w9/A2_matroid_union.md),
B merge-tree double counting (af27dc7d5bbc4af68, w9/B_mergetree.md), C lifted fractional induction (a7d34dc821406b3c8, w9/C_liftinduction.md).
Board sources: agents/front-A2data.md, agents/front-heavy.md (§3), agents/scaffold-duals.md (08:55 correction), agents/front612-supportB.md,
agents/qg-d2-nomixed.md (Rounds 2-3), agents/scaffold-core-sat.md, scaffold-951 512f4b1 duals/.

(a) B_w = {M_z(w)} NOT matroids (13/19); matroid-union inequality Σ_w (r_w(G) − r_w(A)) ≤ |G\A| holds on ALL data.
(b) MergeFrac LP: L* ≤ 1 on all 163 circuits with a |S| ≥ 4 set; optimal π 0/1 on 163/163 ⇒ K-Rado form: ∀K Σ_w min_z |M_z(w)∩K| ≤ |K|.
    Optimal face CAN price N-dependent gates (120) and 3rd+ merges (152); tight big-set pairs share price ≈ L*/2.
(c) At the optimal K, 13/14 adversarial circuits: |M_z(w)∩K| is the same at every zero point z.
(d) Cross-world N-dependent gates X (world-0 merge for a, world-1 merge for b; world 1 := h(z+e_u)=0 ∀u∈S): 116 circuits of ~40k
    (fixh16: 87; none among the 163 with a 4+-set). On all 116: L* with K ⊆ G\X equals L*; HALF-WEIGHT K-RADO
    Σ_w min_z |M_z(w)∩K| ≤ |K\X| + |X∩K|/2 for every 0/1 K (exact MILP); min π(X) on the optimal face = 0.
(e) gAdyD R2: REFINED no-mixed LP ≤ 1 on ALL 34,064 (sets with a heavy unit u, h(e_u)=1, keep all zero points; others only world-0
    (h(z)=1) / world-1 (h(z+e_u)=0 ∀u∈S)); weaker world-1 def h(z|S)=0 fails on 1043. N-dependent cross-world gates priced 0 in EVERY
    optimal dual. ALL 842 essential clean circuits at s − base = 4 have a heavy unit in a set. Split sets ⇔ h(e_u)=1 for some u∈S and
    h(1_{V\S}) = 0 (PROVED).
(f) Shared 3rd+ merges between two 4+-sets are y-free ORs (B1 false 14/37) ⇒ fractional splitting.
(g) Missing 3rd+ merges of hard 4-sets come from a RESOLUTION GADGET (A∨y)∧(A∨¬y) = A (A partial OR of S_w, y = h off S_w);
    y-polluted ORs pay and die under restrictions fixing y; survives essential + rule p + N2 caps (s = base+6, {0123},{045}).
(h) HEAVY POINTS (front-heavy.md): not excluded by current lemmas (special case of G1 per-point x_v:=0; δ_v ≥ 0 for every point on 2559).
    PINNED split (B at own z_{S_b}) REFUTED (gAdyD R3: 320 essential, 313 clean; k4e248 g10 = x3∨(x0∧x1); scaffold: 47 inessential).
    HEAVY SPLIT v2 CHECKED on all 39,168 + 4,764 pairs: sets b ∌ v float over zero points in the half-cube {x_v=1} (pure C0), star of v
    (sunflower) floats freely ⇒ LP ≤ 1. Case I no heavy point ⇒ refined no-mixed (MergeWorld); Case II ⇒ monotone half-cube sub-LP + 1 sunflower.
(i) qg101 FALSE-STATEMENT NOTICE (08:29): S1(g) ("cross-world sharing lives on N-dependent gates") holds for H_z classes but for merge sets
    M_z(w) only under (i) world-1 point z' of b vanishes on S_a and (ii) C0(g)(z_{S_a}) = 0 (Lean crossworld c72d6ff W951/CrossWorld.lean,
    CrossWorldAt.ndep). Counterexamples n=5, S={01,23}, h=x4: f=(x0∨x2)∨(x1∨x3) is world-0 merge of a and world-1 merge of b and N-INDEPENDENT.
    ⇒ quantify the price-vanishing statement over ALL world-0/world-1 double merges, not only N-dependent ones.
Coord's A target: refined MergeFrac (heavy sets: all zero points; others world-0 ↔ C0 merge sets, world-1 ↔ C1, Lean via MergeWorld)
with optimal prices vanishing on cross-world gates.
Lean landing: MergeFrac levels 1–4 (no_minCE_of_mergePrice, bound_of_coverPrice, bound_of_servablePacking); MergeWorld + MergeLink
(coord-951 37d69f6; NoMixedFrac; mergestack d68ad9d world split of the price form); cTAHG W951/Heavy.lean; qg101 CrossWorld.lean.
Test via scaffold (session_01GmnDhdt8ydm1adQLjCP9we), gAdyD (session_01GmnDhgAdyDijthBgZgJFWn), front-612 (session_01GmnDhc6FBZAseL8bDQaYsu).
