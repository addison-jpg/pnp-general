# srepay_opus.md — S-repay on two complementary 4-sets (h = Th_2) and nearby (restart-safe log, Opus)
Code: w9/srepay/ (analyze.py = full lifted menu + ClassFrac LP + collisions; satgen.py = full one-NOT SAT, lifted 2-mode
encoding, canonical form pre-NOT block = cone of h; satfix.py = SAT for the post-NOT block over a FIXED pre-NOT block (e.g. a Th_2 tree),
optional real-mode cleanliness). Uses w9/jcut/bt.py (TT) and w9/s/chk2.py (lp).
System T2x4: n=8, A={0,1,2,3}, B={4,5,6,7}, base 6, both sets hard whenever h(1_A)=h(1_B)=1.

## 0. Readings of S-repay (made precise; M = lifted monotone circuit, s-1 gates; classes from S2.3 menu, each |cl_w| >= d_w by S2.1)
For a choice of one class cl_w per set: U = ∪ cl_w, out = (s-1) - |U|.
 V1 (deficiency form, what a proof needs): def = base - maxflow (b-matching of d_w units into cl_w, gate cap 1); S-repay-V1: def <= out.
     V1 => s-1 >= base.  (Fable's "collisions with multiplicity of an optimal solution": choosing d_w gates per class optimally, the
     minimum multiplicity-collision count IS def; with fractional choice and L* <= 1 it is 0.)
 V2 (multiplicity on WHOLE classes): coll = Σ|cl_w| - |U|; S-repay-V2: coll <= out  <=>  Σ_w |cl_w| <= s-1 (IDENTITY: out - coll = (s-1) - Σ|cl_w|).
     So V2 for the best choice <=> Σ_w m_w <= s-1, m_w = smallest class of set w. Strictly stronger than V1.
 V3 (fractional): if L* <= 1 then the optimal ClassFrac solution has no overload and S-repay holds with 0 collisions.

## 1. PROVED (paper, this log): for TWO sets the deficiency form is EQUIVALENT to the bound, and the bound holds by a JOINT lifted configuration
 (a) Two sets, any choice with |cl_a| >= d_a, |cl_b| >= d_b: maxflow = min(base, |U|) (cut formula), hence
     out - def = (s-1-base) if |U| <= base, and = s-1-|U| >= 0 otherwise.  So S-repay-V1 for two sets <=> s-1 >= base, for EVERY choice.
 (b) LEMMA J (joint world-1 unit configuration).  One-NOT circuit, h(0)=0, any set system.  In M take Z = {(0,1)} (join-closed, all F_w vanish:
     F_w(0,1) = o_w(0) = 0 since 0 in U0) and atoms (e_u,1) for ALL u in V' = ∪S_w.  Every x_v vanishes on Z and is 1 on exactly one atom; y does
     not vanish on Z.  Union-find of S2.1 over all wires vanishing at (0,1): F_w(e_u,1) >= o_w(e_u) = 1 for u in S_w (sandwich F_w(.,1) >= o_w),
     so each S_w ends inside one block; blocks are coarser than the connected components of the hypergraph.  Hence M has
         >= |V'| - c(hypergraph)  OR merge gates,  i.e.  s - 1 >= |V'| - c.
     If h(0)=1, N ≡ 0 and C0 is a monotone circuit for all outputs: s-1 >= base >= |V'|-c.  No heavy-unit assumption is needed.
 (c) For a linear HYPERFOREST (in particular any two sets with |S_a ∩ S_b| <= 1): |V'| - c = base, so s >= base+1.  Two complementary
     4-sets with ANY h (Th_2 included): s >= 7, and S-repay-V1 holds with slack s-1-base >= 0 for every choice of classes.
 => The two-set target is degenerate for S-repay-V1; it uses only points of weight <= 1 (so the "weight >= 2 inputs needed" barrier applies only
    to PER-SET classes, not to joint configurations).  The first non-degenerate S-repay-V1 targets are CYCLIC hypergraphs (|V'|-c < base),
    e.g. a 4-set + two triples closing a cycle.  Joint classes for acyclic subfamilies are a strict enlargement of the ClassFrac menu.

## 2. CHECKED: SAT, T2x4, h free (h(0)=0, both sets hard, essential NOT, live; satgen.py)
 s = 8, 9, 10: UNSAT for every NOT position (pnot 1..s-3).  s = 11: SAT (pnot 1..6), UNSAT pnot 7, 8.  Minimum essential size = 11 (= base+5).
 120 solutions at s=11 (40 each for pnot = 1,2,3) analysed (analyze.py, full menu): all have heavy units (h = x_u ∨ x_v ∨ ..., u∈A, v∈B):
   L*(max-classes) in {0.6, 0.75, 1.0}; V1 slack = V2 slack = s-1-Σm_w in {1,2,4} (minimal classes 3..5); min |cl_a ∩ cl_b| over pairs = 0;
   joint merges = 7 >= 6.  No violation of anything.
 (correction to §2 wording: V1 slack of a choice = (s-1-base) if |U| <= base, else s-1-|U|; the reported number is the max over choices.)

## 3. PROVED (paper) + CHECKED: world-1 unit configuration, merge sets, and the exact charging identity (any system)
Setting: h(0)=0.  Every set w uses the type-1 configuration with ceiling c=0 and unit atoms (e_u,1), u in S_w (same Z = {(0,1)} for all sets).
Run S2.1's union-find per set (atoms S_w) and jointly (atoms V' = ∪S_w), over the wires of M vanishing at (0,1), in circuit order.
 M_w = per-set merge gates; |M_w| = d_w EXACTLY (blocks go from |S_w| to 1 since B(F_w) ⊇ S_w).  J = joint merge gates, |J| >= |V'| - c (Lemma J).
 For a gate g: k_g = #{w : g in M_w}, j_g = [g in J] (an OR merges at most one pair of joint blocks).  Per-set blocks of w refine
 (joint blocks ∩ S_w), so a per-set merge is a joint merge unless the two joint blocks were already joined.
 IDENTITY: Σ_g (j_g - k_g) = |J| - base >= -cyc(H),  cyc(H) := base - (|V'| - c) (cyclomatic number of the linear hypergraph).
 Hence, with X = J \ ∪M_w (joint "cross merges": OR gates s∨t of M, s,t vanishing at (0,1), joining two joint blocks, and for every w one of
 B_w(s), B_w(t) empty), coll = Σ_g (k_g - 1)^+ (collisions among the merge sets, with multiplicity):
     |X|  >=  coll + #{g in ∪M_w \ J}  -  cyc(H).                                   (CHARGE)
 Since X is disjoint from ∪M_w (classes taken = merge sets, |M_w| = d_w), (CHARGE) is S-repay with an explicit repaying set, up to cyc(H):
   * hyperforest systems (two sets in particular, T2x4 with h = Th_2 included): coll <= |X| <= #gates outside ∪M_w.  S-repay PROVED.
   * general systems: S-repay can fail only by <= cyc(H), and then  s-1 >= |J| + #(other gates)  shows exactly what is missing:
       951  <=>  #(gates of M that are not joint world-1 merges)  >=  base - |J|   (<= cyc(H)).
 Structure: a collision (double merge g = s∨t, k_g >= 2) needs BOTH children "mixed" (atoms of >= 2 sets); mixedness is created only by
 cross merges (X).  Example hand_H5 (cross-pair Th_2 tree): the y-free gates (x0∨x4)∨(x1∨x5), (x2∨x6)∨(x3∨x7) and their OR are double merges
 (coll = 3), repaid by the 4 cross leaves x_i∨x_{i+4} (|X| = 4).  NOTE: these collisions are on N-INDEPENDENT gates (contrast S1(g), which
 is about type-0/type-1 cross-world collisions); in the world-1 picture the selector is not needed for a collision.
 CHECKED (srepay/chkJ.py, all 2559 data circuits, all with h(0)=0): Lemma J holds (0 violations), M_w full everywhere, (CHARGE) holds;
 199 circuits have coll > 0, 2491 are cyclic (cyc > 0).

## 4. CHECKED: integral S-repay-V1 on the old data (srepay/v1ilp.py, MILP over one full-menu class per set, n <= 9: 2555 circuits)
 min deficiency over integral choices = 0 on ALL 2555 (an integral collision-free lifted choice always exists) => S-repay-V1 holds trivially,
 min slack 1 (s-1-base = 2 circuits).  So the data never exercises S-repay; only constructed targets can.
