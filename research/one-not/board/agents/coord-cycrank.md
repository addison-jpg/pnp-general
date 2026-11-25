# lcyc951 NOTES (restart-safe) — axis B (hypergraph cycle rank)
Labels: PROVED-PAPER / CHECKED / CONJECTURE / REFUTED. Files only under /home/user/lcyc951/.

## 0. Status
- Phase 1 (lower-bound side) stopped by coordinator RETARGET (front's "S-repay-cyclic" owns it). Results kept in §1.
- Phase 2 (calibration / upper side): measure real essential one-NOT circuits vs cyc(H). See §2+.

## 1. Lower-bound side: what was obtained before the retarget (for front)
Notation: M lifted monotone circuit (s-1 gates), h(0)=0, V = wires with g(0,1)=0, B(g)={u in V': g(e_u,1)=1},
J = joint union-find merges (Lemma J), cyc(H)=base-(|V'|-c).
- L1 PROVED-PAPER (trivial sharpening of Lemma J). AND gates and gates outside V are never in J. So
  s-1 >= |V'|-c + #AND(M) + #(OR gates outside V).  With front's AND2 (essential NOT => >=2 ANDs; UNREFEREED):
  s >= base - cyc + 3 for essential circuits, i.e. F(cyc) = cyc-3. Proves nothing new (cores have cyc >= 4).
- L2 PROVED-PAPER (new; "relative cycle rank"). Let E = easy sets (h(z_{S_w})=0), H_E their hypergraph on V'_E with c_E
  components, cyc(H_E) = sum_E d_w - |V'_E| + c_E. Then
      s >= base + 1 - (cyc(H) - cyc(H_E))      (+ #AND(M) as well).
  Proof. Theorem E (Lean): classes Ebar_w = {OR g: g^1 <= o_w everywhere, g^1(e_u)=1 for >=2 u in S_w}, |Ebar_w| >= d_w,
  pairwise disjoint. Run Lemma J's union-find at (0,1) but START from the partition P0 of V' whose blocks are the
  components of H_E (other points singletons). Invariant "B(g) in one block" as in Lemma J; final blocks <= c; so
  >= |V'| - (|V'_E| - c_E) - c merges J'. A merge g has B(g) meeting two P0-blocks; g in Ebar_w has B(g) ⊆ S_w ⊆ one
  P0-block. So J' ∩ Ebar_w = ∅ and s-1 >= sum_E d_w + |J'|. ∎
  Meaning: only cycles NOT closed inside the easy sub-hypergraph are unpaid. Weak when H_E is connected and spanning
  (then it gives only sum_E d_w + 1, weaker than Cor. E'). Same trick works with any family of pairwise-private
  world-1 classes whose gates have B(g) inside one set.
- L3 remark (PROVED-PAPER, known in other words = partial bound / E0.1): for any c with h(c)=1,
  s >= 1 + sum_{w: S_w ∩ c = ∅} d_w (type-0 classes at Z^0_w, atoms (c+e_u,0); S2.2 gives privacy).
- Where the per-cycle plan breaks (exact): the per-set merge sets M_w at (0,1) satisfy |M_w|=d_w but collide;
  cyc = sum_g mu(g), mu(g) := k_g - [g in J] (k_g = #{w: g in M_w}); a cycle is "paid" by a gate with mu>=1. Nothing at
  weight <= 1 bounds mu(g) <= 1; the weight-2 input e_b+e_c only constrains an AND G=s∧t (B(G)=B(s)∩B(t)) if
  h(e_b+e_c)=0. No per-cycle bound was proved. cyc<=2 gives 951 directly from L1 (not new: R0'+G1.1).
- Induction remark: with a non-cut point v of the incidence graph, sigma(H) <= sigma(H-v) + deg(v) - dead_v and
  cyc(H-v) = cyc(H) - (deg(v)-1); "dead_v >= 2" would give F(cyc) ~ cyc*(d-2)/(d-1); dead_v >= 2 is NOT proved in
  general (single OR-reader x_v ∨ c with N above: c <= AND_w OR(S_w - v) may be a live signal). = front's G1 lane.

## 2. Phase 2 — calibration of real one-NOT circuits against cyc(H)  (code/, tables in this dir)
Code: code/lib.py (measure), code/gens.py (systems + constructed families), code/rundata.py (front's JSON, copied to research/data/),
code/prodfull.py (product design), code/satenum.py (SAT enumeration; uses front/ess.py = front's rf/ess.py encoding).
Every circuit is verified by truth table (w951 Circuit.verify) except n=81 (random points, see 2.4).
Flags: E/e essential (C0 and C1 wrong) or not, C/c clean, R/r all gates read.
### 2.0 Metrics (all at Lemma J's domain: lifted circuit, level y=1, unit atoms (e_u,1), circuit order)
- J = joint merges; unexpl = base-|J| (= cyc(H) when H connected and no cross-component merge).
- M_w = per-set merges (|M_w| = d_w, asserted), k_g = #{w: g in M_w}, mu(g) = k_g - [g in J]. IDENTITY sum_g mu(g) = base-|J|.
  closers = |∪M_w \ J| (non-merge ORs that close a cycle for one set), coll = sum (k_g-1)^+, X = J \ ∪M_w,
  mumax = max mu = "cycles served by one gate" in circuit-order accounting.
- delta  = base - (max matching of the d_w demands into level-1 OR gates in V doing proper w-union work, i.e. B_w(children)
  incomparable) : ORDER-FREE; delta>0 means delta unit merges have no level-1 union gate at all, whatever the order.
- delta2 = same with level-0 work on heavy units (atoms (e_u,0), h(e_u)=1) added: order-free TWO-LEVEL weight<=1 deficit.
- HM/SD/mTmax/excess/rest = coord-lateral defect form (honest merges, split ANDs T, max m(T), sum (m(T)-1), rest);
  identity s-1-base = rest-excess asserted on every circuit with n<=13.
