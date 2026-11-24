import PEqualNP.Outside.L_meta_538

/-!
# L-meta-538 without the subdivision hypothesis

Row L-meta-538 assumes that `K` embeds in a `k`-subdivision (`3 ≤ k`); the proof never uses it.
This is the statement for every graph `K` with a pendant edge `l - p`: the nested-cover description
of minimal circuits passes from `K` minus the pendant edge to `K`.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.MetaComplexity.NestedCover.pendant_edge_general : ∀ (n : ℕ) (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj] (l p : Fin n), (∀ v : Fin n, K.Adj l v ↔ v = p) → (∀ v : Fin n, K.Adj p v ↔ v = l) → (∃ u v : Fin n, K.Adj u v ∧ u ≠ l ∧ u ≠ p) → (∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K' {p}) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K' {p} C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K ∅) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K ∅ C) := by
  intro n K K' _ _ l p hl hp hex hK' hyp C
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  have hpK' : ∀ v, ¬ K'.Adj p v := fun v h => ((hK' p v).1 h).2.2.1 rfl
  have hFrec : ∀ (v w : Fin n), ((v = l ∧ w = p) ∨ (v = p ∧ w = l)) → ∀ x,
      graphFun K ∅ (Function.update (Function.update x w (x w && x v)) v true) = graphFun K ∅ x :=
    fun v w h x => L538_fun_rec K l p hl hp v w h x
  have hFl : ∀ x, graphFun K ∅ (Function.update x l true) = graphFun K' {p} x :=
    fun x => L538_fun_l K K' l p hl hp hK' x
  have hFins : ∀ x, graphFun K' {p} (Function.update x p (x l && x p)) = graphFun K ∅ x :=
    fun x => L538_fun_ins K K' l p hl hp hK' x
  constructor
  · rintro ⟨hmin, hfun⟩
    have hsmall : ∀ v w : Fin n, ((v = l ∧ w = p) ∨ (v = p ∧ w = l)) → ∀ D : Circuit, FanInTwo D →
        circuitFun n D = (fun x => graphFun K ∅ (Function.update x v true)) →
        C.size ≤ D.size + 1 := by
      intro v w hvw D hD hDf
      obtain ⟨D', hD', hsz, hD'f⟩ := L538_prepend D hD v w
      have := hmin.2 D' hD' (by
        funext x; rw [hD'f, hDf, hfun]; exact hFrec v w hvw x)
      omega
    obtain ⟨jg, hjg, y, hy, hyl, hgl, hlonly⟩ := L538_uniq (graphFun K ∅) C hmin hfun l
      (hsmall l p (Or.inl ⟨rfl, rfl⟩)) (L538_fun_dep K l p hl hp l (Or.inl rfl)).1
      (L538_fun_dep K l p hl hp l (Or.inl rfl)).2
    obtain ⟨jg2, hjg2, y2, hy2, hyp2, hgp, hponly⟩ := L538_uniq (graphFun K ∅) C hmin hfun p
      (hsmall p l (Or.inr ⟨rfl, rfl⟩)) (L538_fun_dep K l p hl hp p (Or.inr rfl)).1
      (L538_fun_dep K l p hl hp p (Or.inr rfl)).2
    set C' : Circuit := ⟨L538A.del C.gates jg (n + jg) y, L538A.ren (n + jg) y C.output⟩ with hC'
    have hC'fan : FanInTwo C' := L538A.fanInTwo_del C.gates C.output jg (n + jg) y _ hmin.1
    have hC'size : C'.size + 1 = C.size := by
      show (L538A.del C.gates jg (n + jg) y).length + 1 = C.gates.length
      rw [L538A.del_length _ _ _ _ hjg]; omega
    have hnl' : ∀ j < C'.gates.length, l.val ∉ L538A.deps (gateAt C' j) := by
      intro j hj hmem
      have hjlen : j + 1 < C.gates.length := by
        have : C'.gates.length + 1 = C.gates.length := hC'size
        omega
      by_cases hjj : j < jg
      · rw [L538_del_gate_lt C jg y n hjg j hjj] at hmem
        exact hlonly j (by omega) (by omega) hmem
      · rw [L538_del_gate_ge C jg y n hjg j (by omega) hjlen, L538A.deps_renG] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨i, hi, hie⟩ := hmem
        unfold L538A.ren at hie
        split_ifs at hie with h1 h2
        · subst hie; exact hlonly (j + 1) hjlen (by omega) hi
        · exact hyl hie
        · have := l.isLt; omega
    have hC'out : C'.output ≠ l.val := by
      show L538A.ren (n + jg) y C.output ≠ l.val
      have hne := L538_out_ne K l p hl hp C hfun l (Or.inl rfl)
      unfold L538A.ren
      split_ifs with h1 h2
      · exact hne
      · exact hyl
      · have := l.isLt; omega
    have hC'fun : circuitFun n C' = graphFun K' {p} := by
      funext x
      rw [← L538_noread C' l hnl' hC'out x true, ← hFl x, ← hfun]
      show Circuit.eval ⟨L538A.del C.gates jg (n + jg) y, L538A.ren (n + jg) y C.output⟩
        (List.ofFn (Function.update x l true)) = Circuit.eval C (List.ofFn (Function.update x l true))
      have hlen : (List.ofFn (Function.update x l true)).length = n := List.length_ofFn
      have hval : (C.wires (List.ofFn (Function.update x l true))).getD (n + jg) false =
          (C.wires (List.ofFn (Function.update x l true))).getD y false := by
        rcases hgl with hg | hg
        · rw [L538_gate_val C jg hjg l.val y ⟨by have := l.isLt; omega, hy⟩ hg _ hlen,
            L538_wire_input C _ l]
          simp
        · rw [L538_gate_val C jg hjg y l.val ⟨hy, by have := l.isLt; omega⟩ hg _ hlen,
            L538_wire_input C _ l]
          simp
      have := L538A.del_eval C.gates C.output (List.ofFn (Function.update x l true)) jg y hjg
        (Or.inl (by rw [hlen]; exact hy)) (fun g _ _ => by rw [hlen] at *; exact hval)
        (fun _ => by rw [hlen] at *; exact hval)
      rw [hlen] at this
      exact this
    have hC'min : IsMinimalCircuit n C' := by
      refine ⟨hC'fan, fun D hD hDf => ?_⟩
      obtain ⟨D', hD', hsz, hD'f⟩ := L538_prepend D hD l p
      have := hmin.2 D' hD' (by
        funext x; rw [hD'f, hDf, hC'fun, hfun, ← hFins x, Bool.and_comm])
      have h2 : C'.size + 1 = C.size := hC'size
      omega
    obtain ⟨d', hd'⟩ := (hyp C').1 ⟨hC'min, hC'fun⟩
    have hlenC : C'.gates.length + 1 = C.gates.length := hC'size
    have hops' : ∀ j < C'.gates.length, (gateAt C' j).op ≠ GateOp.not := by
      intro j hj h
      rcases L538_nested_ops K' {p} C' d' hd' j hj with h1 | ⟨h1, _⟩ <;> rw [h] at h1 <;> cases h1
    have hdeps : ∀ g : Gate, g.op ≠ GateOp.not → L538A.deps g = g.inputs := by
      intro g hg; obtain ⟨op, ins⟩ := g; cases op <;> simp_all [L538A.deps]
    have hopsC : ∀ j < C.gates.length, j ≠ jg → (gateAt C j).op ≠ GateOp.not := by
      intro j hj hne
      by_cases hjj : j < jg
      · rw [← L538_del_gate_lt C jg y n hjg j hjj]; exact hops' j (by omega)
      · have := hops' (j - 1) (by omega)
        rw [L538_del_gate_ge C jg y n hjg (j - 1) (by omega) (by omega)] at this
        simp only [L538A.renG] at this
        rwa [show j - 1 + 1 = j by omega] at this
    have hnlS : ∀ j < C'.gates.length, l.val ∉ (gateAt C' j).inputs := fun j hj => by
      rw [← hdeps _ (hops' j hj)]; exact hnl' j hj
    have hjj : jg2 = jg := by
      by_contra hne
      have hrd := L538_preader K' p hpK' C' d' hd'
      have hpin : p.val ∈ (gateAt C jg2).inputs := by
        rcases hgp with h | h <;> rw [h] <;> simp
      have hand : (gateAt C jg2).op = GateOp.and := by
        rcases hgp with h | h <;> rw [h]
      have hlen' : C'.gates.length + 1 = C.gates.length := hC'size
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := hrd jg2 (by omega) (by rw [L538_del_gate_lt C jg y n hjg jg2 hlt]; exact hpin)
        rw [L538_del_gate_lt C jg y n hjg jg2 hlt, hand] at this
        exact absurd this (by intro h; cases h)
      · have hj1 : jg2 - 1 + 1 = jg2 := by omega
        have hg2 := L538_del_gate_ge C jg y n hjg (jg2 - 1) (by omega) (by omega)
        rw [hj1] at hg2
        have hpin' : p.val ∈ (gateAt C' (jg2 - 1)).inputs := by
          rw [hg2]
          simp only [L538A.renG, List.mem_map]
          refine ⟨p.val, hpin, ?_⟩
          unfold L538A.ren
          have := p.isLt
          rw [if_pos (by omega)]
        have := hrd (jg2 - 1) (by omega) hpin'
        rw [hg2] at this
        simp only [L538A.renG] at this
        rw [hand] at this
        exact absurd this (by intro h; cases h)
    subst hjj
    have hyeq : y = p.val := by
      have hlpv : l.val ≠ p.val := fun h => hlp (Fin.ext h)
      rcases hgl with h1 | h1 <;> rcases hgp with h2 | h2 <;> rw [h1] at h2 <;>
        simp only [Gate.mk.injEq, List.cons.injEq, and_true, true_and] at h2 <;> omega
    subst hyeq
    have hrb : ∀ j < jg2, ∀ i ∈ (gateAt C j).inputs, i < n + j := by
      intro j hj i hi
      have := hd'.1 j (by have : C'.gates.length + 1 = C.gates.length := hC'size; omega)
      rw [L538_del_gate_lt C jg2 p.val n hjg j hj] at this
      exact this i hi
    have hponlyS : ∀ j < C.gates.length, j ≠ jg2 → p.val ∉ (gateAt C j).inputs :=
      fun j hj hne => by rw [← hdeps _ (hopsC j hj hne)]; exact hponly j hj hne
    have hI : L538_Ins n p jg2 C C' := L538_del_ins C jg2 hjg p hponlyS
      (L538_out_ne K l p hl hp C hfun p (Or.inr rfl)) hrb
    have hg : gateAt C jg2 = ⟨GateOp.and, [l.val, p.val]⟩ ∨
        gateAt C jg2 = ⟨GateOp.and, [p.val, l.val]⟩ := hgl
    exact L538_up K K' l p hl hp hK' C C' jg2 hI hg hnlS d' hd'
  · rintro ⟨d, hd⟩
    obtain ⟨jg, C', d', hI, hg, hd'⟩ := L538_down K K' l p hl hp hK' C d hd
    obtain ⟨⟨hC'fan, hC'min⟩, hC'fun⟩ := (hyp C').2 ⟨d', hd'⟩
    obtain ⟨hCfan, hCsize⟩ := L538_ins_fan C C' p jg hI
      (by rcases hg with h | h <;> rw [h] <;> simp) hC'fan
    have hCfun : circuitFun n C = graphFun K ∅ := by
      funext x; rw [L538_ins_eval C C' l p jg hI hg x, hC'fun, hFins]
    refine ⟨⟨hCfan, fun D hD hDf => ?_⟩, hCfun⟩
    obtain ⟨D', hD', hsz, hD'f⟩ := L538_elim (graphFun K ∅) D hD (hDf.trans hCfun) l
      (L538_fun_dep K l p hl hp l (Or.inl rfl)).1 (L538_fun_dep K l p hl hp l (Or.inl rfl)).2
    have := hC'min D' hD' (by rw [hD'f, hC'fun]; funext x; exact hFl x)
    omega
