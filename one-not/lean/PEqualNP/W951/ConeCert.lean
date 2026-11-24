import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Cone
import PEqualNP.W951.MergeFrac
import PEqualNP.W951.CubeF2

/-!
# ConeCert: qg-d2's CERT-1c ⇒ the F2 step (coord 13:18)

qg-d2's certificate (one-not/board/agents/qg-d2-ucert.md, checked on 31,503 every-gate-read instances):
for the sets through a chosen `v`, the CONE merge sets at the zero point `Q` (Lemma M's union-find run
only over the gates of the cone of `o_w`) are pairwise disjoint (S) and leave F2 under `x_v := 1` (D).
This file proves the reduction **(D) ∧ (S) at `v` ⇒ `GainF2` at `v`**, with (D) and (S) as hypotheses,
for any zero points `z_w ⊇ Q` off `S_w` (H3c; CERT-1c is `z_w = Q`).

* `coneMerge gates R o z = mergeSet (mask (coneOf n gates o) gates) R z`: gates outside the cone of
  `o` are masked to the constant `0`, so they never merge.
* `mask_hg`, `mask_hU`: masking keeps the gate shapes and adds no NOT gate.
* `coneMerge_card`: Lemma M in the cone: `|R| - 1 ≤ |coneMerge|` (the masked circuit computes the same
  value at `o`, `val_mask`).
* `coneMerge_real`: a cone merge `n + j` is a real OR gate of the cone, `0` at `z` and `1` at `z + e_u`,
  `z + e_u'` for two points `u ≠ u'` of `R` in the REAL circuit.
* `coneMerge_mem_F2`: so it lies in `F2(Q)` (witness `(z, u, u')`).
* `CertD`, `CertS`, **`gainF2_of_cert`**: (D) ∧ (S) ⇒ `GainF2 gates S Q v`, with the explicit
  injection `⋃_{w ∋ v} coneMerge(w) ⊆ F2(Q) \ F2(Q ∪ {v})`.
* `Cert1c` (zero point `Q` for every set), `gainF2_of_cert1c`; `Cert3c` (per-set zero points),
  `gainF2_of_cert3c`.
* **`no_minCE_of_cert_or_local`**: every `Q` with positive base is `CubeLocal`, satisfies LW1, or has a
  `v ∉ Q` with CERT-3c ⇒ no minimal counterexample. So paper proofs of (D) and (S) plug in directly.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section ConeCert

variable {n m : ℕ}

/-- **The cone merge set** of `R` with output `o` at the zero point `z`: Lemma M's union-find over the
gates of the cone of `o` only. -/
noncomputable def coneMerge (gates : List Gate) (R : Finset (Fin n)) (o : ℕ) (z : Fin n → Bool) :
    Finset ℕ :=
  mergeSet (mask (coneOf n gates o) gates) R z

theorem mask_getElem (K : Finset ℕ) (gs : List Gate) (j : ℕ) (hj : j < (mask K gs).length) :
    (mask K gs)[j] = if j ∈ K then gs[j]'(by rw [mask_length] at hj; exact hj) else ⟨GateOp.or, []⟩ := by
  simp [mask, List.getElem_mapIdx]

theorem mask_hg (K : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ mask K gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
  intro g hgm
  obtain ⟨i, hi, rfl⟩ := mem_mask hgm
  split_ifs
  · exact hg _ (List.getElem_mem hi)
  · exact ⟨Or.inr (Or.inl rfl), by simp⟩

theorem mask_hU (K : Finset ℕ) (gs : List Gate) (hU : AtMostOneNot gs) :
    AtMostOneNot (mask K gs) := by
  intro i1 i2 h1 h2 e1 e2
  rw [mask_getElem] at e1 e2
  split_ifs at e1 e2
  exact hU i1 i2 _ _ e1 e2

variable (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

/-- The masked circuit computes the same value at `o`. -/
theorem val_mask_cone (o : ℕ) (x : Fin n → Bool) :
    val (mask (coneOf n gates o) gates) x o = val gates x o :=
  val_mask _ gates.length x gates le_rfl (coneOf_closed n gates o) o (coneOf_out n gates o)

include hg hU in
/-- **Lemma M in the cone**: a cone merge set has at least `|R| - 1` gates. -/
theorem coneMerge_card (R : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) (z : Fin n → Bool)
    (hz : ∀ v ∈ R, z v = false) : R.card - 1 ≤ (coneMerge gates R o z).card := by
  refine mergeSet_card_ge _ (mask_hg _ gates hg) (mask_hU _ gates hU) R z o ?_ fun u hu => ?_
  · rw [val_mask_cone, hev]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    rw [hz v hv] at hzv
    exact absurd hzv (by decide)
  · rw [val_mask_cone, hev]
    exact decide_eq_true ⟨u, hu, by simp [upPt]⟩

include hg hU in
/-- **A cone merge is a real OR gate of the cone with the union-find data in the real circuit.** -/
theorem coneMerge_real {R : Finset (Fin n)} {o : ℕ} {z : Fin n → Bool} {i : ℕ}
    (hi : i ∈ coneMerge gates R o z) :
    ∃ j, i = n + j ∧ ∃ hjl : j < gates.length, j ∈ coneOf n gates o ∧
      (gates[j]'hjl).op = GateOp.or ∧ val gates z i = false ∧
      ∃ u ∈ R, ∃ u' ∈ R, u ≠ u' ∧ val gates (upPt z u) i = true ∧
        val gates (upPt z u') i = true := by
  classical
  set K := coneOf n gates o with hK
  obtain ⟨j, -, rfl⟩ := run_indexT z (upPt z) R (mask K gates) _ i hi
  have h1 := run_sub_DT z (upPt z) R (mask K gates) _ hi
  rw [DT, Finset.mem_filter, Finset.mem_Ico, mask_length] at h1
  obtain ⟨⟨-, hjl'⟩, hz, u, u', huu, hu, hu', h1u, h1u'⟩ := h1
  have hjl : j < gates.length := by omega
  have hjK : j ∈ K := by
    by_contra hjK
    rw [val_mask_out K gates (upPt z u) j hjl hjK] at h1u
    exact absurd h1u (by decide)
  have hv : ∀ x : Fin n → Bool, val (mask K gates) x (n + j) = val gates x (n + j) := fun x =>
    val_mask K gates.length x gates le_rfl (coneOf_closed n gates o) (n + j)
      (Or.inr (Or.inl (by rw [Nat.add_sub_cancel_left]; exact hjK)))
  obtain ⟨hjl2, hor⟩ := mergeSet_or _ (mask_hg K gates hg) (mask_hU K gates hU) R z j hi
  rw [mask_getElem, ite_eq_left hjK] at hor
  rw [hv] at hz h1u h1u'
  exact ⟨j, rfl, hjl, hjK, hor, hz, u, hu, u', hu', huu, h1u, h1u'⟩

include hg hU in
/-- **Cone merges are F2 gates**: for an alive set `S_w` and a zero point `z ⊇ Q` off `S_w`, every
cone merge of `S_w` at `z` lies in `F2(Q)` (witness `(z, u, u')`). -/
theorem coneMerge_mem_F2 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (w : Fin m) (hw : w ∈ aliveSets S Q) (z : Fin n → Bool) (hzS : ∀ u ∈ S w, z u = false)
    (hzQ : ∀ q ∈ Q, z q = true) {i : ℕ} (hi : i ∈ coneMerge gates (S w) (out w) z) :
    i ∈ F2 gates S Q := by
  obtain ⟨j, rfl, hjl, -, hor, hz, u, hu, u', hu', huu, h1, h2⟩ := coneMerge_real gates hg hU hi
  exact mem_F2.mpr ⟨⟨j, rfl, gates[j], List.getElem?_eq_getElem hjl, hor⟩, w, hw, z, u, u', hu, hu',
    huu, hzS, hzQ, hz, h1, h2⟩

/-- **CERT (D)**: no cone merge of a set through `v` lies in `F2(Q ∪ {v})` (it dies under `x_v := 1`). -/
def CertD (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (z : Fin m → Fin n → Bool) : Prop :=
  ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w), i ∉ F2 gates S (insert v Q)

/-- **CERT (S)**: the cone merge sets of the sets through `v` are pairwise disjoint. -/
def CertS (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (z : Fin m → Fin n → Bool) : Prop :=
  ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
    Disjoint (coneMerge gates (S w) (out w) (z w)) (coneMerge gates (S w') (out w') (z w'))

include hg hU in
/-- **(D) ∧ (S) ⇒ the F2 step at `v`**, for any zero points `z_w ⊇ Q` off `S_w`. -/
theorem gainF2_of_cert (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (z : Fin m → Fin n → Bool) (hzS : ∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false)
    (hzQ : ∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true)
    (hD : CertD gates S out Q v z) (hS : CertS gates S out Q v z) : GainF2 gates S Q v := by
  classical
  set C : Fin m → Finset ℕ := fun w => coneMerge gates (S w) (out w) (z w) with hC
  have hpd : ((starSets S Q v : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint C :=
    fun w hw w' hw' hww => hS w hw w' hw' hww
  unfold GainF2
  calc ∑ w ∈ starSets S Q v, ((S w).card - 1)
      ≤ ∑ w ∈ starSets S Q v, (C w).card := Finset.sum_le_sum fun w hw =>
        coneMerge_card gates hg hU (S w) (out w) (hev w) (z w) (hzS w hw)
    _ = ((starSets S Q v).biUnion C).card := (Finset.card_biUnion hpd).symm
    _ ≤ (F2 gates S Q \ F2 gates S (insert v Q)).card := Finset.card_le_card
        (Finset.biUnion_subset.mpr fun w hw i hi => Finset.mem_sdiff.mpr
          ⟨coneMerge_mem_F2 gates hg hU S out Q w (Finset.mem_filter.mp hw).1 (z w) (hzS w hw)
            (hzQ w hw) hi, hD w hw i hi⟩)

/-- **CERT-1c** at `v`: (D) and (S) for the cone merge sets at the zero point `Q` (`canonPt Q`). -/
def Cert1c (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  CertD gates S out Q v (fun _ => canonPt Q) ∧ CertS gates S out Q v (fun _ => canonPt Q)

/-- **CERT-3c** at `v` (qg-d2's H3c): (D) and (S) for per-set zero points `z_w ⊇ Q` off `S_w`. -/
def Cert3c (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  ∃ z : Fin m → Fin n → Bool, (∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false) ∧
    (∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true) ∧ CertD gates S out Q v z ∧
      CertS gates S out Q v z

theorem cert3c_of_cert1c {S : Fin m → Finset (Fin n)} {out : Fin m → ℕ} {Q : Finset (Fin n)}
    {v : Fin n} (h : Cert1c gates S out Q v) : Cert3c gates S out Q v := by
  refine ⟨fun _ => canonPt Q, fun w hw u hu => ?_, fun _ _ q hq => canonPt_eq_true.mpr hq, h.1, h.2⟩
  have hdis := mem_aliveSets.mp (Finset.mem_filter.mp hw).1
  have huQ : u ∉ Q := fun h' => Finset.disjoint_left.mp hdis hu h'
  simp [canonPt, huQ]

include hg hU in
theorem gainF2_of_cert3c (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (h : Cert3c gates S out Q v) : GainF2 gates S Q v := by
  obtain ⟨z, hzS, hzQ, hD, hS⟩ := h
  exact gainF2_of_cert gates hg hU S out Q v hev z hzS hzQ hD hS

include hg hU in
/-- **CERT-1c ⇒ the F2 step at `v`.** -/
theorem gainF2_of_cert1c (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (h : Cert1c gates S out Q v) : GainF2 gates S Q v :=
  gainF2_of_cert3c gates hg hU S out Q v hev (cert3c_of_cert1c gates h)

end ConeCert

/-- **951 from CERT-3c with the local closures**: if every minimal counterexample has a NOT gate such
that every `Q` with positive base is `CubeLocal`, satisfies LW1, or has a point `v ∉ Q` where CERT-3c
holds ((D) and (S) for some zero points `z_w ⊇ Q`), there is no minimal counterexample. -/
theorem no_minCE_of_cert_or_local
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q →
          CubeLocal gates p Q ∨ LW1 gates p S Q ∨ ∃ v, v ∉ Q ∧ Cert3c gates S out Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_gainF2_or_local fun n m S gates out M => by
    obtain ⟨p, hp, hN, hQ⟩ := H n m S gates out M
    refine ⟨p, hp, hN, fun Q hpos => ?_⟩
    rcases hQ Q hpos with h | h | ⟨v, hvQ, hc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨v, hvQ, gainF2_of_cert3c gates M.ce.hg M.ce.hU S out Q v M.ce.hev hc⟩)

end PEqualNP.Outside.L_meta_951_aux
