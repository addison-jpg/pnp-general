import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MUInduct

/-!
# GraphHeavy: front A2's G1 (graph systems, heavy `v`) in UC-gain form

Front A2's paper construction G1 (`one-not/SYNTHESIS-one-not.md` §6.1; coord 12:41), stated as the UC gain
`GainOne gates p S ∅ Q v` of `MUInduct.lean` (`∑_{star} d_w ≤ |UC(∅, Q) \ UC(∅, Q ∪ {v})|`).

Every alive set through `v` has two points `{v, a}` and takes the I0 class at `top_va` (world 0) with
atom points `m_v = Q ∪ {v}` and `m_a = M_a`.

* `C0_of_mem_starCls`: a gate of such a class is `1` at `(Q ∪ {v}, 0)` (with two points, every merge
  joins `v` and `a`), so by Lemma C0 (`not_UCWit_of_C0`) it is not in `UC(∅, Q ∪ {v})`. It is in
  `UC(∅, Q)` (`pureCls_UCWit`: `top_va` is `1` on `Q`).
* `gainOne_graphStar`: if `v` is heavy over `Q` (`h(Q ∪ {v}) = 1`), every `h(M_a) = 1` with `v ∉ M_a`,
  and for any two star neighbours `a ≠ b` one has `b ∉ M_a` or `a ∉ M_b`, the star classes are
  pairwise disjoint (W0, `disjoint_pureI0_pureI0`), each has at least `d_w = 1` gate (`card_pureCls`),
  and all lie in `UC(∅, Q) \ UC(∅, Q ∪ {v})`: `GainOne` at `v`.
* **G1** (`gainOne_G1`): `L` = the light neighbours (`h(Q ∪ {a}) = 0`, `lightNbr`), `X = V \ ({v} ∪ L)`,
  `M_a = X ∪ {a}` for light `a` and `Q ∪ {a}` for heavy `a`. If `h(X ∪ {a}) = 1` for every light `a`,
  `GainOne` holds at `v`.
* `gainOne_G1_of_heavy`: the condition of G1 is automatic when another point `x ≠ v` is heavy over `Q`.

The other construction (GL, lifted classes outside the pure menus) and the residual case are not
here.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section GraphHeavy

variable {n m : ℕ}

/-- The atom points of a star: `m_v = Q ∪ {v}`, `m_a = M_a` for `a ≠ v`. -/
def starM (Q : Finset (Fin n)) (v : Fin n) (M : Fin n → Finset (Fin n)) (u : Fin n) :
    Finset (Fin n) :=
  if u = v then insert v Q else M u

theorem mem_pair_of_card_two {R : Finset (Fin n)} (hR : R.card = 2) {v u x : Fin n} (hv : v ∈ R)
    (hu : u ∈ R) (huv : u ≠ v) (hx : x ∈ R) : x = v ∨ x = u := by
  have hsub : ({v, u} : Finset (Fin n)) ⊆ R := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hv
    · rw [Finset.mem_singleton.mp hy]
      exact hu
  have heq : ({v, u} : Finset (Fin n)) = R :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hR, Finset.card_pair (Ne.symm huv)])
  rw [← heq] at hx
  simpa using hx

/-- **Star gates are `v`-gates**: a gate of the I0 class of a two-point set through `v` (atoms
`starM`) is `1` at `(Q ∪ {v}, 0)`. -/
theorem C0_of_mem_starCls (gates : List Gate) (p : ℕ) (R Q : Finset (Fin n)) (v : Fin n)
    (M : Fin n → Finset (Fin n)) (hR : R.card = 2) (hvR : v ∈ R) {i : ℕ}
    (hi : i ∈ pureCls gates p R (.zero (starM Q v M))) :
    val (lift n p gates) (ext (canonPt (insert v Q)) false) i = true := by
  classical
  have h1 := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h1
  obtain ⟨-, -, c, c', hcc, hc, hc', h1c, h1c'⟩ := h1
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨u', hu', rfl⟩ := mem_liftSet_iff.mp hc'
  have hatom : atom0 (starM Q v M) (Fin.castSucc v) = ext (canonPt (insert v Q)) false := by
    rw [atom0_castSucc, starM, ite_eq_left rfl, Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
  by_cases huv : u = v
  · subst huv
    rwa [hatom] at h1c
  · rcases mem_pair_of_card_two hR hvR hu huv hu' with rfl | rfl
    · rwa [hatom] at h1c'
    · exact absurd rfl hcc

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- Two star classes are disjoint when the neighbour `a` of the first set has an atom avoiding the
second set `{v, b}` (`b ∉ M_a`). -/
theorem disjoint_starCls (Q : Finset (Fin n)) (v : Fin n) (M : Fin n → Finset (Fin n))
    (R R' : Finset (Fin n)) (hR : R.card = 2) (hR' : R'.card = 2) (hvR : v ∈ R) (hvR' : v ∈ R')
    {a b : Fin n} (ha : a ∈ R) (hav : a ≠ v) (hb : b ∈ R') (hbv : b ≠ v) (hab : a ≠ b)
    (hvM : v ∉ M a) (hbM : b ∉ M a) :
    Disjoint (pureCls gates p R (.zero (starM Q v M))) (pureCls gates p R' (.zero (starM Q v M))) := by
  have hA : Disjoint (insert a (starM Q v M a)) R' := by
    rw [starM, ite_eq_right hav, Finset.disjoint_left]
    intro x hx hxR'
    rcases mem_pair_of_card_two hR' hvR' hb hbv hxR' with rfl | rfl
    · rcases Finset.mem_insert.mp hx with h | h
      · exact hav h.symm
      · exact hvM h
    · rcases Finset.mem_insert.mp hx with h | h
      · exact hab h.symm
      · exact hbM h
  refine disjoint_pureI0_pureI0 gates p hp hg hU hN R R' _ _ fun u hu u' hu' huu => ?_
  by_cases huv : u = v
  · subst huv
    rcases mem_pair_of_card_two hR hvR ha hav hu' with h | rfl
    · exact absurd h.symm huu
    · exact Or.inr hA
  · rcases mem_pair_of_card_two hR hvR ha hav hu with rfl | rfl
    · exact absurd rfl huv
    · exact Or.inl hA

include hg hU hN in
/-- **The graph star gain.** Two-point star sets, pairwise meeting in at most one point; `v` heavy
over `Q`; atom points `M_a` with `h(M_a) = 1` and `v ∉ M_a`; for any two star neighbours one atom
avoids the other set. Then `GainOne` at `v`. -/
theorem gainOne_graphStar (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n) (M : Fin n → Finset (Fin n))
    (h2 : ∀ w ∈ starSets S Q v, (S w).card = 2)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hM : ∀ w ∈ starSets S Q v, ∀ a ∈ S w, a ≠ v →
      v ∉ M a ∧ val gates (canonPt (M a)) (n + p) = false)
    (hsep : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → ∀ a ∈ S w, a ≠ v →
      ∀ b ∈ S w', b ≠ v → b ∉ M a ∨ a ∉ M b) :
    GainOne gates p S ∅ Q v := by
  classical
  set mm := starM Q v M with hmm
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  have hvalid : ∀ w ∈ starSets S Q v, PureValid gates p (S w) (.zero mm) := by
    intro w hw
    obtain ⟨hwa, hvw⟩ := (hstar w).mp hw
    have hQ := mem_aliveSets.mp hwa
    refine ⟨fun u hu x hx hxR => ?_, fun u hu => ?_⟩
    · by_cases huv : u = v
      · subst huv
        rw [hmm, starM, ite_eq_left rfl] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rfl
        · exact absurd hx (Finset.disjoint_left.mp hQ hxR)
      · rw [hmm, starM, ite_eq_right huv] at hx
        rcases mem_pair_of_card_two (h2 w hw) hvw hu huv hxR with rfl | rfl
        · exact absurd hx (hM w hw u hu huv).1
        · rfl
    · by_cases huv : u = v
      · subst huv
        rw [hmm, starM, ite_eq_left rfl]
        exact hQv
      · rw [hmm, starM, ite_eq_right huv]
        exact (hM w hw u hu huv).2
  -- the classes lie in `UC(∅, Q) \ UC(∅, Q ∪ {v})`
  have hsub : ∀ w ∈ starSets S Q v, pureCls gates p (S w) (.zero mm) ⊆
      UC gates p S ∅ Q \ UC gates p S ∅ (insert v Q) := by
    intro w hw i hi
    obtain ⟨hwa, hvw⟩ := (hstar w).mp hw
    have hQ0 : ∀ x ∈ Q, (PureOpt.zero mm).zeroPt (S w) x = true := by
      intro x hx
      have : x ∉ S w := fun h => Finset.disjoint_left.mp (mem_aliveSets.mp hwa) h hx
      simp [PureOpt.zeroPt, Zof, this]
    obtain ⟨hor, hwit⟩ := pureCls_UCWit gates p hp hg hU hN (S w) Q _ (hvalid w hw) hQ0 hi
    refine Finset.mem_sdiff.mpr ⟨mem_UC.mpr ⟨hor, w, hwa, hwit⟩, fun hi' => ?_⟩
    obtain ⟨-, w', -, hwit'⟩ := mem_UC.mp hi'
    exact not_UCWit_of_C0 gates p hp hg hU hN (S w') ∅ (insert v Q)
      (C0_of_mem_starCls gates p (S w) Q v M (h2 w hw) hvw hi) hwit'
  -- pairwise disjoint
  have hpd : ((starSets S Q v : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => pureCls gates p (S w) (.zero mm) := by
    intro w hw w' hw' hww
    obtain ⟨-, hvw⟩ := (hstar w).mp hw
    obtain ⟨-, hvw'⟩ := (hstar w').mp hw'
    obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne (by rw [h2 w hw]; norm_num) v
    obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_ne (by rw [h2 w' hw']; norm_num) v
    have hab : a ≠ b := by
      rintro rfl
      have hsub2 : ({v, a} : Finset (Fin n)) ⊆ S w ∩ S w' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_inter.mpr ⟨hvw, hvw'⟩
        · rw [Finset.mem_singleton.mp hy]
          exact Finset.mem_inter.mpr ⟨ha, hb⟩
      have := Finset.card_le_card hsub2
      rw [Finset.card_pair (Ne.symm hav)] at this
      have := hinter w hw w' hw' hww
      omega
    rcases hsep w hw w' hw' hww a ha hav b hb hbv with h | h
    · exact disjoint_starCls gates p hp hg hU hN Q v M (S w) (S w') (h2 w hw) (h2 w' hw') hvw hvw'
        ha hav hb hbv hab (hM w hw a ha hav).1 h
    · exact (disjoint_starCls gates p hp hg hU hN Q v M (S w') (S w) (h2 w' hw') (h2 w hw) hvw' hvw
        hb hbv ha hav (Ne.symm hab) (hM w' hw' b hb hbv).1 h).symm
  unfold GainOne
  calc ∑ w ∈ starSets S Q v, ((S w \ ∅).card - 1)
      ≤ ∑ w ∈ starSets S Q v, (pureCls gates p (S w) (.zero mm)).card :=
        Finset.sum_le_sum fun w hw => by
          rw [Finset.sdiff_empty]
          exact card_pureCls gates p hp hg hU hN (S w) _ (hvalid w hw) (out w) (hev w)
    _ = ((starSets S Q v).biUnion fun w => pureCls gates p (S w) (.zero mm)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (UC gates p S ∅ Q \ UC gates p S ∅ (insert v Q)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

open Classical in
/-- The light neighbours of `v` over `Q`: points `a ≠ v` of an alive set through `v` with
`h(Q ∪ {a}) = 0` (the NOT gate is `1` there). -/
noncomputable def lightNbr (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => a ≠ v ∧ (∃ w ∈ starSets S Q v, a ∈ S w) ∧
    val gates (canonPt (insert a Q)) (n + p) = true

theorem mem_lightNbr {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)} {v a : Fin n} :
    a ∈ lightNbr gates p S Q v ↔ a ≠ v ∧ (∃ w ∈ starSets S Q v, a ∈ S w) ∧
      val gates (canonPt (insert a Q)) (n + p) = true := by
  classical
  rw [lightNbr, Finset.mem_filter]
  simp

/-- `X = V \ ({v} ∪ L)`. -/
noncomputable def g1X (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ \ insert v (lightNbr gates p S Q v)

open Classical in
/-- G1's atom points: `X ∪ {a}` for a light neighbour `a`, `Q ∪ {a}` otherwise. -/
noncomputable def g1M (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (a : Fin n) :
    Finset (Fin n) :=
  if a ∈ lightNbr gates p S Q v then insert a (g1X gates p S Q v) else insert a Q

include hg hU hN in
/-- **G1** (front A2, graph systems, heavy `v`): two-point star sets meeting pairwise in at most one
point, `h(Q ∪ {v}) = 1`, and `h(X ∪ {a}) = 1` for every light neighbour `a` (`X = V \ ({v} ∪ L)`)
⇒ `GainOne` at `v`. -/
theorem gainOne_G1 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (h2 : ∀ w ∈ starSets S Q v, (S w).card = 2)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hX : ∀ a ∈ lightNbr gates p S Q v,
      val gates (canonPt (insert a (g1X gates p S Q v))) (n + p) = false) :
    GainOne gates p S ∅ Q v := by
  classical
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  have hnotQ : ∀ w ∈ starSets S Q v, ∀ x ∈ S w, x ∉ Q := fun w hw x hx hxQ =>
    Finset.disjoint_left.mp (mem_aliveSets.mp ((hstar w).mp hw).1) hx hxQ
  have hvX : v ∉ g1X gates p S Q v := by simp [g1X]
  have hLX : ∀ b ∈ lightNbr gates p S Q v, b ∉ g1X gates p S Q v := by
    intro b hb
    simp [g1X, hb]
  refine gainOne_graphStar gates p hp hg hU hN S out hev Q v (g1M gates p S Q v) h2 hinter hQv
    (fun w hw a ha hav => ?_) (fun w hw w' hw' hww a ha hav b hb hbv => ?_)
  · by_cases hL : a ∈ lightNbr gates p S Q v
    · rw [g1M, ite_eq_left hL]
      refine ⟨fun h => ?_, hX a hL⟩
      rcases Finset.mem_insert.mp h with h | h
      · exact hav h.symm
      · exact hvX h
    · rw [g1M, ite_eq_right hL]
      refine ⟨fun h => ?_, ?_⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact hav h.symm
        · exact hnotQ w hw v ((hstar w).mp hw).2 h
      · cases hval : val gates (canonPt (insert a Q)) (n + p)
        · rfl
        · exact absurd ((mem_lightNbr gates p).mpr ⟨hav, ⟨w, hw, ha⟩, hval⟩) hL
  · have hab : a ≠ b := by
      rintro rfl
      have hsub2 : ({v, a} : Finset (Fin n)) ⊆ S w ∩ S w' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_inter.mpr ⟨((hstar w).mp hw).2, ((hstar w').mp hw').2⟩
        · rw [Finset.mem_singleton.mp hy]
          exact Finset.mem_inter.mpr ⟨ha, hb⟩
      have := Finset.card_le_card hsub2
      rw [Finset.card_pair (Ne.symm hav)] at this
      have := hinter w hw w' hw' hww
      omega
    by_cases hLa : a ∈ lightNbr gates p S Q v
    · by_cases hLb : b ∈ lightNbr gates p S Q v
      · left
        rw [g1M, ite_eq_left hLa]
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hab h.symm
        · exact hLX b hLb h
      · right
        rw [g1M, ite_eq_right hLb]
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hab h
        · exact hnotQ w hw a ha h
    · left
      rw [g1M, ite_eq_right hLa]
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hab h.symm
      · exact hnotQ w' hw' b hb h

include hg hU hN in
/-- **G1 when another point is heavy**: if some `x ≠ v` has `h(Q ∪ {x}) = 1`, the condition of G1
holds (`Q ∪ {x} ⊆ X`), so `GainOne` at a heavy `v`. -/
theorem gainOne_G1_of_heavy (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (h2 : ∀ w ∈ starSets S Q v, (S w).card = 2)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (x : Fin n) (hxv : x ≠ v) (hx : val gates (canonPt (insert x Q)) (n + p) = false) :
    GainOne gates p S ∅ Q v := by
  classical
  refine gainOne_G1 gates p hp hg hU hN S out hev Q v h2 hinter hQv fun a ha => ?_
  obtain ⟨-, ⟨w, hw, -⟩, -⟩ := (mem_lightNbr gates p).mp ha
  have hvQ : v ∉ Q := fun h => Finset.disjoint_left.mp
    (mem_aliveSets.mp (Finset.mem_filter.mp hw).1) (Finset.mem_filter.mp hw).2 h
  have hxL : x ∉ lightNbr gates p S Q v := fun h => by
    rw [((mem_lightNbr gates p).mp h).2.2] at hx
    exact absurd hx (by decide)
  have hQL : ∀ q ∈ Q, q ∉ lightNbr gates p S Q v := by
    intro q hq h
    obtain ⟨-, ⟨w', hw', hqw'⟩, -⟩ := (mem_lightNbr gates p).mp h
    exact Finset.disjoint_left.mp (mem_aliveSets.mp (Finset.mem_filter.mp hw').1) hqw' hq
  refine not_false_of_le gates p hp hg hU hN (canonPt_le fun c hc => ?_) hx
  rw [canonPt_eq_true]
  refine Finset.mem_insert_of_mem ?_
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simp [g1X, hxv, hxL]
  · have hcv : c ≠ v := fun h => hvQ (h ▸ hc)
    simp [g1X, hcv, hQL c hc]

end GraphHeavy

end PEqualNP.Outside.L_meta_951_aux
