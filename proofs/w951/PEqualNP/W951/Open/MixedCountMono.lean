import PEqualNP.W951.Open.MixedCount

/-!
# MixedCountMono: the mixed count for a gate list with no NOT gate (seat A16)

Board `open-one-not`. With no NOT gate there is no DD set (`DDAt` needs an index `p`): a monotone wire
that is `0` at the top zero point `Zof (S b ∪ D)` is `0` at every unit atom `Q + e_u` with
`u ∉ S b`, so two unit merge sets overlap in at most `S a ∩ S b`, which has at most one point.

* `unitMerge_card_ge_and_subset_mono`: the merge set of any alive set has `≥ |S w \ D| - 1` wires and
  lies in `F2Mix`.
* `mixedCount_of_noNot`: `MixedCount gates S` for pairwise `|S a ∩ S b| ≤ 1`, an `out` wire per set
  and no NOT gate.
* `mixedCount_mono`: the same for a `MinCE` (exactly the `hmono` hypothesis of
  `mixedStepNeg_of_ddAbsorb`); `no_minCE_of_ddAbsorb_mono` drops that hypothesis.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Mono

variable {n m : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hnn : ∀ g ∈ gates, g.op ≠ GateOp.not)

include hg hnn

theorem andOr_of_noNot : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hgm
  rcases (hg g hgm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hnn g hgm)

theorem goodT_of_noNot (z : Fin n → Bool) (P : Fin n → Fin n → Bool) (R : Finset (Fin n)) :
    GoodT z P R gates := by
  intro pre g rest h
  have hmem : g ∈ gates := by rw [h]; simp
  exact Or.inl ⟨andOr_of_noNot gates hg hnn g hmem, (hg g hmem).2⟩

/-- Monotone overlap: a wire `0` at `Zof (S b ∪ D)` and `1` at the unit atoms of two distinct points of
`S a \ D` is impossible when `|S a ∩ S b| ≤ 1`. -/
theorem overlap_absurd_mono (S : Fin m → Finset (Fin n)) (a b : Fin m)
    (hab : (S a ∩ S b).card ≤ 1) (Q D : Finset (Fin n)) (hQb : Disjoint Q (S b ∪ D)) (i : ℕ)
    (hzb : val gates (Zof (S b ∪ D)) i = false) {u u' : Fin n} (hu : u ∈ S a \ D)
    (hu' : u' ∈ S a \ D) (huu : u ≠ u')
    (h1 : val gates (upPt (canonPt Q) u) i = true)
    (h2 : val gates (upPt (canonPt Q) u') i = true) : False := by
  have key : ∀ t ∈ S a \ D, val gates (upPt (canonPt Q) t) i = true → t ∈ S b := by
    intro t ht h
    by_contra htb
    have htD : t ∉ D := (Finset.mem_sdiff.mp ht).2
    have hle := unit_le_top hQb (u := t) (by simp [htb, htD])
    have := mono_val gates (andOr_of_noNot gates hg hnn) _ _ (le_imp hle) i h
    rw [hzb] at this
    exact absurd this (by simp)
  have : 2 ≤ (S a ∩ S b).card :=
    Finset.one_lt_card.mpr ⟨u, mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1, key u hu h1⟩, u',
      mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu').1, key u' hu' h2⟩, huu⟩
  omega

/-- **Unit-form merges, monotone.** -/
theorem unitMerge_card_ge_and_subset_mono (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (w : Fin m) (hw : Disjoint Q (S w ∪ D)) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x out = decide (∃ u ∈ S w, x u = true)) :
    (S w \ D).card - 1 ≤ (unitMerge gates S Q D w).card ∧
      unitMerge gates S Q D w ⊆ MixedSlack.F2Mix gates S Q D := by
  classical
  have hwa : w ∈ aliveSets S Q :=
    mem_aliveSets.mpr (Finset.disjoint_of_subset_left Finset.subset_union_left hw.symm)
  have hT := unit_testSystem (R := S w) (D := D) hw
  have hgood := goodT_of_noNot gates hg hnn (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D)
  have hzero : ∀ x ∈ S w, Zof (S w ∪ D) x = false := by
    intro x hx
    simp [Zof, hx]
  refine ⟨?_, ?_⟩
  · refine merge_countT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates hT hgood out
      ?_ fun u hu => ?_
    · rw [hev]
      simpa using fun y hy => hzero y hy
    · rw [hev]
      exact decide_eq_true ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [upPt]⟩
  · intro i hi
    obtain ⟨j, -, rfl, -⟩ :=
      (runMT_mem (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates gates.length i).mp hi
    obtain ⟨hjl, hor⟩ := runMT_or gates hg (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D)
      hT hgood j hi
    obtain ⟨⟨u, hu, u', hu', h1, h2, hne⟩, -⟩ :=
      run_recordT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates gates.length j hi
    have huu : u ≠ u' := fun h => hne (h ▸ rfl)
    have h0 : val gates (Zof (S w ∪ D)) (n + j) = false := by
      have h := run_sub_DT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates _ hi
      simp only [DT, Finset.mem_filter] at h
      exact h.2.1
    have hij : n + j ∈ Finset.Ico n (n + gates.length) := by
      rw [Finset.mem_Ico]; omega
    simp only [MixedSlack.F2Mix, Finset.mem_filter]
    refine ⟨hij, ?_, w, hwa, ?_⟩
    · show IsOrAt gates (n + j - n)
      rw [Nat.add_sub_cancel_left]
      exact ⟨gates[j], List.getElem?_eq_getElem hjl, hor⟩
    have hup : ∀ t ∈ S w \ D, val gates (upPt (canonPt Q) t) (n + j) = true →
        val gates (Function.update (Zof (S w ∪ D)) t true) (n + j) = true := by
      intro t _ h
      exact mono_val gates (andOr_of_noNot gates hg hnn) _ _
        (le_imp (upPt_le_upPt (canonPt_le_top hw) t)) _ h
    refine ⟨Zof (S w ∪ D), u, u', hu, hu', huu, fun x hx => ?_, fun x hx => ?_, h0, hup u hu h1,
      hup u' hu' h2⟩
    · simp [Zof, hx]
    · have : x ∉ S w ∪ D := Finset.disjoint_left.mp hw hx
      simp [Zof, this]

/-- **The mixed count, no NOT gate.** -/
theorem mixedCount_of_noNot (S : Fin m → Finset (Fin n))
    (hov : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hev : ∀ w, ∃ out : ℕ, ∀ x : Fin n → Bool,
      val gates x out = decide (∃ u ∈ S w, x u = true)) :
    MixedSlack.MixedCount gates S := by
  classical
  intro Q D hQD
  have hdis : ∀ w ∈ aliveSets S Q, Disjoint Q (S w ∪ D) := fun w hw =>
    Finset.disjoint_union_right.mpr ⟨(mem_aliveSets.mp hw).symm, hQD⟩
  have hpair : ∀ a ∈ aliveSets S Q, ∀ b ∈ aliveSets S Q, a ≠ b →
      Disjoint (unitMerge gates S Q D a) (unitMerge gates S Q D b) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨hza, u, hu, u', hu', huu, h1, h2⟩ := unitMerge_data gates S Q D a i hia
    obtain ⟨hzb, v, hv, v', hv', hvv, h3, h4⟩ := unitMerge_data gates S Q D b i hib
    exact overlap_absurd_mono gates hg hnn S a b (hov a b hab) Q D (hdis b hb) i hzb hu hu' huu
      h1 h2
  have hsub : (aliveSets S Q).biUnion (unitMerge gates S Q D) ⊆ MixedSlack.F2Mix gates S Q D := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨out, hout⟩ := hev w
    exact (unitMerge_card_ge_and_subset_mono gates hg hnn S Q D w (hdis w hw) out hout).2 hiw
  have hsum : ∑ w ∈ aliveSets S Q, ((S w \ D).card - 1) ≤
      ∑ w ∈ aliveSets S Q, (unitMerge gates S Q D w).card :=
    Finset.sum_le_sum fun w hw => by
      obtain ⟨out, hout⟩ := hev w
      exact (unitMerge_card_ge_and_subset_mono gates hg hnn S Q D w (hdis w hw) out hout).1
  have hu : ∑ w ∈ aliveSets S Q, (unitMerge gates S Q D w).card =
      ((aliveSets S Q).biUnion (unitMerge gates S Q D)).card :=
    (Finset.card_biUnion hpair).symm
  have hfin : baseDQ S D Q ≤ (MixedSlack.F2Mix gates S Q D).card :=
    le_trans hsum (hu ▸ Finset.card_le_card hsub)
  unfold MixedSlack.mslack
  have := (Nat.cast_le (α := ℤ)).mpr hfin
  omega

end Mono

/-- **`MixedCount` for a minimal counterexample with no NOT gate.** -/
theorem mixedCount_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (M : MinCE S gates out)
    (hno : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op ≠ GateOp.not) :
    MixedSlack.MixedCount gates S := by
  refine mixedCount_of_noNot gates M.ce.hg ?_ S M.ce.hS (fun w => ⟨out w, M.ce.hev w⟩)
  intro g hgm
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
  exact hno p hp

/-- `no_minCE` from `DDAbsorb` alone: the monotone case is now closed. -/
theorem no_minCE_of_ddAbsorb_mono
    (hD : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
        ∀ Q D : Finset (Fin n), Disjoint Q D → DDAbsorb gates p S Q D) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_ddAbsorb hD fun _ _ S gates out M hno => mixedCount_mono S gates out M hno

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
