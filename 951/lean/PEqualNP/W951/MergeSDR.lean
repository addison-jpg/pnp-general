import PEqualNP.W951.PriceOff

/-!
# MergeSDR: one zero point per set, pairwise disjoint merge sets

Coord assignment (split with cTAHG, who takes ChainSDR / CU). `MergeSDR S gates`: every set `w` has
a zero point `z_w` (vanishing on `S w`) such that the merge sets `M_{z_w}(w)` are pairwise disjoint.
This is the integral form of `MergeFrac`:
* `mergeFrac_of_mergeSDR`: point masses at the `z_w` form a `MergeFrac` family; hence
  `mergePrice_of_mergeSDR`, `bound_of_mergeSDR` (the 951 bound) and `no_minCE_of_mergeSDR`;
* `mergeSDR_of_integral`: conversely, a `MergeFrac` family with values in `{0, 1}` is a `MergeSDR`.
So `MergeSDR` is exactly `MergeFrac` with an integral `μ`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section SDR

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)

/-- **MergeSDR**: one zero point `z_w` per set, with pairwise disjoint merge sets `M_{z_w}(w)`. -/
def MergeSDR : Prop :=
  ∃ z : Fin m → (Fin n → Bool), (∀ w, ∀ v ∈ S w, z w v = false) ∧
    ∀ a b : Fin m, a ≠ b →
      Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))

/-- **MergeSDR ⇒ MergeFrac**: the point masses at the chosen zero points. -/
theorem mergeFrac_of_mergeSDR (h : MergeSDR S gates) : MergeFrac S gates := by
  classical
  obtain ⟨z, hz, hdisj⟩ := h
  refine ⟨fun w x => if x = z w then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro w x
    dsimp only
    split_ifs <;> norm_num
  · intro w x ⟨v, hv, hxv⟩
    have hne : x ≠ z w := by
      rintro rfl
      rw [hz w v hv] at hxv
      exact absurd hxv (by simp)
    simp [hne]
  · intro w
    simp
  · intro g
    have hterm : ∀ w, ∑ x : Fin n → Bool,
        (if g ∈ mergeSet gates (S w) x then (if x = z w then (1 : ℝ) else 0) else 0) =
        if g ∈ mergeSet gates (S w) (z w) then 1 else 0 := by
      intro w
      rw [Finset.sum_eq_single (z w)]
      · simp
      · intro x _ hx
        simp [hx]
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [hterm]
    -- at most one set has `g` in its chosen merge set
    rw [Finset.sum_boole]
    have hcard : (Finset.univ.filter fun w : Fin m => g ∈ mergeSet gates (S w) (z w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hab
      exact Finset.disjoint_left.mp (hdisj a b hab) ha hb
    exact_mod_cast hcard

/-- **MergeSDR ⇒ MergePrice**. -/
theorem mergePrice_of_mergeSDR (h : MergeSDR S gates) : MergePrice S gates :=
  mergePrice_of_mergeFrac S gates (mergeFrac_of_mergeSDR S gates h)

/-- **MergeSDR gives the 951 bound.** -/
theorem bound_of_mergeSDR (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (h : MergeSDR S gates) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length :=
  bound_of_mergeFrac S gates out hg hU hev (mergeFrac_of_mergeSDR S gates h)

/-- **MergeSDR is integral MergeFrac**: a `MergeFrac` family with values in `{0, 1}` comes from
a `MergeSDR`. -/
theorem mergeSDR_of_integral (μ : Fin m → (Fin n → Bool) → ℝ)
    (hS : ∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0)
    (h1 : ∀ w, ∑ z, μ w z = 1)
    (hload : ∀ g : ℕ, ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) ≤ 1)
    (h01 : ∀ w z, μ w z = 0 ∨ μ w z = 1) : MergeSDR S gates := by
  classical
  have hex : ∀ w, ∃ z, μ w z = 1 := by
    intro w
    by_contra hno
    push Not at hno
    have : ∑ z, μ w z = 0 :=
      Finset.sum_eq_zero fun z _ => (h01 w z).resolve_right (hno z)
    rw [h1 w] at this
    norm_num at this
  choose z hz using hex
  have hnn : ∀ w x, 0 ≤ μ w x := fun w x => by rcases h01 w x with h | h <;> simp [h]
  refine ⟨z, fun w v hv => ?_, fun a b hab => ?_⟩
  · by_contra hzv
    have := hS w (z w) ⟨v, hv, by simpa using hzv⟩
    rw [hz w] at this
    norm_num at this
  · rw [Finset.disjoint_left]
    intro g ha hb
    let f : Fin m → ℝ := fun w => ∑ x, (if g ∈ mergeSet gates (S w) x then μ w x else 0)
    have hf0 : ∀ w, 0 ≤ f w := fun w =>
      Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hnn w x]
    have hfw : ∀ w, g ∈ mergeSet gates (S w) (z w) → 1 ≤ f w := by
      intro w hw
      have := Finset.single_le_sum (f := fun x => if g ∈ mergeSet gates (S w) x then μ w x else 0)
        (fun x _ => by split_ifs <;> simp [hnn w x]) (Finset.mem_univ (z w))
      simp only [hw, ite_true, hz w] at this
      exact this
    have hpair : f a + f b ≤ ∑ w, f w := by
      rw [← Finset.sum_pair hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hf0 w
    have := hload g
    have ha1 := hfw a ha
    have hb1 := hfw b hb
    change ∑ w, f w ≤ 1 at this
    linarith

end SDR

/-- **951 from MergeSDR**: if every minimal counterexample has a MergeSDR, there is none. -/
theorem no_minCE_of_mergeSDR
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → MergeSDR S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M => mergeFrac_of_mergeSDR S gates (H n m S gates out M)

end PEqualNP.Outside.L_meta_951_aux
