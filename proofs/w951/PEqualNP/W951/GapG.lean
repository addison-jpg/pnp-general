import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.Frame
import PEqualNP.W951.Cone

/-! Gap-G as a Lean statement, and its consequence.

A test system for a set `S` is a zero point `z`, test points `p u` (`u ∈ S`) and a read-closed
gate set `K` containing the output; counting is done in the circuit masked to `K`.
`GapG` says: there are test systems for all sets whose counted wire sets are pairwise disjoint.
`bound_of_gapG` shows that this gives the L-meta-951 bound. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- A valid test system for set `S` with output wire `o`. -/
structure TestSys (n : ℕ) (gates : List Gate) (S : Finset (Fin n)) (o : ℕ) where
  z : Fin n → Bool
  p : Fin n → Fin n → Bool
  K : Finset ℕ
  hzS : ∀ v ∈ S, z v = false
  hpS : ∀ u ∈ S, p u u = true
  hT : ∀ u ∈ S, ∀ c : Fin n, p u c = true → z c = false → c = u
  hcl : ReadClosed n gates.length K gates
  hout : o < n ∨ o - n ∈ K ∨ n + gates.length ≤ o
  hgood : GoodT z p S (mask K gates)

/-- The wires counted by a test system. -/
noncomputable def TestSys.cnt {n : ℕ} {gates : List Gate} {S : Finset (Fin n)} {o : ℕ}
    (σ : TestSys n gates S o) : Finset ℕ :=
  DT σ.z σ.p S (mask σ.K gates)

/-- Lemma G for a test system: the counted wires number at least `|S| - 1`. -/
theorem TestSys.card_ge {n : ℕ} {gates : List Gate} {S : Finset (Fin n)} {o : ℕ}
    (σ : TestSys n gates S o)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ S, x v = true)) :
    S.card - 1 ≤ σ.cnt.card := by
  have hm : ∀ x : Fin n → Bool, val (mask σ.K gates) x o = val gates x o := fun x =>
    val_mask σ.K gates.length x gates le_rfl σ.hcl o σ.hout
  apply countT_bound σ.z σ.p S σ.hT (mask σ.K gates) σ.hgood o
  · rw [hm, hev, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv'⟩
    rw [σ.hzS v hv] at hv'
    exact absurd hv' (by simp)
  · intro u hu
    rw [hm, hev, decide_eq_true_eq]
    exact ⟨u, hu, σ.hpS u hu⟩

/-- Gap-G: test systems for all sets with pairwise disjoint counted wires. -/
def GapG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∃ σ : ∀ w, TestSys n gates (S w) (out w),
    ∀ a b : Fin m, a ≠ b → Disjoint (σ a).cnt (σ b).cnt

/-- Gap-G gives the bound. -/
theorem bound_of_gapG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hg : GapG S gates out) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨σ, hdisj⟩ := hg
  have hsub : ∀ w, (σ w).cnt ⊆ Finset.Ico n (n + gates.length) := by
    intro w i hi
    simp only [TestSys.cnt, DT, Finset.mem_filter, mask_length] at hi
    exact hi.1
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, ((σ w).cnt).card :=
        Finset.sum_le_sum fun w _ => (σ w).card_ge (hev w)
    _ ≤ (Finset.Ico n (n + gates.length)).card :=
        PEqualNP.Base.Matching.sum_card_le_of_pairwiseDisjoint _ _ _ (fun a _ b _ hab => hdisj a b hab) fun w _ => hsub w
    _ = gates.length := by simp

end PEqualNP.Outside.L_meta_951_aux
