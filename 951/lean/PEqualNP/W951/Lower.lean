import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Dead

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

section
variable {m : ℕ} (S : Fin m → Finset (Fin n))
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
  (gates : List Gate) (out : Fin m → ℕ)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))

include hev in
/-- The output of a pair `{v, u}` is a gate that is dead on `{x v = false}`. -/
theorem pair_out (v : Fin n) (w : Fin m) (hv : v ∈ S w) (hc : (S w).card = 2) :
    ∃ u, u ≠ v ∧ u ∈ S w ∧ n ≤ out w ∧ out w - n ∈ DC v gates ∧
      ∀ x : Fin n → Bool, val gates x (out w) = (x v || x u) := by
  classical
  obtain ⟨a, b, hab, hSw⟩ := Finset.card_eq_two.mp hc
  have : ∃ u, u ≠ v ∧ S w = {v, u} := by
    rw [hSw] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨b, hab.symm, hSw⟩
    · exact ⟨a, hab, by rw [hSw, Finset.pair_comm]⟩
  obtain ⟨u, huv, hSu⟩ := this
  have hval : ∀ x : Fin n → Bool, val gates x (out w) = (x v || x u) := by
    intro x
    rw [hev w x, hSu]
    simp
  have hvv : val gates (eof v) (out w) = true := by rw [hval]; simp [eof]
  have huu : val gates (eof u) (out w) = true := by rw [hval]; simp [eof]
  have hn : n ≤ out w := by
    by_contra hlt
    push_neg at hlt
    rw [val_inp _ _ _ hlt] at hvv huu
    have e1 := eof_true3 hvv
    have e2 := eof_true3 huu
    exact huv (e2.symm.trans e1)
  have hL : out w - n < gates.length := by
    by_contra hge
    rw [val_ge _ _ _ (by omega)] at hvv
    exact absurd hvv (by simp)
  refine ⟨u, huv, by rw [hSu]; simp, hn, ?_, hval⟩
  simp only [DC, Finset.mem_filter, Finset.mem_range]
  refine ⟨hL, Or.inl ⟨u, by have := u.2; omega, fun x hx => ?_⟩⟩
  rw [show n + (out w - n) = out w by omega, hval, hx, val_inp _ _ _ u.2]
  simp

include hS hg hev in
/-- R0, counting part: if at most one set through `v` has size `≥ 3`, at least `deg v` gates
are dead on `{x v = false}`. -/
theorem DC_lower (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (v : Fin n)
    (hbig : (Finset.univ.filter fun w : Fin m => v ∈ S w ∧ 3 ≤ (S w).card).card ≤ 1) :
    (Finset.univ.filter fun w : Fin m => v ∈ S w).card ≤ (DC v gates).card := by
  classical
  set P := Finset.univ.filter fun w : Fin m => v ∈ S w ∧ (S w).card = 2 with hP
  set Bg := Finset.univ.filter fun w : Fin m => v ∈ S w ∧ 3 ≤ (S w).card with hBg
  have hmemP : ∀ w, w ∈ P ↔ v ∈ S w ∧ (S w).card = 2 := by intro w; simp [hP]
  have hmemB : ∀ w, w ∈ Bg ↔ v ∈ S w ∧ 3 ≤ (S w).card := by intro w; simp [hBg]
  have hsplit : (Finset.univ.filter fun w : Fin m => v ∈ S w) ⊆ P ∪ Bg := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.mem_union, hmemP, hmemB]
    have := h2 w
    by_cases h : (S w).card = 2
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, by omega⟩
  have hcard1 := (Finset.card_le_card hsplit).trans (Finset.card_union_le P Bg)
  set kk : Fin m → ℕ := fun w => out w - n with hkk
  have hinj : Set.InjOn kk (P : Set (Fin m)) := by
    intro w hw w' hw' he
    rw [Finset.mem_coe, hmemP] at hw hw'
    obtain ⟨u, huv, hu, hn, -, hval⟩ := pair_out S gates out hev v w hw.1 hw.2
    obtain ⟨u', huv', hu', hn', -, hval'⟩ := pair_out S gates out hev v w' hw'.1 hw'.2
    have ho : out w = out w' := by simp only [hkk] at he; omega
    have h1 := hval (eof u)
    rw [ho, hval'] at h1
    have h3 : eof u u' = true := by simpa [eof, huv.symm] using h1
    have h4 := eof_true3 h3
    subst h4
    by_contra hne
    have := hS w w' hne
    have h5 : 1 < (S w ∩ S w').card :=
      Finset.one_lt_card.mpr ⟨v, by simp [hw.1, hw'.1], u', by simp [hu, hu'], huv.symm⟩
    omega
  have himg : P.image kk ⊆ DC v gates := by
    intro k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
    rw [hmemP] at hw
    obtain ⟨u, -, -, -, hd, -⟩ := pair_out S gates out hev v w hw.1 hw.2
    exact hd
  have hcardP : P.card = (P.image kk).card := (Finset.card_image_of_injOn hinj).symm
  by_cases hB0 : Bg.card = 0
  · have := Finset.card_le_card himg
    omega
  have hB1 : Bg.card = 1 := by omega
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (by omega : 0 < Bg.card)
  rw [hmemB] at hw0
  suffices hss : P.image kk ⊂ DC v gates by
    have := Finset.card_lt_card hss
    omega
  refine Finset.ssubset_iff_subset_ne.mpr ⟨himg, fun heq => ?_⟩
  -- every dead gate is a pair output: toggle argument
  set x1 : Fin n → Bool := fun i => decide (i ≠ v ∧ ∃ w ∈ P, i ∈ S w) with hx1
  set x2 : Fin n → Bool := Function.update x1 v true with hx2
  have hfin : ∀ i, i ≠ (v : ℕ) → val gates x1 i = val gates x2 i := by
    refine val_congr_of_insens v gates x1 x2
      (fun _ hj => by rw [hx2, Function.update_of_ne (Fin.ne_of_val_ne hj)]) fun k hk => ?_
    by_cases hd : k ∈ DC v gates
    · rw [← heq] at hd
      obtain ⟨w, hw, hwk⟩ := Finset.mem_image.mp hd
      obtain ⟨u, huv, hu, hn, -, hval⟩ := pair_out S gates out hev v w ((hmemP w).mp hw).1
        ((hmemP w).mp hw).2
      have ho : out w = n + k := by simp only [hkk] at hwk; omega
      have h1u : x1 u = true := by
        simp only [hx1, decide_eq_true_eq]
        exact ⟨huv, w, hw, hu⟩
      left
      rw [← ho, hval, hval, hx2, Function.update_of_ne huv, h1u]
      simp
    · exact Or.inr (insens_of_notDead v gates k hk (hg _ (List.getElem_mem hk)) fun hdd =>
        hd (by simp only [DC, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hdd⟩))
  have hov := ne_inp_of_orOn v gates (out w0) (S w0) (h2 w0) fun x _ => hev w0 x
  have hA := hev w0 x1
  have hB := hev w0 x2
  rw [hfin _ hov, hB] at hA
  have hT : decide (∃ u ∈ S w0, x2 u = true) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨v, hw0.1, by simp [hx2]⟩
  have hF : decide (∃ u ∈ S w0, x1 u = true) = false := by
    simp only [decide_eq_false_iff_not]
    rintro ⟨t, ht, hxt⟩
    simp only [hx1, decide_eq_true_eq] at hxt
    obtain ⟨htv, w, hw, htw⟩ := hxt
    rw [hmemP] at hw
    have hne : w ≠ w0 := by
      rintro rfl
      omega
    have := hS w w0 hne
    have h5 : 1 < (S w ∩ S w0).card :=
      Finset.one_lt_card.mpr ⟨v, by simp [hw.1, hw0.1], t, by simp [ht, htw], htv.symm⟩
    omega
  rw [hT, hF] at hA
  exact absurd hA (by simp)

end

end PEqualNP.Outside.L_meta_951_aux
