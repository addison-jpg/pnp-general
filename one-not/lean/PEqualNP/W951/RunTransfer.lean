import PEqualNP.W951.MergeRunT

/-! RunTransfer: the union-find run of a circuit with its constant and copy gates removed.

Coord 11:59 (the restricted-circuit link of cTAHG's PureHeredity note): a restricted circuit deletes
the gates that are constant, or copies of an earlier wire, on a subcube, and keeps the others with
their values. This file proves, for the run of `MergeRunT.lean` at any zero point `z` and test points
`p u` (`u ∈ R`), that such a deletion changes nothing but the wire numbers:

* `not_mgT_of_constOrCopy`: a gate that is constant, or a copy of an earlier wire, at the run's
  points never merges. Constant `false`: its trace is empty. Constant `true`: it is `1` at `z`.
  Copy of wire `j`: same trace as `j`, and after the run reaches it the elements of that trace
  already share one label (`runLT_inv`).
* `mgT_iff_keep`, `mstepT_keep`: a kept gate whose values agree with the original gate at the run's
  points makes the same step.
* `run_transfer`: for a kept-gate map `e` (strictly increasing, kept gate `t` of `gs'` stands for
  gate `e t` of `gs`, values equal at the run's points) and every other gate of `gs` constant or a
  copy there: the final labellings are equal and the merge set of `gs` is the merge set of `gs'`
  with wire `n + t` renamed `n + e t`.

The points are given by a predicate `P` that holds at `z` and at every `p u`; for a restriction
`P` is the subcube. Nothing here mentions a restriction or a lift. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section RunTransfer

variable {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))

/-- **No merge at constants or copies.** -/
theorem not_mgT_of_constOrCopy (gs : List Gate) (P : (Fin n → Bool) → Prop)
    (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (hz : P z) (hp : ∀ u ∈ R, P (p u)) (k : ℕ)
    (hk : (∃ c, ∀ x, P x → val gs x (n + k) = c) ∨
      (∃ j < n + k, ∀ x, P x → val gs x (n + k) = val gs x j)) :
    ¬ MgT z p R gs (runLT z p R gs k) k := by
  rintro ⟨hzk, hcard⟩
  rcases hk with ⟨c, hc⟩ | ⟨j, hj, hcp⟩
  · cases c
    · have he : trRT p R gs (n + k) = ∅ := by
        rw [trRT, Finset.filter_eq_empty_iff]
        intro u hu h
        rw [hc _ (hp u hu)] at h
        exact absurd h (by simp)
      rw [he] at hcard
      simp at hcard
    · rw [hc _ hz] at hzk
      exact absurd hzk (by simp)
  · have hinv := runLT_inv z p R gs hT k
    have hzj : val gs z j = false := by rw [← hcp _ hz]; exact hzk
    have hle : ((trRT p R gs (n + k)).image (runLT z p R gs k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      rw [trRT, Finset.mem_filter] at hu hv
      exact hinv j hj hzj u hu.1 v hv.1 (by rw [← hcp _ (hp u hu.1)]; exact hu.2)
        (by rw [← hcp _ (hp v hv.1)]; exact hv.2)
    omega

theorem mgT_iff_keep (gs gs' : List Gate) (l : Fin n → Fin n) (k t : ℕ)
    (h0 : val gs z (n + k) = val gs' z (n + t))
    (h1 : trRT p R gs (n + k) = trRT p R gs' (n + t)) :
    MgT z p R gs l k ↔ MgT z p R gs' l t := by
  unfold MgT
  rw [h0, h1]

theorem mstepT_keep (gs gs' : List Gate) (l : Fin n → Fin n) (k t : ℕ)
    (h0 : val gs z (n + k) = val gs' z (n + t))
    (h1 : trRT p R gs (n + k) = trRT p R gs' (n + t)) :
    mstepT z p R gs l k = mstepT z p R gs' l t := by
  unfold mstepT MgT
  simp only [h0, h1]

/-- **Run transfer.** Deleting gates that are constants or copies at the run's points, and keeping
the others with their values, keeps the final labelling and renames the merge set. -/
theorem run_transfer (gs gs' : List Gate) (e : ℕ → ℕ) (P : (Fin n → Bool) → Prop)
    (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (hz : P z) (hp : ∀ u ∈ R, P (p u))
    (he : ∀ t t', t < t' → t' < gs'.length → e t < e t')
    (hlt : ∀ t < gs'.length, e t < gs.length)
    (hkeep : ∀ t < gs'.length, ∀ x, P x → val gs' x (n + t) = val gs x (n + e t))
    (hdead : ∀ k < gs.length, (∀ t < gs'.length, e t ≠ k) →
      (∃ c, ∀ x, P x → val gs x (n + k) = c) ∨
        (∃ j < n + k, ∀ x, P x → val gs x (n + k) = val gs x j)) :
    runLT z p R gs gs.length = runLT z p R gs' gs'.length ∧
      runMT z p R gs gs.length = (runMT z p R gs' gs'.length).image (fun i => n + e (i - n)) := by
  have key : ∀ k ≤ gs.length, ∃ t ≤ gs'.length, (∀ t' < t, e t' < k) ∧
      (∀ t', t ≤ t' → t' < gs'.length → k ≤ e t') ∧
      runLT z p R gs k = runLT z p R gs' t ∧
      runMT z p R gs k = (runMT z p R gs' t).image (fun i => n + e (i - n)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨0, Nat.zero_le _, fun t' h => absurd h (Nat.not_lt_zero _),
        fun t' _ _ => Nat.zero_le _, rfl, by simp [runMT]⟩
    | succ k ih =>
      intro hk
      obtain ⟨t, ht, hbefore, hafter, hL, hM⟩ := ih (by omega)
      by_cases hkept : t < gs'.length ∧ e t = k
      · obtain ⟨htl, het⟩ := hkept
        have h0 : val gs z (n + k) = val gs' z (n + t) := by
          rw [hkeep t htl z hz, het]
        have h1 : trRT p R gs (n + k) = trRT p R gs' (n + t) := by
          unfold trRT
          exact Finset.filter_congr fun u hu => by rw [hkeep t htl _ (hp u hu), het]
        refine ⟨t + 1, htl, fun t' h => ?_, fun t' h h' => ?_, ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
          · exact Nat.lt_succ_of_lt (hbefore t' h)
          · omega
        · have := he t t' (by omega) h'
          omega
        · rw [runLT_succ, runLT_succ, hL]
          exact mstepT_keep z p R gs gs' _ k t h0 h1
        · have hmg := mgT_iff_keep z p R gs gs' (runLT z p R gs' t) k t h0 h1
          simp only [runMT]
          rw [hL, hM]
          by_cases hm : MgT z p R gs' (runLT z p R gs' t) t
          · rw [ite_eq_left (hmg.mpr hm), ite_eq_left hm, Finset.image_insert, Nat.add_sub_cancel_left, het]
          · rw [ite_eq_right (fun h => hm (hmg.mp h)), ite_eq_right hm]
      · have hdk : ∀ t' < gs'.length, e t' ≠ k := by
          intro t' ht' h
          by_cases h1 : t' < t
          · have := hbefore t' h1
            omega
          · rcases Nat.lt_or_ge t t' with h3 | h3
            · have := he t t' h3 ht'
              have := hafter t le_rfl (by omega)
              omega
            · have : t' = t := by omega
              subst this
              exact hkept ⟨ht', h⟩
        have hno := not_mgT_of_constOrCopy z p R gs P hT hz hp k (hdead k (by omega) hdk)
        refine ⟨t, ht, fun t' h => by have := hbefore t' h; omega, fun t' h h' => ?_, ?_, ?_⟩
        · have := hafter t' h h'
          have := hdk t' h'
          omega
        · rw [runLT_succ, mstepT_nomerge z p R gs hno, hL]
        · simp only [runMT]
          rw [ite_eq_right hno]
          exact hM
  obtain ⟨t, ht, -, hafter, hL, hM⟩ := key gs.length le_rfl
  have htt : t = gs'.length := by
    by_contra h
    have := hafter t le_rfl (by omega)
    have := hlt t (by omega)
    omega
  subst htt
  exact ⟨hL, hM⟩

end RunTransfer

end PEqualNP.Outside.L_meta_951_aux
