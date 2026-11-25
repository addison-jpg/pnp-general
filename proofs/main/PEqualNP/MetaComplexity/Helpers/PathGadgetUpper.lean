import PEqualNP.Outside.L_meta_572

/-!
# The path-gadget upper bound of L-meta-572 without side conditions

Row L-meta-572 assumes `u ≠ v`, `3 ≤ h`, `g` false at the all-false input and two witnesses; its
proof uses none of them. This is the same statement for every `N`, `h`, `u`, `v`, `g`: a circuit
for `g` (or for `g` with the two-wire gadget) gives one for `g` OR the path gadget of length
`2 h + 1` with `3 h + 3` (respectively `3 h`) more gates.
-/

open PEqualNP.Outside.L_meta_572_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.MetaComplexity.PathGadget.path_gadget_upper : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize N g s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s + 3)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g s
  have hul := u.isLt
  have hvl := v.isLt
  constructor
  · rintro ⟨D, hF, hsz, hD⟩
    refine ⟨extC N (N + (2 * h + 1)) id D (ts1 N h u.val v.val), extC_fanin _ _ _ _ _ hF, ?_, ?_⟩
    · rw [extC_size]
      have e : (ts1 N h u.val v.val).length = h + 1 := by simp [ts1]
      have : D.size ≤ s := hsz
      omega
    · intro x
      have hσ : ∀ i, i < (List.ofFn (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))).length →
          id i < (List.ofFn x).length ∧
            (List.ofFn (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))).getD i false
              = (List.ofFn x).getD (id i) false := by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        refine ⟨by simp only [id]; omega, ?_⟩
        rw [getD_ofFn _ i hi, id, getD_ofFn x i (by omega)]
        rfl
      have hts : ∀ τ ∈ ts1 N h u.val v.val, τ.1 < (List.ofFn x).length ∧
          τ.2.1 < (List.ofFn x).length ∧ τ.2.2 < (List.ofFn x).length := by
        intro τ hτ
        simp only [ts1, List.mem_map, List.mem_range] at hτ
        obtain ⟨k, hk, rfl⟩ := hτ
        simp only [List.length_ofFn]
        refine ⟨by omega, ?_, ?_⟩ <;> split_ifs <;> omega
      have key := extC_eval D _ _ id _ hσ hts
      simp only [List.length_ofFn] at key
      apply Bool.eq_iff_iff.mpr
      rw [key, hD]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact or_congr Iff.rfl
        ((comb1 N h (fun i => (List.ofFn x).getD i false) u.val v.val).trans
          (fin_conv N (2 * h + 1) x u v).symm)
  · rintro ⟨D, hF, hsz, hD⟩
    refine ⟨extC (N + 2) (N + (2 * h + 1)) (fun i => if i ≤ N then i else N + 2 * h) D (ts2 N h),
      extC_fanin _ _ _ _ _ hF, ?_, ?_⟩
    · rw [extC_size]
      have e : (ts2 N h).length = h := by simp [ts2]
      have : D.size ≤ s := hsz
      omega
    · intro x
      obtain ⟨x', hx'⟩ : ∃ x' : Fin (N + 2) → Bool, ∀ i : Fin (N + 2),
          x' i = (List.ofFn x).getD (if i.val ≤ N then i.val else N + 2 * h) false :=
        ⟨_, fun _ => rfl⟩
      have hσ : ∀ i, i < (List.ofFn x').length →
          (fun i => if i ≤ N then i else N + 2 * h) i < (List.ofFn x).length ∧
            (List.ofFn x').getD i false
              = (List.ofFn x).getD ((fun i => if i ≤ N then i else N + 2 * h) i) false := by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        refine ⟨by split_ifs <;> omega, ?_⟩
        rw [getD_ofFn x' i hi, hx']
      have hts : ∀ τ ∈ ts2 N h, τ.1 < (List.ofFn x).length ∧
          τ.2.1 < (List.ofFn x).length ∧ τ.2.2 < (List.ofFn x).length := by
        intro τ hτ
        simp only [ts2, List.mem_map, List.mem_range] at hτ
        obtain ⟨k, hk, rfl⟩ := hτ
        simp only [List.length_ofFn]
        exact ⟨by omega, by omega, by omega⟩
      have key := extC_eval D _ _ (fun i => if i ≤ N then i else N + 2 * h) _ hσ hts
      simp only [List.length_ofFn] at key
      have hDx := hD x'
      beta_reduce at hDx
      have e1 : (fun i : Fin N => x' (Fin.castAdd 2 i))
          = fun i : Fin N => x (Fin.castAdd (2 * h + 1) i) := by
        funext i
        have := i.isLt
        rw [hx', if_pos (by simp), getD_ofFn x _ (by simp; omega)]
        rfl
      have e2 : ∀ q : Fin N, x' (Fin.castAdd 2 q) = (List.ofFn x).getD q.val false := by
        intro q
        have := q.isLt
        rw [hx', if_pos (by simp)]
        rfl
      have e4 : x' (Fin.natAdd N (0 : Fin 2)) = (List.ofFn x).getD N false := by
        rw [hx', if_pos (by simp)]
        simp
      have e5 : x' (Fin.natAdd N (1 : Fin 2)) = (List.ofFn x).getD (N + 2 * h) false := by
        rw [hx', if_neg (by simp)]
      rw [e1, e2 u, e2 v, e4, e5] at hDx
      apply Bool.eq_iff_iff.mpr
      rw [key, hDx]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      have E := (comb2 N h (fun i => (List.ofFn x).getD i false) u.val v.val).trans
        (fin_conv N (2 * h + 1) x u v).symm
      constructor
      · rintro (((hg | h1) | h2) | h3)
        · exact Or.inl hg
        · exact Or.inr (E.mp (Or.inl h1))
        · exact Or.inr (E.mp (Or.inr (Or.inl h2)))
        · exact Or.inr (E.mp (Or.inr (Or.inr h3)))
      · rintro (hg | hE)
        · exact Or.inl (Or.inl (Or.inl hg))
        · rcases E.mpr hE with h1 | h2 | h3
          · exact Or.inl (Or.inl (Or.inr h1))
          · exact Or.inl (Or.inr h2)
          · exact Or.inr h3
