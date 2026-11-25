import PEqualNP.General.XorExtension

/-!
# Fixing an input saves a gate, on either side; the cost of a negated fresh input

* `restrict_one`: if `F` depends on its last input and is not constant once that input is set
  to `c`, then setting it to `c` saves one gate. (`L_meta_174.gate_elim` is the case `c = true`.)
* `neg_and_lower`, `neg_and_upper`: for a non-constant `f` and a fresh input `x`,
  `C f + 1 ≤ C(¬x ∧ f) ≤ C f + 2`, every gate counted.
-/

namespace PEqualNP.General.XorExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_174

/-- **One gate, either side.** -/
theorem restrict_one (n s : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (c : Bool)
    (hdep : ∃ y : Fin n → Bool, F (Fin.snoc y false) ≠ F (Fin.snoc y true))
    (hnc : ∃ y y' : Fin n → Bool, F (Fin.snoc y c) ≠ F (Fin.snoc y' c))
    (h : HasCircuitSize (n + 1) F (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => F (Fin.snoc y c)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz1 : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hlen : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hv : ∀ (c : Bool) (y : Fin n → Bool), val n gs c C.output y = F (Fin.snoc y c) := by
    intro c y
    unfold val
    rw [← ofFn_snoc, hgs, wiresFrom_norm, ← hev]; rfl
  have hnc' : ¬ K n gs c C.output := by
    rintro ⟨b, hb⟩
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hv c y, ← hv c y', hb y, hb y']
  have hrd : ∃ j, Rd n gs j := by
    by_contra hno
    obtain ⟨y, hy⟩ := hdep
    have hs : Split n gs C.output y := by
      show val n gs false C.output y ≠ val n gs true C.output y
      rw [hv, hv]; exact hy
    have hB := block n gs y (fun i => i = n) rfl
      (fun j hj _ _ i hr hBi _ => by
        rw [show i = n from hBi] at hr
        exact hno ⟨j, hj, hr⟩) C.output hs
    apply hnc'
    rw [show C.output = n from hB]
    exact Kx n gs c
  obtain ⟨j, hj⟩ := hrd
  obtain ⟨C', ok', hsz', hev'⟩ := se n c gs hnok C.output hnc' {j}
    (fun i hi => by rw [Finset.mem_singleton.1 hi]; exact rd_red n gs hnok j hj c)
  rw [Finset.card_singleton] at hsz'
  exact ⟨C', ok', by omega, fun y => by rw [hev' y, hv]⟩

/-- **Lower bound.** A circuit with `s + 1` gates for `¬x ∧ f` gives one with `s` gates for `f`. -/
theorem neg_and_lower (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => !x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
      (s + 1)) : HasCircuitSize n f s := by
  have hT : ∃ y : Fin n → Bool, f y = true := by
    obtain ⟨y, y', hne⟩ := hf
    cases hy : f y with
    | true => exact ⟨y, hy⟩
    | false =>
      cases hy' : f y' with
      | true => exact ⟨y', hy'⟩
      | false => exact absurd (hy.trans hy'.symm) hne
  have key := restrict_one n s _ false
    (by obtain ⟨y, hy⟩ := hT; exact ⟨y, by simp [hy]⟩)
    (by obtain ⟨y, y', hne⟩ := hf; exact ⟨y, y', by simpa using hne⟩) h
  simpa using key

lemma and_eval2 (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

/-- **Upper bound.** A circuit with `s` gates for `f` gives one with `s + 2` gates for
`¬x ∧ f`: one NOT gate and one AND gate. -/
theorem neg_and_upper (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => !x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
      (s + 2) := by
  obtain ⟨D, hok, hsz, hev⟩ := add_dummy n s f h
  have hsz1 : D.gates.length ≤ s := hsz
  have hWl : ∀ x : Fin (n + 1) → Bool,
      (wiresFrom D.gates (List.ofFn x)).length = n + 1 + D.gates.length := by
    intro x; simp [length_wiresFrom]
  have ho : ∀ x : Fin (n + 1) → Bool, (wiresFrom D.gates (List.ofFn x)).getD D.output false =
      f (fun i : Fin n => x i.castSucc) := hev
  by_cases hd : D.output < n + 1 + D.gates.length
  · refine ⟨⟨D.gates ++ [⟨GateOp.not, [n]⟩] ++
        [⟨GateOp.and, [n + 1 + D.gates.length, D.output]⟩], n + 1 + D.gates.length + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact hok g hg
        · have he : g = ⟨GateOp.not, [n]⟩ := List.mem_singleton.1 hg
          subst g
          simp
      · have he : g = ⟨GateOp.and, [n + 1 + D.gates.length, D.output]⟩ :=
          List.mem_singleton.1 hg
        subst g
        simp
    · simp only [Circuit.size, List.length_append, List.length_singleton]
      omega
    · intro x
      set W := wiresFrom D.gates (List.ofFn x) with hW
      have hWx : W.length = n + 1 + D.gates.length := hWl x
      have hn : W.getD n false = x (Fin.last n) := by
        rw [hW, getD_wiresFrom _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
        rfl
      set v := GateOp.not.eval ([n].map fun i => W.getD i false) with hv
      have hv' : v = !x (Fin.last n) := by
        rw [hv]; show (!W.getD n false) = _; rw [hn]
      have h1 : (W ++ [v]).getD (n + 1 + D.gates.length) false = !x (Fin.last n) := by
        rw [getD_snoc_len _ _ _ _ hWx, hv']
      have h2 : (W ++ [v]).getD D.output false = f (fun i : Fin n => x i.castSucc) := by
        rw [getD_snoc_ne _ _ _ _ (by rw [hWx]; omega)]; exact ho x
      show (wiresFrom (D.gates ++ [⟨GateOp.not, [n]⟩] ++
        [⟨GateOp.and, [n + 1 + D.gates.length, D.output]⟩]) (List.ofFn x)).getD
          (n + 1 + D.gates.length + 1) false = _
      rw [wiresFrom_snoc, wiresFrom_snoc, ← hW, ← hv]
      rw [getD_snoc_len _ _ _ _ (by simp [hWx])]
      show GateOp.and.eval [(W ++ [v]).getD (n + 1 + D.gates.length) false,
        (W ++ [v]).getD D.output false] = _
      rw [and_eval2, h1, h2]
  · -- the output wire of `D` does not exist: `f` is constantly `false`
    have hf0 : ∀ x : Fin (n + 1) → Bool, f (fun i : Fin n => x i.castSucc) = false := by
      intro x
      rw [← ho x, List.getD_eq_default _ _ (by rw [hWl x]; omega)]
    refine ⟨⟨[], n + 1⟩, by intro g hg; simp at hg, by simp [Circuit.size], fun x => ?_⟩
    show (List.ofFn x).getD (n + 1) false =
      (!x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
    rw [hf0 x, Bool.and_false]
    exact List.getD_eq_default _ _ (by simp)

end PEqualNP.General.XorExtension
