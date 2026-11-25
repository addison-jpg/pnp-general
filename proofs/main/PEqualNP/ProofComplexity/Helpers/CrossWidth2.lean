import PEqualNP.ProofComplexity.Helpers.CrossGeneral

/-!
# The `a × b` cross formula has a Res(2, ⊕) refutation of polynomial length

In fact every term of the refutation is a single equation, so this is an ordinary resolution
refutation (it works for every `k ≥ 1`): for each `j`, cut `x_0 ∨ … ∨ x_{a-1}` successively
against `¬x_i ∨ ¬y_j` to get `¬y_j`, then cut `y_0 ∨ … ∨ y_{b-1}` against all `¬y_j`.
-/

namespace PEqualNP.ProofComplexity.CrossWidth2

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.CrossGeneral

variable {a b : ℕ}

/-- `x_i = 1` for `i ≥ n`. -/
def Xr (a b n : ℕ) : LinKLine (Var a b) :=
  (Finset.univ.filter (fun i : Fin a => n ≤ i.val)).image
    (fun i => ({ev (Sum.inl i : Var a b) true} : LinTerm (Var a b)))

/-- `y_j = 0 ∨ x_i = 1 (i ≥ n)`. -/
def Rl (j : Fin b) (n : ℕ) : LinKLine (Var a b) :=
  insert ({ev (Sum.inr j : Var a b) false} : LinTerm (Var a b)) (Xr a b n)

def Wl (j : Fin b) : LinKLine (Var a b) := {{ev (Sum.inr j : Var a b) false}}

/-- `y_j = 1` for `j ≥ m`. -/
def Sl (a b m : ℕ) : LinKLine (Var a b) :=
  (Finset.univ.filter (fun j : Fin b => m ≤ j.val)).image
    (fun j => ({ev (Sum.inr j : Var a b) true} : LinTerm (Var a b)))

theorem cut_single {V : Type} [DecidableEq V] (C D : LinKLine V) (e : LinEq V)
    (hC : ({e} : LinTerm V) ∈ C) (hD : ({negLinEq e} : LinTerm V) ∈ D) :
    IsLinKCut C D (C.erase {e} ∪ D.erase {negLinEq e}) := by
  refine ⟨{e}, hC, ?_, ?_⟩
  · intro e' he'
    rw [Finset.mem_singleton] at he'
    subst he'; exact hD
  · simp [Finset.sdiff_singleton_eq_erase]

theorem Xr_zero : (Xr a b 0) = linKOfClause (Xc a b) := by
  ext T
  simp [Xr, linKOfClause, linOfClause, Xc, Finset.image_image, ev]

theorem Sl_zero : (Sl a b 0) = linKOfClause (Yc a b) := by
  ext T
  simp [Sl, linKOfClause, linOfClause, Yc, Finset.image_image, ev]

theorem Xr_full : (Xr a b a) = ∅ := by
  rw [Xr, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro i _; have := i.2; omega

theorem Sl_full : (Sl a b b) = ∅ := by
  rw [Sl, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro i _; have := i.2; omega

theorem Xr_erase (n : ℕ) (hn : n < a) :
    (Xr a b n).erase {ev (Sum.inl ⟨n, hn⟩ : Var a b) true} = Xr a b (n + 1) := by
  ext T
  simp only [Xr, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hne, i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rcases Nat.eq_or_lt_of_le hi with h | h
    · exfalso; apply hne
      have : i = ⟨n, hn⟩ := Fin.ext h.symm
      rw [this]
    · omega
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, i, by omega, rfl⟩
    intro h
    have := Finset.singleton_inj.mp h
    simp [ev, Fin.ext_iff] at this
    omega

theorem Sl_erase (m : ℕ) (hm : m < b) :
    (Sl a b m).erase {ev (Sum.inr ⟨m, hm⟩ : Var a b) true} = Sl a b (m + 1) := by
  ext T
  simp only [Sl, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hne, i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rcases Nat.eq_or_lt_of_le hi with h | h
    · exfalso; apply hne
      have : i = ⟨m, hm⟩ := Fin.ext h.symm
      rw [this]
    · omega
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, i, by omega, rfl⟩
    intro h
    have := Finset.singleton_inj.mp h
    simp [ev, Fin.ext_iff] at this
    omega

theorem ne_yx (j : Fin b) (i : Fin a) :
    ({ev (Sum.inr j : Var a b) false} : LinTerm (Var a b)) ≠ {ev (Sum.inl i : Var a b) true} := by
  intro h
  have := Finset.singleton_inj.mp h
  simp [ev] at this

theorem mem_Xr (n : ℕ) (i : Fin a) (h : n ≤ i.val) :
    ({ev (Sum.inl i : Var a b) true} : LinTerm (Var a b)) ∈ Xr a b n := by
  simp only [Xr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, h, rfl⟩

theorem mem_Sl (m : ℕ) (j : Fin b) (h : m ≤ j.val) :
    ({ev (Sum.inr j : Var a b) true} : LinTerm (Var a b)) ∈ Sl a b m := by
  simp only [Sl, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, h, rfl⟩

theorem step0 (ha : 0 < a) (j : Fin b) :
    IsLinKCut (Xr a b 0) (linKOfClause (Nc ⟨0, ha⟩ j)) (Rl j 1) := by
  have h := cut_single (Xr a b 0) (linKOfClause (Nc ⟨0, ha⟩ j))
    (ev (Sum.inl ⟨0, ha⟩ : Var a b) true)
    (mem_Xr 0 ⟨0, ha⟩ (Nat.zero_le _))
    (by rw [NL_eq]; exact Finset.mem_insert_self _ _)
  have hneg : negLinEq (ev (Sum.inl ⟨0, ha⟩ : Var a b) true) =
      ev (Sum.inl ⟨0, ha⟩ : Var a b) false := rfl
  rw [hneg, Xr_erase 0 ha, NL_eq,
    Finset.erase_insert (by rw [Finset.mem_singleton]; exact ne_lr _ _)] at h
  have e : Xr a b (0 + 1) ∪ {{ev (Sum.inr j : Var a b) false}} = Rl j 1 := by
    ext T
    simp only [Rl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rwa [e] at h

theorem step (n : ℕ) (hn : n < a) (j : Fin b) :
    IsLinKCut (Rl j n) (linKOfClause (Nc ⟨n, hn⟩ j)) (Rl j (n + 1)) := by
  have h := cut_single (Rl j n) (linKOfClause (Nc ⟨n, hn⟩ j))
    (ev (Sum.inl ⟨n, hn⟩ : Var a b) true)
    (Finset.mem_insert_of_mem (mem_Xr n ⟨n, hn⟩ le_rfl))
    (by rw [NL_eq]; exact Finset.mem_insert_self _ _)
  have hneg : negLinEq (ev (Sum.inl ⟨n, hn⟩ : Var a b) true) =
      ev (Sum.inl ⟨n, hn⟩ : Var a b) false := rfl
  rw [hneg, Rl, Finset.erase_insert_of_ne (ne_yx _ _), Xr_erase n hn, NL_eq,
    Finset.erase_insert (by rw [Finset.mem_singleton]; exact ne_lr _ _)] at h
  have e : insert ({ev (Sum.inr j : Var a b) false} : LinTerm (Var a b)) (Xr a b (n + 1)) ∪
      {{ev (Sum.inr j : Var a b) false}} = Rl j (n + 1) := by
    ext T
    simp only [Rl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rwa [e] at h

theorem stepS (m : ℕ) (hm : m < b) :
    IsLinKCut (Sl a b m) (Wl ⟨m, hm⟩) (Sl a b (m + 1)) := by
  have h := cut_single (Sl a b m) (Wl ⟨m, hm⟩) (ev (Sum.inr ⟨m, hm⟩ : Var a b) true)
    (mem_Sl m ⟨m, hm⟩ le_rfl) (Finset.mem_singleton_self _)
  have hneg : negLinEq (ev (Sum.inr ⟨m, hm⟩ : Var a b) true) =
      ev (Sum.inr ⟨m, hm⟩ : Var a b) false := rfl
  rw [hneg, Sl_erase m hm, Wl, Finset.erase_singleton, Finset.union_empty] at h
  exact h

theorem Rl_full (j : Fin b) : (Rl j a : LinKLine (Var a b)) = Wl j := by
  rw [Rl, Xr_full, Wl, Finset.insert_empty]

theorem card_Xr (n : ℕ) : ∀ T ∈ (Xr a b n), T.card ≤ 2 := by
  intro T hT
  simp only [Xr, Finset.mem_image] at hT
  obtain ⟨i, _, rfl⟩ := hT
  simp

theorem card_Rl (j : Fin b) (n : ℕ) : ∀ T ∈ (Rl j n : LinKLine (Var a b)), T.card ≤ 2 := by
  intro T hT
  rcases Finset.mem_insert.mp hT with rfl | h
  · simp
  · exact card_Xr n T h

theorem card_Wl (j : Fin b) : ∀ T ∈ (Wl j : LinKLine (Var a b)), T.card ≤ 2 := by
  intro T hT
  rw [Wl, Finset.mem_singleton] at hT
  subst hT; simp

theorem card_Sl (m : ℕ) : ∀ T ∈ (Sl a b m), T.card ≤ 2 := by
  intro T hT
  simp only [Sl, Finset.mem_image] at hT
  obtain ⟨i, _, rfl⟩ := hT
  simp

/-- Derivations in `Res(2, ⊕)` from the cross formula. -/
abbrev Der2 (a b : ℕ) (π : List (LinKLine (Var a b))) : Prop :=
  IsLinKDerivation 2 IsLinKWeakening ((fun C => linKOfClause C) '' crossF a b) π

theorem der_of_axioms2 : ∀ L : List (LinKLine (Var a b)),
    (∀ C ∈ L, ∃ D, D ∈ crossF a b ∧ linKOfClause D = C) → Der2 a b L := by
  intro L
  induction L with
  | nil => intro _; exact IsLinKDerivation.nil
  | cons C L ih =>
    intro h
    refine IsLinKDerivation.ax (ih fun D hD => h D (List.mem_cons_of_mem _ hD))
      (h C List.mem_cons_self) ?_
    obtain ⟨D, _, rfl⟩ := h C List.mem_cons_self
    intro T hT
    rw [card_one hT]; omega

theorem chain1 (ha : 0 < a) (j : Fin b) : ∀ n, 1 ≤ n → n ≤ a → ∀ π : List (LinKLine (Var a b)),
    Der2 a b π → linKOfClause (Xc a b) ∈ π → (∀ i, linKOfClause (Nc i j) ∈ π) →
    ∃ π', Der2 a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ Rl j n ∈ π' ∧ π'.length ≤ π.length + n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _ π hπ hX hN
    refine ⟨Rl j 1 :: π, ?_, fun C hC => List.mem_cons_of_mem _ hC, List.mem_cons_self, by simp⟩
    exact IsLinKDerivation.cut hπ (C := Xr a b 0) (by rw [Xr_zero]; exact hX) (hN ⟨0, ha⟩)
      (step0 ha j) (card_Rl j 1)
  | succ n hn ih =>
    intro hna π hπ hX hN
    obtain ⟨π', h1, h2, h3, h4⟩ := ih (by omega) π hπ hX hN
    refine ⟨Rl j (n + 1) :: π', ?_, fun C hC => List.mem_cons_of_mem _ (h2 C hC),
      List.mem_cons_self, ?_⟩
    · exact IsLinKDerivation.cut h1 h3 (h2 _ (hN ⟨n, by omega⟩)) (step n (by omega) j)
        (card_Rl j _)
    · simp; omega

theorem rowsW (ha : 0 < a) : ∀ m, m ≤ b → ∀ π : List (LinKLine (Var a b)), Der2 a b π →
    linKOfClause (Xc a b) ∈ π → (∀ i j, linKOfClause (Nc i j) ∈ π) →
    ∃ π', Der2 a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ (∀ j : Fin b, j.val < m → Wl j ∈ π') ∧
      π'.length ≤ π.length + m * a := by
  intro m
  induction m with
  | zero =>
    intro _ π hπ _ _
    exact ⟨π, hπ, fun _ h => h, fun j hj => by omega, by simp⟩
  | succ m ih =>
    intro hm π hπ hX hN
    obtain ⟨π1, h1, h2, h3, h4⟩ := ih (by omega) π hπ hX hN
    obtain ⟨π2, g1, g2, g3, g4⟩ := chain1 ha ⟨m, by omega⟩ a ha le_rfl π1 h1 (h2 _ hX)
      (fun i => h2 _ (hN i _))
    refine ⟨π2, g1, fun C hC => g2 C (h2 C hC), ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact g2 _ (h3 j h)
      · have : j = ⟨m, by omega⟩ := Fin.ext h
        rw [this, ← Rl_full]; exact g3
    · have : (m + 1) * a = m * a + a := by rw [Nat.add_mul, Nat.one_mul]
      omega

theorem cutsS : ∀ m, m ≤ b → ∀ π : List (LinKLine (Var a b)), Der2 a b π →
    Sl a b 0 ∈ π → (∀ j : Fin b, Wl j ∈ π) →
    ∃ π', Der2 a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ Sl a b m ∈ π' ∧ π'.length ≤ π.length + m := by
  intro m
  induction m with
  | zero =>
    intro _ π hπ hS _
    exact ⟨π, hπ, fun _ h => h, hS, by simp⟩
  | succ m ih =>
    intro hm π hπ hS hW
    obtain ⟨π1, h1, h2, h3, h4⟩ := ih (by omega) π hπ hS hW
    refine ⟨Sl a b (m + 1) :: π1, ?_, fun C hC => List.mem_cons_of_mem _ (h2 C hC),
      List.mem_cons_self, ?_⟩
    · exact IsLinKDerivation.cut h1 h3 (h2 _ (hW ⟨m, by omega⟩)) (stepS m (by omega))
        (card_Sl _)
    · simp; omega

/-- **Main theorem.** For `a, b ≥ 1` the cross formula has a Res(2, ⊕) refutation (all of whose
terms are single equations) with at most `2ab + b + 2` lines. -/
theorem cross_refutation2 (ha : 0 < a) (hb : 0 < b) :
    ∃ π : List (LinKLine (Var a b)), IsLinKRefutation 2 (crossF a b) π ∧
      π.length ≤ 2 * a * b + b + 2 := by
  have h0 : Der2 a b (axList a b) := by
    apply der_of_axioms2
    intro C hC
    simp only [axList, List.mem_cons, List.mem_flatMap, List.mem_map] at hC
    rcases hC with rfl | rfl | ⟨i, _, j, _, rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨i, j, rfl⟩), rfl⟩
  have hXm : linKOfClause (Xc a b) ∈ axList a b := by simp [axList]
  have hYm : linKOfClause (Yc a b) ∈ axList a b := by simp [axList]
  have hNm : ∀ i j, linKOfClause (Nc i j) ∈ axList a b := by
    intro i j
    simp only [axList, List.mem_cons, List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inr ⟨i, List.mem_finRange _, j, List.mem_finRange _, rfl⟩)
  obtain ⟨π1, h1, h2, h3, h4⟩ := rowsW ha b le_rfl _ h0 hXm hNm
  obtain ⟨π2, g1, g2, g3, g4⟩ := cutsS b le_rfl π1 h1 (by rw [Sl_zero]; exact h2 _ hYm)
    (fun j => h3 j j.2)
  rw [Sl_full] at g3
  refine ⟨π2, ⟨g1, g3⟩, ?_⟩
  have hl := axList_length (a := a) (b := b)
  have e1 : b * a = a * b := Nat.mul_comm b a
  have e2 : 2 * a * b = 2 * (a * b) := Nat.mul_assoc 2 a b
  omega

end PEqualNP.ProofComplexity.CrossWidth2
