import PEqualNP.Defs.ProofComplexityLinK

/-!
# The `a × b` cross formula has a Res(b, ⊕) refutation with at most `2ab + 3` lines
-/

namespace PEqualNP.ProofComplexity.CrossGeneral

open PEqualNP.ProofComplexity

abbrev Var (a b : ℕ) : Type := Fin a ⊕ Fin b

variable {a b : ℕ}

def ev (v : Var a b) (s : Bool) : LinEq (Var a b) := ({v}, s)

def Xc (a b : ℕ) : Clause (Var a b) := Finset.univ.image (fun i : Fin a => (Sum.inl i, true))
def Yc (a b : ℕ) : Clause (Var a b) := Finset.univ.image (fun j : Fin b => (Sum.inr j, true))
def Nc (i : Fin a) (j : Fin b) : Clause (Var a b) := {(Sum.inl i, false), (Sum.inr j, false)}

/-- The cross formula. -/
def crossF (a b : ℕ) : Set (Clause (Var a b)) :=
  {C | C = Xc a b ∨ C = Yc a b ∨ ∃ i j, C = Nc i j}

/-- The term `y_j = 0` for all `j < m`. -/
def Y (m : ℕ) : LinTerm (Var a b) :=
  (Finset.univ.filter (fun j : Fin b => j.val < m)).image (fun j => ev (Sum.inr j) false)

theorem card_Y (m : ℕ) : (Y m : LinTerm (Var a b)).card ≤ b := by
  unfold Y
  calc _ ≤ _ := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = b := by simp

/-- the line `x_i = 0 ∨ (y_j = 0 for j < m)`. -/
def M (i : Fin a) (m : ℕ) : LinKLine (Var a b) := {{ev (Sum.inl i) false}, Y m}

/-- the line after cutting away the first `n` x's. -/
def Lx (n : ℕ) : LinKLine (Var a b) :=
  (Finset.univ.filter (fun i : Fin a => n ≤ i.val)).image (fun i => {ev (Sum.inl i) true}) ∪
    (if 0 < n then {Y b} else ∅)

theorem Lx_zero : (Lx 0 : LinKLine (Var a b)) = linKOfClause (Xc a b) := by
  ext T
  simp [Lx, linKOfClause, linOfClause, Xc, Finset.image_image, ev]

theorem Y_ne (i : Fin a) (m : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) :
    (Y m : LinTerm (Var a b)) ≠ {ev (Sum.inl i) false} := by
  intro h
  have : ev (Sum.inr ⟨0, hb⟩) false ∈ (Y m : LinTerm (Var a b)) := by
    simp [Y, ev]; omega
  rw [h] at this
  simp [ev] at this

theorem Y_succ (m : ℕ) (hm : m < b) :
    (Y (m + 1) : LinTerm (Var a b)) = Y m ∪ {ev (Sum.inr ⟨m, hm⟩) false} := by
  ext e
  simp only [Y, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : j.val < m
    · exact Or.inl ⟨j, h, rfl⟩
    · right; have : j = ⟨m, hm⟩ := Fin.ext (show j.val = m by omega)
      rw [this]
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨⟨m, hm⟩, by simp, rfl⟩

theorem NL_eq (i : Fin a) (j : Fin b) :
    linKOfClause (Nc i j) = {{ev (Sum.inl i) false}, {ev (Sum.inr j) false}} := by
  simp [linKOfClause, linOfClause, Nc, Finset.image_insert, ev]

theorem ne_lr (i : Fin a) (j : Fin b) :
    ({ev (Sum.inl i) false} : LinTerm (Var a b)) ≠ {ev (Sum.inr j) false} := by
  intro h
  have := Finset.singleton_inj.mp h
  simp [ev] at this

theorem and_step (i : Fin a) (m : ℕ) (hm : m < b) (h1 : 1 ≤ m) :
    IsLinKAndIntro (M i m : LinKLine (Var a b)) (linKOfClause (Nc i ⟨m, hm⟩))
      (M i (m + 1)) := by
  have hb : 1 ≤ b := by omega
  refine ⟨Y m, {ev (Sum.inr ⟨m, hm⟩) false}, ?_, ?_, ?_⟩
  · simp [M]
  · simp [NL_eq]
  · rw [NL_eq, M, M, Y_succ m hm]
    have e1 : ({{ev (Sum.inl i) false}, Y m} : LinKLine (Var a b)).erase (Y m)
        = {{ev (Sum.inl i) false}} := by
      rw [Finset.erase_insert_of_ne (Ne.symm (Y_ne i m h1 hb))]
      simp [Finset.erase_singleton]
    have e2 : ({{ev (Sum.inl i) false}, {ev (Sum.inr ⟨m, hm⟩) false}} : LinKLine (Var a b)).erase
        {ev (Sum.inr ⟨m, hm⟩) false} = {{ev (Sum.inl i) false}} := by
      rw [Finset.erase_insert_of_ne (Ne.symm (ne_lr i _).symm.symm |>.symm)]
      simp
    rw [e1, e2]
    ext T; simp

theorem Yb_ne (i : Fin a) (s : Bool) (hb : 1 ≤ b) :
    (Y b : LinTerm (Var a b)) ≠ {ev (Sum.inl i) s} := by
  intro h
  have : ev (Sum.inr ⟨0, hb⟩) false ∈ (Y b : LinTerm (Var a b)) := by
    simp [Y, ev]
  rw [h] at this
  simp [ev] at this

theorem cut_step (n : ℕ) (hn : n < a) (hb : 1 ≤ b) :
    IsLinKCut (Lx n : LinKLine (Var a b)) (M ⟨n, hn⟩ b) (Lx (n + 1)) := by
  refine ⟨{ev (Sum.inl ⟨n, hn⟩) true}, ?_, ?_, ?_⟩
  · simp only [Lx, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨⟨n, hn⟩, le_refl _, rfl⟩
  · intro e he
    simp at he
    subst he
    simp [M, negLinEq, ev]
  · have hY := Y_ne (a := a) ⟨n, hn⟩ b hb hb
    ext T
    simp [Lx, M, negLinEq, ev] at hY ⊢
    have hY2 := Yb_ne (a := a) ⟨n, hn⟩ true hb
    simp only [ev] at hY2
    by_cases hT : T = Y b
    · subst hT
      simp [hY, hY2]
    · by_cases h0 : 0 < n <;> simp [hT, h0]
      all_goals
        constructor
        · rintro ⟨k, hk, rfl⟩
          refine ⟨?_, k, by omega, rfl⟩
          intro h
          have := Finset.singleton_inj.mp h
          have h2 : k = ⟨n, hn⟩ := by simpa using this
          subst h2
          exact absurd hk (by simp)
        · rintro ⟨h1, k, hk, rfl⟩
          refine ⟨k, ?_, rfl⟩
          rcases Nat.eq_or_lt_of_le hk with h | h
          · exfalso; apply h1
            have : k = ⟨n, hn⟩ := Fin.ext h.symm
            rw [this]
          · omega

theorem Lx_last (ha : 0 < a) : (Lx a : LinKLine (Var a b)) = {Y b} := by
  ext T
  simp [Lx, ha]

theorem final_cut (ha : 0 < a) :
    IsLinKCut (Lx a : LinKLine (Var a b)) (linKOfClause (Yc a b)) ∅ := by
  refine ⟨Y b, ?_, ?_, ?_⟩
  · simp [Lx_last ha]
  · intro e he
    simp [Y] at he
    obtain ⟨j, rfl⟩ := he
    simp [linKOfClause, linOfClause, Yc, negLinEq, ev]
  · rw [Lx_last ha]
    ext T
    simp [linKOfClause, linOfClause, Yc, Y, negLinEq, ev, Finset.image_image]

/-- Derivations in `Res(b, ⊕)` from the cross formula. -/
abbrev Der (a b : ℕ) (π : List (LinKLine (Var a b))) : Prop :=
  IsLinKDerivation b IsLinKWeakening ((fun C => linKOfClause C) '' crossF a b) π

theorem card_one {C : Clause (Var a b)} {T : LinTerm (Var a b)} (h : T ∈ linKOfClause C) :
    T.card = 1 := by
  simp only [linKOfClause, linOfClause, Finset.mem_image] at h
  obtain ⟨q, ⟨l, _, rfl⟩, rfl⟩ := h
  simp

theorem wM (hb : 1 ≤ b) (i : Fin a) (m : ℕ) : ∀ T ∈ (M i m : LinKLine (Var a b)), T.card ≤ b := by
  intro T hT
  simp only [M, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · simpa using hb
  · exact card_Y m

theorem wLx (hb : 1 ≤ b) (n : ℕ) : ∀ T ∈ (Lx n : LinKLine (Var a b)), T.card ≤ b := by
  intro T hT
  simp only [Lx, Finset.mem_union, Finset.mem_image] at hT
  rcases hT with ⟨i, _, rfl⟩ | hT
  · simpa using hb
  · split_ifs at hT
    · simp at hT; subst hT; exact card_Y b
    · simp at hT

theorem M_one (hb : 1 ≤ b) (i : Fin a) :
    (M i 1 : LinKLine (Var a b)) = linKOfClause (Nc i ⟨0, hb⟩) := by
  rw [NL_eq, M]
  have : (Y 1 : LinTerm (Var a b)) = {ev (Sum.inr ⟨0, hb⟩) false} := by
    ext e
    simp [Y]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have : j = ⟨0, hb⟩ := Fin.ext hj
      rw [this]
    · rintro rfl; exact ⟨⟨0, hb⟩, rfl, rfl⟩
  rw [this]

theorem chain (hb : 1 ≤ b) (i : Fin a) : ∀ m, 1 ≤ m → m ≤ b → ∀ π : List (LinKLine (Var a b)),
    Der a b π → (∀ j, linKOfClause (Nc i j) ∈ π) →
    ∃ π', Der a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ M i m ∈ π' ∧ π'.length ≤ π.length + (m - 1) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _ π hπ hN
    exact ⟨π, hπ, fun _ h => h, by rw [M_one hb]; exact hN _, by simp⟩
  | succ m hm ih =>
    intro hmb π hπ hN
    obtain ⟨π', h1, h2, h3, h4⟩ := ih (by omega) π hπ hN
    refine ⟨M i (m + 1) :: π', ?_, fun C hC => List.mem_cons_of_mem _ (h2 C hC),
      List.mem_cons_self, ?_⟩
    · exact IsLinKDerivation.andIntro h1 h3 (h2 _ (hN ⟨m, by omega⟩)) (and_step i m (by omega) hm)
        (wM hb i _)
    · simp; omega

theorem rows (hb : 1 ≤ b) : ∀ n, n ≤ a → ∀ π : List (LinKLine (Var a b)), Der a b π →
    (∀ i j, linKOfClause (Nc i j) ∈ π) →
    ∃ π', Der a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ (∀ i : Fin a, i.val < n → M i b ∈ π') ∧
      π'.length ≤ π.length + n * (b - 1) := by
  intro n
  induction n with
  | zero =>
    intro _ π hπ _
    exact ⟨π, hπ, fun _ h => h, fun i hi => by omega, by simp⟩
  | succ n ih =>
    intro hn π hπ hN
    obtain ⟨π1, h1, h2, h3, h4⟩ := ih (by omega) π hπ hN
    obtain ⟨π2, g1, g2, g3, g4⟩ := chain hb ⟨n, by omega⟩ b hb le_rfl π1 h1
      (fun j => h2 _ (hN _ j))
    refine ⟨π2, g1, fun C hC => g2 C (h2 C hC), ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact g2 _ (h3 i h)
      · have : i = ⟨n, by omega⟩ := Fin.ext h
        rw [this]; exact g3
    · calc π2.length ≤ π1.length + (b - 1) := g4
        _ ≤ π.length + n * (b - 1) + (b - 1) := by omega
        _ = π.length + (n + 1) * (b - 1) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem cuts (hb : 1 ≤ b) : ∀ n, n ≤ a → ∀ π : List (LinKLine (Var a b)), Der a b π →
    linKOfClause (Xc a b) ∈ π → (∀ i : Fin a, M i b ∈ π) →
    ∃ π', Der a b π' ∧ (∀ C ∈ π, C ∈ π') ∧ Lx n ∈ π' ∧ π'.length ≤ π.length + n := by
  intro n
  induction n with
  | zero =>
    intro _ π hπ hX _
    exact ⟨π, hπ, fun _ h => h, by rw [Lx_zero]; exact hX, by simp⟩
  | succ n ih =>
    intro hn π hπ hX hM
    obtain ⟨π1, h1, h2, h3, h4⟩ := ih (by omega) π hπ hX hM
    refine ⟨Lx (n + 1) :: π1, ?_, fun C hC => List.mem_cons_of_mem _ (h2 C hC),
      List.mem_cons_self, ?_⟩
    · exact IsLinKDerivation.cut h1 h3 (h2 _ (hM ⟨n, by omega⟩)) (cut_step n (by omega) hb)
        (wLx hb _)
    · simp; omega

theorem der_of_axioms (hb : 1 ≤ b) : ∀ L : List (LinKLine (Var a b)),
    (∀ C ∈ L, ∃ D, D ∈ crossF a b ∧ linKOfClause D = C) → Der a b L := by
  intro L
  induction L with
  | nil => intro _; exact IsLinKDerivation.nil
  | cons C L ih =>
    intro h
    refine IsLinKDerivation.ax (ih fun D hD => h D (List.mem_cons_of_mem _ hD))
      (h C List.mem_cons_self) ?_
    obtain ⟨D, _, rfl⟩ := h C List.mem_cons_self
    intro T hT
    rw [card_one hT]; exact hb

/-- The axiom list: the two long clauses followed by the `a * b` binary clauses. -/
def axList (a b : ℕ) : List (LinKLine (Var a b)) :=
  linKOfClause (Xc a b) :: linKOfClause (Yc a b) ::
    (List.finRange a).flatMap (fun i => (List.finRange b).map (fun j => linKOfClause (Nc i j)))

theorem axList_length : (axList a b).length = 2 + a * b := by
  simp [axList, List.length_flatMap]
  omega

/-- **Main theorem.** For `a, b ≥ 1` the cross formula with the clauses `x_0 ∨ … ∨ x_{a-1}`,
`y_0 ∨ … ∨ y_{b-1}` and `¬x_i ∨ ¬y_j` has a Res(b, ⊕) refutation with at most `2ab + 3` lines. -/
theorem cross_refutation (ha : 0 < a) (hb : 0 < b) :
    ∃ π : List (LinKLine (Var a b)), IsLinKRefutation b (crossF a b) π ∧
      π.length ≤ 2 * a * b + 3 := by
  have hb1 : 1 ≤ b := hb
  have h0 : Der a b (axList a b) := by
    apply der_of_axioms hb1
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
  obtain ⟨π1, h1, h2, h3, h4⟩ := rows hb1 a le_rfl _ h0 hNm
  obtain ⟨π2, g1, g2, g3, g4⟩ := cuts hb1 a le_rfl π1 h1 (h2 _ hXm)
    (fun i => h3 i i.2)
  refine ⟨∅ :: π2, ⟨?_, List.mem_cons_self⟩, ?_⟩
  · exact IsLinKDerivation.cut g1 g3 (g2 _ (h2 _ hYm)) (final_cut ha) (by simp)
  · have hl := axList_length (a := a) (b := b)
    have e1 : a * (b - 1) = a * b - a := Nat.mul_sub_one a b
    have e2 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    simp only [List.length_cons]
    rw [Nat.mul_assoc]
    omega

end PEqualNP.ProofComplexity.CrossGeneral
