import PEqualNP.General.KannanDefs

/-!
# Kannan's theorem, uniform half: the language of the lexicographically first hard table

`KL k`, its circuit lower bound (`KL_not_SIZE`) and its `∃ ∀ ∃` characterization
(`mem_KL_iff`) with the computable predicate `Check`.
-/

namespace PEqualNP.General.Kannan

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers PEqualNP.Library
open PEqualNP.General.SizeHierarchy

/-- The `i`-th point at length `n`: the `m` low bits of `i`, then `n - m` zeros. -/
def pt (k n i : ℕ) : List Bool := enc (mm k n) i ++ List.replicate (n - mm k n) false

theorem length_pt (k n i : ℕ) : (pt k n i).length = n := by
  have := min_le_right (m0 k n) n
  simp [pt, mm] at *

/-- `C` computes the table `T` (entry `i` at the point `pt k n i`, `i < N`). -/
def computes (k n : ℕ) (C : Circuit) (T : List Bool) : Bool :=
  (List.range (NN k n)).all fun i => C.eval (pt k n i) == T.getD i false

/-- A hard table: of length `N` and computed by no circuit string of length `ell k n`. -/
def Hard (k n : ℕ) (T : List Bool) : Prop :=
  T.length = NN k n ∧ ∀ s : List Bool, s.length = ell k n → computes k n (decCirc k n s) T = false

open Classical in
/-- The lexicographically first hard table (`[]` if there is none). -/
noncomputable def Tstar (k n : ℕ) : List Bool :=
  if h : ∃ T, Hard k n T then
    (InvImage.wf val wellFounded_lt).min {T | Hard k n T} h
  else []

/-- The table index of `x`: the value of its first `m` bits. -/
def idx (k : ℕ) (x : List Bool) : ℕ := bv (x.take (mm k x.length))

/-- The language. -/
def KL (k : ℕ) : Language Bool :=
  {x | (Tstar k x.length).getD (idx k x) false = true}

/-- The check: `C` does not compute `T`; `T` is `1` at `x`; if `T' <lex T` then `C'`
computes `T'`. -/
def Check (k : ℕ) (x T C T' C' : List Bool) : Bool :=
  !computes k x.length (decCirc k x.length C) T && T.getD (idx k x) false &&
    (!decide (val T' < val T) || computes k x.length (decCirc k x.length C') T')

/-! ### The characterization -/

theorem mem_KL_iff_min (k : ℕ) (x : List Bool) :
    x ∈ KL k ↔ ∃ T, Hard k x.length T ∧ T.getD (idx k x) false = true ∧
      ∀ T', Hard k x.length T' → ¬ val T' < val T := by
  set n := x.length
  have hwf := InvImage.wf val wellFounded_lt
  by_cases h : ∃ T, Hard k n T
  · have hT : Tstar k n = hwf.min {T | Hard k n T} h := by simp [Tstar, h]
    have hmem : Hard k n (Tstar k n) := hT ▸ hwf.min_mem {T | Hard k n T} h
    have hmin : ∀ T', Hard k n T' → ¬ val T' < val (Tstar k n) :=
      fun T' hT' => by rw [hT]; exact hwf.not_lt_min {T | Hard k n T} hT'
    constructor
    · intro hx; exact ⟨Tstar k n, hmem, hx, hmin⟩
    · rintro ⟨T, hTh, hTx, hTmin⟩
      have heq : T = Tstar k n := by
        apply val_inj (hTh.1.trans hmem.1.symm)
        have := hmin T hTh; have := hTmin _ hmem; omega
      show (Tstar k n).getD _ _ = true
      rw [← heq]; exact hTx
  · have hT : Tstar k n = [] := by simp [Tstar, h]
    constructor
    · intro hx; change (Tstar k n).getD _ _ = true at hx; rw [hT] at hx; simp at hx
    · rintro ⟨T, hTh, -⟩; exact absurd ⟨T, hTh⟩ h

/-- (b) The `∃ ∀ ∃` characterization: blocks `T`, then `C` and `T'`, then `C'`. -/
theorem mem_KL_iff (k : ℕ) (x : List Bool) :
    x ∈ KL k ↔ ∃ T : List Bool, T.length = NN k x.length ∧
      ∀ C : List Bool, C.length = ell k x.length →
      ∀ T' : List Bool, T'.length = NN k x.length →
      ∃ C' : List Bool, C'.length = ell k x.length ∧ Check k x T C T' C' = true := by
  rw [mem_KL_iff_min]
  generalize hn : x.length = n
  have hz : (List.replicate (ell k n) false).length = ell k n := by simp
  have hzN : (List.replicate (NN k n) false).length = NN k n := by simp
  constructor
  · rintro ⟨T, ⟨hTl, hTs⟩, hTx, hTmin⟩
    refine ⟨T, hTl, fun C hC T' hT' => ?_⟩
    by_cases hlt : val T' < val T
    · have hnh : ¬ Hard k n T' := fun h => hTmin T' h hlt
      have : ∃ C', C'.length = ell k n ∧ computes k n (decCirc k n C') T' = true := by
        by_contra hc; push Not at hc
        exact hnh ⟨hT', fun s hs => by simpa using hc s hs⟩
      obtain ⟨C', hC', hc⟩ := this
      exact ⟨C', hC', by
        simp only [Check, hn, hTs C hC, hTx, hc, Bool.not_false, Bool.and_true, Bool.or_true]⟩
    · exact ⟨_, hz, by
        simp only [Check, hn, hTs C hC, hTx, decide_eq_false hlt, Bool.not_false, Bool.and_true,
          Bool.true_or]⟩
  · rintro ⟨T, hTl, h⟩
    have hTs : ∀ s, s.length = ell k n → computes k n (decCirc k n s) T = false := by
      intro s hs
      obtain ⟨C', -, hc⟩ := h s hs _ hzN
      simp only [Check, hn, Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact hc.1.1
    refine ⟨T, ⟨hTl, hTs⟩, ?_, ?_⟩
    · obtain ⟨C', -, hc⟩ := h _ hz _ hzN
      simp only [Check, hn, Bool.and_eq_true] at hc
      exact hc.1.2
    · intro T' hT' hlt
      obtain ⟨C', hC', hc⟩ := h _ hz T' hT'.1
      simp only [Check, hn, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hc
      rcases hc.2 with h1 | h1
      · exact h1 hlt
      · rw [hT'.2 C' hC'] at h1; exact absurd h1 (by simp)

/-! ### The lower bound -/

theorem idx_pt (k n i : ℕ) (hi : i < NN k n) : idx k (pt k n i) = i := by
  unfold idx; rw [length_pt]
  simp only [pt]
  rw [List.take_left' (by simp), bv_enc, Nat.mod_eq_of_lt (by simpa [NN] using hi)]

/-- Some table is hard at lengths where the count is small. -/
theorem exists_hard_table (k n : ℕ) (hcnt : count n (n ^ (k + 1)) < 2 ^ 2 ^ mm k n) :
    ∃ T, Hard k n T := by
  obtain ⟨g, hg⟩ := exists_hard_pad n (n ^ (k + 1)) (mm k n) (min_le_right _ _) hcnt
  let vec : ℕ → Fin (mm k n) → Bool := fun i j => (enc (mm k n) i).getD j false
  refine ⟨(List.range (NN k n)).map fun i => g (vec i), by simp, fun s _ => ?_⟩
  by_contra hc
  simp only [Bool.not_eq_false, computes, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  obtain ⟨v, hv⟩ := hg (decCirc k n s) (decCirc_basic k n s) (by rw [decCirc_size]; rfl)
  apply hv
  have hi : bv (List.ofFn v) < NN k n := by
    have := bv_lt (List.ofFn v); simpa [NN] using this
  have he : enc (mm k n) (bv (List.ofFn v)) = List.ofFn v := by
    have := enc_bv (List.ofFn v); simpa using this
  have h := hc _ hi
  have hvec : vec (bv (List.ofFn v)) = v := by
    funext j; simp only [vec, he]; simp [List.getD_eq_getElem?_getD]
  simp only [pt, he] at h
  rw [h, List.getD_eq_getElem?_getD]
  simp [hi, hvec]

/-- (a) `KL k` has no circuits of size `c n ^ k + c`. -/
theorem KL_not_SIZE (k c : ℕ) : KL k ∉ SIZE (fun n => c * n ^ k + c) := by
  intro hL
  obtain ⟨t, ht⟩ := exists_lin_lt_two_pow (3 * (k + 1) + 9 + (k + 2) + 2 * c + 2) (k + 2)
  have htc : 2 * c + 2 ≤ 2 ^ t := by nlinarith
  set n := 2 ^ t with hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hlog : lam n = t + 1 := by
    unfold lam; rw [hn, Nat.log_pow (by norm_num)]
  have hm0 : m0 k n ≤ n := by
    unfold m0; rw [hlog]; nlinarith
  have hmm : mm k n = m0 k n := min_eq_left hm0
  have hcnt : count n (n ^ (k + 1)) < 2 ^ 2 ^ mm k n := by rw [hmm]; exact count_lt k n hn2
  obtain ⟨T0, hT0⟩ := exists_hard_table k n hcnt
  have hstar := (mem_KL_iff_min k (List.replicate n false))
  -- the hard first table
  have hwf := InvImage.wf val wellFounded_lt
  have hex : ∃ T, Hard k n T := ⟨T0, hT0⟩
  have hTs : Tstar k n = hwf.min {T | Hard k n T} hex := by simp [Tstar, hex]
  have hmem : Hard k n (Tstar k n) := hTs ▸ hwf.min_mem {T | Hard k n T} hex
  obtain ⟨C, hC, hsz, hdec⟩ := hL n
  have hcl : c * n ^ k + c ≤ n ^ (k + 1) := by
    have : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn0
    have h1 : c ≤ c * n ^ k := Nat.le_mul_of_pos_right _ this
    have h2 : 2 * c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul_right _ (by omega)
    rw [pow_succ]; nlinarith
  obtain ⟨d, hd⟩ := exists_decode n (BB k n) C hC (hsz.trans hcl)
  apply absurd (hmem.2 _ (length_encCirc k n d))
  rw [decCirc_encCirc]
  simp only [Bool.not_eq_false, computes, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi
  rw [hd _ (length_pt k n i)]
  have h1 := hdec _ (length_pt k n i)
  have h2 : pt k n i ∈ KL k ↔ (Tstar k n).getD i false = true := by
    show (Tstar k (pt k n i).length).getD (idx k (pt k n i)) false = true ↔ _
    rw [length_pt, idx_pt k n i hi]
  exact Bool.eq_iff_iff.mpr (h1.trans h2)

end PEqualNP.General.Kannan
