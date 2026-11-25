import PEqualNP.General.KannanSigma

/-!
# Kannan's theorem, uniform half: the check on short data regions

A variant of the block reduction of `KannanSigma` in which the blocks have length
`blkK K n = K n ^ K + K` for any `K ≥ KK k`, and the check only looks at the first
`D = blk k n` symbols of each block (the data regions). The data regions are cut out of the
witness by a mask (`zipSel (mask k K n) w`), and the check on the regions is `CoreFn`.
-/

namespace PEqualNP.General.Kannan

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers PEqualNP.Library
open PEqualNP.General.SizeHierarchy

/-- Block length with constant `K`. -/
def blkK (K n : ℕ) : ℕ := K * n ^ K + K

/-- The check on the concatenation `sel` of the three data regions (each of length
`D = blk k |x|`). -/
def CoreFn (k : ℕ) (x sel : List Bool) : Bool :=
  Check k x (sel.take (NN k x.length))
    ((sel.drop (blk k x.length)).take (ell k x.length))
    (((sel.drop (blk k x.length)).drop (ell k x.length)).take (NN k x.length))
    ((sel.drop (2 * blk k x.length)).take (ell k x.length))

/-- Keep the symbols of `w` at the positions where `u` is `true`. -/
def zipSel : List Bool → List Bool → List Bool
  | b :: u, a :: w => if b then a :: zipSel u w else zipSel u w
  | _, _ => []

/-- The mask of the data regions: three blocks of length `s`, the first `D` symbols kept. -/
def maskOf (D s : ℕ) : List Bool :=
  let m := List.replicate D true ++ List.replicate (s - D) false
  m ++ m ++ m

/-- The mask at length `n`. -/
def mask (k K n : ℕ) : List Bool := maskOf (blk k n) (blkK K n)

theorem zipSel_true (D : ℕ) (u w y : List Bool) (hy : y.length = D) :
    zipSel (List.replicate D true ++ u) (y ++ w) = y ++ zipSel u w := by
  induction D generalizing y with
  | zero => cases y with
    | nil => simp
    | cons _ _ => simp at hy
  | succ D ih => cases y with
    | nil => simp at hy
    | cons a y =>
      simp only [List.replicate_succ, List.cons_append, zipSel, ite_true]
      rw [ih y (by simpa using hy)]

theorem zipSel_false (E : ℕ) (u w y : List Bool) (hy : y.length = E) :
    zipSel (List.replicate E false ++ u) (y ++ w) = zipSel u w := by
  induction E generalizing y with
  | zero => cases y with
    | nil => simp
    | cons _ _ => simp at hy
  | succ E ih => cases y with
    | nil => simp at hy
    | cons a y =>
      simp only [List.replicate_succ, List.cons_append, zipSel]
      exact ih y (by simpa using hy)

theorem zipSel_nil_right (u : List Bool) : zipSel u [] = [] := by
  cases u <;> rfl

theorem zipSel_block (D s : ℕ) (hD : D ≤ s) (u w y : List Bool) (hy : y.length = s) :
    zipSel ((List.replicate D true ++ List.replicate (s - D) false) ++ u) (y ++ w) =
      y.take D ++ zipSel u w := by
  have hy' : y = y.take D ++ y.drop D := (List.take_append_drop D y).symm
  rw [List.append_assoc, hy', List.append_assoc, zipSel_true D _ _ _ (by simp; omega),
    zipSel_false (s - D) _ _ _ (by simp; omega)]
  rw [← hy']

theorem zipSel_maskOf (D s : ℕ) (hD : D ≤ s) (y1 y2 y3 : List Bool) (h1 : y1.length = s)
    (h2 : y2.length = s) (h3 : y3.length = s) :
    zipSel (maskOf D s) (y1 ++ (y2 ++ y3)) = y1.take D ++ (y2.take D ++ y3.take D) := by
  unfold maskOf
  simp only
  rw [List.append_assoc, zipSel_block D s hD _ _ _ h1, zipSel_block D s hD _ _ _ h2]
  have := zipSel_block D s hD [] [] y3 h3
  simp only [List.append_nil, zipSel_nil_right] at this
  rw [this]

theorem CoreFn_blocks (k : ℕ) (x y1 y2 y3 : List Bool) (s : ℕ) (hs : blk k x.length ≤ s)
    (h1 : y1.length = s) (h2 : y2.length = s) (h3 : y3.length = s) :
    CoreFn k x (zipSel (maskOf (blk k x.length) s) (y1 ++ (y2 ++ y3))) =
      Check k x (y1.take (NN k x.length)) (y2.take (ell k x.length))
        ((y2.drop (ell k x.length)).take (NN k x.length)) (y3.take (ell k x.length)) := by
  rw [zipSel_maskOf _ s hs _ _ _ h1 h2 h3]
  have hge := blk_ge k x.length
  set D := blk k x.length
  have l1 : (y1.take D).length = D := by simp; omega
  have l2 : (y2.take D).length = D := by simp; omega
  unfold CoreFn
  rw [List.take_append_of_le_length (by omega), List.take_take, min_eq_left (by omega),
    List.drop_left' l1, List.take_append_of_le_length (by simp; omega), List.take_take,
    min_eq_left (by omega), List.drop_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega), List.drop_take,
    List.take_take, show 2 * D = D + D by omega, ← List.drop_drop, List.drop_left' l1,
    List.drop_left' l2, List.take_take, min_eq_left (by omega)]
  congr 1
  rw [min_eq_left (by omega)]

theorem mem_KL_iff_blocksS (k : ℕ) (x : List Bool) (s : ℕ) (hge : NN k x.length + ell k x.length ≤ s) :
    x ∈ KL k ↔ ∃ y1 : List Bool, y1.length = s ∧
      ∀ y2 : List Bool, y2.length = s →
      ∃ y3 : List Bool, y3.length = s ∧
        Check k x (y1.take (NN k x.length)) (y2.take (ell k x.length))
          ((y2.drop (ell k x.length)).take (NN k x.length)) (y3.take (ell k x.length)) = true := by
  rw [mem_KL_iff]
  constructor
  · rintro ⟨T, hT, h⟩
    have hy1 : (T ++ List.replicate (s - NN k x.length) false).length = s := by simp; omega
    refine ⟨_, hy1, fun y2 hy2 => ?_⟩
    obtain ⟨C', hC', hc⟩ := h (y2.take (ell k x.length)) (by simp; omega)
      ((y2.drop (ell k x.length)).take (NN k x.length)) (by simp; omega)
    refine ⟨C' ++ List.replicate (s - ell k x.length) false, by simp; omega, ?_⟩
    rw [List.take_left' hT, List.take_left' hC']
    exact hc
  · rintro ⟨y1, hy1, h⟩
    refine ⟨y1.take (NN k x.length), by simp; omega, fun C hC T' hT' => ?_⟩
    have hy2 : (C ++ (T' ++ List.replicate (s - ell k x.length - NN k x.length)
        false)).length = s := by simp; omega
    obtain ⟨y3, hy3, hc⟩ := h _ hy2
    refine ⟨y3.take (ell k x.length), by simp; omega, ?_⟩
    rw [List.take_left' hC, List.drop_left' hC, List.take_left' hT'] at hc
    exact hc

theorem blk_le_blkK (k K n : ℕ) (hK : KK k ≤ K) : blk k n ≤ blkK K n := by
  unfold blk blkK
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have h1 : 0 < KK k := by unfold KK; positivity
    rw [zero_pow (by omega), zero_pow (by omega)]; omega
  · have : n ^ KK k ≤ n ^ K := Nat.pow_le_pow_right h0 hK
    have := Nat.mul_le_mul hK this
    omega

/-- The characterization with the mask: blocks of length `blkK K |x|`, then `CoreFn` on the
data regions. -/
theorem mem_KL_iff_mask (k K : ℕ) (hK : KK k ≤ K) (x : List Bool) :
    x ∈ KL k ↔ Alt 3 (blkK K x.length)
      (fun w => CoreFn k x (zipSel (mask k K x.length) w) = true) := by
  have hb := blk_le_blkK k K x.length hK
  have hge := blk_ge k x.length
  rw [mem_KL_iff_blocksS k x (blkK K x.length) (by omega), alt3]
  apply exists_congr; intro y1
  apply and_congr_right; intro hy1
  apply forall_congr'; intro y2
  apply imp_congr_right; intro hy2
  apply exists_congr; intro y3
  apply and_congr_right; intro hy3
  unfold mask
  rw [CoreFn_blocks k x y1 y2 y3 _ hb hy1 hy2 hy3]

/-- `Alt 3` only looks at strings of length `3 s`. -/
theorem alt3_congr (s : ℕ) (P Q : List Bool → Prop)
    (h : ∀ w : List Bool, w.length = 3 * s → (P w ↔ Q w)) : Alt 3 s P ↔ Alt 3 s Q := by
  rw [alt3, alt3]
  apply exists_congr; intro y1
  apply and_congr_right; intro hy1
  apply forall_congr'; intro y2
  apply imp_congr_right; intro hy2
  apply exists_congr; intro y3
  apply and_congr_right; intro hy3
  exact h _ (by simp; omega)

/-- The masked check, decidable in linear time on the witnesses of the right length. -/
def MaskLinTime (k K : ℕ) : Prop :=
  ∃ (R : Set (List Bool × List Bool)) (K' : ℕ),
    DecidableInTime encodePair R (fun l => K' * l + K') ∧
      ∀ x w : List Bool, w.length = 3 * blkK K x.length →
        ((x, w) ∈ R ↔ CoreFn k x (zipSel (mask k K x.length) w) = true)

theorem kannan_of_mask (k K : ℕ) (hK : KK k ≤ K) (h : MaskLinTime k K) : KL k ∈ SigmaP 3 := by
  obtain ⟨R, K', hdec, hR⟩ := h
  refine ⟨K, R, K', hdec, fun x => ?_⟩
  rw [mem_KL_iff_mask k K hK]
  exact alt3_congr _ _ _ (fun w hw => (hR x w hw).symm)

end PEqualNP.General.Kannan
