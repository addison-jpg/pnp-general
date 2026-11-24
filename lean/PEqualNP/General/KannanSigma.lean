import PEqualNP.General.KannanLang

/-!
# Kannan's theorem, uniform half: the reduction to a linear-time check

`SigmaP j`: the languages in `SigmaV j (fun n => K * n ^ K + K)` for some `K`.
`KL k` is in `SigmaP 3` once the block check `CheckW k` is decidable in linear time
(`CheckLinTime k`, a named hypothesis, not proved here).
-/

namespace PEqualNP.General.Kannan

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers PEqualNP.Library
open PEqualNP.General.SizeHierarchy

/-- Sigma_j^p in verifier form: blocks of length `K n ^ K + K`, then a linear-time check. -/
def SigmaP (j : ℕ) : Set (Language Bool) :=
  {L | ∃ K : ℕ, L ∈ SigmaV j (fun n => K * n ^ K + K)}

/-- The constant of the block length. -/
def KK (k : ℕ) : ℕ := (2 ^ (3 * (k + 1) + 9) * 2 ^ (k + 2) + 10) * 2 ^ (2 * k + 4)

/-- The block length. -/
def blk (k n : ℕ) : ℕ := KK k * n ^ KK k + KK k

theorem blk_ge (k n : ℕ) : NN k n + ell k n ≤ blk k n := by
  set p := n + 1
  set E := 2 * k + 4
  set q := p ^ (k + 1)
  set A1 := 2 ^ (3 * (k + 1) + 9) * 2 ^ (k + 2)
  have hp : 1 ≤ p := by omega
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp
  have hpq : p ≤ q := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ q := Nat.pow_le_pow_right hp (by omega)
  have hqE : q * q ≤ p ^ E := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hp (by omega)
  have hN : NN k n ≤ A1 * p ^ E := by
    have h1 : NN k n ≤ 2 ^ m0 k n := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    have h2 := m0_le_pow k n
    have h3 : (2 * (n + 1)) ^ (k + 2) = 2 ^ (k + 2) * p ^ (k + 2) := mul_pow _ _ _
    have h4 : p ^ (k + 2) ≤ p ^ E := Nat.pow_le_pow_right hp (by omega)
    calc NN k n ≤ 2 ^ (3 * (k + 1) + 9) * (2 ^ (k + 2) * p ^ (k + 2)) := by
          rw [← h3]; exact h1.trans h2
      _ ≤ 2 ^ (3 * (k + 1) + 9) * (2 ^ (k + 2) * p ^ E) := by gcongr
      _ = A1 * p ^ E := by ring
  have hB : BB k n ≤ q := Nat.pow_le_pow_left (by omega) _
  have hw : ww k n ≤ 2 * q := by unfold ww; omega
  have hg : gw k n ≤ 8 * q := by unfold gw; omega
  have hl : ell k n ≤ 10 * p ^ E := by
    unfold ell
    have : BB k n * gw k n ≤ q * (8 * q) := Nat.mul_le_mul hB hg
    nlinarith
  have hpE : p ^ E ≤ 2 ^ E * n ^ E + 2 ^ E := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [p, h0]; exact Nat.one_le_two_pow
    · have : p ^ E ≤ (2 * n) ^ E := Nat.pow_le_pow_left (by omega) _
      rw [mul_pow] at this; exact this.trans (Nat.le_add_right _ _)
  have hEK : E ≤ KK k := by
    have : E < 2 ^ E := Nat.lt_two_pow_self
    calc E ≤ 2 ^ E := this.le
      _ ≤ KK k := by unfold KK; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hnE : n ^ E ≤ n ^ KK k := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [zero_pow (show E ≠ 0 by omega)]
    · exact Nat.pow_le_pow_right h0 hEK
  have hKK : KK k = (A1 + 10) * 2 ^ E := rfl
  unfold blk
  calc NN k n + ell k n ≤ (A1 + 10) * p ^ E := by nlinarith
    _ ≤ (A1 + 10) * (2 ^ E * n ^ E + 2 ^ E) := Nat.mul_le_mul_left _ hpE
    _ = KK k * n ^ E + KK k := by rw [hKK]; ring
    _ ≤ KK k * n ^ KK k + KK k := by gcongr

/-- The check applied to the three blocks of `w` (each of length `blk k |x|`): `T` and `T'` are
the first `N` bits of blocks one and two-after-`C`, `C` and `C'` the first `ell` bits of blocks
two and three. -/
def CheckW (k : ℕ) (x w : List Bool) : Bool :=
  let s := blk k x.length
  let N := NN k x.length
  let l := ell k x.length
  let y1 := w.take s
  let y2 := (w.drop s).take s
  let y3 := w.drop (2 * s)
  Check k x (y1.take N) (y2.take l) ((y2.drop l).take N) (y3.take l)

/-- The remaining machine step (a named hypothesis): the block check is decidable in time
linear in the length of the pair. -/
def CheckLinTime (k : ℕ) : Prop :=
  ∃ (R : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair R (fun l => K * l + K) ∧
      ∀ x w : List Bool, (x, w) ∈ R ↔ CheckW k x w = true

theorem alt3 (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ y1 : List Bool, y1.length = s ∧ ∀ y2 : List Bool, y2.length = s →
      ∃ y3 : List Bool, y3.length = s ∧ P (y1 ++ (y2 ++ y3)) := by
  simp only [Alt, List.append_nil, not_not, not_exists, not_and, not_forall, exists_prop]

theorem CheckW_blocks (k : ℕ) (x y1 y2 y3 : List Bool) (h1 : y1.length = blk k x.length)
    (h2 : y2.length = blk k x.length) :
    CheckW k x (y1 ++ (y2 ++ y3)) =
      Check k x (y1.take (NN k x.length)) (y2.take (ell k x.length))
        ((y2.drop (ell k x.length)).take (NN k x.length)) (y3.take (ell k x.length)) := by
  simp only [CheckW]
  rw [List.take_left' h1, List.drop_left' h1, List.take_left' h2,
    show 2 * blk k x.length = y1.length + y2.length by omega, ← List.drop_drop,
    List.drop_left' rfl, List.drop_left' rfl]

theorem mem_KL_iff_blocks (k : ℕ) (x : List Bool) :
    x ∈ KL k ↔ ∃ y1 : List Bool, y1.length = blk k x.length ∧
      ∀ y2 : List Bool, y2.length = blk k x.length →
      ∃ y3 : List Bool, y3.length = blk k x.length ∧ CheckW k x (y1 ++ (y2 ++ y3)) = true := by
  rw [mem_KL_iff]
  have hge := blk_ge k x.length
  constructor
  · rintro ⟨T, hT, h⟩
    have hy1 : (T ++ List.replicate (blk k x.length - NN k x.length) false).length =
        blk k x.length := by simp; omega
    refine ⟨_, hy1, fun y2 hy2 => ?_⟩
    obtain ⟨C', hC', hc⟩ := h (y2.take (ell k x.length)) (by simp; omega)
      ((y2.drop (ell k x.length)).take (NN k x.length)) (by simp; omega)
    refine ⟨C' ++ List.replicate (blk k x.length - ell k x.length) false, by simp; omega, ?_⟩
    rw [CheckW_blocks k x _ _ _ hy1 hy2, List.take_left' hT, List.take_left' hC']
    exact hc
  · rintro ⟨y1, hy1, h⟩
    refine ⟨y1.take (NN k x.length), by simp; omega, fun C hC T' hT' => ?_⟩
    have hy2 : (C ++ (T' ++ List.replicate (blk k x.length - ell k x.length - NN k x.length)
        false)).length = blk k x.length := by simp; omega
    obtain ⟨y3, hy3, hc⟩ := h _ hy2
    refine ⟨y3.take (ell k x.length), by simp; omega, ?_⟩
    rw [CheckW_blocks k x _ _ _ hy1 hy2, List.take_left' hC, List.drop_left' hC,
      List.take_left' hT'] at hc
    exact hc

/-- (c) Given the linear-time check, `KL k` is in `SigmaP 3`. -/
theorem kannan_of_check (k : ℕ) (h : CheckLinTime k) : KL k ∈ SigmaP 3 := by
  obtain ⟨R, K, hdec, hR⟩ := h
  refine ⟨KK k, R, K, hdec, fun x => ?_⟩
  rw [mem_KL_iff_blocks, alt3]
  simp only [hR]
  rfl

/-- Kannan's theorem, uniform half, modulo the linear-time check. -/
theorem kannan_uniform_of_check (k : ℕ) (h : CheckLinTime k) :
    ∃ L : Language Bool, L ∈ SigmaP 3 ∧ ∀ c : ℕ, L ∉ SIZE (fun n => c * n ^ k + c) :=
  ⟨KL k, kannan_of_check k h, KL_not_SIZE k⟩

end PEqualNP.General.Kannan
