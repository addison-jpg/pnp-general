import PEqualNP.General.FischerInverter
import PEqualNP.General.Gaps
import Mathlib.Tactic.Linarith

/-!
# Fischer's construction, part 3: L-gen-104

`⌈log₂ (n + 1)⌉` NOT gates suffice up to a polynomial blow-up (Markov 1958, Fischer 1975):
`PEqualNP.General.Gap.L104` with `p = 30 (X + 1)³`.
-/

namespace PEqualNP.General.Fischer

open PEqualNP.CircuitLowerBounds

/-- `2 ^ ⌈log₂ (n + 1)⌉`: one more than the largest number of ones that can be written with
`⌈log₂ (n + 1)⌉` digits. -/
def Kn (n : ℕ) : ℕ := 2 ^ Nat.clog 2 (n + 1)

theorem Kn_gt (n : ℕ) : n < Kn n := Nat.le_pow_clog (by norm_num) (n + 1)

theorem Kn_le (n : ℕ) : Kn n ≤ 2 * n + 1 := by
  unfold Kn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 := Nat.pow_pred_clog_lt_self 2 (show 1 < n + 1 by omega)
    have h2 := Nat.clog_pos (show 1 < 2 by norm_num) (show 1 < n + 1 by omega)
    obtain ⟨r, hr⟩ : ∃ r, Nat.clog 2 (n + 1) = r + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
    rw [hr] at h1 ⊢
    simp only [Nat.pred_succ] at h1
    rw [Nat.pow_succ]; omega

/-- All threshold tables. -/
def G1 (n : ℕ) : List Gate := dpAll n (Kn n) (n + 1)

/-- The digits. -/
def BS (n : ℕ) : List Gate × (ℕ → ℕ) :=
  bitsSt n n (n + 1) (Nat.clog 2 (n + 1)) (TI n (Kn n) n) (G1 n) (Nat.clog 2 (n + 1))

/-- The inverter: constants, thresholds, digits and negated inputs. -/
def G3 (n : ℕ) : List Gate := negSt n (n + 1) (Kn n) (BS n).2 (TI n (Kn n)) (BS n).1 n

/-- The wire of the `i`-th negated input in the inverter. -/
def negF (n i : ℕ) : ℕ := negW (n + (BS n).1.length) (Kn n) (n + 1) i

theorem G3_length (n : ℕ) :
    (G3 n).length + 5 ≤ 2 + 2 * Kn n * n * (n + 1) + 5 * Kn n + 2 * Kn n * n := by
  have h1 : (BS n).1.length + 5 ≤ (G1 n).length + 5 * Kn n :=
    bitsSt_length n n (n + 1) (Nat.clog 2 (n + 1)) (TI n (Kn n) n) (G1 n) (Nat.clog 2 (n + 1))
  have h2 : (G3 n).length = (BS n).1.length + 2 * Kn n * n :=
    negSt_length n (n + 1) (Kn n) (BS n).2 (TI n (Kn n)) (BS n).1 n
  have h3 : (G1 n).length = 2 + 2 * Kn n * n * (n + 1) := dpAll_length n (Kn n) (n + 1)
  omega

theorem G3_spec (n : ℕ) (x : List Bool) (hx : x.length = n) :
    Ext [] (G3 n) (Nat.clog 2 (n + 1)) ∧ n + 1 < n + (G3 n).length ∧
      V (G3 n) x n = true ∧ V (G3 n) x (n + 1) = false ∧
      ∀ i < n, negF n i < n + (G3 n).length ∧ V (G3 n) x (negF n i) = !x.getD i false := by
  set r := Nat.clog 2 (n + 1) with hr
  set K := Kn n with hK
  have hKr : K = 2 ^ r := rfl
  obtain ⟨hext1, hT⟩ : Ext consts (G1 n) 0 ∧ ∀ i < n + 1, ∀ k ≤ K,
      TI n K i k < n + (G1 n).length ∧ V (G1 n) x (TI n K i k) =
        decide (k ≤ cntF (fun l => if l = i then false else x.getD l false) n) :=
    dpAll_spec n K x hx (n + 1)
  have hG1 : Ext [] (G1 n) 0 := consts_ext.trans hext1
  have hG1l : 2 ≤ (G1 n).length := by
    have := hext1.length; simpa [consts] using this
  set N := cntF (fun l => x.getD l false) n with hN
  have hNn : N ≤ n := cntF_le _ _
  have hNK : N < K := lt_of_le_of_lt hNn (Kn_gt n)
  obtain ⟨cv1, cv2⟩ := consts_val x
  rw [hx] at cv1 cv2
  have vt : V (G1 n) x n = true := by rw [hext1.pre.V x _ (by simp [consts, hx]), cv1]
  have vf : V (G1 n) x (n + 1) = false := by rw [hext1.pre.V x _ (by simp [consts, hx]), cv2]
  have hTfull : ∀ k < 2 ^ r, TI n K n k < n + (G1 n).length ∧
      V (G1 n) x (TI n K n k) = decide (k ≤ N) := by
    intro k hk
    obtain ⟨a1, a2⟩ := hT n (by omega) k (by omega)
    refine ⟨a1, ?_⟩
    rw [a2, hN]
    congr 2
    exact cntF_congr fun l hl => by simp [show l ≠ n by omega]
  obtain ⟨hextB, hH⟩ : Ext (G1 n) (BS n).1 r ∧ ∀ q < 2 ^ r, (BS n).2 q < n + (BS n).1.length ∧
      V (BS n).1 x ((BS n).2 q) = decide (N / 2 ^ (r - r) = q) := bits_spec n n (n + 1) r (TI n K n) (G1 n) x hx N (by omega)
    (by omega) vt (by omega) vf hTfull r le_rfl
  have hpB : Pre (G1 n) (BS n).1 := hextB.pre
  have hBl := hextB.length
  have hHr : ∀ k < K, (BS n).2 k < n + (BS n).1.length ∧ V (BS n).1 x ((BS n).2 k) =
      decide (N = k) := by
    intro k hk
    obtain ⟨a1, a2⟩ := hH k hk
    exact ⟨a1, by rw [a2]; simp⟩
  have hTI : ∀ i < n, ∀ k < K, TI n K i k < n + (BS n).1.length ∧ V (BS n).1 x (TI n K i k) =
      decide (k ≤ cntF (fun l => if l = i then false else x.getD l false) n) := by
    intro i hi k hk
    obtain ⟨a1, a2⟩ := hT i (by omega) k (by omega)
    exact ⟨by omega, by rw [hpB.V x _ (by omega), a2]⟩
  have hneg := neg_spec n (n + 1) K (BS n).2 (TI n K) (BS n).1 x hx n N
    (fun i => cntF (fun l => if l = i then false else x.getD l false) n) hNK (by omega)
    (by rw [hpB.V x _ (by omega), vf]) hHr hTI n le_rfl
  have hext3 : Ext (BS n).1 (G3 n) 0 := negSt_ext _ _ _ _ _ _ _
  have hp3 : Pre (G1 n) (G3 n) := hpB.trans hext3.pre
  have h3l := hext3.length
  refine ⟨(hG1.trans hextB).trans hext3 |>.cast (by omega), by omega,
    by rw [hp3.V x _ (by omega), vt], by rw [hp3.V x _ (by omega), vf], fun i hi => ?_⟩
  obtain ⟨a1, a2⟩ := hneg i hi
  refine ⟨a1, ?_⟩
  unfold negF G3
  rw [a2]
  have he := cntF_erase (fun l => x.getD l false) i n
  simp only [hi, if_true] at he
  rw [hN, ← he]
  cases x.getD i false <;> simp

/-- The circuit with `⌈log₂ (n + 1)⌉` NOT gates simulating `C` on inputs of length `n`. -/
def fischerCircuit (n : ℕ) (C : Circuit) : Circuit :=
  dualCircuit n n (n + 1) (negF n) C (G3 n)

/-- **L-gen-104** (Markov 1958, Fischer 1975): `⌈log₂ (n + 1)⌉` NOT gates are as good as any
number, up to a polynomial factor. -/
theorem L104 : PEqualNP.General.Gap.L104 := by
  refine ⟨Polynomial.C 30 * (Polynomial.X + 1) ^ 3, fun s L hL n => ?_⟩
  obtain ⟨C, hC, hs, hd⟩ := hL n
  obtain ⟨hext, hlt, -, -, hneg⟩ := G3_spec n (List.replicate n false) (by simp)
  obtain ⟨hext', hsize, heval⟩ := dual_correct n n (n + 1) (negF n) C (G3 n) hC
    (by omega) hlt (fun i hi => (hneg i hi).1)
    (fun x hx => by
      obtain ⟨-, -, v1, v2, v3⟩ := G3_spec n x hx
      exact ⟨v1, v2, fun i hi => (v3 i hi).2⟩)
  obtain ⟨hg, hn⟩ := good_of_ext (hext.trans hext')
  refine ⟨fischerCircuit n C, hg, ?_, hn.le, ?_⟩
  · unfold fischerCircuit
    rw [hsize]
    have hl := G3_length n
    have hK := Kn_le n
    simp only [Circuit.size] at hs ⊢
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    set m := s n + n with hm
    have hnm : n ≤ m := by omega
    have hsm : s n ≤ m := by omega
    have hK' : Kn n ≤ 2 * m + 1 := by omega
    have e1 : Kn n * n * (n + 1) ≤ (2 * m + 1) * m * (m + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hK' hnm) (by omega)
    have e2 : Kn n * n ≤ (2 * m + 1) * m := Nat.mul_le_mul hK' hnm
    have e3 : (2 * m + 1) * m * (m + 1) ≤ 2 * (m + 1) ^ 3 := by nlinarith
    have e4 : (2 * m + 1) * m ≤ 2 * (m + 1) ^ 3 := by nlinarith
    have e5 : m + 1 ≤ (m + 1) ^ 3 := by nlinarith
    have q1 : 2 * Kn n * n * (n + 1) = 2 * (Kn n * n * (n + 1)) := by ring
    have q2 : 2 * Kn n * n = 2 * (Kn n * n) := by ring
    have hcs : C.size = C.gates.length := rfl
    omega
  · intro x hx
    unfold fischerCircuit
    rw [heval x hx]
    exact hd x hx

end PEqualNP.General.Fischer
