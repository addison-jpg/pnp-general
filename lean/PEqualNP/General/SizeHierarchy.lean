import PEqualNP.CircuitLowerBounds.Helpers.Shannon
import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# The circuit-size hierarchy

For every `k` there is a language in P/poly (with an explicit polynomial bound) that has no
circuits of size `c * n ^ k + c`, for any `c`. At length `n`, the language is a hard function
(by counting) on the first `mm n` bits, where `mm n = min (m0 n) n` and `m0 n` is about
`(k + 2) * log n`.
-/

namespace PEqualNP.General.SizeHierarchy

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers

/-- Counting on padded inputs: if there are fewer descriptors than functions on `m ≤ n` bits,
some function `g` on `m` bits is not computed, on zero-padded inputs, by any basic circuit
on `n` inputs with at most `s` gates. -/
theorem exists_hard_pad (n s m : ℕ) (hmn : m ≤ n) (h : count n s < 2 ^ 2 ^ m) :
    ∃ g : (Fin m → Bool) → Bool, ∀ C : Circuit, Basic C → C.size ≤ s →
      ∃ v : Fin m → Bool, C.eval (List.ofFn v ++ List.replicate (n - m) false) ≠ g v := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective
      (fun (d : CD n s) (v : Fin m → Bool) =>
        (decode d).eval (List.ofFn v ++ List.replicate (n - m) false)) := by
    intro f
    obtain ⟨C, hC, hs, hf⟩ := hcon f
    obtain ⟨d, hd⟩ := exists_decode n s C hC hs
    refine ⟨d, funext fun v => (hd _ ?_).trans (hf v)⟩
    simp; omega
  have hcard := Fintype.card_le_of_surjective _ hsurj
  rw [card_CD] at hcard
  simp at hcard
  omega

/-- The parameters. -/
def lam (n : ℕ) : ℕ := Nat.log 2 n + 1

def m0 (k n : ℕ) : ℕ := (k + 2) * lam n + 3 * (k + 1) + 9

def mm (k n : ℕ) : ℕ := min (m0 k n) n

theorem count_lt (k n : ℕ) (hn : 2 ≤ n) :
    count n (n ^ (k + 1)) < 2 ^ 2 ^ m0 k n := by
  have hn0 : 0 < n := by omega
  have hq : n ^ (k + 1) ≤ n ^ (k + 1) := le_rfl
  have h1 := count_le n (k + 1) (n ^ (k + 1)) hn (by omega) hq
  have hlam : n < 2 ^ lam n := Nat.lt_pow_succ_log_self (by norm_num) n
  set l := lam n with hl
  have hK : (3 * (k + 1) + 8) * n ^ (k + 1) ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (by omega) (pow_pos hn0 _))
  have h2 : n ^ ((3 * (k + 1) + 8) * n ^ (k + 1)) ≤
      (2 ^ l) ^ ((3 * (k + 1) + 8) * n ^ (k + 1)) :=
    Nat.pow_le_pow_left hlam.le _
  have h3 : l * ((3 * (k + 1) + 8) * n ^ (k + 1)) < 2 ^ m0 k n := by
    have hA : l < 2 ^ l := Nat.lt_two_pow_self
    have hB : 3 * (k + 1) + 8 < 2 ^ (3 * (k + 1) + 8) := Nat.lt_two_pow_self
    have hC : n ^ (k + 1) ≤ 2 ^ (l * (k + 1)) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hlam.le _
    have hD : l * (3 * (k + 1) + 8) < 2 ^ l * 2 ^ (3 * (k + 1) + 8) := Nat.mul_lt_mul'' hA hB
    have hpos : 0 < n ^ (k + 1) := pow_pos hn0 _
    calc l * ((3 * (k + 1) + 8) * n ^ (k + 1))
        = (l * (3 * (k + 1) + 8)) * n ^ (k + 1) := by ring
      _ < (2 ^ l * 2 ^ (3 * (k + 1) + 8)) * 2 ^ (l * (k + 1)) :=
          Nat.mul_lt_mul_of_lt_of_le hD hC (by positivity)
      _ = 2 ^ (l + (3 * (k + 1) + 8) + l * (k + 1)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ m0 k n := Nat.pow_le_pow_right (by omega) (by unfold m0; rw [← hl]; nlinarith)
  calc count n (n ^ (k + 1)) ≤ n ^ ((3 * (k + 1) + 8) * n ^ (k + 1)) := h1
    _ ≤ (2 ^ l) ^ ((3 * (k + 1) + 8) * n ^ (k + 1)) := h2
    _ = 2 ^ (l * ((3 * (k + 1) + 8) * n ^ (k + 1))) := by rw [← pow_mul]
    _ < 2 ^ 2 ^ m0 k n := Nat.pow_lt_pow_right (by omega) h3

open Classical in
/-- The hard function on the first `mm k n` bits at length `n`. -/
noncomputable def G (k n : ℕ) : (Fin (mm k n) → Bool) → Bool :=
  if h : count n (n ^ (k + 1)) < 2 ^ 2 ^ mm k n then
    Classical.choose (exists_hard_pad n (n ^ (k + 1)) (mm k n) (min_le_right _ _) h)
  else fun _ => false

/-- The language. -/
def Lk (k : ℕ) : Language Bool :=
  {x | G k x.length (fun i : Fin (mm k x.length) => x.getD (i : ℕ) false) = true}

theorem mem_Lk (k n : ℕ) (x : List Bool) (hx : x.length = n) :
    x ∈ Lk k ↔ G k n (fun i : Fin (mm k n) => x.getD (i : ℕ) false) = true := by
  subst hx; rfl

theorem m0_le_pow (k n : ℕ) : 2 ^ m0 k n ≤ 2 ^ (3 * (k + 1) + 9) * (2 * (n + 1)) ^ (k + 2) := by
  have h1 : 2 ^ lam n ≤ 2 * (n + 1) := by
    unfold lam
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [pow_succ]
      have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hn)
      omega
  have : m0 k n = lam n * (k + 2) + (3 * (k + 1) + 9) := by unfold m0; ring
  rw [this, pow_add, pow_mul, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)

theorem Lk_mem_PPoly (k : ℕ) : Lk k ∈ PPoly := by
  refine ⟨Polynomial.C (5 * 2 ^ (3 * (k + 1) + 9) * 2 ^ (k + 2)) * (Polynomial.X + 1) ^ (k + 2), ?_⟩
  intro n
  have hmm : mm k n ≤ n := min_le_right _ _
  obtain ⟨gs, out, ok, len, _, ev⟩ :=
    PEqualNP.MetaComplexity.Helpers.shannon (mm k n) (G k n) n hmm
  refine ⟨⟨gs, out⟩, ok, ?_, ?_⟩
  · have h1 : gs.length ≤ 5 * 2 ^ mm k n := by omega
    have h2 : 2 ^ mm k n ≤ 2 ^ m0 k n := Nat.pow_le_pow_right (by omega) (min_le_left _ _)
    have h3 := m0_le_pow k n
    have h4 : (2 * (n + 1)) ^ (k + 2) = 2 ^ (k + 2) * (n + 1) ^ (k + 2) := mul_pow _ _ _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    show gs.length ≤ _
    calc gs.length ≤ 5 * 2 ^ mm k n := h1
      _ ≤ 5 * (2 ^ (3 * (k + 1) + 9) * (2 * (n + 1)) ^ (k + 2)) :=
          Nat.mul_le_mul_left _ (h2.trans h3)
      _ = _ := by rw [h4]; ring
  · intro x hx
    have h := ev x hx
    have hm := mem_Lk k n x hx
    rw [hm]
    show (_ : Bool) = true ↔ _
    have : (PEqualNP.MetaComplexity.Helpers.wiresFrom gs x).getD out false =
        G k n (fun i : Fin (mm k n) => x.getD (i : ℕ) false) := h
    exact this ▸ Iff.rfl

theorem Lk_not_SIZE (k : ℕ) (c : ℕ) : Lk k ∉ SIZE (fun n => c * n ^ k + c) := by
  intro hL
  -- choose n = 2 ^ t
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
  obtain ⟨C, hC, hsz, hdec⟩ := hL n
  have hcl : c * n ^ k + c ≤ n ^ (k + 1) := by
    have : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn0
    have h1 : c ≤ c * n ^ k := Nat.le_mul_of_pos_right _ this
    have h2 : 2 * c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul_right _ (by omega)
    rw [pow_succ]; nlinarith
  have hcnt : count n (n ^ (k + 1)) < 2 ^ 2 ^ mm k n := by rw [hmm]; exact count_lt k n hn2
  have hspec := Classical.choose_spec
    (exists_hard_pad n (n ^ (k + 1)) (mm k n) (min_le_right _ _) hcnt)
  obtain ⟨v, hv⟩ := hspec C hC (hsz.trans hcl)
  apply hv
  have hGdef : G k n = Classical.choose
      (exists_hard_pad n (n ^ (k + 1)) (mm k n) (min_le_right _ _) hcnt) := by
    simp [G, hcnt]
  have hlen : (List.ofFn v ++ List.replicate (n - mm k n) false).length = n := by
    simp; have := min_le_right (m0 k n) n; unfold mm; omega
  have h1 := hdec _ hlen
  have hx : (List.ofFn v ++ List.replicate (n - mm k n) false) ∈ Lk k ↔ G k n v = true := by
    rw [mem_Lk k n _ hlen]
    have : (fun i : Fin (mm k n) => (List.ofFn v ++ List.replicate (n - mm k n) false).getD
        (i : ℕ) false) = v := by
      funext i
      rw [List.getD_append _ _ _ _ (by simp)]
      simp
    rw [this]
  rw [hx, hGdef] at h1
  exact Bool.eq_iff_iff.mpr h1

theorem size_hierarchy (k : ℕ) :
    ∃ L : Language Bool, L ∈ PPoly ∧ ∀ c : ℕ, L ∉ SIZE (fun n => c * n ^ k + c) :=
  ⟨Lk k, Lk_mem_PPoly k, Lk_not_SIZE k⟩

end PEqualNP.General.SizeHierarchy
