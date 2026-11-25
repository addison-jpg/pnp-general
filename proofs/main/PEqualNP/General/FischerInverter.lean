import PEqualNP.General.FischerBasic

/-!
# Fischer's construction, part 2: the inverter with `⌈log₂ (n + 1)⌉` NOT gates

Threshold functions by dynamic programming, the binary digits of the number of ones computed
from the top with one NOT gate each, the negated inputs from the digits and thresholds, and the
dual rail of `FischerBasic` on top.
-/

namespace PEqualNP.General.Fischer

open PEqualNP.CircuitLowerBounds

/-- The number of `l < j` with `b l`. -/
def cntF (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cntF b j + (b j).toNat

theorem cntF_le (b : ℕ → Bool) (j : ℕ) : cntF b j ≤ j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [cntF]; cases b j <;> simp <;> omega

/-! ### Thresholds by dynamic programming -/

/-- The wire of `T_k` (at least `k` of the first `j` variables) in the threshold table. -/
def dpW (B K t f : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then t else f
  | j + 1, k => if k = 0 then t else B + 2 * K * j + 2 * (k - 1) + 1

/-- The threshold table over the variables `vf 0, vf 1, …`, after `j` layers. -/
def dpSt (n K t f : ℕ) (vf : ℕ → ℕ) (gs : List Gate) : ℕ → List Gate
  | 0 => gs
  | j + 1 => pairBlk n (fun k => [vf j, dpW (n + gs.length) K t f j k])
      (fun k => dpW (n + gs.length) K t f j (k + 1)) (dpSt n K t f vf gs j) K

theorem dpSt_length (n K t f : ℕ) (vf : ℕ → ℕ) (gs : List Gate) (j : ℕ) :
    (dpSt n K t f vf gs j).length = gs.length + 2 * K * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [dpSt, pairBlk_length, ih]; ring

theorem dpSt_ext (n K t f : ℕ) (vf : ℕ → ℕ) (gs : List Gate) (j : ℕ) :
    Ext gs (dpSt n K t f vf gs j) 0 := by
  induction j with
  | zero => exact Ext.refl gs
  | succ j ih => exact ih.trans (pairBlk_ext _ _ _ _ (fun k => by simp) K)

theorem thr_step (b : Bool) (c k : ℕ) :
    (decide (k + 1 ≤ c) || b && decide (k ≤ c)) = decide (k + 1 ≤ c + b.toNat) := by
  cases b <;> simp <;> omega

theorem dp_spec (n K t f : ℕ) (vf : ℕ → ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (J : ℕ) (ht : t < n + gs.length) (hvt : V gs x t = true)
    (hf : f < n + gs.length) (hvf : V gs x f = false)
    (hv : ∀ l < J, vf l < n + gs.length) :
    ∀ j ≤ J, ∀ k ≤ K, dpW (n + gs.length) K t f j k < n + (dpSt n K t f vf gs j).length ∧
      V (dpSt n K t f vf gs j) x (dpW (n + gs.length) K t f j k) =
        decide (k ≤ cntF (fun l => V gs x (vf l)) j) := by
  intro j hj
  induction j with
  | zero =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; simp [dpW, ht, hvt, dpSt]
    · simp [dpW, h0, hf, hvf, dpSt, cntF]
  | succ j ih =>
    intro k hk
    have ih' := ih (by omega)
    set st := dpSt n K t f vf gs j with hst
    have hlen : st.length = gs.length + 2 * K * j := dpSt_length _ _ _ _ _ _ _
    have hext : Ext gs st 0 := dpSt_ext _ _ _ _ _ _ _
    have hlen1 : (dpSt n K t f vf gs (j + 1)).length = gs.length + 2 * K * (j + 1) :=
      dpSt_length _ _ _ _ _ _ _
    have hext1 : Ext gs (dpSt n K t f vf gs (j + 1)) 0 := dpSt_ext _ _ _ _ _ _ _
    by_cases h0 : k = 0
    · subst h0
      simp only [dpW, ite_true, Nat.zero_le, decide_true]
      refine ⟨by rw [hlen1]; omega, ?_⟩
      rw [hext1.V x t (by omega), hvt]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hidx : dpW (n + gs.length) K t f (j + 1) (k' + 1) = n + st.length + 2 * k' + 1 := by
      simp only [dpW]; simp; rw [hlen]; ring
    rw [hidx]
    refine ⟨by rw [hlen1, hlen, Nat.mul_succ]; omega, ?_⟩
    have hj' : j < J := by omega
    have h1 := V_pairBlk n (fun k => [vf j, dpW (n + gs.length) K t f j k])
      (fun k => dpW (n + gs.length) K t f j (k + 1)) st x hx (show k' < K by omega)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have := hv j hj'; omega
        · exact (ih' k' (by omega)).1)
      (by have := (ih' (k' + 1) hk).1; omega)
    have e : dpSt n K t f vf gs (j + 1) = pairBlk n (fun k => [vf j, dpW (n + gs.length) K t f j k])
      (fun k => dpW (n + gs.length) K t f j (k + 1)) st K := rfl
    rw [e, h1]
    have hp : Pre st (pairBlk n (fun k => [vf j, dpW (n + gs.length) K t f j k])
        (fun k => dpW (n + gs.length) K t f j (k + 1)) st K) := pairBlk_pre _ _ _ st (Nat.zero_le K)
    rw [hp.V x _ (by rw [hx]; exact (ih' (k' + 1) hk).1)]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [(ih' (k' + 1) hk).2, (ih' k' (by omega)).2, hext.V x _ (by have := hv j hj'; omega)]
    simp only [cntF]
    exact thr_step _ _ _

/-! ### OR of ANDs of pairs -/

/-- The wire of the running OR after `q` pairs (`f` for none). -/
def accIdx (B f q : ℕ) : ℕ := if q = 0 then f else B + 2 * q - 1

/-- `OR_{q < Q} (H q ∧ T q)`, as a chain; the result is at `accIdx (n + gs.length) f Q`. -/
def orBlk (n f : ℕ) (H T : ℕ → ℕ) (gs : List Gate) (Q : ℕ) : List Gate :=
  pairBlk n (fun q => [H q, T q]) (fun q => accIdx (n + gs.length) f q) gs Q

theorem orBlk_length (n f : ℕ) (H T : ℕ → ℕ) (gs : List Gate) (Q : ℕ) :
    (orBlk n f H T gs Q).length = gs.length + 2 * Q := pairBlk_length _ _ _ _ _

theorem orBlk_ext (n f : ℕ) (H T : ℕ → ℕ) (gs : List Gate) (Q : ℕ) :
    Ext gs (orBlk n f H T gs Q) 0 := pairBlk_ext _ _ _ _ (fun q => by simp) Q

theorem orBlk_spec (n f : ℕ) (H T : ℕ → ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (Q : ℕ) (hf : f < n + gs.length) (hvf : V gs x f = false)
    (hH : ∀ q < Q, H q < n + gs.length) (hT : ∀ q < Q, T q < n + gs.length) :
    ∀ q ≤ Q, accIdx (n + gs.length) f q < n + (orBlk n f H T gs Q).length ∧
      V (orBlk n f H T gs Q) x (accIdx (n + gs.length) f q) =
        (List.range q).any fun q' => V gs x (H q') && V gs x (T q') := by
  have hlen := orBlk_length n f H T gs Q
  have hpre : Pre gs (orBlk n f H T gs Q) := (orBlk_ext n f H T gs Q).pre
  intro q hq
  induction q with
  | zero =>
    have e0 : accIdx (n + gs.length) f 0 = f := rfl
    rw [e0, hlen]
    refine ⟨by omega, ?_⟩
    rw [hpre.V x f (by omega), hvf]; rfl
  | succ q ih =>
    obtain ⟨-, ih2⟩ := ih (by omega)
    have hidx : accIdx (n + gs.length) f (q + 1) = n + gs.length + 2 * q + 1 := by
      simp [accIdx]; omega
    rw [hidx, hlen]
    refine ⟨by omega, ?_⟩
    have h1 := V_pairBlk n (fun q => [H q, T q]) (fun q => accIdx (n + gs.length) f q) gs x hx
      (show q < Q by omega)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hH q (by omega)
        · exact hT q (by omega))
      (by unfold accIdx; split_ifs <;> omega)
    unfold orBlk
    rw [h1]
    unfold orBlk at ih2
    rw [ih2, List.range_succ, List.any_append]
    simp

/-! ### Arithmetic of binary digits -/

theorem div_two_pow_succ (N j : ℕ) : N / 2 ^ (j + 1) = N / 2 ^ j / 2 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem bit_any (N j d : ℕ) (hN : N / 2 ^ (j + 1) < 2 ^ d) :
    ((List.range (2 ^ d)).any fun q =>
      decide (N / 2 ^ (j + 1) = q) && decide ((2 * q + 1) * 2 ^ j ≤ N)) =
      decide (N / 2 ^ j % 2 = 1) := by
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  have key : ∀ q, (2 * q + 1) * 2 ^ j ≤ N ↔ 2 * q + 1 ≤ N / 2 ^ j := fun q =>
    (Nat.le_div_iff_mul_le hp).symm
  have hd := div_two_pow_succ N j
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, -, h1, h2⟩
    rw [key] at h2
    omega
  · intro h
    refine ⟨N / 2 ^ (j + 1), hN, rfl, ?_⟩
    rw [key]; omega

theorem bit_eq (N j q : ℕ) (b : Bool) (hb : b = decide (N / 2 ^ j % 2 = 1)) :
    (decide (N / 2 ^ (j + 1) = q / 2) && (if q % 2 = 1 then b else !b)) =
      decide (N / 2 ^ j = q) := by
  have hd := div_two_pow_succ N j
  subst hb
  rw [hd]
  generalize N / 2 ^ j = a
  by_cases hq : q % 2 = 1 <;> simp only [hq, ite_true, ite_false] <;>
    by_cases ha : a % 2 = 1 <;> simp [ha] <;> omega

/-! ### The binary digits of the number of ones -/

/-- Digit step `d` (digit `r - 1 - d`): from the wires `H q = [N / 2 ^ (r - d) = q]` to the
digit, its negation (the one NOT gate), and the wires `[N / 2 ^ (r - d - 1) = q]`. -/
def bitStep (n f r : ℕ) (T : ℕ → ℕ) (d : ℕ) (gs : List Gate) (H : ℕ → ℕ) : List Gate :=
  hBlk (fun q => ⟨GateOp.and, [H (q / 2),
      if q % 2 = 1 then accIdx (n + gs.length) f (2 ^ d)
      else n + (orBlk n f H (fun q => T ((2 * q + 1) * 2 ^ (r - 1 - d))) gs (2 ^ d)).length]⟩)
    (orBlk n f H (fun q => T ((2 * q + 1) * 2 ^ (r - 1 - d))) gs (2 ^ d) ++
      [⟨GateOp.not, [accIdx (n + gs.length) f (2 ^ d)]⟩]) (2 ^ (d + 1))

/-- The digit wires after `d` steps, and the wires `[N / 2 ^ (r - d) = q]`. -/
def bitsSt (n t f r : ℕ) (T : ℕ → ℕ) (gs : List Gate) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => (gs, fun _ => t)
  | d + 1 => ((bitStep n f r T d (bitsSt n t f r T gs d).1 (bitsSt n t f r T gs d).2),
      fun q => n + (bitsSt n t f r T gs d).1.length + 2 * 2 ^ d + 1 + q)

theorem bitStep_length (n f r : ℕ) (T : ℕ → ℕ) (d : ℕ) (gs : List Gate) (H : ℕ → ℕ) :
    (bitStep n f r T d gs H).length = gs.length + 4 * 2 ^ d + 1 := by
  simp only [bitStep, hBlk_length, List.length_append, orBlk_length, List.length_cons,
    List.length_nil, Nat.pow_succ]
  ring

theorem bitsSt_length (n t f r : ℕ) (T : ℕ → ℕ) (gs : List Gate) (d : ℕ) :
    (bitsSt n t f r T gs d).1.length + 5 ≤ gs.length + 5 * 2 ^ d := by
  induction d with
  | zero => simp [bitsSt]
  | succ d ih =>
    simp only [bitsSt, bitStep_length, Nat.pow_succ]
    have := Nat.one_le_two_pow (n := d)
    omega

theorem Ext.cast {a b : List Gate} {k l : ℕ} (h : Ext a b k) (e : k = l) : Ext a b l := e ▸ h

theorem any_range_congr {Q : ℕ} {p p' : ℕ → Bool} (h : ∀ q < Q, p q = p' q) :
    (List.range Q).any p = (List.range Q).any p' := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [List.range_succ, List.any_append, List.any_append, ih (fun q hq => h q (by omega)),
      List.any_cons, List.any_cons, h Q (by omega)]
    rfl

theorem bits_spec (n t f r : ℕ) (T : ℕ → ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (N : ℕ) (hN : N < 2 ^ r)
    (ht : t < n + gs.length) (hvt : V gs x t = true)
    (hf : f < n + gs.length) (hvf : V gs x f = false)
    (hT : ∀ k < 2 ^ r, T k < n + gs.length ∧ V gs x (T k) = decide (k ≤ N)) :
    ∀ d ≤ r, Ext gs (bitsSt n t f r T gs d).1 d ∧
      ∀ q < 2 ^ d, (bitsSt n t f r T gs d).2 q < n + (bitsSt n t f r T gs d).1.length ∧
        V (bitsSt n t f r T gs d).1 x ((bitsSt n t f r T gs d).2 q) =
          decide (N / 2 ^ (r - d) = q) := by
  intro d hd
  induction d with
  | zero =>
    refine ⟨Ext.refl gs, fun q hq => ?_⟩
    obtain rfl : q = 0 := by simpa using hq
    refine ⟨ht, ?_⟩
    simp [bitsSt, hvt, Nat.div_eq_of_lt hN]
  | succ d ih =>
    obtain ⟨hext, hH⟩ := ih (by omega)
    set st := (bitsSt n t f r T gs d).1 with hst
    set H := (bitsSt n t f r T gs d).2 with hHdef
    set j := r - 1 - d with hj
    have hrj : r - d = j + 1 := by omega
    have hrj' : r - (d + 1) = j := by omega
    have hlenst := hext.length
    set T' := fun q => T ((2 * q + 1) * 2 ^ j) with hT'
    set st1 := orBlk n f H T' st (2 ^ d) with hst1
    set b := accIdx (n + st.length) f (2 ^ d) with hb
    have hpre0 : Pre gs st := hext.pre
    -- range facts
    have hkr : ∀ q < 2 ^ d, (2 * q + 1) * 2 ^ j < 2 ^ r := by
      intro q hq
      have e : 2 ^ r = 2 ^ (d + 1) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
      rw [e]
      apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos j)
      rw [Nat.pow_succ]; omega
    have hT'v : ∀ q < 2 ^ d, T' q < n + st.length ∧ V st x (T' q) =
        decide ((2 * q + 1) * 2 ^ j ≤ N) := by
      intro q hq
      obtain ⟨a1, a2⟩ := hT _ (hkr q hq)
      exact ⟨by simp only [hT']; omega, by simp only [hT']; rw [hpre0.V x _ (by omega), a2]⟩
    have hor := orBlk_spec n f H T' st x hx (2 ^ d) (by omega)
      (by rw [hpre0.V x _ (by omega), hvf]) (fun q hq => (hH q hq).1)
      (fun q hq => (hT'v q hq).1) (2 ^ d) le_rfl
    have hNd : N / 2 ^ (j + 1) < 2 ^ d := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      have : d + (j + 1) = r := by omega
      rw [this]; exact hN
    have hbv : V st1 x b = decide (N / 2 ^ j % 2 = 1) := by
      rw [hor.2, ← bit_any N j d hNd]
      apply any_range_congr
      intro q hq
      rw [(hH q hq).2, (hT'v q hq).2, hrj]
    set st2 := st1 ++ [⟨GateOp.not, [b]⟩] with hst2
    set nb := n + st1.length with hnb
    set g : ℕ → Gate := fun q => ⟨GateOp.and, [H (q / 2), if q % 2 = 1 then b else nb]⟩ with hg
    have e1 : (bitsSt n t f r T gs (d + 1)).1 = hBlk g st2 (2 ^ (d + 1)) := rfl
    have hl1 : st1.length = st.length + 2 * 2 ^ d := orBlk_length _ _ _ _ _ _
    have e2 : ∀ q, (bitsSt n t f r T gs (d + 1)).2 q = n + st2.length + q := by
      intro q
      show n + st.length + 2 * 2 ^ d + 1 + q = _
      rw [hst2, List.length_append, hl1]; simp; omega
    rw [e1]
    have hl2 : (hBlk g st2 (2 ^ (d + 1))).length = st2.length + 2 ^ (d + 1) := hBlk_length _ _ _
    have x1 : Ext st st1 0 := orBlk_ext _ _ _ _ _ _
    have x2 : Ext st1 st2 1 := Ext.snoc_not st1 [b] (by simp)
    have x3 : Ext st2 (hBlk g st2 (2 ^ (d + 1))) (0 * 2 ^ (d + 1)) :=
      hBlk_ext g st2 0 (fun q => by simp [hg, GoodG]) (fun q => nots_and _) _
    refine ⟨(((hext.trans x1).trans x2).trans x3).cast (by omega), fun q hq => ?_⟩
    rw [e2]
    have hst2l : st2.length = st1.length + 1 := by simp [hst2]
    refine ⟨by rw [hl2]; omega, ?_⟩
    have hb1 : b < n + st1.length := by
      rw [← hnb]; exact hor.1
    have hH2 : H (q / 2) < n + st.length := (hH (q / 2) (by rw [Nat.pow_succ] at hq; omega)).1
    have hin : ∀ i ∈ (g q).inputs, i < x.length + st2.length := by
      intro i hi
      rw [hx, hst2l]
      simp only [hg, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; omega
      · rw [h]; split_ifs
        · omega
        · rw [hnb]; omega
    have hv := V_hBlk g st2 x hq hin
    rw [hx] at hv
    rw [hv]
    have p12 : Pre st1 st2 := pre_append _ _
    have p02 : Pre st st2 := x1.pre.trans p12
    have vH : V st2 x (H (q / 2)) = decide (N / 2 ^ (j + 1) = q / 2) := by
      rw [p02.V x _ (by omega), (hH (q / 2) (by rw [Nat.pow_succ] at hq; omega)).2, hrj]
    have vb : V st2 x b = decide (N / 2 ^ j % 2 = 1) := by
      rw [p12.V x _ (by omega), hbv]
    have vnb : V st2 x nb = !decide (N / 2 ^ j % 2 = 1) := by
      have := V_snoc st1 ⟨GateOp.not, [b]⟩ x
      rw [hx] at this
      rw [hnb, hst2, this]
      simp [GateOp.eval, hbv]
    rw [hrj', ← bit_eq N j q _ rfl]
    simp only [hg, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id]
    rw [vH]
    split_ifs
    · rw [vb]
    · rw [vnb]

/-! ### Counting -/

theorem cntF_congr {b b' : ℕ → Bool} {j : ℕ} (h : ∀ l < j, b l = b' l) : cntF b j = cntF b' j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [cntF]; rw [ih (fun l hl => h l (by omega)), h j (by omega)]

theorem cntF_erase (b : ℕ → Bool) (i j : ℕ) :
    cntF (fun l => if l = i then false else b l) j + (if i < j then (b i).toNat else 0) =
      cntF b j := by
  induction j with
  | zero => simp [cntF]
  | succ j ih =>
    simp only [cntF]
    by_cases hj : j = i
    · subst hj
      simp only [if_true, Bool.toNat_false, Nat.add_zero, Nat.lt_irrefl, if_false] at ih ⊢
      simp only [Nat.lt_succ_self, if_true]; omega
    · simp only [hj, if_false]
      by_cases hij : i < j
      · simp only [hij, if_true] at ih
        simp only [show i < j + 1 by omega, if_true]; omega
      · simp only [hij, if_false] at ih
        simp only [show ¬ i < j + 1 by omega, if_false]; omega

/-! ### The negated inputs -/

/-- For `i < I`: `OR_{k < K} ([N = k] ∧ T_k(x with input i set to 0))`, which is `¬ x_i`. -/
def negSt (n f K : ℕ) (Hr : ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (gs : List Gate) : ℕ → List Gate
  | 0 => gs
  | i + 1 => orBlk n f Hr (TI i) (negSt n f K Hr TI gs i) K

/-- The wire of the `i`-th negated input. -/
def negW (B K f i : ℕ) : ℕ := accIdx (B + 2 * K * i) f K

theorem negSt_length (n f K : ℕ) (Hr : ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (gs : List Gate) (i : ℕ) :
    (negSt n f K Hr TI gs i).length = gs.length + 2 * K * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [negSt, orBlk_length, ih]; ring

theorem negSt_ext (n f K : ℕ) (Hr : ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (gs : List Gate) (i : ℕ) :
    Ext gs (negSt n f K Hr TI gs i) 0 := by
  induction i with
  | zero => exact Ext.refl gs
  | succ i ih => exact ih.trans (orBlk_ext _ _ _ _ _ _)

theorem any_eq_le (N K c : ℕ) (h : N < K) :
    ((List.range K).any fun k => decide (N = k) && decide (k ≤ c)) = decide (N ≤ c) := by
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, rfl, h⟩; exact h
  · intro h'; exact ⟨N, h, rfl, h'⟩

theorem neg_spec (n f K : ℕ) (Hr : ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (gs : List Gate) (x : List Bool)
    (hx : x.length = n) (I N : ℕ) (c : ℕ → ℕ) (hNK : N < K)
    (hf : f < n + gs.length) (hvf : V gs x f = false)
    (hHr : ∀ k < K, Hr k < n + gs.length ∧ V gs x (Hr k) = decide (N = k))
    (hTI : ∀ i < I, ∀ k < K, TI i k < n + gs.length ∧ V gs x (TI i k) = decide (k ≤ c i)) :
    ∀ i' ≤ I, ∀ i < i', negW (n + gs.length) K f i < n + (negSt n f K Hr TI gs i').length ∧
      V (negSt n f K Hr TI gs i') x (negW (n + gs.length) K f i) = decide (N ≤ c i) := by
  intro i' hi'
  induction i' with
  | zero => intro i hi; omega
  | succ i' ih =>
    intro i hi
    set st := negSt n f K Hr TI gs i' with hst
    have hext : Ext gs st 0 := negSt_ext _ _ _ _ _ _ _
    have hlen : st.length = gs.length + 2 * K * i' := negSt_length _ _ _ _ _ _ _
    have e : negSt n f K Hr TI gs (i' + 1) = orBlk n f Hr (TI i') st K := rfl
    have hl1 : (orBlk n f Hr (TI i') st K).length = st.length + 2 * K := orBlk_length _ _ _ _ _ _
    have hp : Pre st (orBlk n f Hr (TI i') st K) := (orBlk_ext _ _ _ _ _ _).pre
    rw [e, hl1]
    rcases Nat.lt_or_ge i i' with h | h
    · obtain ⟨a1, a2⟩ := ih (by omega) i h
      exact ⟨by omega, by rw [hp.V x _ (by rw [hx]; exact a1), a2]⟩
    · obtain rfl : i = i' := by omega
      have hpre := hext.pre
      have hsp := orBlk_spec n f Hr (TI i) st x hx K (by omega)
        (by rw [hpre.V x f (by omega), hvf])
        (fun q hq => by have := (hHr q hq).1; omega)
        (fun q hq => by have := (hTI i (by omega) q hq).1; omega) K le_rfl
      have hidx : negW (n + gs.length) K f i = accIdx (n + st.length) f K := by
        simp only [negW, hlen]; congr 1; omega
      rw [hidx, ← hl1]
      refine ⟨hsp.1, ?_⟩
      rw [hsp.2, ← any_eq_le N K (c i) hNK]
      apply any_range_congr
      intro k hk
      rw [hpre.V x _ (by have := (hHr k hk).1; omega), (hHr k hk).2,
        hpre.V x _ (by have := (hTI i (by omega) k hk).1; omega), (hTI i (by omega) k hk).2]

/-! ### All threshold tables -/

/-- The variables of table `i`: input `i` replaced by the constant-false wire `n + 1`. -/
def vfI (n i l : ℕ) : ℕ := if l = i then n + 1 else l

/-- The constants: wire `n` is `true`, wire `n + 1` is `false`. -/
def consts : List Gate := [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩]

/-- Tables `0, …, i - 1`. -/
def dpAll (n K : ℕ) : ℕ → List Gate
  | 0 => consts
  | i + 1 => dpSt n K n (n + 1) (vfI n i) (dpAll n K i) n

/-- The wire of `T_k` in table `i`. -/
def TI (n K i k : ℕ) : ℕ := dpW (n + 2 + 2 * K * n * i) K n (n + 1) n k

theorem dpAll_length (n K i : ℕ) : (dpAll n K i).length = 2 + 2 * K * n * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [dpAll, dpSt_length, ih]; ring

theorem consts_ext : Ext [] consts 0 := by
  simpa [consts] using (Ext.snoc_and [] [] (by simp)).trans (Ext.snoc_or [⟨GateOp.and, []⟩] [] (by simp))

theorem consts_val (x : List Bool) :
    V consts x x.length = true ∧ V consts x (x.length + 1) = false := by
  constructor
  · simpa [GateOp.eval, consts] using V_pair_fst [] ⟨GateOp.and, []⟩ ⟨GateOp.or, []⟩ x
  · simpa [GateOp.eval, consts] using V_pair_snd [] ⟨GateOp.and, []⟩ ⟨GateOp.or, []⟩ x

theorem dpAll_spec (n K : ℕ) (x : List Bool) (hx : x.length = n) :
    ∀ i', Ext consts (dpAll n K i') 0 ∧ ∀ i < i', ∀ k ≤ K,
      TI n K i k < n + (dpAll n K i').length ∧
      V (dpAll n K i') x (TI n K i k) =
        decide (k ≤ cntF (fun l => if l = i then false else x.getD l false) n) := by
  intro i'
  induction i' with
  | zero => exact ⟨Ext.refl _, fun i hi => by omega⟩
  | succ i' ih =>
    obtain ⟨hext, hT⟩ := ih
    set st := dpAll n K i' with hst
    have hlen : st.length = 2 + 2 * K * n * i' := dpAll_length _ _ _
    have e : dpAll n K (i' + 1) = dpSt n K n (n + 1) (vfI n i') st n := rfl
    have hext1 : Ext st (dpSt n K n (n + 1) (vfI n i') st n) 0 := dpSt_ext _ _ _ _ _ _ _
    have hpre : Pre consts st := hext.pre
    obtain ⟨cv1, cv2⟩ := consts_val x
    rw [hx] at cv1 cv2
    have vt : V st x n = true := by rw [hpre.V x _ (by simp [consts, hx]), cv1]
    have vf : V st x (n + 1) = false := by rw [hpre.V x _ (by simp [consts, hx]), cv2]
    rw [e]
    refine ⟨hext.trans hext1, fun i hi k hk => ?_⟩
    rcases Nat.lt_or_ge i i' with h | h
    · obtain ⟨a1, a2⟩ := hT i h k hk
      exact ⟨by have := hext1.length; omega, by rw [hext1.V x _ (by rw [hx]; exact a1), a2]⟩
    · obtain rfl : i = i' := by omega
      have hd := dp_spec n K n (n + 1) (vfI n i) st x hx n (by omega) vt (by omega) vf
        (fun l hl => by unfold vfI; split_ifs <;> omega) n le_rfl k hk
      have hidx : dpW (n + st.length) K n (n + 1) n k = TI n K i k := by
        simp only [TI, hlen]; congr 1; ring
      rw [hidx] at hd
      refine ⟨hd.1, ?_⟩
      rw [hd.2]
      congr 2
      apply cntF_congr
      intro l hl
      unfold vfI
      split_ifs with h1
      · exact vf
      · exact V_input _ x l (by omega)

end PEqualNP.General.Fischer
