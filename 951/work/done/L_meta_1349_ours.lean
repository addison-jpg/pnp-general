import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349_aux

def F (h : ℕ) (uv : ℕ × ℕ) : ℕ :=
  ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0
      else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) -
    (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0
      else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) *
    (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)

theorem val_mid (h i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ h + 1) :
    2 ^ h * (2 ^ h + 1) / 2 ^ (i - 1) = (2 ^ h + 1) * 2 ^ (h + 1 - i) := by
  have e : 2 ^ h * (2 ^ h + 1) = 2 ^ (i - 1) * ((2 ^ h + 1) * 2 ^ (h + 1 - i)) := by
    have : 2 ^ h = 2 ^ (i - 1) * 2 ^ (h + 1 - i) := by
      rw [← pow_add]; congr 1; omega
    calc 2 ^ h * (2 ^ h + 1) = (2 ^ (i - 1) * 2 ^ (h + 1 - i)) * (2 ^ h + 1) := by
          rw [← this]
      _ = 2 ^ (i - 1) * ((2 ^ h + 1) * 2 ^ (h + 1 - i)) := by ring
  rw [e, Nat.mul_div_cancel_left _ (by positivity)]

theorem half_sq (N : ℕ) (hN : 2 ∣ N) : N * N / 2 = N * (N / 2) := by
  obtain ⟨M, rfl⟩ := hN
  rw [show 2 * M * (2 * M) = 2 * (M * (2 * M)) by ring, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num)]
  ring

theorem key (h K a : ℕ) (hh : 1 ≤ h) (hK : 3 ≤ K) (ha : a + (K - 1) ≤ h + 2) :
    2 ^ h * 2 ^ h / 2 * (2 ^ (K - 1 - 1) - 1) ≤ F h (a, a + (K - 1)) := by
  set N := 2 ^ h with hNdef
  set d := K - 1 - 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hNe : 2 ∣ N := by
    rw [hNdef]; exact dvd_pow_self 2 (by omega)
  obtain ⟨M, hM⟩ := hNe
  have hM1 : 1 ≤ M := by omega
  have hhalf : N * N / 2 = N * M := by rw [half_sq N ⟨M, hM⟩, hM]; simp
  rw [hhalf]
  have hD : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  unfold F
  simp only
  by_cases hv : a + (K - 1) = h + 2
  · -- v = h + 2
    rw [if_pos hv]
    have hv0 : a + (K - 1) ≠ 0 := by omega
    rw [if_neg hv0, if_pos hv]
    by_cases ha0 : a = 0
    · -- K = h + 3, d = h + 1, 2 ^ d = 2 * N
      rw [if_pos ha0]
      have hdh : d = h + 1 := by omega
      have h2d : 2 ^ d = 2 * N := by rw [hdh, pow_succ, hNdef]; ring
      rw [h2d]
      have : 2 * N - 1 ≤ 2 * N := Nat.sub_le _ _
      calc N * M * (2 * N - 1) ≤ N * M * (2 * N) := Nat.mul_le_mul_left _ this
        _ = N * N * N := by rw [hM]; ring
        _ ≤ (N * N + N + 1 - 0) * N := by
            rw [Nat.sub_zero]; nlinarith
    · rw [if_neg ha0]
      have hah : a ≠ h + 2 := by omega
      rw [if_neg hah, val_mid h a (by omega) (by omega)]
      have hda : h + 1 - a = d := by omega
      rw [hda, Nat.sub_zero]
      -- ((N + 1) * 2 ^ d - N) * N ≥ N * M * (2 ^ d - 1)
      have hge : N * (2 ^ d - 1) ≤ (N + 1) * 2 ^ d - N := by
        have : N * (2 ^ d - 1) + N = N * 2 ^ d := by
          rw [Nat.mul_sub, Nat.mul_one]; have : N ≤ N * 2 ^ d := Nat.le_mul_of_pos_right _ (by positivity)
          omega
        have : N * 2 ^ d ≤ (N + 1) * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
        omega
      calc N * M * (2 ^ d - 1) ≤ N * N * (2 ^ d - 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ = (N * (2 ^ d - 1)) * N := by ring
        _ ≤ ((N + 1) * 2 ^ d - N) * N := Nat.mul_le_mul_right _ hge
  · -- v ≤ h + 1
    have hvle : a + (K - 1) ≤ h + 1 := by omega
    have hv0 : a + (K - 1) ≠ 0 := by omega
    rw [if_neg hv0, if_neg hv, if_neg hv, val_mid h (a + (K - 1)) (by omega) hvle]
    set e := h + 1 - (a + (K - 1)) with he
    -- weight: 2 ^ (v - 1) - 1, with 2 ^ (v - 1) * 2 ^ e = N
    have hsplit : 2 ^ (a + (K - 1) - 1) * 2 ^ e = N := by
      rw [← pow_add, hNdef]; congr 1; omega
    by_cases ha0 : a = 0
    · rw [if_pos ha0]
      have hvd : a + (K - 1) - 1 = d := by omega
      rw [hvd] at hsplit ⊢
      -- 2 * 2 ^ e ≤ N
      have hE : 2 * 2 ^ e ≤ N := by
        rw [← hsplit]; exact Nat.mul_le_mul_right _ hD
      have hEM : 2 ^ e ≤ M := by omega
      have hZ : (N + 1) * 2 ^ e ≤ N * M + M := by
        calc (N + 1) * 2 ^ e ≤ (N + 1) * M := Nat.mul_le_mul_left _ hEM
          _ = N * M + M := by ring
      have hY : N * N = 2 * (N * M) := by rw [hM]; ring
      have hXM : M ≤ N * M := Nat.le_mul_of_pos_left _ (by omega)
      have hA : N * M ≤ N * N + N + 1 - ((N + 1) * 2 ^ e - N) := by
        omega
      exact Nat.mul_le_mul_right _ hA
    · rw [if_neg ha0]
      have hah : a ≠ h + 2 := by omega
      rw [if_neg hah, val_mid h a (by omega) (by omega)]
      -- (N+1) * 2^(h+1-a) - N - ((N+1) * 2^e - N) >= (N+1) * 2^e * (2^(d+1) - 1)
      have hae : h + 1 - a = e + (d + 1) := by omega
      rw [hae, pow_add]
      have hX : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      rw [hX]
      set D := 2 ^ d with hDdef
      set E := 2 ^ e with hEdef
      set W := 2 ^ (a + (K - 1) - 1) with hWdef
      have hW2 : 2 ≤ W := by
        rw [hWdef]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a + (K - 1) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hdiff : (N + 1) * (E * (2 * D)) - N - ((N + 1) * E - N) = (N + 1) * E * (2 * D - 1) := by
        have h1 : (N + 1) * E ≤ (N + 1) * (E * (2 * D)) := by
          have : E ≤ E * (2 * D) := Nat.le_mul_of_pos_right _ (by omega)
          exact Nat.mul_le_mul_left _ this
        have h2 : N ≤ (N + 1) * E := by
          have : 1 ≤ E := Nat.one_le_two_pow
          nlinarith
        rw [Nat.mul_sub, Nat.mul_one]
        have : (N + 1) * E * (2 * D) = (N + 1) * (E * (2 * D)) := by ring
        omega
      rw [hdiff]
      -- (N+1) * E * (2D - 1) * (W - 1) >= N * M * (D - 1)
      have hWE : W * E = N := hsplit
      have hEW : N ≤ 2 * ((W - 1) * E) := by
        rw [Nat.sub_mul, Nat.one_mul, hWE]
        have : 2 * E ≤ N := by rw [← hWE]; exact Nat.mul_le_mul_right _ hW2
        omega
      have h2D : D - 1 ≤ 2 * D - 1 := by omega
      have hMN : N = 2 * M := hM
      calc N * M * (D - 1) ≤ N * M * (2 * D - 1) := Nat.mul_le_mul_left _ h2D
        _ ≤ (N + 1) * ((W - 1) * E) * (2 * D - 1) := by
            apply Nat.mul_le_mul_right
            have : M ≤ (W - 1) * E := by omega
            exact Nat.mul_le_mul (by omega) this
        _ = (N + 1) * E * (2 * D - 1) * (W - 1) := by ring

theorem pigeon (t K h : ℕ) (P : Finset ℕ) (hP : P.card + 1 ≤ 2 ^ t) (hK : 2 ≤ K)
    (hfit : (K - 1) * 2 ^ t ≤ h + 2) :
    ∃ a, a + (K - 1) ≤ h + 2 ∧ ∀ w ∈ P, ¬ (a < w ∧ w ≤ a + (K - 1)) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j ∈ Finset.range (2 ^ t), ∃ w ∈ P,
      j * (K - 1) < w ∧ w ≤ j * (K - 1) + (K - 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    apply hcon
    calc j * (K - 1) + (K - 1) = (j + 1) * (K - 1) := by ring
      _ ≤ 2 ^ t * (K - 1) := Nat.mul_le_mul_right _ hj
      _ = (K - 1) * 2 ^ t := by ring
      _ ≤ h + 2 := hfit
  choose! g hgP hg using hall
  have hinj : Set.InjOn g (Finset.range (2 ^ t) : Set ℕ) := by
    intro j1 hj1 j2 hj2 heq
    have k1 := hg j1 hj1
    have k2 := hg j2 hj2
    have hpos : 0 < K - 1 := by omega
    have d1 : (g j1 - 1) / (K - 1) = j1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have : (j1 + 1) * (K - 1) = j1 * (K - 1) + (K - 1) := by ring
        omega
    have d2 : (g j2 - 1) / (K - 1) = j2 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have : (j2 + 1) * (K - 1) = j2 * (K - 1) + (K - 1) := by ring
        omega
    rw [← d1, ← d2, heq]
  have := Finset.card_le_card_of_injOn g (fun j hj => hgP j hj) hinj
  rw [Finset.card_range] at this
  omega

end PEqualNP.Outside.L_meta_1349_aux

open PEqualNP.Outside.L_meta_1349_aux in
theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  set K := (h + 3 + 2 ^ t - 1) / 2 ^ t with hKdef
  by_cases hK : K ≤ 2
  · have : K - 1 - 1 = 0 := by omega
    rw [this]
    simp
  push_neg at hK
  have hne : (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (F h))).Nonempty := by
    apply Finset.Nonempty.image
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, Finset.card_empty,
      zero_add, true_and]
    exact Nat.one_le_two_pow
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  change _ ≤ WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (F h))).min
  rw [hm, WithTop.untopD_coe]
  obtain ⟨P, hP, hPm⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
  rw [← hPm]
  rw [Finset.mem_filter, Finset.mem_powerset] at hP
  have hfit : (K - 1) * 2 ^ t ≤ h + 2 := by
    have hpos : 0 < 2 ^ t := by positivity
    have h1 : K * 2 ^ t ≤ h + 3 + 2 ^ t - 1 := Nat.div_mul_le_self _ _
    have h2 : (K - 1) * 2 ^ t + 2 ^ t = K * 2 ^ t := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  obtain ⟨a, ha, hcut⟩ := pigeon t K h P hP.2 (by omega) hfit
  have hmem : (a, a + (K - 1)) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
      (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, hcut⟩
  exact le_trans (key h K a hh hK ha) (Finset.le_sup (f := F h) hmem)
