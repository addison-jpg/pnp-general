import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.Charge
import PEqualNP.Kernel.Circuit
import PEqualNP.Kernel.W951Core

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Cone-restricted charging: gates outside a read-closed set `K` become constants -/

def mask (K : Finset ℕ) (gs : List Gate) : List Gate :=
  gs.mapIdx fun k g => if k ∈ K then g else ⟨GateOp.or, []⟩

theorem mask_snoc (K : Finset ℕ) (gs : List Gate) (g : Gate) :
    mask K (gs ++ [g]) = mask K gs ++ [if gs.length ∈ K then g else ⟨GateOp.or, []⟩] := by
  simp [mask, List.mapIdx_append]

theorem mask_length (K : Finset ℕ) (gs : List Gate) : (mask K gs).length = gs.length := by
  simp [mask]

theorem mask_range (gs : List Gate) (L : ℕ) (hL : gs.length ≤ L) :
    mask (Finset.range L) gs = gs := by
  induction gs using List.reverseRecOn with
  | nil => simp [mask]
  | append_singleton gs g ih =>
    rw [mask_snoc, ih (by simp at hL; omega)]
    have : gs.length ∈ Finset.range L := by simp at hL ⊢; omega
    simp [this]

/-- `K` is closed under reads (up to wire `n + L`). -/
def ReadClosed (n L : ℕ) (K : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), k ∈ K → ∀ i ∈ (gs[k]'hk).inputs, n ≤ i → i < n + L → i - n ∈ K

/-- The list evaluator `val` satisfies the kernel's snoc law (this is `val_snoc`). -/
theorem val_snocLaw {n : ℕ} (x : Fin n → Bool) :
    Kernel.SnocLaw n (fun (g : Gate) v => g.op.eval (g.inputs.map v)) (fun gs => val gs x) :=
  fun gs g i => val_snoc gs g x i

/-- From the kernel transfer lemma `Kernel.SnocLaw.mapIdx_congr`. -/
theorem val_mask {n : ℕ} (K : Finset ℕ) (L : ℕ) (x : Fin n → Bool) :
    ∀ gs : List Gate, gs.length ≤ L → ReadClosed n L K gs →
      ∀ i, (i < n ∨ i - n ∈ K ∨ n + gs.length ≤ i) → val (mask K gs) x i = val gs x i :=
  fun gs hL hcl i hi => Kernel.val_mask_viaDag K L x gs hL hcl i hi

/-- Cone-restricted charging hypothesis: each set `w` uses a read-closed `K w` containing its
output and counts `D` in the circuit where gates outside `K w` are constants. -/
def ChargeOKc {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ (Q : Fin m → Finset (Fin n)) (K : Fin m → Finset ℕ), (∀ w, S w ⊆ Q w) ∧
    (∀ w, ReadClosed n gates.length (K w) gates) ∧
    (∀ w, out w < n ∨ out w - n ∈ K w ∨ n + gates.length ≤ out w) ∧
    (∀ w, Good (Q w) (mask (K w) gates)) ∧
    ∑ w, (D (Q w) (S w) (mask (K w) gates)).card ≤ gates.length

theorem L951_core_c {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hc : ChargeOKc S gates out) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨Q, K, hSQ, hcl, hout, hgood, hsum⟩ := hc
  have hevm : ∀ (w : Fin m) (x : Fin n → Bool),
      val (mask (K w) gates) x (out w) = decide (∃ v ∈ S w, x v = true) := by
    intro w x
    rw [val_mask (K w) gates.length x gates le_rfl (hcl w) (out w) (hout w)]
    exact hev w x
  have hbound : ∀ w, (S w).card - 1 ≤ (D (Q w) (S w) (mask (K w) gates)).card := by
    intro w
    obtain ⟨l, hinv, hcard⟩ := main_inv (Q w) (S w) (mask (K w) gates) (hgood w)
    have hz : val (mask (K w) gates) (Zof (Q w)) (out w) = false := by
      rw [hevm, decide_eq_false_iff_not]
      rintro ⟨v, hv, hv'⟩
      simp [Zof, hSQ w hv] at hv'
    have he : ∀ u ∈ S w, val (mask (K w) gates) (eof u) (out w) = true := by
      intro u hu
      rw [hevm]
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, by simp [eof]⟩
    have h1 : ((S w).image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv (out w) u v hz (he u hu) (he v hv)).2 hu hv
    omega
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, (D (Q w) (S w) (mask (K w) gates)).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ ≤ gates.length := hsum

theorem val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    val gs x (n + j) = (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => val (gs.take j) x i) :=
  Kernel.listVal_gate gs x j hj

theorem val_mask_out {n : ℕ} (K : Finset ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : j < gs.length) (hjK : j ∉ K) : val (mask K gs) x (n + j) = false :=
  Kernel.val_mask_out_viaDag K gs x j hj hjK

theorem mem_mask {K : Finset ℕ} {gs : List Gate} {g : Gate} (h : g ∈ mask K gs) :
    ∃ (i : ℕ) (hi : i < gs.length), g = if i ∈ K then gs[i] else ⟨GateOp.or, []⟩ := by
  unfold mask at h
  obtain ⟨i, hi, hg⟩ := List.mem_mapIdx.mp h
  exact ⟨i, by simpa using hi, hg.symm⟩

/-- Masking away every NOT gate leaves only AND/OR gates, so every zero set is `Good`. -/
theorem good_mask_noNot {n : ℕ} (K : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hK : ∀ (i : ℕ) (hi : i < gs.length), i ∈ K → (gs[i]'hi).op ≠ GateOp.not)
    (Q : Finset (Fin n)) : Good Q (mask K gs) := by
  intro pre g rest hdec
  have hgm : g ∈ mask K gs := by rw [hdec]; simp
  left
  obtain ⟨i, hi, hgi⟩ := mem_mask hgm
  rw [hgi]
  split_ifs with h
  · have hm := hg (gs[i]'hi) (List.getElem_mem hi)
    rcases hm.1 with h1 | h1 | h1
    · exact ⟨Or.inl h1, hm.2⟩
    · exact ⟨Or.inr h1, hm.2⟩
    · exact absurd h1 (hK i hi h)
  · exact ⟨Or.inr rfl, by simp⟩

theorem mask_take (K : Finset ℕ) (gs : List Gate) (i : ℕ) :
    (mask K gs).take i = mask K (gs.take i) := by
  apply List.ext_getElem
  · simp [mask]
  · intro k h1 h2
    simp [mask, List.getElem_mapIdx]

theorem readClosed_take {n L : ℕ} {K : Finset ℕ} {gs : List Gate} (i : ℕ)
    (hcl : ReadClosed n L K gs) : ReadClosed n L K (gs.take i) := by
  intro k hk hkK j hj h1 h2
  have hk' : k < gs.length := by simp at hk; omega
  exact hcl k hk' hkK j (by simpa using hj) h1 h2

/-- Masking with a read-closed set keeps `Good`. -/
theorem good_mask_of_good {n : ℕ} (K : Finset ℕ) (gates : List Gate) (Q : Finset (Fin n))
    (hcl : ReadClosed n gates.length K gates) (hgood : Good Q gates) :
    Good Q (mask K gates) := by
  intro pre g rest hdec
  have hi : pre.length < gates.length := by
    have := congrArg List.length hdec; simp [mask_length] at this; omega
  have hpre : pre = mask K (gates.take pre.length) := by
    rw [← mask_take, hdec]; simp
  have hg : g = (mask K gates)[pre.length]'(by rw [mask_length]; exact hi) := by
    simp [hdec]
  have hgv : g = if pre.length ∈ K then gates[pre.length] else ⟨GateOp.or, []⟩ := by
    rw [hg]; simp [mask, List.getElem_mapIdx]
  by_cases hK : pre.length ∈ K
  · rw [if_pos hK] at hgv
    have hsplit : gates = gates.take pre.length ++ gates[pre.length] :: gates.drop (pre.length + 1) := by
      simp
    have horig := hgood _ _ _ hsplit
    have hmap : ∀ y : Fin n → Bool,
        (gates[pre.length].inputs.map fun j => val pre y j) =
          gates[pre.length].inputs.map fun j => val (gates.take pre.length) y j := by
      intro y
      apply List.map_congr_left
      intro j hj
      have e : val pre y j = val (mask K (gates.take pre.length)) y j :=
        congrArg (fun l => val l y j) hpre
      rw [e]
      apply val_mask K gates.length y (gates.take pre.length) (by simp) (readClosed_take _ hcl)
      by_cases hjn : j < n
      · exact Or.inl hjn
      · by_cases hjL : j < n + gates.length
        · exact Or.inr (Or.inl (hcl pre.length hi hK j hj (by omega) hjL))
        · right; right; simp; omega
    rw [hgv]
    rcases horig with h | h | h
    · exact Or.inl h
    · right; left; rw [hmap]; exact h
    · right; right; intro u; rw [hmap]; exact h u
  · rw [if_neg hK] at hgv
    rw [hgv]
    exact Or.inl ⟨Or.inr rfl, by simp⟩

/-- The cone of wire `o`: the intersection of all read-closed sets containing it. -/
noncomputable def coneOf (n : ℕ) (gates : List Gate) (o : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range gates.length).filter fun k => ∀ K : Finset ℕ,
    ReadClosed n gates.length K gates → (n ≤ o → o < n + gates.length → o - n ∈ K) → k ∈ K

theorem coneOf_closed (n : ℕ) (gates : List Gate) (o : ℕ) :
    ReadClosed n gates.length (coneOf n gates o) gates := by
  classical
  intro k hk hkK j hj h1 h2
  simp only [coneOf, Finset.mem_filter, Finset.mem_range] at hkK ⊢
  refine ⟨by omega, fun K hK ho => ?_⟩
  exact hK k hk (hkK.2 K hK ho) j hj h1 h2

theorem coneOf_out (n : ℕ) (gates : List Gate) (o : ℕ) :
    o < n ∨ o - n ∈ coneOf n gates o ∨ n + gates.length ≤ o := by
  classical
  by_cases h1 : o < n
  · exact Or.inl h1
  · by_cases h2 : o < n + gates.length
    · right; left
      simp only [coneOf, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, fun K _ ho => ho (by omega) h2⟩
    · right; right; omega

/-- Theorem X for cone-restricted charging. -/
theorem charge_of_pair_c {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (K : Fin m → Finset ℕ)
    (gates : List Gate) (out : Fin m → ℕ)
    (hSQ : ∀ w, S w ⊆ Q w) (hcl : ∀ w, ReadClosed n gates.length (K w) gates)
    (hout : ∀ w, out w < n ∨ out w - n ∈ K w ∨ n + gates.length ≤ out w)
    (hgood : ∀ w, Good (Q w) (mask (K w) gates))
    (hpair : ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1) :
    ChargeOKc S gates out := by
  classical
  refine ⟨Q, K, hSQ, hcl, hout, hgood, ?_⟩
  -- a counted wire of a masked circuit is a kept gate, where the mask agrees with the original
  have kept : ∀ w i, i ∈ D (Q w) (S w) (mask (K w) gates) →
      ∀ y : Fin n → Bool, val (mask (K w) gates) y i = val gates y i := by
    intro w i hi y
    simp only [D, Finset.mem_filter, Finset.mem_Ico, mask_length] at hi
    obtain ⟨⟨h1, h2⟩, -, u, -, -, -, -, hu, -⟩ := hi
    have hK : i - n ∈ K w := by
      by_contra hk
      have := val_mask_out (K w) gates (eof u) (i - n) (by omega) hk
      rw [show n + (i - n) = i by omega] at this
      rw [this] at hu
      exact absurd hu (by simp)
    exact val_mask (K w) gates.length y gates le_rfl (hcl w) i (Or.inr (Or.inl hK))
  have cross : ∀ a b : Fin m, ∀ i, i ∈ D (Q a) (S a) (mask (K a) gates) →
      i ∈ D (Q b) (S b) (mask (K b) gates) → 2 ≤ (S a ∩ Q b).card := by
    intro a b i hia hib
    have ka := kept a i hia
    have kb := kept b i hib
    simp only [D, Finset.mem_filter] at hia hib
    obtain ⟨-, -, u, v, huv, huR, hvR, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hu' : val (mask (K b) gates) (eof u) i = true := by rw [kb, ← ka]; exact hu
    have hv' : val (mask (K b) gates) (eof v) i = true := by rw [kb, ← ka]; exact hv
    have hub := inv_mem (Q b) _ (hgood b) i u hzb hu'
    have hvb := inv_mem (Q b) _ (hgood b) i v hzb hv'
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ Q b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huR, hub⟩
      · exact Finset.mem_inter.mpr ⟨hvR, hvb⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair huv] at this
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Q a) (S a) (mask (K a) gates)) (D (Q b) (S b) (mask (K b) gates)) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    have h1 := cross a b i hia hib
    have h2 := cross b a i hib hia
    rcases hpair a b hab with h | h <;> omega
  calc ∑ w, (D (Q w) (S w) (mask (K w) gates)).card
      ≤ (Finset.Ico n (n + gates.length)).card :=
        PEqualNP.Base.Matching.sum_card_le_of_pairwiseDisjoint _ _ _ hdisj fun w _ i hi => by
          simp only [D, Finset.mem_filter, mask_length] at hi
          exact hi.1
    _ = gates.length := by simp

theorem chargeOKc_of {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hc : ChargeOK S gates) : ChargeOKc S gates out := by
  obtain ⟨Q, hSQ, hgood, hsum⟩ := hc
  have hm : mask (Finset.range gates.length) gates = gates := mask_range gates _ le_rfl
  refine ⟨Q, fun _ => Finset.range gates.length, hSQ, ?_, ?_, ?_, ?_⟩
  · intro w k hk _ i _ h1 h2
    simp; omega
  · intro w
    by_cases h : out w < n
    · exact Or.inl h
    · by_cases h' : out w < n + gates.length
      · right; left; simp; omega
      · right; right; omega
  · intro w; rw [hm]; exact hgood w
  · simpa [hm] using hsum

end PEqualNP.Outside.L_meta_951_aux
