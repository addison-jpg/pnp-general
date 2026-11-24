import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.TwoWorld
import PEqualNP.W951.Small3
import PEqualNP.W951.GapG

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The hard branch: some NOT gate is false at some zero point `Zof (S w)`. Derived from the
only open statement `no_minCE` (`hard_case`, Final.lean) and implies it (`no_minCE_of_hardCase`,
MinCE.lean). -/
def HardCase : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates)
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1)),
    False

/-- The hard case after the Two-World reduction: the hard case WITH some DD set
(C1 true at the zero point of S, and C0 false at some unit vector of S). -/
def HardCaseDD : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates)
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1))
    (hDD : ∃ w, val (C1 gates) (Zof (S w)) (out w) = true ∧
      ∃ u ∈ S w, val (C0 gates) (eof u) (out w) = false),
    False

/-- The hard case after T1 (front, Small3.lean): additionally some set has at least 4 elements. -/
def HardCaseDD4 : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates)
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1))
    (hDD : ∃ w, val (C1 gates) (Zof (S w)) (out w) = true ∧
      ∃ u ∈ S w, val (C0 gates) (eof u) (out w) = false)
    (h4 : ∃ w, 4 ≤ (S w).card),
    False

/-- Proved: if every set has at most 3 elements, T1 (`small3_bound`) already contradicts `hlt`. -/
theorem hardCaseDD_of_4 (h : HardCaseDD4) : HardCaseDD := by
  intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD
  by_cases h4 : ∃ w, 4 ≤ (S w).card
  · exact h S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD h4
  · push_neg at h4
    have := small3_bound S h2 hS gates out hg hU hev hclean (fun w => by have := h4 w; omega)
    omega

/-- Proved: without a DD set the Two-World count (`bound_of_noDD`) already contradicts `hlt`. -/
theorem hardCase_of_DD (h : HardCaseDD) : HardCase := by
  intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt
  by_cases hd : ∃ w, val (C1 gates) (Zof (S w)) (out w) = true ∧
      ∃ u ∈ S w, val (C0 gates) (eof u) (out w) = false
  · exact h S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hd
  · have hno : ∀ w, val (C1 gates) (Zof (S w)) (out w) = false ∨
        ∀ u ∈ S w, val (C0 gates) (eof u) (out w) = true := by
      intro w
      cases hA : val (C1 gates) (Zof (S w)) (out w)
      · exact Or.inl rfl
      · refine Or.inr fun u hu => ?_
        cases hB : val (C0 gates) (eof u) (out w)
        · exact absurd ⟨w, hA, u, hu, hB⟩ hd
        · rfl
    have := bound_of_noDD S hS gates out hg hev hno
    omega

/-- A sufficient condition, not the open statement itself: under the hard-case hypotheses
(minus the size assumption), some test system per set has pairwise disjoint counts.
STRONGER than `HardCase`; it may fail even if 951 is true, so it is a route, not the sorry. -/
def GapGHard : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates),
    GapG S gates out

/-- Proved bridge: Gap-G on the hard case closes the hard case. -/
theorem hardCase_of_gapG (hG : GapGHard) : HardCase := by
  intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt
  have hb := bound_of_gapG S gates out hev
    (hG S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N)
  omega

end PEqualNP.Outside.L_meta_951_aux
