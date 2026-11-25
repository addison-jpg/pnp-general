import PEqualNP.W951.Hard
import PEqualNP.W951.FracMatch

/-! Bridge: FracMatch (fractional charge, weaker than MatchG / Gap-G) on the hard case closes it. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- FracMatch under the hard-case hypotheses (minus the size assumption). A route, not the sorry. -/
def FracMatchHard : Prop :=
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
    FracMatch S gates out

/-- Proved bridge: FracMatch on the hard case closes the hard case. -/
theorem hardCase_of_fracMatch (hF : FracMatchHard) : HardCase := by
  intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt
  have hb := bound_of_fracMatch S gates out
    (hF S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N)
  omega

end PEqualNP.Outside.L_meta_951_aux
