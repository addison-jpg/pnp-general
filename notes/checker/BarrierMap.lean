import PEqualNP.Library.L057
import PEqualNP.Library.L061
import PEqualNP.Library.L062
import PEqualNP.Library.L065
import PEqualNP.Library.L076
import PEqualNP.Library.L084
import PEqualNP.Library.L085

open PEqualNP.Library

-- Relativization map: neither P^A = NP^A nor P^A /= NP^A holds for every oracle A.
-- A physical resource used only as a black box is an oracle, so no such argument decides P vs NP.
theorem relativization_map :
    ¬ (∀ A : Language Bool, OracleP A = OracleNP A) ∧
    ¬ (∀ A : Language Bool, OracleP A ≠ OracleNP A) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨B, hB⟩ := PEqualNP.Library.L062
    exact hB (h B)
  · obtain ⟨A, hA⟩ := PEqualNP.Library.L061
    exact h A hA

-- Algebrization map: for every injective naming of field elements, neither inclusion
-- holds for every oracle with every multiquadratic extension.
theorem algebrization_map (codes : FieldCodes) (hc : FieldCodes.Injective codes) :
    ¬ (∀ (A : Language Bool) (E : AlgExtension), IsMultiquadraticExtension A E →
        OracleNP A ⊆ OracleP (extOracle codes E)) ∧
    ¬ (∀ (A : Language Bool) (E : AlgExtension), IsMultiquadraticExtension A E →
        ¬ OracleNP (extOracle codes E) ⊆ OracleP A) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨A, E, hE, hA⟩ := PEqualNP.Library.L065 codes hc
    exact hA (h A E hE)
  · obtain ⟨A, E, hE, hA⟩ := PEqualNP.Library.L076 codes hc
    exact h A E hE hA

-- The empty oracle is the unrelativized world: no added resource gives back P and NP,
-- and any added resource only enlarges P.
theorem empty_oracle_map :
    OracleP (∅ : Set (List Bool)) = P ∧ OracleNP (∅ : Set (List Bool)) = NP ∧
    ∀ A : Language Bool, P ⊆ OracleP A :=
  ⟨PEqualNP.Library.L084, PEqualNP.Library.L085, PEqualNP.Library.L057⟩

#print axioms relativization_map
#print axioms algebrization_map
#print axioms empty_oracle_map
