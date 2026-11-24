import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-163: why P_CTC asks for every consistent distribution. If the definition asked only
for some Deutsch-consistent distribution on whose registers the answer is right, every language,
even an undecidable one, would qualify: the circuit leaves a one-bit register unchanged, so the
point mass on the bit "x is in L" is consistent, and the read-out answers that bit. -/

theorem PEqualNP.QuantumGravity.L163 :
    ∀ L : Language Bool, ∃ (p : Polynomial ℕ) (ans : List Bool × List Bool → Bool)
      (next : List Bool × List Bool → List Bool),
      PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
          Computability.encodeBool ans ∧
        PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
          (fun y : List Bool => y) next ∧
        ∀ x : List Bool, ∃ μ : PMF (List.Vector Bool (p.eval x.length)),
          PEqualNP.QuantumGravity.DeutschConsistent
              (PEqualNP.QuantumGravity.ctcRegisterMap next x (p.eval x.length)) μ ∧
            ∀ r ∈ μ.support, (ans (x, r.toList) = true ↔ x ∈ L) :=
  PEqualNP.QuantumGravity.Helpers.some_consistent_decides
