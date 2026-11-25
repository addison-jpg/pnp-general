import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-166: Brun's counter on a register of bits. On input `x`, the circuit keeps the register
`r` when the test `φ (x, r)` holds and otherwise adds one to `r`, read as a binary number with
the least significant bit first, modulo `2^m`. If some `m`-bit register passes the test, every
Deutsch-consistent distribution of the induced register map charges only registers that pass
it. This is row L-qg-009 with the register read as a number modulo `2^m`, and the classical core
of NP inside P_CTC. -/

theorem PEqualNP.QuantumGravity.L166 :
    ∀ (φ : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
      (∃ s : List.Vector Bool m, φ (x, s.toList) = true) →
        ∀ μ : PMF (List.Vector Bool m),
          PEqualNP.QuantumGravity.DeutschConsistent
              (PEqualNP.QuantumGravity.ctcRegisterMap
                (fun q => if φ q = true then q.2 else PEqualNP.QuantumGravity.bitsSucc q.2) x m)
              μ →
            ∀ r ∈ μ.support, φ (x, r.toList) = true :=
  fun φ x m hs _ hμ _ hr => PEqualNP.QuantumGravity.Helpers.counter_register_support φ x m hs hμ hr
