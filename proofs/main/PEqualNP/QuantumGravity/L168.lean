import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-168: the deterministic decision rule for P_CTC. For a language in P_CTC, with register
length `m = p (length of x)`, start from any `m`-bit register, apply the register map `2^m`
times and read the answer there: it says whether `x` is in the language. The rule takes
exponentially many steps of a polynomial-time circuit; turning it into a machine is gap
L-qg-169. -/

theorem PEqualNP.QuantumGravity.L168 :
    ∀ L ∈ PEqualNP.QuantumGravity.PCTC, ∃ (p : Polynomial ℕ)
      (ans : List Bool × List Bool → Bool) (next : List Bool × List Bool → List Bool),
      PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
          Computability.encodeBool ans ∧
        PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
          (fun y : List Bool => y) next ∧
        ∀ (x : List Bool) (r₀ : List.Vector Bool (p.eval x.length)),
          (x ∈ L ↔ ans (x, ((PEqualNP.QuantumGravity.ctcRegisterMap next x
            (p.eval x.length))^[2 ^ p.eval x.length] r₀).toList) = true) :=
  fun _ hL => PEqualNP.QuantumGravity.Helpers.PCTC_iterate_rule hL
