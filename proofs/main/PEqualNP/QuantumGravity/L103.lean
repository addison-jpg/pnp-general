import PEqualNP.QuantumGravity.Gaps
import PEqualNP.QuantumGravity.Helpers.PrefixSearch

/-! L-qg-103: P = NP inverts every polynomial-time function. If P = NP, every polynomial-time,
length-preserving `f : List Bool → List Bool` has a polynomial-time `g` with `f (g (f x)) = f x`
for every `x`. The proof is prefix search: the strings `pairB y p` such that some `w` has
`f (p ++ w) = y` form a language in NP (the witness is `w`); under P = NP it is decided in
polynomial time, and `|y|` calls to the decider extend the empty prefix one bit at a time to a
preimage of `y`. The contrapositive: a worst-case one-way function gives P ≠ NP. So the classical
one-way functions that quantum gravity hardness arguments assume (Aaronson's form of Harlow and
Hayden's argument for decoding Hawking radiation) cannot exist if P = NP. -/

theorem PEqualNP.QuantumGravity.L103 : PEqualNP.QuantumGravity.Gap.L103 :=
  fun hP f hf hlen =>
    PEqualNP.QuantumGravity.Helpers.PrefixSearch.invertible_of_P_eq_NP hP f hf hlen
