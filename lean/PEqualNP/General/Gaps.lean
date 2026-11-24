import PEqualNP.Defs

/-!
The open gaps of the general program (ids `L-gen-1NN`): lower bounds for circuits of AND, OR and
NOT gates with any number of NOT gates. Each gap is a `Prop` definition: this file states the gaps
and proves none of them, so it holds no `sorry`. L-gen-101 implies P ≠ NP; nothing here says that
P versus NP is settled.
-/

namespace PEqualNP.General.Gap

open PEqualNP.CircuitLowerBounds PEqualNP.General

/-- L-gen-101: some language in NP has no circuits of polynomial size. Every language in P has
them, so this gives P ≠ NP. This is the circuit form of the P versus NP problem. -/
def L101 : Prop :=
  ∃ L ∈ PEqualNP.Library.NP, L ∉ PPoly

/-- L-gen-102: the fixed-degree form. For every degree `k`, some language in NP has no circuits of
size `c * n ^ k + c`, whatever the constant `c`. The language may depend on `k`. Kannan (1982)
proves this with the second level of the polynomial hierarchy in place of NP; for NP it is open
for every `k ≥ 1`. -/
def L102 : Prop :=
  ∀ k : ℕ, ∃ L ∈ PEqualNP.Library.NP, ∀ c : ℕ, L ∉ SIZE fun n => c * n ^ k + c

/-- L-gen-103: the smallest open case. Some language in NP has no circuits of linear size. The
best lower bounds known for explicit functions are linear (about `5 n` gates of AND, OR, NOT). -/
def L103 : Prop :=
  ∃ L ∈ PEqualNP.Library.NP, ∀ c : ℕ, L ∉ SIZE fun n => c * n + c

/-- L-gen-104: `⌈log₂ (n + 1)⌉` NOT gates are as good as any number, up to a polynomial factor
(Markov 1958; Fischer 1975). With it, a superpolynomial lower bound for circuits with
`⌈log₂ (n + 1)⌉` NOT gates is a superpolynomial lower bound for all circuits. -/
def L104 : Prop :=
  ∃ p : Polynomial ℕ, ∀ s : ℕ → ℕ,
    SIZE s ⊆ SIZENot (fun n => p.eval (s n + n)) (fun n => Nat.clog 2 (n + 1))

end PEqualNP.General.Gap
