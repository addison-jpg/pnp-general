import PEqualNP.Defs

/-!
The open gaps of the quantum gravity program. Each gap is one statement, written in Lean, that
still needs a proof. Here each gap is a `Prop` definition: this file states the gaps and proves
none of them, so it holds no `sorry`. A proof of gap `L-qg-1NN` is a file `L1NN.lean` beside this
one, declaring `theorem PEqualNP.QuantumGravity.L1NN : PEqualNP.QuantumGravity.Gap.L1NN`.
The board (`BOARD.md` at the root of the repository) tracks which gaps are open.
-/

namespace PEqualNP.QuantumGravity.Gap

open PEqualNP.QuantumGravity

/-- L-qg-101: exponential complexity for local reversible circuits. Some reversible map of `n`
bits has no circuit of at most `k` gates that each act on at most three bits, whenever
`((n + 1)^3 * 8! + 1)^k < (2^n)!`. The work is the count of local gates
(at most `(n + 1)^3 * 8!`); the rest is L-qg-001. -/
def L101 : Prop :=
  ∀ n k : ℕ, ((n + 1) ^ 3 * 40320 + 1) ^ k < (2 ^ n).factorial →
    ∃ g : Equiv.Perm (Fin n → Bool), g ∉ ReachableIn (localGates n) k

/-- L-qg-102: Deutsch consistency for a probabilistic classical register. Every Markov kernel on
a nonempty finite register has a stationary distribution. This is the classical half of
Aaronson and Watrous's closed timelike curve model, where the circuit on the curve may flip
coins; L-qg-008 is the deterministic case. Checked: `L102.lean`. -/
def L102 : Prop :=
  ∀ (S : Type) [Fintype S] [Nonempty S] (K : S → PMF S), ∃ μ : PMF S, μ.bind K = μ

/-- L-qg-103: P = NP inverts every polynomial-time function. If P = NP, then every
polynomial-time, length-preserving function is invertible in polynomial time. The contrapositive
reads: a worst-case one-way function gives P ≠ NP. Aaronson's form of Harlow and Hayden's
argument derives the hardness of decoding Hawking radiation from injective one-way functions
secure against quantum computers; each of those is a worst-case one-way function, so through
this gap the same assumption gives P ≠ NP. The assumptions of Brakerski (EFI pairs) and of
pseudorandom quantum states are not known to give P ≠ NP. -/
def L103 : Prop :=
  PEqualNP.Library.P = PEqualNP.Library.NP →
    ∀ f : List Bool → List Bool,
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f →
        (∀ x, (f x).length = x.length) → InvertibleInPolyTime f

/-- L-qg-169: P_CTC is inside EXP. Row L-qg-168 gives the decision rule: apply the register map
`2^m` times from the all-`false` register and read the answer. What is missing is the machine:
an exponential clock for `2 ^ p(n)` (the padding machine `expPad` composed with a polynomial
clock), a bounded iteration of the register map that carries the input along (the iteration
machine of `Library/Machines/Iter.lean` iterates a function of one string, so the pair
(input, register) has to be packed into one string and the cut-or-pad step computed), and the
time bookkeeping into `2 ^ (n ^ k) + k`, as in `Library/Universal/BruteForce.lean`. Aaronson and
Watrous prove the stronger P_CTC = PSPACE; `Defs/Classes.lean` has no PSPACE. -/
def L169 : Prop :=
  PCTC ⊆ PEqualNP.Library.EXP

/-! ### Quantum circuits (board card D-qg-1, ids L-qg-110 to L-qg-119)

The definitions are in `Defs/QuantumGravityCircuits.lean`. "The Haar measure" is every
left-invariant probability measure `μ` on the unitary group; there is exactly one (the module
documentation of `Defs/QuantumGravityCircuits.lean` says why). -/

open MeasureTheory

/-- L-qg-110: no countable gate set is exactly universal. For every countable gate set `S` of
unitaries of `n` qubits, some unitary of `n` qubits is a product of no finite word of gates from
`S`: the words are countable, the unitary group is not. A finite classical gate set can reach
every reversible map of `n` bits exactly (L-qg-006 assumes one that does), because there are
finitely many; a quantum gate set can only approximate, which is why `ApproxReachableIn`
exists. Checked: `L110.lean`. -/
def L110 : Prop :=
  ∀ (n : ℕ) (S : Set (qubitUnitaryGroup n)), S.Countable →
    ∃ U : qubitUnitaryGroup n, ∀ k : ℕ, U ∉ ReachableIn S k

/-- L-qg-111: errors add. If `U` is within `ε` of a product of at most `k` gates and `W` is within
`δ` of a product of at most `m` gates, then `U * W` is within `ε + δ` of a product of at most
`k + m` gates. This is Knill's Lemma 2.3 (1995) in the operator norm, the error bound of
Bernstein and Vazirani for approximate quantum circuits; it is the approximate form of
L-qg-003. Checked: `L111.lean`. -/
def L111 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix.unitaryGroup ι ℂ)) (k m : ℕ)
    (ε δ : ℝ) (U W : Matrix.unitaryGroup ι ℂ),
    U ∈ ApproxReachableIn S k ε → W ∈ ApproxReachableIn S m δ →
      U * W ∈ ApproxReachableIn S (k + m) (ε + δ)

/-- L-qg-112: approximate complexity grows at most linearly in time. If one step `U` of a time
evolution is within `ε` of a product of at most `k` gates, then `t` steps, `U ^ t`, are within
`t ε` of a product of at most `t k` gates. The approximate form of L-qg-004. Checked:
`L112.lean`. -/
def L112 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix.unitaryGroup ι ℂ)) (k : ℕ) (ε : ℝ)
    (U : Matrix.unitaryGroup ι ℂ),
    U ∈ ApproxReachableIn S k ε → ∀ t : ℕ, U ^ t ∈ ApproxReachableIn S (t * k) (t * ε)

/-- L-qg-113: compiling one gate set into another. If every gate of `T` is within `δ` of a
product of at most `m` gates of `S`, then every unitary within `ε` of a product of at most `k`
gates of `T` is within `ε + k δ` of a product of at most `k m` gates of `S`. With the
Solovay-Kitaev theorem as the compiler, approximate complexity changes by at most a
polylogarithmic factor between universal gate sets. Checked: `L113.lean`. -/
def L113 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S T : Set (Matrix.unitaryGroup ι ℂ)) (k m : ℕ)
    (ε δ : ℝ), 0 ≤ δ → (∀ g ∈ T, g ∈ ApproxReachableIn S m δ) →
      ApproxReachableIn T k ε ⊆ ApproxReachableIn S (k * m) (ε + k * δ)

/-- L-qg-114: reversible circuits are quantum circuits. A reversible map `g` of the basis states
has a circuit of at most `k` gates from `S` exactly when its unitary `permUnitary g` is a product
of at most `k` of the unitaries `permUnitary s`, `s ∈ S`. So exact quantum complexity over
permutation gates is classical reversible complexity, and the classical rows L-qg-001 to
L-qg-007 are statements about quantum circuits of permutation gates. This is how a reversible
circuit for a function `f` becomes the unitary `|x, y⟩ ↦ |x, y ⊕ f x⟩` of the decoding arguments
of track B. Checked: `L114.lean`. -/
def L114 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Equiv.Perm ι)) (k : ℕ) (g : Equiv.Perm ι),
    g ∈ ReachableIn S k ↔ permUnitary g ∈ ReachableIn (permUnitary '' S) k

/-- L-qg-115: the Haar measure of a ball. There is a constant `C` such that, on every number `n`
of qubits, the operator norm ball of radius `ε` around any unitary has Haar measure at most
`(C ε)^(4^n)`; `4^n` is the real dimension of the unitary group of `n` qubits. Two sources give
it. Knill (1995, Lemma 4.3 with `k = 2^n`) states the bound
`(1 - ε²/2)^(-2^n) (ε √(1 - ε²/4))^(4^n)` for `ε < √2`, in the norm of the largest column of
`U - V`, which is at most the operator norm; for `ε ≤ 1` it is at most `(2 ε)^(4^n)`. Szarek
(1998, Theorem 7) proves that the operator norm covering numbers of the unitary group are at
least `(c / ε)^(4^n)` for `ε ≤ 2`, with a universal constant `c`; the balls of radius `ε` around
a maximal `2 ε`-separated set are disjoint, so each has measure at most `(2 ε / c)^(4^n)` for
`ε ≤ 1`. Difficulty: hard, needs integration over the unitary group. -/
def L115 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ]
      [μ.IsMulLeftInvariant] (V : qubitUnitaryGroup n) (ε : ℝ), 0 ≤ ε →
      μ.real {U | opDist (V : Matrix (Qubits n) (Qubits n) ℂ) (U : Matrix (Qubits n) (Qubits n) ℂ)
        ≤ ε} ≤ (C * ε) ^ (4 ^ n)

/-- L-qg-116: the quantum counting bound, in Knill's form. There is a constant `C` such that,
for every finite gate set `S` of unitaries of `n` qubits, the unitaries within `ε` of a product
of at most `k` gates from `S` have Haar measure at most `(|S| + 1)^k (C ε)^(4^n)`. So `S`
reaches, within small `ε`, only a vanishing fraction of the unitaries with
`k log (|S| + 1) = o(4^n log (1 / (C ε)))` gates: almost every unitary needs
`Ω(4^n log(1/ε) / log |S|)` gates. This is Knill's Theorem 4.1 and Corollary 4.2 (1995), with
a finite gate set in place of his finite net of `g`-qubit gates. Difficulty: follows from
L-qg-115 by L-qg-117. -/
def L116 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ]
      [μ.IsMulLeftInvariant] (S : Finset (qubitUnitaryGroup n)) (k : ℕ) (ε : ℝ), 0 ≤ ε →
      μ.real (ApproxReachableIn (S : Set (qubitUnitaryGroup n)) k ε) ≤
        ((S.card : ℝ) + 1) ^ k * (C * ε) ^ (4 ^ n)

/-- L-qg-117: the ball bound gives the counting bound. L-qg-115 implies L-qg-116, with the same
constant: the unitaries within `ε` of a product of at most `k` gates lie in at most
`(|S| + 1)^k` balls (L-qg-001). Checked: `L117.lean`. -/
def L117 : Prop :=
  L115 → L116

/-- L-qg-118: the counting bound gives a hard unitary. If L-qg-116 holds, there is a constant
`c > 0` such that, whenever `(|S| + 1)^k < (c / ε)^(4^n)`, some unitary of `n` qubits is not
within `ε` of any product of at most `k` gates from `S`. This is the quantum form of L-qg-002.
Checked: `L118.lean`. -/
def L118 : Prop :=
  L116 → ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (S : Finset (qubitUnitaryGroup n)) (k : ℕ) (ε : ℝ), 0 < ε →
      ((S.card : ℝ) + 1) ^ k < (c / ε) ^ (4 ^ n) →
        ∃ U : qubitUnitaryGroup n, U ∉ ApproxReachableIn (S : Set (qubitUnitaryGroup n)) k ε

/-- L-qg-119: exact circuits of two-qubit gates, by dimension. If `9 k + 3 n + 1 < 4^n`, the
unitaries of `n` qubits that are products of at most `k` two-qubit gates have Haar measure `0`.
Write each gate as `(A ⊗ B) K (A' ⊗ B')` with `K` in a 3-parameter family and single-qubit
`A, B, A', B'`, and move `A' ⊗ B'` into the gates before it: each gate then adds at most `9`
dimensions, the first layer of single-qubit gates `3 n`, the global phase `1`, and the unitary
group has dimension `4^n`. This is Knill's Theorem 3.4 (1995), which formalizes the argument of
Barenco et al. (1995): almost every unitary needs at least `(4^n - 3 n - 1) / 9` two-qubit
gates. The same dimension count underlies Haferkamp et al.'s proof (2022) of linear growth of
exact complexity. Difficulty: hard, needs the image of a smooth map from a lower-dimensional
manifold to be Haar-null. -/
def L119 : Prop :=
  ∀ (n k : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant],
    9 * k + 3 * n + 1 < 4 ^ n → μ (ReachableIn (twoQubitGates n) k) = 0

/-- L-qg-120: Deutsch's consistency condition for a quantum register. Every quantum channel on
`Fin d`, `d > 0`, given in Kraus form, has a fixed density matrix. This is the condition Deutsch
puts on the state of a register on a closed timelike curve; L-qg-008 is the classical,
deterministic case. Rows L-qg-122 (a channel maps density matrices to density matrices) and
L-qg-123 (unital channels fix the maximally mixed state) are the first steps; row L-qg-126
derives L-qg-121 from this gap. -/
def L120 : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
    0 < d → IsKrausFamily K → ∃ ρ, IsDensityMatrix ρ ∧ krausMap K ρ = ρ

/-- L-qg-121: Deutsch's quantum consistency for the classical case embedded. Every quantum
channel on `Fin d`, `d > 0`, that maps matrices diagonal in the computational basis to
diagonal matrices has a fixed density matrix that is diagonal. On diagonal density matrices
such a channel acts as a stochastic matrix. Row L-qg-125 proves the deterministic case (the
channel of a map of the basis); rows L-qg-126 and L-qg-127 derive this gap from L-qg-120 and
from L-qg-102. -/
def L121 : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
    0 < d → IsKrausFamily K → MapsDiagonalToDiagonal K →
      ∃ ρ, IsDensityMatrix ρ ∧ ρ.IsDiag ∧ krausMap K ρ = ρ

end PEqualNP.QuantumGravity.Gap
