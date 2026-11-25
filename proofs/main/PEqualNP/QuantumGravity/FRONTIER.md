# The quantum gravity frontier and the next formal targets

Seat Q1 of [`qg-frontier`](../../../../boards/tasks/qg-frontier.md), 2026-11-25. The survey rows, with
read status, are in [`research/LITERATURE.md`](../../../../research/LITERATURE.md) §I, "Frontier survey". This note
explains how the next formal targets were ranked. The targets are the `OPEN (Sonnet)` lines on the
task board. No statement here is about physics: complexity = volume, complexity = action and the
existence of closed timelike curves stay premises written in prose, as the README of this
directory says. Nothing here bears on P versus NP.

## What the repository already proves

- **Counting core of "most unitaries need exponentially many gates".** L-qg-115 (Haar small ball,
  `Open/L115.lean`, C = 4) gives L-qg-116 (Knill's count for a *finite* gate set) through L-qg-117,
  and L-qg-118 gives a hard unitary. `L119_weak` (`Open/KnillParam.lean`) shows that products of
  k two-qubit gates have Haar measure 0 when 16k < 4^n. The exact 9k + 3n + 1 form waits on
  `KnillParametrization` (KAK for U(4); seat C4 on `open-qg`).
- **CTCs.** Deutsch-consistent distributions exist (L-qg-008, 160, 167). P, NP and coNP lie in
  P_CTC (L-qg-161, 162, 165), and P_CTC ⊆ EXP (L-qg-169, `Open/L169.lean`). PSPACE is not defined
  in the repository.
- **Holographic codes.** The stabilizer core of the HaPPY code is checked (L-qg-140 to 149): the
  five-qubit code has distance 3, and in the six-qubit perfect state every 3-set of qubits
  determines a stabilizer element uniquely. The README's track F row ("none yet") is out of date.

## Where the frontier is

Haferkamp, Faist, Kothakonda, Eisert and Yunger Halpern (2022) proved Brown and Susskind's
linear-growth conjecture for *exact* complexity. The main text was read (status TXT). Their proof
has two halves.

- **Upper half.** The accessible dimension of an R-gate architecture is at most 9R + 3n, by
  counting parameters. This is our `KnillParametrization`, and `L119_weak` already gives it with
  16 in place of 9.
- **Lower half.** A Clifford point at which the contraction map's Jacobian has rank at least T.
  Then a real-algebraic Lemma 1: the low-rank locus is algebraic and of measure 0. Then the
  constant-rank theorem and compactness. Current Mathlib has neither semialgebraic dimension
  theory nor the constant-rank theorem. This half is not a Sonnet seat.

The *approximate* version at constant error is still open in the literature. Haferkamp (2023)
gets only √ growth there (search result, not read). The recent work builds approximate unitary
designs and pseudorandom unitaries: Chen et al. 2024, Schuster, Haferkamp and Huang 2024, and Ma
and Huang 2024. None of it is in Lean reach: each needs representation theory of the unitary
group or quantum cryptography.

## Ranking (value × reachability in current Mathlib)

1. **Knill's count for the continuous two-qubit gate set (1a → 1b → 1c).**
   - **Value: high.** It turns the checked finite-gate-set count (L-qg-116) into the standard
     theorem about all two-qubit gates with error ε: the Haar measure of the unitaries within ε
     of k two-qubit gates is at most `((n+1)² (C(k+1)/ε)^32 + 1)^k (cε)^(4^n)`. So almost every
     unitary needs Ω(4^n log(1/ε) / (log n + log k + log(1/ε))) gates. This is the approximate,
     robust counterpart of `L119_weak`, and it is the honest Lean form of the "exponential
     saturation" half of the second law of complexity.
   - **Reach: high.** The steps are a triangle-inequality bound on the operator norm of
     `W ⊗ 1` (1a); a finite net of the gates from a grid on the matrix entries (1b; the exponent
     32 is crude, which does not matter); then L-qg-113 with m = 1, and L-qg-116 (1c). Everything
     else is already proved.
2. **CTC reset cycle.**
   - **Value: medium.** It is the combinatorial core of PSPACE ⊆ P_CTC, the direction of
     Aaronson and Watrous (2009) that the repository lacks. The step map, with a reset to the
     start configuration on halting, has every consistent distribution supported on the cycle
     through the start. Once a space-bounded machine model exists, the class statement follows.
   - **Reach: very high.** It is a finite-orbit argument on top of
     `Helpers.mem_range_iterate_of_consistent`.
   - **Not ranked.** Defining PSPACE (Mathlib's Turing machines have no space measure) and the
     quantum side, BQP_CTC ⊆ PSPACE. That side needs fixed points of superoperators computed in
     polynomial space, which is far.
3. **Two-level (Givens / Reck) decomposition.**
   - **Value: medium.** Every unitary of dimension d is a product of at most d(d+1)/2 two-level
     unitaries. This is the "complexity saturates" upper bound, which pairs with the lower bounds
     already proved. Gray-code compilation to two-qubit gates is the next step after this one, and
     is not ranked.
   - **Reach: medium.** Column elimination by induction on d, using only Mathlib linear algebra.
     The reindexing is the main cost.
4. **L-qg-119 at 15k + 1.**
   - **Value: low to medium.** One global phase instead of one per gate. It is still far from
     9k + 3n + 1.
   - **Reach: medium to low.** It needs a 15-parameter countable differentiable cover of U(4) up
     to phase, which is not obviously easier than the Cayley-chart argument already done. If the
     cover is the blocker, the seat writes that lemma down as its result.

## Not ranked, and why

- **Complexity = volume and complexity = action.** These are physics identifications, not
  mathematical statements. Belin et al. (2022) show that many bulk observables grow the same way.
- **Nielsen's geometric complexity.** It needs right-invariant Finsler or Riemannian metrics and
  geodesics on SU(2^n), which Mathlib does not have. Haferkamp et al. note that their bound does
  not imply Nielsen's.
- **The Haferkamp lower half.** See above: real algebraic geometry and the constant-rank theorem.
- **HaPPY beyond the stabilizer core.** The statement that the 3-qubit marginals of the perfect
  state are maximally mixed needs stabilizer-state density matrices. It is possible later; it is
  of lower value than ranks 1 to 3.
