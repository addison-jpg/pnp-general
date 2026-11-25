# Task: open-qg

- **Statement:** The four open quantum-gravity statements: L-qg-115, 116, 119, 169.
- **Seats:**
  - C1 (Sonnet): L-qg-116 from L-qg-115 (union bound), as a checked conditional theorem
  - C2 (Opus): L-qg-119 (dimension count) or L-qg-115 (ball volume), whichever is reachable, or the exact missing Mathlib lemma
  - C3 (Sonnet): L-qg-169 (P_CTC inside EXP): the cheapest missing piece, or a precise plan
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- L-qg-115 (C = 4), L-qg-116 (unconditional) and L-qg-169 are proved; L-qg-119 holds in the weak form 16k.
- Open: `KnillParametrization` (countably many differentiable maps from ℝ^(9k+3n+1) cover the k-gate products; needs KAK for U(4), not in Mathlib). That is the one open quantum statement; L-qg-119 follows from it (`L119_of_knillParametrization`).
- Seat now: C4 (Sonnet): `KnillParametrization`, or the weaker parametrization via the exponential map with the exact bound it gives (16 per gate and the 15k+1 form are done).

## Refuted / dead

- None. L-qg-115 needed no packing or density argument: Fubini over the Cayley chart suffices.

## Decided (one line each; the file holds the proof)

- C1: L-qg-116 from L-qg-115, checked (wraps L117 / `Helpers.knill_of_ball`). -> `lean/PEqualNP/QuantumGravity/Open/L116OfL115.lean::L116_of_L115`
- C3: L-qg-169 CHECKED in full, `PCTC ⊆ EXP` (machine = iterGrow of a packed-state step over expPad(pairB x (un m)); N ≥ 2^m steps land on a cycle; standard axioms only). -> `Open/L169.lean::PCTC_subset_EXP`
- C2: conditional `L119_of_knillParametrization : KnillParametrization → Gap.L119`; Haar-null half `haar_null_of_image` proved (images of lower-dimensional differentiable maps are Haar-null, via the Cayley chart). -> `Open/L119.lean`
- C5 (Opus): L-qg-115 CHECKED, `haar_small_ball : Gap.L115` (C = 4); Fubini over C2's Cayley chart; standard axioms only. -> `Open/L115.lean`
- C4 (Sonnet): L-qg-119 weak form CHECKED, `L119_weak : 16 * k < 4 ^ n → μ (ReachableIn (twoQubitGates n) k) = 0` (every unitary is `phase m • cayley (skewOf A)`; a two-qubit gate is a block ≤ 4x4, so 16 parameters per gate). -> `Open/KnillParam.lean`
- F2 (Fable): `KnillParametrization` and the exact L-qg-119 CHECKED, `L119 : Gap.L119` (9k + 3n + 1 < 4^n ⇒ measure zero), standard axioms only. KAK for U(4) without Lie theory: a symmetric unitary is O diag Oᵀ with O real orthogonal (Cayley chart + real spectral theorem), so V = R diag Oᵀ; every real orthogonal 4×4 matrix is a product of left/right unit-quaternion multiplications and one sign, and those are tensor products in the magic basis. Each gate's right tensor factor is absorbed into a layer of single-qubit gates. No open quantum statement of the four remains. -> `Open/KAK.lean::kak`, `Open/KAKParam.lean::L119`
