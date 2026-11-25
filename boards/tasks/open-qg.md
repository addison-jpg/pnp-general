# Task: open-qg

- **Statement:** The four open quantum-gravity statements: L-qg-115, 116, 119, 169.
- **Seats:**
  - C1 (Sonnet): L-qg-116 from L-qg-115 (union bound), as a checked conditional theorem
  - C2 (Opus): L-qg-119 (dimension count) or L-qg-115 (ball volume), whichever is reachable, or the exact missing Mathlib lemma
  - C3 (Sonnet): L-qg-169 (P_CTC inside EXP): the cheapest missing piece, or a precise plan
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- L-qg-116 follows from L-qg-115 (checked, C1). So the quantum side is down to L-qg-115, L-qg-119, L-qg-169. L-qg-169 is now proved (C3, `Open/L169.lean`, checked against `Gap.L169`, standard axioms only).
- L-qg-119 ← `KnillParametrization` (C2, checked, `Open/L119.lean`; also proved there: images of lower-dimensional differentiable maps are Haar-null in U(ι), via the Cayley chart).
- Open: `KnillParametrization` (countably many differentiable maps from ℝ^(9k+3n+1) cover the k-gate products; needs KAK for U(4)) and L-qg-115 (Haar small ball; needs Haar vs volume in a chart).
- Seats now: C4 (Sonnet): `KnillParametrization`, or the weaker parametrization via the exponential map with the exact bound it gives; C5 (Opus): L-qg-115.

## Lines (TAKEN / DECIDED only)

- C1 (Sonnet): L-qg-116 from L-qg-115 checked: `PEqualNP.QuantumGravity.Open.L116_of_L115` in lean/PEqualNP/QuantumGravity/Open/L116OfL115.lean (wraps existing L117 / Helpers.knill_of_ball; builds). L-qg-115 itself still open.
- C3 (Sonnet): L-qg-169 CHECKED in full: `PEqualNP.QuantumGravity.Open.L169.PCTC_subset_EXP : PCTC ⊆ EXP` in lean/PEqualNP/QuantumGravity/Open/L169.lean (builds; no sorry). Machine = iterGrow of a packed-state step over expPad(pairB x (un m)); N ≥ 2^m steps land on a cycle.
- C2 [DECIDED] L-qg-119: checked conditional `L119_of_knillParametrization : KnillParametrization → Gap.L119` in `lean/PEqualNP/QuantumGravity/Open/L119.lean`; the Haar-null half (`haar_null_of_image`) is proved. Missing lemma: `KnillParametrization` (KAK form of two-qubit gates, not in Mathlib). L-qg-115 not attempted (needs Haar = chart volume comparison).
