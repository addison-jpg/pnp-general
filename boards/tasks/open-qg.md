# Task: open-qg

- **Statement:** The four open quantum-gravity statements: L-qg-115, 116, 119, 169.
- **Seats:**
  - C1 (Sonnet): L-qg-116 from L-qg-115 (union bound), as a checked conditional theorem
  - C2 (Opus): L-qg-119 (dimension count) or L-qg-115 (ball volume), whichever is reachable, or the exact missing Mathlib lemma
  - C3 (Sonnet): L-qg-169 (P_CTC inside EXP): the cheapest missing piece, or a precise plan
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- L-qg-116 follows from L-qg-115 (checked, C1). So the quantum side is down to L-qg-115, L-qg-119, L-qg-169.
- Seats now: C2 (Opus, L-qg-119 or L-qg-115, running), C3 (Sonnet, L-qg-169, running).

## Lines (TAKEN / DECIDED only)

- C1 (Sonnet): L-qg-116 from L-qg-115 checked: `PEqualNP.QuantumGravity.Open.L116_of_L115` in lean/PEqualNP/QuantumGravity/Open/L116OfL115.lean (wraps existing L117 / Helpers.knill_of_ball; builds). L-qg-115 itself still open.
