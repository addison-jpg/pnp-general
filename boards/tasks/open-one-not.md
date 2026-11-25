# Task: open-one-not

- **Statement:** The general case of the one-NOT theorem: no smallest counterexample (`no_minCE`).
- **Seats:**
  - A1 (Opus): paper proof attempt of the mixed step at states of negative slack, the one local statement no circuit has broken
  - A2 (Sonnet): mixed slack as a Lean definition in the project's terms, so the missing arrow can be stated
  - A3 (Sonnet): search for a counterexample to the mixed step and to the step under no gate-saving rewiring, on irreducible circuits with a read NOT gate
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- **F2-transfer** (from A1): in a minimal counterexample, for each restriction (Q, D) the witness count |F2'| is at least base'. Minimality only gives gates' ≥ base', and |F2'| ≤ gates', so it points the wrong way. The proof must use the one-NOT hypothesis: without it the step fails (146 of 248 negative states at t = 4).
- `MixedStepNeg` is **equivalent** to the full count (checked, `MixedStepNegIff.lean`). It is a restatement, not a reduction. Do not attack it as a local lemma.
- Seats now: A3 (Sonnet, search, running), A4 (Opus): F2-transfer under one NOT gate, A5 (Sonnet): test F2-transfer at t = 1 on every stored instance and find where the NOT gate is used.

## Lines (TAKEN / DECIDED only)

- A2 DONE: Open/MixedSlack.lean defines mslack and MixedStepNeg (Prop) and proves MixedStepNeg -> no_minCE; the arrow itself is unproved.
- 2026-11-25 A1 (Opus) DECIDED: mixed step at negative states = the count at every mixed state (checked, Open/MixedStepNegIff.lean); fails at t=4 only at negative states; obstacle = F2-transfer (minimality gives gates' >= base', step needs |F2'| >= base'). Note: one-not/research/open/A1_mixed_step.md
- 2026-11-25 A4 (Opus) TAKEN: F2-transfer under one NOT gate (where the NOT gate enters under restriction; attack on stored instances first). Note will be one-not/research/open/A4_f2_transfer.md
- 2026-11-25 A5 (Sonnet) TAKEN: test F2-transfer at t = 1 on every stored one-NOT instance and random irreducible one-NOT circuits; record NOT alive/killed vs gates' - |F2'|. Files: one-not/research/open/A5_transfer_t1.py, A5_transfer_t1.md
- 2026-11-25 A5 (Sonnet) DECIDED: F2-transfer |F2'| >= base' holds at every restriction (1,353,627 with base' > 0) of 3,263 one-NOT circuits, n 4..10, 0 failures (tested, checked twice); tight in both NOT-alive and NOT-killed states, so no NOT-use shows up in the data. Note: one-not/research/open/A5_transfer_t1.md
