# Task: open-one-not

- **Statement:** The general case of the one-NOT theorem: no smallest counterexample (`no_minCE`).
- **Seats:**
  - A1 (Opus): paper proof attempt of the mixed step at states of negative slack, the one local statement no circuit has broken
  - A2 (Sonnet): mixed slack as a Lean definition in the project's terms, so the missing arrow can be stated
  - A3 (Sonnet): search for a counterexample to the mixed step and to the step under no gate-saving rewiring, on irreducible circuits with a read NOT gate
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Lines (TAKEN / DECIDED only)

- A2 DONE: Open/MixedSlack.lean defines mslack and MixedStepNeg (Prop) and proves MixedStepNeg -> no_minCE; the arrow itself is unproved.
- 2026-11-25 A1 (Opus) DECIDED: mixed step at negative states = the count at every mixed state (checked, Open/MixedStepNegIff.lean); fails at t=4 only at negative states; obstacle = F2-transfer (minimality gives gates' >= base', step needs |F2'| >= base'). Note: one-not/research/open/A1_mixed_step.md
