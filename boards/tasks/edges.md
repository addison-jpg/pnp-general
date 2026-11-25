> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: edges

- **Serves:** the whole structure (asteroid, the base verifier, the board tree).
- **Source:** owner, 2026-11-24: "now that we have this huge structure, redirect some inconsequential guys to fixing up the edges."
- **Statement:** Three small seats, no new mathematics:
  - **A, records:** every finding that waits for a second seat is rerun from its evidence and confirmed or corrected; stale lines in the asteroid docs are fixed against the code.
  - **B, language:** the cheap WISH items: `hyps(c)` (the Theorem's other hypotheses, with its Lean checker `hypsB`), an `if … then …` form in claims, the NOT-gate fix (the flip-classes count as a first-class function, so that claims about many NOT gates do not silently use the one-NOT count).
  - **C, Lean:** pin `LMeta951Stmt` to `L_meta_951`, move the example instances out of `AsteroidSound*.lean`, the short corollaries listed in `research/one-not/board/agents/fable-cheap-proofs.md`.
- **Done when:** `python3 -m asteroid test` and `cd proofs/w951 && lake build PEqualNP.Verify.All` both pass after each seat's commit.
- **Seats:** three small agents of main.

## Lines (TAKEN / DECIDED only)

- 21:46 seat A (main's Sonnet) TAKEN
- 21:47 seat B (main's Sonnet) TAKEN
- 21:47 seat C (main's Sonnet) TAKEN
