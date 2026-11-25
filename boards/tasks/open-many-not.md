# Task: open-many-not

- **Statement:** Whether two or more NOT gates can save gates on these functions.
- **Seats:**
  - B1 (Opus): the per-set flip lemma in Lean, any number of NOT gates
  - B2 (Sonnet): every circuit for the OR of four inputs needs at least 3 gates, any number of NOT gates, as a Lean theorem by exhaustive check
  - B3 (Sonnet): SAT search for a circuit with two NOT gates and fewer than base gates
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- Single output is settled (B2): OR of n inputs needs n−1 AND/OR gates with any number of NOT gates.
- Open: systems of several overlapping ORs, where NOT gates could let gates be shared.
- Seats now: B1 (Opus, flip lemma, running), B3 (Sonnet, SAT, running), B4 (Sonnet): extend B2's partition argument to systems of several ORs, any number of NOT gates; prove the strongest true bound.

## Lines (TAKEN / DECIDED only)

- B2 DECIDED: proved in Lean (Open/Or4ManyNot.lean): OR of n inputs needs n-1 AND/OR gates with any number of NOT gates (free); OR4 needs 3. Structural, no enumeration.
