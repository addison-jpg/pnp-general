# Task: open-many-not

- **Statement:** Whether two or more NOT gates can save gates on these functions.
- **Seats:**
  - B1 (Opus): the per-set flip lemma in Lean, any number of NOT gates
  - B2 (Sonnet): every circuit for the OR of four inputs needs at least 3 gates, any number of NOT gates, as a Lean theorem by exhaustive check
  - B3 (Sonnet): SAT search for a circuit with two NOT gates and fewer than base gates
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Lines (TAKEN / DECIDED only)

- B2 DECIDED: proved in Lean (Open/Or4ManyNot.lean): OR of n inputs needs n-1 AND/OR gates with any number of NOT gates (free); OR4 needs 3. Structural, no enumeration.
