# Task: all-not-gates

- **Serves:** C4 (any number of NOT gates), `notes/beyond-one-not.md` statements S3 and S1.
- **Source:** owner, 2026-11-24: "use asteroid with lean backend to continue aggressively".
- **Statement:** Two things that can be PROVED now, for circuits with any number of NOT gates.
  - **Seat 1, the per-set lemma (S3 a):** in every correct circuit, at every zero point of every set S there are at least |S| − 1 flip classes. Paper proof in `notes/beyond-one-not.md`; put it in Lean, in the project's definitions.
  - **Seat 2, exact small cases:** for a fixed small set system, NO correct circuit with fewer than base gates exists, whatever the number of NOT gates. The search has found none; make it a Lean theorem (an enumeration the kernel runs, with a proof that the enumeration misses no circuit), and give asteroid a claim form for it.
- **Done when:** each seat has a checked theorem that the pure-Lean verifier accepts, and an asteroid program that uses it.
- **Seats:** two agents of main.

## Lines (TAKEN / DECIDED only)

