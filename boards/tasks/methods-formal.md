# Task: methods-formal (formalizing Addison's methods, tied to ath)

- **Source:** coord for Addison, 2026-11-25. Card approved; seat must be a FABLE (Addison: "in what world does a sonnet do this"; design and formalization, not retrieval).
- **Constraints:** low cost; own files only; no interference with the flagship.
- **Label:** definitions and theorems about the method, not results about circuits. Findings go under their own program, "methods".
- **Goal:** turn the methods this project actually runs on into checked definitions, with ath syntax where it fits.
  1. **Forced pairs.** Every open cell gets a prover and a refuter. A cell's state is one of {open, tested, refuted, checked}, with legal transitions. Prove the invariants, for example: a cell can't be both checked and refuted when the statements match exactly.
  2. **Multidimensional bounds.** A bound is a vector over axes (size, depth, fan-out, #NOT, ...), not a scalar. Define the Pareto frontier and dominance. Prove that the frontier is an antichain and that adding a point updates it monotonically. Link to L6 and worlds-map as data.
  3. **The board as semantics.** Give boards.py's rule a Lean semantics: verified findings propagate up the tree; checked needs Lean; the others need a second seat. Prove propagation is monotone: adding findings never removes a verified count.
  4. **Levels.** Finite → polynomial → limit, as projections. Reuse `Unify.collapse_iff_injective`; don't duplicate it.
  5. **Lifting refuted forms.** The project's history went: real-merge form refuted, then the lifted form built from it. Model it as a DAG of statements with "weakens / lifts" edges. This is the correct version of the tree caveat in philosophy; reuse `Philosophy/DAG.lean` where it fits.
- **ath side:** if cheap, an ath surface for declaring a cell with its axes and its prover/refuter pair, e.g. `claim X over (size, nots) pair prover:F1 refuter:REF1`. It compiles to the Lean definitions or to findings records. Coordinate with the asteroid owner's files; don't edit `eval_sound`.

## Seats
- Fable (main), TAKEN at dispatch. -> lean/PEqualNP/Methods/*.lean, methods/README.md

## Lines (TAKEN / DECIDED only)
