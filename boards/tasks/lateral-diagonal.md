# Task: lateral-diagonal (one diagonal theorem across language, philosophy and mathematics)

- **Source:** coord for Addison, 2026-11-25 (card approved, low priority).
- **Hard rule:** must not interfere with the flagship. It shares no files with the flagship or one-not, takes no seats from F1, LIT1 or REF1, and runs only on idle compute (`nice`, one Lean build at a time).
- **Spine:** Lawvere's fixed point theorem (1969). If some e : A → (A → B) is point-surjective, then every f : B → B has a fixed point. Contrapositive: when B has a map with no fixed point, no such e exists. `Camus.no_total_answer` already uses it.
- **Instances,** one Lean file each, all derived from ONE Lean Lawvere lemma:
  - Mathematics: Cantor (no surjection A → Set A), Russell's paradox.
  - Computation: the halting problem, bridged to Mathlib's `ComputablePred.halting_problem` rather than re-proved.
  - Language: Tarski-style undefinability of truth for a small toy language. A natural pick is a fragment of asteroid's own claim language. State it only if it is literally provable; drop it otherwise.
  - Philosophy: `Camus.no_total_answer` re-derived from the common lemma, so it becomes one instance among the others.
- **Deliverable:** `lateral/README.md`, a table of the instances with theorem names and what is checked versus what is analogy. Findings are recorded under their own program (not circuits).
- **Novelty:** the unification itself is classical (Lawvere 1969; Yanofsky 2003, "A universal approach to self-referential paradoxes, incompleteness and fixed points"). The README says so. What's new is only one checked Lean spine across these instances, plus the asteroid instance. LITERATURE.md rows carry read status.

## Seats
- Sonnet, low priority (main's judgement: these are standard results, so a Sonnet first; a Fable only if a Sonnet fails, per the seat rule). -> lean/PEqualNP/Lateral/*.lean, lateral/README.md

## Lines (TAKEN / DECIDED only)
- TAKEN (Sonnet, 2026-11-25): Lawvere spine, instances, README.
