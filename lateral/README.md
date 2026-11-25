# lateral: one diagonal theorem

Novelty, stated plainly: the unification is classical (Lawvere 1969, "Diagonal arguments and cartesian closed categories"; Yanofsky 2003, "A universal approach to self-referential paradoxes, incompleteness and fixed points"). Mathlib already has the surjective form (`Function.exists_fixed_point_of_surjective`) and says so in its docstring. What is new here is only one checked Lean spine reused by the instances below. Nothing here bears on P vs NP.

Spine: `lean/PEqualNP/Lateral/Lawvere.lean` (`lawvere_diag`, `lawvere_surjective`, `no_row_of_fixed_point_free`, `not_surjective_of_fixed_point_free`).

| Instance | Theorem | Status |
|---|---|---|
| Lawvere spine | `Lateral/Lawvere.lean::lawvere_diag` | checked (diagonal form; surjective form is Mathlib's) |
| Cantor | `Lateral/Cantor.lean::cantor_from_lawvere` | checked, derived from the spine with `g = Not` |
| Russell | `Lateral/Cantor.lean::russell_from_lawvere` | checked: naive comprehension over any relation fails; this is Russell's argument, not ZF |
| Computability | `Lateral/Halting.lean::no_computable_enumeration` | checked, derived from the spine with `g = succ` (no computable enumeration of computable functions) |
| Halting problem | `Lateral/Halting.lean::halting_bridge` | checked, but it only restates Mathlib's `ComputablePred.halting_problem` (proved there via Rice). Not derived from Lawvere; the link is analogy, with `no_computable_enumeration` as the nearest derived neighbour |
| Camus | `Lateral/CamusInstance.lean::camus_from_lawvere` | checked: `Camus.no_total_answer` re-derived from the spine, Camus.lean untouched. Reading Camus this way is a modelling choice (analogy) |
| Tarski / asteroid claim language | none | DROPPED, see below |

## Why the asteroid / Tarski instance was dropped

Tarski undefinability needs a language that can talk about its own sentences (a coding of syntax, then a definable substitution or diagonal function). Asteroid's claim language has no formal syntax in this repository that Lean could take as a toy fragment, and writing a fresh arithmetised toy language would be a standalone project, not an instance of asteroid. We state no such theorem. The abstract shape (no truth predicate T with T(code A) iff A, via a fixed-point-free negation) is the same Lawvere pattern; that is a remark, not a checked result.

Build: `cd lean && nice -n 19 lake build PEqualNP.Lateral.<Name>` for Lawvere, Cantor, Halting, CamusInstance.
