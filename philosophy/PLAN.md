# Plan: a formal ladder up to Deleuze (seat P1, 2026-11-25)

Scope and honesty. Every definition below models a *cited reading*, named next to it. Nothing here
says what Deleuze meant; readings differ (Smith 2003 and Badiou 1997 follow opposite routes through
mathematics). Sources and read status are in `LITERATURE.md`, section M. No source was read in full;
most are search results only, so each reading below is "as reported", to be re-read before P2 relies on it.
No formal Deleuze exists in the literature found: the existing formalisations stop at Spinoza and
Leibniz-style compossibility, and Fisher has none. The top two rungs are ours to build.

## The ladder (each step has a Mathlib home)

| Rung | Concept | Reading it follows | Mathlib structure |
|---|---|---|---|
| A. Aristotle (the foil) | potentiality (dunamis) to actuality (energeia), Metaphysics Θ: the possible is a pre-image of the real and *resembles* it; realisation adds existence to a given form. Deleuze (Difference and Repetition, ch. 4, as reported by Smith and Duffy) opposes the virtual, which is real and does not resemble its actualisations, to the possible | Aristotle, Metaphysics Θ (not opened: memory, to be cited from a translation); Deleuze via the readings in LITERATURE.md M2 | a relation `Realises : Possible → Real → Prop` that is *resemblance-preserving* (an injection, the possible is a subset of the real); the virtual model is the contrast: actuals are not copies of the virtual |
| 0. Mereology | parthood is a partial order; sums; atomless regions | Leśniewski, Leonard-Goodman; Clarke 1981 for connection (models are Boolean algebras) | `PartialOrder`, `CompleteLattice`, `CompleteBooleanAlgebra` |
| 1. Spinoza | substance (maximal), attributes, modes (parts of substance), "in" and "conceived through"; expression of substance in modes | Jarrett 1978 and later Prover9, Coq, Agda, Lean pieces (they needed implicit axioms); Duffy 2006 reads expression through the differential | a `CompleteLattice` with a top (substance) plus a family of sublattices (attributes); modes = elements below the top |
| 2. Leibniz | monads as complete concepts; compossibility; a world is a maximal compossible set; the differential as genetic element | SEP "Leibniz's Modal Metaphysics" (definition of compossibility); Duffy, Smith 2005 for the calculus | a symmetric relation on a type, worlds = maximal cliques (`SimpleGraph.IsClique`); no Monadology formalisation exists, so this is hand-made |
| 3. Deleuze | multiplicity = manifold with a metric; difference = differential relation dy/dx; virtual = problem = vector field with singularities; actual = solution = integral curve; intensity | DeLanda 2002 ch. 1 (manifolds, vector fields, singularities, basins); Plotnitsky (Riemann); Smith 2006 (problematics vs axiomatics); Lautman (problem/solution) | `IsRiemannianManifold`, `TangentSpace`, `ContMDiff`, `IsMIntegralCurve`, `deriv`, `mfderiv` (all present in the project's Mathlib checkout) |

Rung A is the contrast case (possible / real, resemblance) that makes non-resemblance a statement. Rungs 0-2 are context and check that the encoding style works; P2 does not need to finish them. The
Badiou objection is the test the rung-3 model must pass: if the virtual is only an image of the
actual it is a simulacrum, and the actual must not be a blur or a tear away from it. In the model:
actuals must be *determined by* the virtual (solutions of the field) without a second ground.

## What P2 is building (coordinator, 2026-11-25), and how it reads this ladder

`lean/PEqualNP/Philosophy/Deleuze.lean` is being written in parallel, so the plan follows it:
(1) Aristotle's possible and its realisation (rung A, the foil); (2) problem = vector field;
(3) actual = singular points of the field (the zeros, "actual" as the places where the problem
resolves); (4) non-resemblance: `V` and `2V` have the same actual, so the actual does not
copy the virtual; (5) nondegenerate solutions are isolated (inverse function theorem); (6)
multiplicity as dimension. The definitions list below is the earlier P1 sketch, in which the actual is
an integral curve; the two are both in the literature reading (DeLanda: singularities organise the
field; trajectories are drawn to them), so P2's choice (actual = singular points) is the
singularity half and integral curves are the dynamical half. Where they differ, P2's file wins.

## The first Lean definitions for P2 (P1 sketch; superseded where it differs from the above)

Work on a finite-dimensional normed space `E` first (`ℝ`, `ℝ²`): it keeps every definition checkable
with `deriv` and `HasDerivAt`, and the manifold version is a generalisation to state, not to prove.
Use a general manifold only if the first four go through.

1. `Problem E` := a C¹ vector field `v : E → E` (the virtual: a differential relation `dx/dt = v x`,
   no trajectory yet). Reading: Smith 2006, Lautman; difference lives in the relation, not in the solutions.
   `Problem.singularities v := {x | v x = 0}`. Reading: DeLanda ch. 1 (singularities as the topological
   features that organise the field). Lemma: for `v x = x` the singularity set is `{0}`.
2. `Solution v γ` := `∀ t, HasDerivAt γ (v (γ t)) t` (the actual; `IsMIntegralCurve` on manifolds).
   Reading: Smith 2006, DeLanda ("trajectories drawn toward singularities"). Lemmas: the constant
   curve at a singularity is a solution; a solution at a non-singular point is not constant.
3. `Actualises v γ` and the *plurality* lemma: one problem has distinct actualisations that differ
   (for `v x = x`, `γ t = exp t` and `γ t = 2 exp t`), and the problem fixes them up to the initial
   condition (Mathlib's `ExistUnique`). Reading: Duffy 2006 (one differential, many integral
   curves), Badiou's challenge (actual determined by virtual). This was the planned non-trivial
   content; it was NOT built (`Deleuze.lean` has only `Trajectory.const`, and the delivered
   theorems are the simpler ones).
4. `Intensity v x` := `‖v x‖`, a degree attached to a point of the virtual that vanishes exactly on
   the singularities. Reading: DeLanda ("a science of the virtual is a science of intensities") only
   as a *crude* choice; this is the weakest of the five and should be labelled as a model decision.
5. (optional) `Expression`: a monotone map from a lattice of modes into the virtual, the Spinoza
   rung (rung 1) pointed at rung 3. Do this only if 1-4 are done and the lattice encoding is cheap.

Doc comments must name the reading and source of each definition (task rule). Artefact warning
(from Kirchner, Benzmüller, Zalta 2019): record which lemmas hold because of the Lean encoding, not
because of the reading.

## Virtual / actual versus the repository's three levels

(This is the board's reading; the model does not prove it.)
- Actual = the bottom, finite circuits. One circuit on n inputs is a solution: a particular trajectory.
- Virtual = the problem all circuits answer: the base value Σ(|S|−1) and the inequality gates ≥ base.
  The middle level (Φ, degree-n polynomial densities) is the virtual written as a field; the top
  (n → ∞, densities of small patterns, the limit object) is the virtual as a multiplicity of
  unbounded dimension.
- Singularities of the field = tight circuits (slack 0), the points where "gates minus base" vanishes;
  the 245 non-up-set tight Fano cubes are a singularity set to test. Stability near-tight circuits
  looks like the known tight ones = basins of attraction (DeLanda). This is analogy, and the Lean
  bridge (P3) should state it as a definition, not claim it.
- Badiou's objection has a concrete form here: an asymptotic limit is real-valued, the count is
  integer and exact. The virtual does not ground the actual until a stability step repairs the o(n).
- Caveat for P3: `Phi` and `slack` are not Lean definitions in `lean/` as such; the nearest are
  `Phi1` (`lean/PEqualNP/MetaComplexity/Helpers/LocGraph.lean`) and `mslackVal`
  (`one-not/lean/PEqualNP/W951/AsteroidMixed.lean`). P3 must locate or state them first.

## Fisher: is there a cheap footing?

Yes, thin. No formal treatment exists (searched once). Hauntology (futures that were possible and
are cancelled but still exert pressure; Fisher after Derrida, with Berardi's "slow cancellation of the
future") fits a branching-time structure: states `S`, a successor relation `R`, a "now" `s₀`. A lost
future is a state reachable earlier (in some history through `R*` from an ancestor of `s₀`) and not
reachable from `s₀`. In Lean, a plain `structure` with `R : S → S → Prop`, `Lost s₀ f := (∃ a, R* a s₀ ∧ R* a f) ∧ ¬ R* s₀ f`, and a lemma that
`Lost` is empty on a linear order or when every branching state is a descendant of `s₀`. No Mathlib
library is needed (Mathlib has no CTL). It models only "cancelled possibility"; it does not capture
the affective or ideological half of capitalist realism. Seat P4 may go ahead as a small file; the
link to Deleuze (a lost future = a virtual whose actualisations are no longer reachable) is a one-line
remark, not a result.
