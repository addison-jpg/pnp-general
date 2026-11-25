# Task: philosophy-formal (formal philosophy, built crudely up to Deleuze; Mark Fisher if cheap)

- **Source:** Addison, 2026-11-25: "preexisting logical formulations of philosophy exist, and could probably be build (maybe crudely) up to deleuze. him specifically, yes. mark fisher if its cheap. this could work with the base of this entire thing if synced properly thru boards and low level folders. worth a hack." Addison asked for this to be taken very seriously.
- **Statement:** start from existing formalisations of philosophy and build a crude, checked Lean model of Deleuze's core concepts. Connect it to the base of this repository through the boards.
  - Existing formalisations include computational metaphysics (Zalta's abstract objects in Isabelle/HOL, Benzmüller's ontological arguments), formal ontology and mereology, and formalisations of Spinoza and Leibniz.
  - Deleuze's core concepts: multiplicity, difference in itself, virtual / actual, problem / solution, intensity.
  - The connection to this repository: Deleuze's virtual / actual pair reads closely onto the repository's three levels. The actual is finite circuits. The virtual is the polynomial and limit levels, a structure of problems that the finite cases actualise.
- **Honesty:** this is a formal *model* of one reading of Deleuze, not a proof about Deleuze. Readings are contested: Badiou, DeLanda, Duffy and Smith read the mathematics differently. Every definition names the reading it follows and cites it.
- **Where it lives:** `philosophy/` at the repository root, with its own README. Lean code goes in `lean/PEqualNP/Philosophy/` and imports only Mathlib. Results become findings like everything else.

## Seats (Sonnet by default; one line each)

- OPEN (Sonnet) P1: literature with read status, added as a new section of LITERATURE.md.
  - Existing logical formalisations of philosophy: computational metaphysics, Spinoza, Leibniz, mereology, Whitehead's mereotopology, Hegel attempts.
  - Mathematical readings of Deleuze: DeLanda, *Intensive Science and Virtual Philosophy*; Duffy, *Deleuze and Mathematics*; Plotnitsky; Smith on Deleuze and the calculus; Badiou's critique; Lautman as the source.
  - Any formal treatment of Mark Fisher (hauntology, capitalist realism).
  - Then a one-page plan, `philosophy/PLAN.md`: which formal ladder to climb (for example mereology → Spinoza → Leibniz → Deleuze), which Mathlib structures each concept maps to, and the three to five definitions to write first.
- DECIDED P2 (done, see Lines):  `lean/PEqualNP/Philosophy/Deleuze.lean`. The first definitions from PLAN.md, each with a doc comment naming its reading and source, plus small checked lemmas that make the definitions non-trivial. One example of the kind wanted: an actual solution is a point where the problem's vector field vanishes, and distinct actualisations of one virtual structure differ.
- TAKEN P3 (Sonnet), was OPEN, after P2 (file moved to one-not/lean/PEqualNP/Philosophy/Bridge.lean, since slack/Phi live in the one-not Lake project): the bridge to the repository. State the repository's finite (circuit), polynomial (Φ) and limit levels as instances of P2's virtual / actual structure, in `lean/PEqualNP/Philosophy/Bridge.lean`, importing the existing `Phi` and `slack` definitions.
- OPEN (Sonnet) P4 (see DECIDED line below), cheap, Fisher: hauntology as a branching-time modal structure, futures that were possible and are no longer reachable. A small Lean file or a note, only if P1 finds a cheap footing.

## Lines (TAKEN / DECIDED only)
- P1 (Sonnet) DECIDED: LITERATURE.md section M (about 25 rows, none read in full; philarchive and tu-dresden fetches blocked) and philosophy/PLAN.md: ladder mereology, Spinoza, Leibniz, Deleuze (vector field = virtual, integral curve = actual), five Lean definitions for P2 (Problem, Solution, plurality lemma, Intensity, optional Expression), Fisher gets a thin branching-time footing for P4. -> philosophy/PLAN.md
- P2 (Sonnet) [DECIDED P2]: lean/PEqualNP/Philosophy/Deleuze.lean builds, standard axioms only: realize_mem, actual_smul, distinct_problems_same_actual, actual_not_injective, nondegenerate_isolated, not_linearEquiv_of_dimension_ne, extensive_union, intensive_not_additive
- P4 (Sonnet) DECIDED: lean/PEqualNP/Philosophy/Fisher.lean builds, no axioms: lost_mono, haunted_mono (cancellation irreversible, uses linear past), haunted_of_branch, capitalist_realism, not_lost_of_total, 4-node tree example by decide. Models only cancelled possibility.
- P3 (Sonnet) [DECIDED P3]: one-not/lean/PEqualNP/Philosophy/Bridge.lean builds, standard axioms only (Problem/actual restated from Deleuze.lean). Actual = slack table, virtual = Phi (`Phi_eq_PhiT`, corners `PhiT_zero`, `Phi_one`); non-resemblance both ways at n=2: `PhiT_not_injective` (different tables, equal Phi), `corners_not_injective` (equal corners, different Phi); `LimitTarget` is a def only, no proof. Formal analogy, claims nothing about Deleuze or circuits.
