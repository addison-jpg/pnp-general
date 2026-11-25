# Task: philosophy-formal (formal philosophy, built crudely up to Deleuze; Mark Fisher if cheap)

- **Source:** Addison, 2026-11-25: "preexisting logical formulations of philosophy exist, and could probably be build (maybe crudely) up to deleuze. him specifically, yes. mark fisher if its cheap. this could work with the base of this entire thing if synced properly thru boards and low level folders. worth a hack." Addison asked for this to be taken very seriously.
- **Statement:** start from existing formalisations of philosophy and build a crude, checked Lean model of Deleuze's core concepts. Connect it to the base of this repository through the boards.
  - Existing formalisations include computational metaphysics (Zalta's abstract objects in Isabelle/HOL, Benzmüller's ontological arguments), formal ontology and mereology, and formalisations of Spinoza and Leibniz.
  - Deleuze's core concepts: multiplicity, difference in itself, virtual / actual, problem / solution, intensity.
  - The connection to this repository: Deleuze's virtual / actual pair reads closely onto the repository's three levels. The actual is finite circuits. The virtual is the polynomial and limit levels, a structure of problems that the finite cases actualise.
- **Honesty:** this is a formal *model* of one reading of Deleuze, not a proof about Deleuze. Readings are contested: Badiou, DeLanda, Duffy and Smith read the mathematics differently. Every definition names the reading it follows and cites it.
- **Where it lives:** `philosophy/` at the repository root, with its own README. Lean code goes in `lean/PEqualNP/Philosophy/` and imports only Mathlib. Results become findings like everything else.

## Seats (Sonnet by default; one line each)

- P1 literature and `philosophy/PLAN.md`: existing logical formalisations of philosophy (computational metaphysics, Spinoza, Leibniz, mereology, Whitehead's mereotopology, Hegel attempts); mathematical readings of Deleuze (DeLanda, *Intensive Science and Virtual Philosophy*; Duffy, *Deleuze and Mathematics*; Plotnitsky; Smith on Deleuze and the calculus; Badiou's critique; Lautman as the source); any formal treatment of Mark Fisher (hauntology, capitalist realism); a one-page plan.
- P2 `lean/PEqualNP/Philosophy/Deleuze.lean`: the first definitions from PLAN.md, each with a doc comment naming its reading and source, plus small checked lemmas that make the definitions non-trivial (an actual solution is a point where the problem's vector field vanishes; distinct actualisations of one virtual structure differ).
- P3 the bridge: the repository's finite (circuit), polynomial (Φ) and limit levels as instances of P2's virtual / actual structure, importing `Phi` and `slack` (file lives in `one-not/lean/PEqualNP/Philosophy/Bridge.lean`, since slack/Phi live in the one-not Lake project).
- P4 Fisher: hauntology as a branching-time modal structure, futures that were possible and are no longer reachable.

## OPEN / STOPPED

- No open seat. `LimitTarget` in Bridge.lean is a def only, no proof.

## Refuted / dead

- None. Bridge shows the analogy is not an identification: Φ does not determine the slack table (`PhiT_not_injective`) and equal corners do not determine Φ (`corners_not_injective`), at n = 2.

## Decided (one line each; the file holds the proof)

- P1: LITERATURE.md section M (about 25 rows, none read in full; philarchive and tu-dresden fetches blocked) and `philosophy/PLAN.md`: ladder mereology, Spinoza, Leibniz, Deleuze (vector field = virtual, integral curve = actual), five Lean definitions for P2, Fisher on a thin branching-time footing.
- P2: `lean/PEqualNP/Philosophy/Deleuze.lean` builds, standard axioms only: `realize_mem`, `actual_smul`, `distinct_problems_same_actual`, `actual_not_injective`, `nondegenerate_isolated`, `not_linearEquiv_of_dimension_ne`, `extensive_union`, `intensive_not_additive`.
- P3: `one-not/lean/PEqualNP/Philosophy/Bridge.lean` builds, standard axioms only: actual = slack table, virtual = Φ (`Phi_eq_PhiT`, corners `PhiT_zero`, `Phi_one`); non-resemblance both ways at n = 2. Φ is a projection of the slack table, not the whole virtual. Formal analogy, claims nothing about Deleuze or circuits.
- P4: `lean/PEqualNP/Philosophy/Fisher.lean` builds, no axioms: `lost_mono`, `haunted_mono` (cancellation irreversible, uses linear past), `haunted_of_branch`, `capitalist_realism`, `not_lost_of_total`, a 4-node tree example by `decide`. Models only cancelled possibility.
- U1 (Fable, asked for by name by Addison) DECIDED: unification of Fisher, Deleuze, Hegel, Camus, Beauvoir on Fisher's frame. lean/PEqualNP/Philosophy/{Hegel,Camus,Beauvoir,Unify}.lean and one-not/lean/PEqualNP/Philosophy/LevelGap.lean build, standard axioms at most. Main: `unified`, `permanence_iff_no_reconciliation`, `determinate_negation`, `barbarian_iff_lost`, `each_seeks_the_death_of_the_other`, `serious_iff_not_free`, `no_total_answer`, `revolt`, `collapse_iff_injective`, `level_gap`; board rows as a frame: `refuted_lost_forever`, `board_realism`. Failed: "will others free", master / slave, an adjoint cylinder between the levels. "The Barbarians" is not a Beauvoir title; it is Barrès's word in her 1926 diary (search summaries only). -> philosophy/UNIFY.md, LITERATURE.md M5

## Sanity check (coord, for Addison, 2026-11-25), recorded by main
- CLOSED: the search for a Beauvoir text called "The Barbarians". Addison: "there aint gonna be one called the barbarians". The word is Barrès's (*Sous l'œil des barbares*), taken up in her 1926 diary. Do not search for the title again.
- ONLY ANALOGY, model mismatch: by `permanence_iff_no_reconciliation`, a tree forbids reconciliation, but the real one-NOT history did reconcile. The lifted MUL / LiftSDR was built out of refuted real-merge forms. So `refuted_lost_forever` and `board_realism` hold for the hand-coded seven-row tree only, not for the real board, which is a DAG. A DAG model (with joins) is OPEN, and `lost_mono` fails there as stated (UNIFY.md already notes joins break it).
- `level_gap` (one-not/lean/PEqualNP/Philosophy/LevelGap.lean) is proved at n = 2 only. Any prose must say so (UNIFY.md fix passed to the review-fix seat).
- Counting: philosophy findings are now reported separately from the circuit results in boards/TREE.md ("Root counts by program"); they never count toward the circuit numbers.
- Independent review: philosophy/REVIEW.md (54 rows: 13 fine, 34 overclaim, 3 vacuous, 4 misattribution); being applied by a Sonnet seat.
- F3 (Fable) DECIDED, DAG frame: `lean/PEqualNP/Philosophy/DAG.lean` builds, standard axioms. Replacement for `lost_mono`: `lost_or_past` (still lost or now past, never ahead). With conflict (event structures): permanent iff the states clash, else recovered at the union (`lost_forever_iff_clash`, `lost_undone_iff_not_clash`); `salvage_greatest`; tree iff no concurrent forms (`linear_past_iff_no_concurrent`). Beauvoir: `keeps_own_open_iff_keeps_shared_futures` (thin; fails without coherence, `open_each_not_whole`); failed: the other enlarging my freedom (`open_join_iff` rules it out). Ten board rows as data: `history_not_tree`, `lost_mono_fails_on_history`, `refuted_never_returns`, `salvage_pure`. Board wording corrected: the forms refuted when the target moved were pure-class ones; the real-merge price form died at 13:25. -> philosophy/DAG.md
