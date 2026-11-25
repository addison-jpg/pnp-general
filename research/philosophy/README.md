# research/philosophy/

A crude, checked formal model of one reading of Deleuze's core concepts (multiplicity,
difference, virtual / actual, problem / solution, intensity). `PLAN.md` plans a ladder of existing
formalisations (mereology, Spinoza, Leibniz, then Deleuze); only the Deleuze rung is built.

It models cited readings (DeLanda, Duffy, Smith, Plotnitsky, Lautman). It claims nothing about what
Deleuze meant, and a model is not a proof about a text.

- [`PLAN.md`](PLAN.md): the ladder, the first Lean definitions, the bridge to this repository.
- Lean code: [`proofs/main/PEqualNP/Philosophy/Deleuze.lean`](../../proofs/main/PEqualNP/Philosophy/Deleuze.lean) (Mathlib only). Fisher, Hegel, Camus, Beauvoir, Unify are next to it; the Bridge and LevelGap files are in `proofs/w951/PEqualNP/Philosophy/` and import project code. An independent review and what was done about it: [`REVIEW.md`](REVIEW.md).
- [`UNIFY.md`](UNIFY.md): one frame for Fisher, Deleuze, Hegel, Camus and Beauvoir (Fisher's branching time, enriched), what is checked, what is analogy, what failed. Lean: `Hegel.lean`, `Camus.lean`, `Beauvoir.lean`, `Unify.lean` next to `Deleuze.lean` and `Fisher.lean`.
- Literature with honest read status: `research/LITERATURE.md`, section M. Board: `boards/tasks/philosophy-formal.md`.
