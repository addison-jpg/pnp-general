# One frame for Fisher, Deleuze, Hegel, Camus and Beauvoir (philosophy-unification seat, 2026-11-25)

Asked for by Addison: "push mark fishers ideas, this could seriously be unifying ... like hegel, camus. just try things."

**Status after review (2026-11-25).** An independent review (`REVIEW.md`) found that the theorem names and bold lines claimed more than the Lean shows. This file was rewritten to say what each theorem shows; philosophical labels below are ours, not the writers'. Several theorems were renamed (see `REVIEW.md`, "Status after review").

**Honesty first.** Everything checked here is a theorem about orders, lists and sets. Each is a formal model of a cited reading. None is a claim about what any of these writers meant, none is about circuits, and none bears on P versus NP. Read status of every source is in `research/LITERATURE.md`, section M5. Almost nothing was read in full.

## The frame in two sentences

A search is a tree of decisions, and a tree of decisions is one of Fisher's branching frames with a first moment (`Hegel.Path`). In that one object a lost route (an incomparable moment) has six consequences, which we label, in turn, Fisher's lost future staying lost, a determinate divergence point (our reading of Hegel), a `Free` moment in the past, a `Barbarian` (our name for an incomparable moment) with no common future, a past that is one chain, and an endless ascent along which it stays lost. `Unify.unified` bundles these six consequences of `Lost m f`; the philosophical labels are ours.

## What each writer becomes in the frame

| Writer | Concept | In the frame | Checked as |
|---|---|---|---|
| Fisher | lost future, hauntology | a moment that was reachable earlier and is neither ahead nor behind now | `Fisher.Lost`, `Fisher.lost_mono` (seat P4) |
| Fisher | capitalist realism (our label only) | `∀ → ¬∃¬` over reachable futures plus an unfolding of `Lost`; ideology and imagination are not modelled | `Fisher.no_alternative_of_all_reachable`; hand-coded tree: `Unify.board_all_futures_extend_A4` |
| (not Deleuze.lean's model) | a second, unrelated use of "actual/virtual" | the past of the present is one chain / the whole tree; equal past length does not fix the tree | `Beauvoir.facticity_isChain`, `Unify.same_past_length_different_haunting` |
| Hegel (our reading) | determinate negation | lost routes share a longest common prefix and then differ; the point is unique. Hegel's notion concerns the content of a refuted standpoint | `Hegel.determinate_negation`, `Hegel.determinate_negation_unique` |
| (not Aufhebung) | removing one element | `D \ {c}` is the greatest subset of `D` avoiding `c`; the counterexample is deleted, not preserved | `Hegel.sublate_greatest`, `sublate_preserves`, `sublate_ssubset` |
| Lawvere's shape, toy | adjoint cylinder | even and odd embeddings of ℕ with `half` as common retraction | `Hegel.even_odd_embeddings_with_half`, `even_half_adjoint`, `half_odd_adjoint` |
| Camus (our choice of model) | the absurd | Cantor/Lawvere on `M → M → Prop`; calling it the absurd is our choice | `Camus.no_total_answer` |
| (not Camus's revolt) | no maximal element | gives an infinite strict chain; Camus's revolt is a lucid stance, not a chain | `Camus.revolt`, `Camus.revolt_keeps_ghosts` |
| (induction on ℕ) | chains of implications | induction over ℕ and well-foundedness of ℕ; the board chain is not encoded | `Camus.chain_closes`, `Camus.no_infinite_descent` |
| (antisymmetry) | `Iic m ∩ Ici m = {m}` | a fact about partial orders; the name "ambiguity" is ours | `Beauvoir.ambiguity` |
| our definitions | `Free`, `Serious` | `Free` = two exclusive futures; `Serious` = future is a chain; the iff is De Morgan on them; not Beauvoir's accounts | `Beauvoir.serious_iff_not_free` |
| Barrès / Beauvoir's word | `Barbarian` = `Other` | incomparable moments; in a rooted frame the same as `Lost`. Modelling other persons as unchosen branches of one timeline is our decision | `Beauvoir.barbarian_iff_lost` |
| (epigraph, our label) | `lost_mono` twice; no common upper bound | "death" is only "becoming `Lost`"; the struggle's self-defeat is not modelled | `Beauvoir.lost_both_ways`, `no_recognition_between_barbarians` |

## The connections that are theorems

1. **The lost is the other** (`Hegel.lost_iff_other`, `Hegel.trichotomy`). In a frame with a first moment, a lost future is exactly a moment incomparable with the present. Every moment is past, open or lost, so nothing leaves the frame. This is a fact about a partial order with a bottom; it says nothing about files or witnesses.
2. **Every ghost is the trace of a freedom, and every free act leaves a ghost** (`Beauvoir.haunted_past_free`, `Beauvoir.free_act_haunts`). In our definitions, `Haunted` and `Free` are one fact seen from after and from before. A world of serious moments is never haunted (`serious_world_unhaunted`).
3. **The barbarians are one's own lost futures** (`Beauvoir.barbarian_iff_lost`, `barbarian_past_free`). The other is made of what the self gave up at a free moment of its own past. Other persons are here modelled as unchosen branches of one timeline, a modelling decision. The reading "she hates barbarians because she hates herself" is unconfirmed; the model has no hatred in it, only the identity of the two sets.
4. **Permanence against reconciliation** (`Unify.permanence_iff_no_reconciliation`, in any partial order). Lost futures stay lost for ever exactly when no lost pair ever meets again. In a partial order, `lost_mono` holds iff no lost pair has a common upper bound; calling the latter "recognition" is our label. A tree has the first and so forbids the second (`no_recognition_between_barbarians`). A history with joins has the second and loses the first (`Unify.diamond_reconciles`). This is a short order-theoretic lemma.
5. **Levels and ambiguity** (`Unify.collapse_iff_injective`, `Unify.ambiguity_of_levels`). Along a projection from a lower level to an upper one, "some preimage has S" and "every preimage has S" agree for all S exactly when the projection is injective. The Bridge file proved, for some pairs of integer tables on `Fin 2` (n = 2 only), that the projection to Φ is not injective, so in the one-not project `Bridge.level_gap` (file `proofs/w951/PEqualNP/Philosophy/LevelGap.lean`) gives, for integer tables on two points only (n = 2), a set S whose image under the table-to-polynomial map is not inside its kernel image (some table with this polynomial has the property, but not every one does). This is a generic fact about non-injective maps; no Beauvoir label is claimed. The Bridge file proved non-injectivity only for arbitrary integer tables on `Fin 2`, not for slack tables of circuits.

## The repository's own history in the frame

`Unify.lean`, section 6, encodes seven rows of the one-NOT board as data: the line A4 → A7 → A10 → BottomPay and the refuted rows C2, C4, L5.

- `refuted_lost`, `refuted_lost_forever`: in the hand-coded seven-row tree only, each refuted row is a lost future of the present and stays one (`lost_mono` applied to the encoding). This is an encoding check, true by definition of `route`.
- `refuted_determinate`: each parts from the present at a determinate decision.
- `board_all_futures_extend_A4` (formerly `board_realism`): in that tree only, every future reachable from the present extends A4. True by definition of `route`; nothing on the real board can fail it. Not "capitalist realism on the board".
- `board_revolt`: the search can always continue, and the refuted rows are lost along the whole continuation.

The names and statuses are copied from the boards. The tree shape is this seat's encoding. Lean does not check the rows themselves.

## The three levels

| Level | Reading | Checked |
|---|---|---|
| Finite (circuits, the actual) | the place where reductions must close, because sizes are natural numbers | `Camus.no_infinite_descent` |
| Polynomial (Φ) | a projection of the finite table; image and kernel image differ for some S (n = 2, arbitrary tables only) | `Unify.collapse_iff_injective`, `Bridge.level_gap`, with P3's `PhiT_not_injective` |
| Limit | open; the place with no last moment | `Camus.Absurd`, `Camus.revolt` are about frames only; `Bridge.LimitTarget` remains a definition with no proof |

The level reading is analogy. The theorems in the right column are true of the abstract objects named, and say nothing about circuits.

## Only analogy (not checked, and should not be read as checked)

- **The tree is not the real history.** `refuted_lost_forever` and `board_all_futures_extend_A4` hold for the hand-coded seven-row tree only. The real one-NOT history is a DAG, not a tree: the lifted MUL / LiftSDR was built from refuted real-merge forms, which is a reconciliation. By `permanence_iff_no_reconciliation`, a tree forbids that, so the permanence of loss shown in the tree does not describe the real project.
- `level_gap` is proved at n = 2 only, for arbitrary integer tables, not slack tables of circuits.

- That the board's chain of reductions *is* Hegel's determinate negation. What is checked is that lost routes differ from the present at a definite point, and that a counterexample fixes the greatest surviving domain. Whether an obstacle "determines the next statement" on the real board is a judgement.
- That Camus's absurd *is* the diagonal argument. `no_total_answer` is Cantor's theorem; calling it the absurd is this seat's choice.
- That the limit level is "absurd". Nothing is proved about the limit level.
- Beauvoir's hatred, self-contempt and the "attack on an agent" reading. The model has positions only.

## What failed, or was not tried

- **"To will oneself free is also to will others free."** No non-trivial theorem found. In a tree, two selves that are barbarians to each other share no future at all, so the frame cannot even state a shared open future. Result 4 says why: reciprocity needs joins, and joins undo permanence. A frame for Beauvoir's ethics would be a directed graph with merges, in which `lost_mono` is false.
- **Master and slave.** Only the bare point that a fight to the death rules out recognition (`no_recognition_between_barbarians`). No model of labour, dependence or the reversal.
- **Paraconsistent dialectic.** Only the textbook fact that Priest's LP has contradictions without explosion (`Hegel.lp_no_explosion`). It is not connected to the frame, and the literature disputes that Hegel is paraconsistent.
- **Lawvere's adjoint cylinder inside the frame.** The cylinder is checked on ℕ only. No adjoint triple with two full outer maps was found between the repository's levels; what the levels have is the weaker triple image ⊣ preimage ⊣ kernel image (`Unify.level_adjoints`).
- **The slack table as the virtual.** The Bridge finding suggested it. Here the virtual is the search tree, a different object. The two readings are not joined.
- **Same past, different tree** is stated through equal length of the past, not through an order isomorphism of the two pasts.

## "The barbarians": what was verified

- **No text by Beauvoir titled "The Barbarians" was found** (one search). Her 1954 novel is *The Mandarins*.
- **Confirmed from search summaries only** (the diary itself was not opened; bookforum.com is outside this session's network):
  - *Diary of a Philosophy Student, Volume 1, 1926-27* (University of Illinois Press, 2006): the editors' notes place Beauvoir reading Maurice Barrès, *Sous l'œil des barbares* (1888, first volume of *Le Culte du moi*), in the entry of 5 October 1926.
  - A Bookforum review reports that, inspired by Barrès, she felt surrounded by "barbarians", and quotes the diary: "You are all barbarians, even if you might be right, O you who are not me!"
  - On 10 July 1927 she names her problem "this opposition of self and other" (Simons, "Beauvoir's Early Philosophy: 1926-27", in the same volume), two years before meeting Sartre.
  - Writers the diary reflects on or quotes, per reviews: Kant, Bergson (the *Essai sur les données immédiates*, quoted at length), Nietzsche, Schopenhauer, Barrès, Claudel, Cocteau, Gide, Alain-Fournier, Rivière, Mauriac, Goethe.
- **Not confirmed:** "Claudia" as the source (Claudel is among the writers she reads, and may be the name remembered; the barbarians come from Barrès); the philosopher Alain and Lagneau in the diary; the phrase about the claws of society; the date of the quoted line; the French wording; any statement by Beauvoir that the hatred of the barbarians is self-hatred.
- ***She Came to Stay* (*L'Invitée*, 1943):** confirmed from secondary sources that its epigraph is Hegel's "Chaque conscience poursuit la mort de l'autre" and that it ends with Françoise killing Xavière. The Stanford Encyclopedia entry adds that the murder destroys a particular other, not the other as such (`Beauvoir.not_every_other_dies` is the model of that remark). Pierre's part was not checked. The novel was not opened.
- ***Wartime Diary*:** not verified in this session. Not used.

The model uses only "you who are not me" and "even if you might be right".

## Files

- `proofs/main/PEqualNP/Philosophy/Hegel.lean`, `Camus.lean`, `Beauvoir.lean`, `Unify.lean` (Mathlib only; standard axioms `propext`, `Classical.choice`, `Quot.sound` at most; build with `lake build PEqualNP.Philosophy.Unify`).
- `proofs/w951/PEqualNP/Philosophy/LevelGap.lean` (imports the Bridge file).
