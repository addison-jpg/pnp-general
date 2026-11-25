# One frame for Fisher, Deleuze, Hegel, Camus and Beauvoir (philosophy-unification seat, 2026-11-25)

Asked for by Addison: "push mark fishers ideas, this could seriously be unifying ... like hegel, camus. just try things."

**Honesty first.** Everything checked here is a theorem about orders, lists and sets. Each is a formal model of a cited reading. None is a claim about what any of these writers meant, none is about circuits, and none bears on P versus NP. Read status of every source is in `LITERATURE.md`, section M5. Almost nothing was read in full.

## The frame in two sentences

A search is a tree of decisions, and a tree of decisions is one of Fisher's branching frames with a first moment (`Hegel.Path`). In that one object a refuted route is at once Fisher's lost future, Hegel's determinate negation, the trace of one of Beauvoir's free moments, Beauvoir's "barbarian", a branch of Deleuze's virtual that the actual line does not show, and a ghost that Camus's endless ascent carries with it; this is one checked theorem, `Unify.unified`.

## What each writer becomes in the frame

| Writer | Concept | In the frame | Checked as |
|---|---|---|---|
| Fisher | lost future, hauntology | a moment that was reachable earlier and is neither ahead nor behind now | `Fisher.Lost`, `Fisher.lost_mono` (seat P4) |
| Fisher | capitalist realism | every future reachable from here has property P; the alternatives are lost futures | `Fisher.capitalist_realism`, on the board: `Unify.board_realism` |
| Deleuze | actual / virtual | the past of the present (one chain) / the whole tree | `Beauvoir.facticity_isChain`, `Unify.actual_does_not_determine_virtual` |
| Hegel | determinate negation | a lost route parts from the present at one definite pair of decisions, and that point is unique | `Hegel.determinate_negation`, `Hegel.determinate_negation_unique` |
| Hegel | sublation | a claim refuted at `c` continues on the greatest domain that avoids `c`; nothing else is given up | `Hegel.sublate_greatest`, `sublate_preserves`, `sublate_ssubset` |
| Hegel, Lawvere | unity and identity of opposites | an adjoint triple with two opposite embeddings: even ⊣ half ⊣ odd on ℕ | `Hegel.unity_and_identity_of_opposites` |
| Camus | the absurd | no assignment of verdicts to moments covers every question about moments | `Camus.no_total_answer` (Lawvere's fixed point theorem) |
| Camus | revolt | with no last moment, every moment starts an endless strict ascent, and lost futures stay lost along it | `Camus.revolt`, `Camus.revolt_keeps_ghosts` |
| Camus | the reduction that never closes | a chain of reductions closes all the way down if it closes anywhere; a size-lowering chain must stop | `Camus.chain_closes`, `Camus.no_infinite_descent` |
| Beauvoir | ambiguity | the present is the only point shared by the given past and the open future | `Beauvoir.ambiguity` |
| Beauvoir | freedom, the serious man | a moment is free when it opens two exclusive futures; seriousness reads the future as one line, and is exactly the denial of freedom | `Beauvoir.serious_iff_not_free` |
| Beauvoir | the barbarians | the one who is not me, was never me and cannot become me; in a rooted frame, exactly my lost futures | `Beauvoir.barbarian_iff_lost` |
| Beauvoir, Hegel | "each consciousness seeks the death of the other" | every continuation of a self cancels its barbarian, both ways; no moment holds both | `Beauvoir.each_seeks_the_death_of_the_other`, `no_recognition_between_barbarians` |

## The connections that are theorems

1. **The lost is the other** (`Hegel.lost_iff_other`, `Hegel.trichotomy`). In a frame with a first moment, a lost future is exactly a moment incomparable with the present. Every moment is past, open or lost, so nothing leaves the frame. That is the formal side of the repository keeping refuted rows with their counterexample files.
2. **Every ghost is the trace of a freedom, and every free act leaves a ghost** (`Beauvoir.haunted_past_free`, `Beauvoir.free_act_haunts`). Fisher's haunting and Beauvoir's freedom are one fact seen from after and from before. A world of serious moments is never haunted (`serious_world_unhaunted`).
3. **The barbarians are one's own lost futures** (`Beauvoir.barbarian_iff_lost`, `barbarian_past_free`). The other is made of what the self gave up at a free moment of its own past. This is as far as the model goes toward Addison's reading "she hates barbarians because she hates herself": the model has no hatred in it, only the identity of the two sets.
4. **Permanence against reconciliation** (`Unify.permanence_iff_no_reconciliation`, in any partial order). Lost futures stay lost for ever exactly when no lost pair ever meets again. Fisher's irreversible cancellation and Hegel's recognition exclude each other. A tree has the first and so forbids the second (`no_recognition_between_barbarians`). A history with joins has the second and loses the first (`Unify.diamond_reconciles`). This is the main new statement.
5. **Levels and ambiguity** (`Unify.collapse_iff_injective`, `Unify.ambiguity_of_levels`). Along a projection from a lower level to an upper one, "some preimage has S" and "every preimage has S" agree for all S exactly when the projection is injective. The Bridge file proved the projection from the finite slack table to Φ is not injective, so in the one-not project `Bridge.level_gap` (file `one-not/lean/PEqualNP/Philosophy/LevelGap.lean`) gives a property of tables on two points that may hold at a polynomial without having to. This is the formal reading of Beauvoir's ambiguity as the refusal to identify the two sides.

## The repository's own history in the frame

`Unify.lean`, section 6, encodes seven rows of the one-NOT board as data: the line A4 → A7 → A10 → BottomPay and the refuted rows C2, C4, L5.

- `refuted_lost`, `refuted_lost_forever`: each refuted row is a lost future of the present, and stays one however the search continues (`lost_mono` applied to the board).
- `refuted_determinate`: each parts from the present at a determinate decision.
- `board_realism`: from the present, every reachable future passes through A4, and each refuted row is an alternative that was possible earlier and is now lost.
- `board_revolt`: the search can always continue, and the refuted rows are lost along the whole continuation.

The names and statuses are copied from the boards. The tree shape is this seat's encoding. Lean does not check the rows themselves.

## The three levels

| Level | Reading | Checked |
|---|---|---|
| Finite (circuits, the actual) | the place where reductions must close, because sizes are natural numbers | `Camus.no_infinite_descent` |
| Polynomial (Φ) | a projection of the finite table; possibility and necessity above come apart | `Unify.collapse_iff_injective`, `Bridge.level_gap`, with P3's `PhiT_not_injective` |
| Limit | open; the place with no last moment | `Camus.Absurd`, `Camus.revolt` are about frames only; `Bridge.LimitTarget` remains a definition with no proof |

The level reading is analogy. The theorems in the right column are true of the abstract objects named, and say nothing about circuits.

## Only analogy (not checked, and should not be read as checked)

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

- `lean/PEqualNP/Philosophy/Hegel.lean`, `Camus.lean`, `Beauvoir.lean`, `Unify.lean` (Mathlib only; standard axioms `propext`, `Classical.choice`, `Quot.sound` at most; build with `lake build PEqualNP.Philosophy.Unify`).
- `one-not/lean/PEqualNP/Philosophy/LevelGap.lean` (imports the Bridge file).
