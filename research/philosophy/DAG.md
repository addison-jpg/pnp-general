# The DAG frame: research states with joins (seat F3, 2026-11-25)

Lean: `proofs/main/PEqualNP/Philosophy/DAG.lean` (Mathlib plus `Fisher.lean`). Build: `cd lean && lake build PEqualNP.Philosophy.DAG`. No `sorry`. `#print axioms` on every theorem: `propext`, `Classical.choice`, `Quot.sound` at most.

**What this is.** The reviews found that the tree model does not describe the real board, which reconciled (`boards/tasks/philosophy-formal.md`, "model mismatch"). This file builds the model with joins and proves what replaces `Fisher.lost_mono` in it. Every theorem is about partial orders or event structures. The philosophical labels are ours. Nothing here is about circuits or bears on P versus NP.

**The formalism is not ours.** Sections 2 and 3 use prime event structures with binary conflict and their configurations (Nielsen, Plotkin, Winskel 1981; Winskel 1987; cited from memory, not re-read). The facts proved there are textbook facts about that formalism. What this seat adds is the reading, the comparison with Fisher's tree, and the encoding of the board.

## 1. Checked

### Any partial order

| Theorem | Statement | Vacuous? |
|---|---|---|
| `lost_or_past` | If `f` is lost at `m` and `m ≤ m'`, then `f` is lost at `m'` or `f ≤ m'`. | No. It is three lines, and it is the exact replacement for `lost_mono`: with a linear past the second case cannot happen. |
| `lost_never_ahead` | A lost `f` is never ahead again: `¬ m' ≤ f` for every `m' ≥ m`. | One line (transitivity). Stated because it is the part of permanence that survives joins. |
| `lost_forever_iff_apart` | A loss is permanent exactly when the two have no common later state. | No, but small. It is the pointwise form of `Unify.permanence_iff_no_reconciliation`. |
| `lost_undone_iff_rejoin` | A loss is undone at some later moment exactly when a common later state exists. | Small; follows from `lost_or_past`. |

`Lost`, `Rejoin` and `Apart` are the same formulas as `Unify.LostP`, `Beauvoir.Recognise` and `BeauvoirQG.Beyond`. They are restated so the file needs only `Fisher.lean`.

### Forms with conflict (`Forms`, `State`)

A `Forms` is a set of forms (definitions, statements, counterexamples) with "built using" (`≤`) and a conflict relation that is inherited by whatever is built on either side. A `State` is a set of forms closed under "built using" with no two in conflict. States are ordered by inclusion.

| Theorem | Statement | Vacuous? |
|---|---|---|
| `rejoin_iff_not_clash`, `join_isLUB` | Two states have a common later state exactly when no form of one conflicts with a form of the other. Then their union is a state and is the least one. | No. The proof builds the union and checks it. |
| `bounded_of_pairwise` | States that can be joined two at a time can be joined all at once. | No. It is false in a general partial order (`tri_pairwise_not_bounded`). |
| `lost_forever_iff_clash` | **Which losses stay permanent:** exactly those between states that clash. | Follows from the two rows above. |
| `lost_undone_iff_not_clash` | **Which losses a join recovers:** exactly those with no clash, at the union. | Same. |
| `salvage_greatest`, `salvage_rejoin`, `salvage_eq_iff` | From a branch `y` that clashes with `x`, there is a greatest earlier state of `y` that `x` can still be joined with: the forms of `y` in conflict with nothing in `x`. | No. A greatest one need not exist in a general partial order; here it does because conflict is binary and inherited. |
| `linear_past_iff_no_concurrent` | The states have a linear past (are a Fisher frame) exactly when no two forms are concurrent, that is, unrelated and not in conflict. | No. Both directions need a short argument. |
| `all_loss_permanent_iff_no_concurrent` | Every loss is permanent exactly when no two forms are concurrent. | No. |
| `frameOfNoConcurrent` | With no concurrent forms, `State E` is a `Fisher.Frame`, so `Fisher.lean` applies unchanged. | A definition. |

So Fisher's tree is the special case of this frame in which any two independent forms exclude each other.

### Beauvoir's sentence

`Open x e`: some later state of `x` holds the form `e`. `Choice x`: two forms, each open to `x`, in conflict with each other.

| Theorem | Statement | Vacuous? |
|---|---|---|
| `rejoin_iff_forall_open` | A whole other state can share a future with `x` exactly when each of its forms, alone, is open to `x`. | No. False without binary conflict: `open_each_not_whole`. |
| `keeps_own_open_iff_keeps_shared_futures` | A move from `x` to `x'` closes off no form that was open to `x` exactly when every state that could be joined with `x` can still be joined with `x'`. | Not true by definition, but thin. Right to left is the special case of a one-form state. Left to right is the row above. |
| `open_each_not_whole`, `tri_pairwise_not_bounded` | In the proper subsets of a three-element set, each form of the other is open to the self and the other as a whole is not. | A counterexample, by computation. It shows the two rows above have content. |
| `open_join_iff` | A joined state has open exactly the forms open to both. | Short. It is a negative result (see section 3). |
| `choice_join_iff`, `sharedChoiceFails` | A joined state has a real choice exactly when one choice is open to both. Each having a choice of their own is not enough (a case in the board data). | `choice_join_iff` is an unfolding. The counterexample is computed. |

### The one-NOT history as data

Ten rows and their "built using" edges are copied by this seat from `boards/one-not.md` (2026-11-24 lines "09:30", "10:45", "OFFICIAL TARGET 10:47", "12:20 TARGET WARNING", "OFFICIAL TARGET ~12:27", "DECISION 12:46", "13:25 integrator [DEAD]"), `research/one-not/DEAD_ENDS.md` family D, the Lean names `liftSDR_of_pureSDR` (`W951/PureGP.lean`) and `mergeSet_eq_lift` (`W951/PureLLift.lean`), and commit 7e0da84. Lean checks the encoding only.

| Theorem | Statement | What kind of check |
|---|---|---|
| `instance : Forms Row` | The table is a partial order with an inherited, irreflexive conflict. | Encoding check. It would fail if a row were built on both a claim and its counterexample. |
| `present` | The rows not recorded as refuted form a state. | Encoding check. It would fail if a kept row were built on a refuted claim. |
| `history_not_tree`, `history_states_not_tree`, `targets_concurrent` | The lifted classes have two unrelated parents. The open targets LiftSDR / MUL and BottomPay are concurrent. Neither the rows nor the states are a Fisher frame. | Computed from the edges. |
| `lines_reconciled`, `lost_mono_fails_on_history` | The merge-set line and the pure-class line were lost to each other and both lie in the past of the lifted classes. `lost_mono` is false for the states of this history. | Computed from the edges. |
| `closed_iff_refuted` | The rows closed to the present are exactly the rows recorded as refuted. | Compares two columns that this seat wrote (edges plus refutation list against the `kind` column). A consistency check of the table. |
| `refuted_never_returns`, `refuted_branch_lost_forever` | A refuted claim is in no later state of the present, and its branch stays lost. | General theory applied to the table. |
| `salvage_pure`, `salvage_merge` | From the branch of "PureSDR for every correct circuit" the present can take over exactly the pure classes. From the branch of the real-merge price form, exactly the merge sets. | Computed. |
| `refuted_material_reused` | Pure classes, merge sets and `cxMU_dd` are all in the past of the lifted target. | True by the edges as written. |

**Answer to the task's question.** With joins, a refuted claim stays lost for ever, because it conflicts with its counterexample and conflict is inherited. The material the claim was about is not lost: it is the salvage, and the lifted target was built on it. The tree could not say this because it had one node for both.

## 2. Interpretation (not checked, and should not be read as checked)

- **A refuted row is two things.** Splitting each refuted row into a definition and a universal claim is this seat's decision. The conclusion "the material was reused" is put in by that split and by the edges; Lean cannot confirm that the lifted forms were in fact built from the pure classes and merge sets. The sources say that pure classes and real merge sets are lifted classes; "built using" is a reading of that.
- **One correction to the board's wording.** `boards/tasks/philosophy-formal.md` says the lifted target was built from "refuted real-merge forms". On `boards/one-not.md`, the forms refuted when the target moved (12:20 to 12:27) were the pure-class ones (`cxMU_dd`). The real-merge price form is recorded dead at 13:25 (STAR4), after the move. Both refutations are in the table; the edge into the lifted target is from `cxMU_dd` only.
- **Fisher.** "A lost future never becomes a future again; it can only become part of a later past" is our gloss of `lost_or_past`. It is a statement about orders. Whether a future that returns only as material counts as "lost" in Fisher's sense is not something the model can settle.
- **Hegel.** `salvage` keeps a content of the refuted branch, where `Hegel.sublate` only deleted one element. Calling it determinate negation or Aufhebung would be our label. The model has no account of why the content is kept.
- **Beauvoir.** In `keeps_own_open_iff_keeps_shared_futures`, "to will oneself free" is read as "to close off nothing that was open to oneself" and "to will others free" as "to break no shared future with any other state". Both readings are ours and much weaker than hers. Her argument in *The Ethics of Ambiguity* is that my projects need other freedoms to take them up; the theorem says something different and smaller.
- **Other persons.** States are sets of forms, not persons. The model has no agents, so "self" and "other" are just two states.
- **A consequence that cuts against the reading.** Any open form that conflicts with another open form closes that one off when adopted. So a move that "closes nothing off" adopts only forms that conflict with nothing still open. The theorem therefore concerns a narrow class of moves.

## 3. Failed

- **"The other's freedom enlarges mine."** Not found, and the frame rules it out: by `open_join_iff` a join never adds an open form, it can only narrow. What the other contributes in this model is forms already built, which is the definition of "built using", so a statement of the kind "my future requires your act" is true by the heredity axiom and was not stated as a theorem.
- **A shared choice from two separate ones.** False (`sharedChoiceFails`).
- **Recognition, master and slave.** Not attempted. `Rejoin` is still only "a common later state".
- **The whole board.** Ten rows of one episode (2026-11-24, merge sets to the lifted target, plus the line to BottomPay as one row). The chain A4, A7, A10 is one row here. The refuted rows C2, C4 and L5 of the seven-row tree in `Unify.lean` are not placed, because their edges to the lifted forms were not established from the boards.
- **Clock times.** The board's times mix time zones, so no times are encoded and "earlier" is only "built using".
- **Git log as a source.** Only two commits are used (7e0da84, ee732a5). The edges come from board lines, not from commit ancestry.
- **Finite causes.** The event-structure axiom that each form has finitely many causes is not assumed; nothing proved here needs it, and nothing here uses the domain theory that does.
