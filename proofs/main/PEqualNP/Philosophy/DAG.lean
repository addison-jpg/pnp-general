import Mathlib
import PEqualNP.Philosophy.Fisher

/-!
# The DAG frame: research states with joins (seat F3)

HONESTY. Every theorem here is about partial orders and about event structures. Each definition
names its reading. The readings are ours; nothing is claimed about what Fisher, Hegel or Beauvoir
meant, nothing is about circuits, and nothing bears on P versus NP. Section 4 encodes ten rows of
the one-NOT board as DATA; Lean checks the encoding, never the rows.

Why this file. `Fisher.lost_mono` needs a linear past, so it describes a tree. By
`Unify.permanence_iff_no_reconciliation` a tree forbids reconciliation. The real board history
reconciled (the lifted target was built from the material of refuted forms), so the tree is the
wrong model (`boards/tasks/philosophy-formal.md`, "model mismatch").

The existing formalisation used: prime event structures with binary conflict and their
configurations (Nielsen, Plotkin, Winskel, "Petri nets, event structures and domains, part I",
Theoretical Computer Science 13 (1981); Winskel, "Event structures", LNCS 255 (1987)). Cited from
memory, not re-read. Finiteness of causes, which those papers assume, is not assumed here and is
not needed for what is proved. The results of sections 2 and 3 are textbook facts about that
formalism (coherence of the configuration domain), proved here from Mathlib plus `Fisher.lean`.

Reading of Beauvoir's sentence: *Pour une morale de l'ambiguïté* (1947), end of part II, in
Frechtman's translation "To will oneself free is also to will others free". Cited from memory, in
copyright, not re-read. Prose: `research/philosophy/DAG.md`.
-/

namespace PEqualNP.Philosophy.DAG

/-! ## 1. Any partial order: what replaces `lost_mono` -/

section Order

variable {P : Type*} [PartialOrder P]

/-- Reading: Fisher's lost future, as in `Fisher.Lost`, with no linear past assumed. `f` was
reachable from a common earlier moment, and is now neither ahead of `m` nor behind it. The same
formula as `Unify.LostP`. -/
def Lost (m f : P) : Prop := (∃ a, a ≤ m ∧ a ≤ f) ∧ ¬ m ≤ f ∧ ¬ f ≤ m

/-- Reading: a join, a later state that has both in its past. The same formula as
`Beauvoir.Recognise`; "reconciliation" is our word for it. -/
def Rejoin (m f : P) : Prop := ∃ w, m ≤ w ∧ f ≤ w

/-- Reading: no later state has both in its past. The same formula as `BeauvoirQG.Beyond`. -/
def Apart (m f : P) : Prop := ¬ Rejoin m f

/-- On a Fisher frame `Lost` is `Fisher.Lost`. -/
theorem lost_iff_fisher {M : Type*} [Fisher.Frame M] {m f : M} : Lost m f ↔ Fisher.Lost m f :=
  Iff.rfl

/-- **The replacement for `lost_mono`.** In any partial order, a lost future is, at every later
moment, either still lost or part of the past. -/
theorem lost_or_past {m m' f : P} (h : m ≤ m') (hl : Lost m f) : Lost m' f ∨ f ≤ m' := by
  obtain ⟨⟨a, ham, haf⟩, hmf, _⟩ := hl
  by_cases hf : f ≤ m'
  · exact Or.inr hf
  · exact Or.inl ⟨⟨a, ham.trans h, haf⟩, fun h' => hmf (h.trans h'), hf⟩

/-- What stays permanent with joins: a lost future is never ahead again. -/
theorem lost_never_ahead {m m' f : P} (h : m ≤ m') (hl : Lost m f) : ¬ m' ≤ f :=
  fun h' => hl.2.1 (h.trans h')

/-- With a linear past the second case of `lost_or_past` cannot occur; this is `Fisher.lost_mono`
again. -/
theorem lost_mono_of_frame {M : Type*} [Fisher.Frame M] {m m' f : M} (h : m ≤ m')
    (hl : Lost m f) : Lost m' f :=
  Fisher.lost_mono h hl

/-- Being apart is inherited by all later states on both sides. -/
theorem apart_mono {m m' f f' : P} (hm : m ≤ m') (hf : f ≤ f') (h : Apart m f) : Apart m' f' :=
  fun ⟨w, hw, hw'⟩ => h ⟨w, hm.trans hw, hf.trans hw'⟩

/-- A loss is permanent exactly when the two are apart. Pointwise form of
`Unify.permanence_iff_no_reconciliation`. -/
theorem lost_forever_iff_apart {m f : P} (hl : Lost m f) :
    (∀ m', m ≤ m' → Lost m' f) ↔ Apart m f := by
  constructor
  · rintro h ⟨w, hw, hw'⟩
    exact (h w hw).2.2 hw'
  · intro h m' hm
    refine (lost_or_past hm hl).resolve_right fun hf => h ⟨m', hm, hf⟩

/-- A loss is undone at some later moment exactly when a join exists. -/
theorem lost_undone_iff_rejoin {m f : P} (hl : Lost m f) :
    (∃ m', m ≤ m' ∧ ¬ Lost m' f) ↔ Rejoin m f := by
  constructor
  · rintro ⟨m', hm, hn⟩
    rcases lost_or_past hm hl with h | h
    · exact absurd h hn
    · exact ⟨m', hm, h⟩
  · rintro ⟨w, hw, hw'⟩
    exact ⟨w, hw, fun h => h.2.2 hw'⟩

end Order

/-! ## 2. Forms with conflict: which losses are permanent, and what a join recovers -/

/-- Reading: the forms (definitions, statements, counterexamples) that a research history can
adopt. `a ≤ b`: `b` was built using `a`. `conflict a b`: no state can hold both, as with a
universal claim and its counterexample. Conflict is inherited by everything built on either side.
This is a prime event structure with binary conflict (Nielsen, Plotkin, Winskel 1981), without the
finite-causes axiom. -/
class Forms (E : Type*) extends PartialOrder E where
  /-- No state holds both. -/
  conflict : E → E → Prop
  conflict_symm : ∀ {a b : E}, conflict a b → conflict b a
  conflict_irrefl : ∀ a : E, ¬ conflict a a
  conflict_hered : ∀ {a b c : E}, conflict a b → b ≤ c → conflict a c

open Forms

section FormsTheory

variable {E : Type*} [Forms E]

/-- Reading: a research state, the set of forms adopted so far. It contains whatever its forms
were built from, and holds no two forms in conflict. This is a configuration of the event
structure. -/
@[ext] structure State (E : Type*) [Forms E] where
  /-- The forms adopted. -/
  carrier : Set E
  lower : ∀ {a b : E}, a ≤ b → b ∈ carrier → a ∈ carrier
  free : ∀ {a b : E}, a ∈ carrier → b ∈ carrier → ¬ conflict a b

/-- States are ordered by inclusion: `x ≤ y` reads "`y` is a later state of `x`". -/
instance : PartialOrder (State E) :=
  PartialOrder.lift State.carrier fun _ _ h => State.ext h

theorem State.le_def {x y : State E} : x ≤ y ↔ x.carrier ⊆ y.carrier := Iff.rfl

/-- The state before anything is adopted. -/
def State.empty : State E where
  carrier := ∅
  lower := fun _ h => h.elim
  free := fun h => h.elim

theorem State.empty_le (x : State E) : State.empty ≤ x := fun _ h => h.elim

/-- Reading: the least state that holds the form `e`, its whole provenance. -/
def cone (e : E) : State E where
  carrier := Set.Iic e
  lower := fun hab hb => le_trans hab hb
  free := fun {_ b} (ha : _ ≤ e) (hb : b ≤ e) hc =>
    conflict_irrefl e (conflict_hered (conflict_symm (conflict_hered hc hb)) ha)

theorem cone_le_iff {e : E} {x : State E} : cone e ≤ x ↔ e ∈ x.carrier :=
  ⟨fun h => h (le_refl e : e ∈ Set.Iic e), fun h _ ha => x.lower ha h⟩

theorem cone_le_cone {e e' : E} : cone e ≤ cone e' ↔ e ≤ e' := cone_le_iff

/-- Reading: some form of `x` is in conflict with some form of `y`. -/
def Clash (x y : State E) : Prop := ∃ a ∈ x.carrier, ∃ b ∈ y.carrier, conflict a b

/-- The union of two states with no clash is a state: the join. -/
def join (x y : State E) (h : ¬ Clash x y) : State E where
  carrier := x.carrier ∪ y.carrier
  lower := fun hab hb => hb.imp (x.lower hab) (y.lower hab)
  free := by
    rintro a b (ha | ha) (hb | hb) hc
    · exact x.free ha hb hc
    · exact h ⟨a, ha, b, hb, hc⟩
    · exact h ⟨b, hb, a, ha, conflict_symm hc⟩
    · exact y.free ha hb hc

theorem join_isLUB (x y : State E) (h : ¬ Clash x y) : IsLUB {x, y} (join x y h) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rintro z (rfl | rfl)
    · exact fun _ ha => Or.inl ha
    · exact fun _ ha => Or.inr ha
  · rintro a (ha | ha)
    · exact hw (Set.mem_insert _ _) ha
    · exact hw (Set.mem_insert_of_mem _ rfl) ha

/-- Two states have a join exactly when no form of one conflicts with a form of the other. -/
theorem rejoin_iff_not_clash {x y : State E} : Rejoin x y ↔ ¬ Clash x y :=
  ⟨fun ⟨w, hx, hy⟩ ⟨_, ha, _, hb, hc⟩ => w.free (hx ha) (hy hb) hc,
    fun h => ⟨join x y h, fun _ ha => Or.inl ha, fun _ ha => Or.inr ha⟩⟩

theorem apart_iff_clash {x y : State E} : Apart x y ↔ Clash x y := by
  rw [Apart, rejoin_iff_not_clash, not_not]

/-- Coherence: a family of states that can be joined two at a time can be joined all at once. -/
theorem bounded_of_pairwise {ι : Type*} (x : ι → State E) (h : ∀ i j, Rejoin (x i) (x j)) :
    ∃ w : State E, ∀ i, x i ≤ w := by
  refine ⟨⟨⋃ i, (x i).carrier, ?_, ?_⟩, fun i _ ha => Set.mem_iUnion.2 ⟨i, ha⟩⟩
  · intro a b hab hb
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hb
    exact Set.mem_iUnion.2 ⟨i, (x i).lower hab hi⟩
  · intro a b ha hb hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    exact rejoin_iff_not_clash.1 (h i j) ⟨a, hi, b, hj, hc⟩

/-- Between states, lost means incomparable (the empty state is below both). -/
theorem lost_iff_incomparable {x y : State E} : Lost x y ↔ ¬ x ≤ y ∧ ¬ y ≤ x :=
  ⟨fun h => h.2, fun h => ⟨⟨State.empty, State.empty_le x, State.empty_le y⟩, h⟩⟩

/-- **Which losses stay permanent.** Between research states a loss is permanent exactly when the
two states clash. -/
theorem lost_forever_iff_clash {x y : State E} (h : Lost x y) :
    (∀ x', x ≤ x' → Lost x' y) ↔ Clash x y :=
  (lost_forever_iff_apart h).trans apart_iff_clash

/-- **Which losses a join recovers.** A loss is undone later exactly when the states do not
clash, and then it is undone at the union. -/
theorem lost_undone_iff_not_clash {x y : State E} (h : Lost x y) :
    (∃ x', x ≤ x' ∧ ¬ Lost x' y) ↔ ¬ Clash x y :=
  (lost_undone_iff_rejoin h).trans rejoin_iff_not_clash

/-- Reading: what `x` can take over from `y`: the forms of `y` not in conflict with any form of
`x`. (Our reading of "the refuted branch keeps a content"; compare `Hegel.sublate`, which only
deletes.) -/
def salvage (x y : State E) : State E where
  carrier := {b | b ∈ y.carrier ∧ ∀ a ∈ x.carrier, ¬ conflict a b}
  lower := fun hab hb =>
    ⟨y.lower hab hb.1, fun a ha hc => hb.2 a ha (conflict_hered hc hab)⟩
  free := fun ha hb => y.free ha.1 hb.1

theorem salvage_le (x y : State E) : salvage x y ≤ y := fun _ h => h.1

theorem salvage_rejoin (x y : State E) : Rejoin x (salvage x y) :=
  rejoin_iff_not_clash.2 fun ⟨a, ha, _, hb, hc⟩ => hb.2 a ha hc

/-- **What a join recovers from a clashing branch.** Among the earlier states of `y` that `x`
can still be joined with there is a greatest one, `salvage x y`. -/
theorem salvage_greatest {x y z : State E} (hz : z ≤ y) (h : Rejoin x z) : z ≤ salvage x y :=
  fun b hb => ⟨hz hb, fun a ha hc => rejoin_iff_not_clash.1 h ⟨a, ha, b, hb, hc⟩⟩

/-- Nothing is given up exactly when the two can be joined. -/
theorem salvage_eq_iff {x y : State E} : salvage x y = y ↔ Rejoin x y :=
  ⟨fun h => h ▸ salvage_rejoin x y, fun h => le_antisymm (salvage_le x y) (salvage_greatest le_rfl h)⟩

/-- Reading: two forms that are independent: neither was built from the other and they are not
in conflict. A tree has none. -/
def Concurrent (e e' : E) : Prop := ¬ e ≤ e' ∧ ¬ e' ≤ e ∧ ¬ conflict e e'

theorem cone_rejoin_of_not_conflict {e e' : E} (h : ¬ conflict e e') :
    Rejoin (cone e) (cone e') :=
  rejoin_iff_not_clash.2 fun ⟨_, ha, _, hb, hc⟩ =>
    h (conflict_symm (conflict_hered (conflict_symm (conflict_hered hc hb)) ha))

/-- **Fisher's tree is the frame with no independent forms.** The states have a linear past
exactly when no two forms are concurrent. -/
theorem linear_past_iff_no_concurrent :
    (∀ a b c : State E, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a) ↔ ¬ ∃ e e' : E, Concurrent e e' := by
  constructor
  · rintro h ⟨e, e', h1, h2, h3⟩
    obtain ⟨w, hw, hw'⟩ := cone_rejoin_of_not_conflict h3
    rcases h _ _ w hw hw' with c | c
    · exact h1 (cone_le_cone.1 c)
    · exact h2 (cone_le_cone.1 c)
  · intro h a b c ha hb
    by_contra hc
    rw [not_or] at hc
    obtain ⟨p, hpa, hpb⟩ := Set.not_subset.1 hc.1
    obtain ⟨q, hqb, hqa⟩ := Set.not_subset.1 hc.2
    exact h ⟨p, q, fun hpq => hpb (b.lower hpq hqb), fun hqp => hqa (a.lower hqp hpa),
      c.free (ha hpa) (hb hqb)⟩

/-- Every loss between states is permanent exactly when no two forms are concurrent. -/
theorem all_loss_permanent_iff_no_concurrent :
    (∀ x y : State E, Lost x y → Apart x y) ↔ ¬ ∃ e e' : E, Concurrent e e' := by
  constructor
  · rintro h ⟨e, e', h1, h2, h3⟩
    exact h (cone e) (cone e')
      (lost_iff_incomparable.2 ⟨fun c => h1 (cone_le_cone.1 c), fun c => h2 (cone_le_cone.1 c)⟩)
      (cone_rejoin_of_not_conflict h3)
  · rintro h x y hl ⟨w, hx, hy⟩
    obtain ⟨p, hpx, hpy⟩ := Set.not_subset.1 hl.2.1
    obtain ⟨q, hqy, hqx⟩ := Set.not_subset.1 hl.2.2
    exact h ⟨p, q, fun hpq => hpy (y.lower hpq hqy), fun hqp => hqx (x.lower hqp hpx),
      w.free (hx hpx) (hy hqy)⟩

/-- With no concurrent forms the states are a Fisher frame, so all of `Fisher.lean` applies. -/
@[reducible] def frameOfNoConcurrent (h : ¬ ∃ e e' : E, Concurrent e e') : Fisher.Frame (State E) :=
  { (inferInstance : PartialOrder (State E)) with
    linear_past := linear_past_iff_no_concurrent.2 h }

/-! ## 3. Beauvoir's sentence, in this frame -/

/-- Reading: the form `e` is still open to the state `x`: some later state of `x` holds it. -/
def Open (x : State E) (e : E) : Prop := Rejoin x (cone e)

theorem open_iff {x : State E} {e : E} : Open x e ↔ ∀ a ∈ x.carrier, ¬ conflict a e := by
  rw [Open, rejoin_iff_not_clash]
  exact ⟨fun h a ha hc => h ⟨a, ha, e, le_refl e, hc⟩,
    fun h ⟨a, ha, _, hb, hc⟩ => h a ha (conflict_hered hc hb)⟩

/-- A whole other state can share a future with `x` exactly when each of its forms, taken alone,
is still open to `x`. -/
theorem rejoin_iff_forall_open {x y : State E} : Rejoin x y ↔ ∀ b ∈ y.carrier, Open x b := by
  rw [rejoin_iff_not_clash]
  exact ⟨fun h b hb => open_iff.2 fun a ha hc => h ⟨a, ha, b, hb, hc⟩,
    fun h ⟨a, ha, b, hb, hc⟩ => open_iff.1 (h b hb) a ha hc⟩

/-- **The candidate for "to will oneself free is also to will others free".** A move from `x` to
`x'` closes off no form that was open to `x` exactly when it breaks no shared future: every state
that could be joined with `x` can still be joined with `x'`. The left side speaks of single forms
open to the self; the right side of whole other states. The step from left to right is coherence
(`rejoin_iff_forall_open`); it fails without binary conflict (`open_each_not_whole`). "Free" as
"closes nothing off" is our reading and is much weaker than Beauvoir's freedom. -/
theorem keeps_own_open_iff_keeps_shared_futures (x x' : State E) :
    (∀ e, Open x e → Open x' e) ↔ (∀ y : State E, Rejoin x y → Rejoin x' y) :=
  ⟨fun h _ hy => rejoin_iff_forall_open.2 fun b hb => h b (rejoin_iff_forall_open.1 hy b hb),
    fun h e he => h (cone e) he⟩

/-- A shared state has open exactly the forms open to both. So in this model a join never adds
an open form; the other can only narrow what is open. This is the part of Beauvoir's claim the
frame does NOT give. -/
theorem open_join_iff {x y : State E} (h : ¬ Clash x y) {e : E} :
    Open (join x y h) e ↔ Open x e ∧ Open y e := by
  simp only [open_iff]
  exact ⟨fun hj => ⟨fun a ha => hj a (Or.inl ha), fun a ha => hj a (Or.inr ha)⟩,
    fun hj a ha => ha.elim (hj.1 a) (hj.2 a)⟩

/-- Reading: a real choice at `x`: two forms, each open, that exclude each other. (`Beauvoir.Free`
asks only for incomparable futures; with joins those need not exclude each other.) -/
def Choice (x : State E) : Prop := ∃ e e', Open x e ∧ Open x e' ∧ conflict e e'

/-- A shared state has a real choice exactly when some one choice is open to both. Each having a
choice of their own is not enough (`sharedChoiceFails`). -/
theorem choice_join_iff {x y : State E} (h : ¬ Clash x y) :
    Choice (join x y h) ↔
      ∃ e e', (Open x e ∧ Open y e) ∧ (Open x e' ∧ Open y e') ∧ conflict e e' := by
  simp only [Choice, open_join_iff]

end FormsTheory

/-! ### The same statement fails without coherence

The proper subsets of a three-element set, ordered by inclusion: three forms that are compatible
two at a time but not all together. This order is not the states of any `Forms`. -/

/-- The seven proper subsets of `Fin 3`. -/
abbrev Tri : Type := {s : Finset (Fin 3) // s ≠ Finset.univ}

/-- One form alone. -/
def Tri.atom (i : Fin 3) : Tri := ⟨{i}, by revert i; decide⟩

/-- Forms 1 and 2 together: another state, as a whole. -/
def Tri.pair : Tri := ⟨{1, 2}, by decide⟩

/-- In `Tri` the three single forms can be joined two at a time but not all at once
(compare `bounded_of_pairwise`). -/
theorem tri_pairwise_not_bounded :
    (∀ i j : Fin 3, Rejoin (Tri.atom i) (Tri.atom j)) ∧ ¬ ∃ w : Tri, ∀ i, Tri.atom i ≤ w := by
  constructor
  · intro i j
    refine ⟨⟨{i, j}, by revert i j; decide⟩, ?_, ?_⟩
    · show ({i} : Finset (Fin 3)) ⊆ {i, j}
      simp
    · show ({j} : Finset (Fin 3)) ⊆ {i, j}
      simp
  · rintro ⟨⟨w, hw⟩, h⟩
    refine hw (Finset.eq_univ_iff_forall.2 fun i => ?_)
    have := h i
    exact (Finset.singleton_subset_iff.1 this)

/-- In `Tri`, each form of the other (`1` alone, `2` alone) can still be joined with the self
(`0`), and the other as a whole (`{1, 2}`) cannot (compare `rejoin_iff_forall_open`). -/
theorem open_each_not_whole :
    Rejoin (Tri.atom 0) (Tri.atom 1) ∧ Rejoin (Tri.atom 0) (Tri.atom 2) ∧
      Tri.atom 1 ≤ Tri.pair ∧ Tri.atom 2 ≤ Tri.pair ∧ ¬ Rejoin (Tri.atom 0) Tri.pair := by
  refine ⟨⟨⟨{0, 1}, by decide⟩, by decide, by decide⟩, ⟨⟨{0, 2}, by decide⟩, by decide, by decide⟩,
    by decide, by decide, ?_⟩
  rintro ⟨⟨w, hw⟩, h0, h12⟩
  refine hw (Finset.eq_univ_iff_forall.2 fun i => ?_)
  have h0' : (0 : Fin 3) ∈ w := Finset.singleton_subset_iff.1 h0
  have h1' : (1 : Fin 3) ∈ w := h12 (by decide)
  have h2' : (2 : Fin 3) ∈ w := h12 (by decide)
  fin_cases i <;> assumption

/-! ## 4. The one-NOT history as data

DATA, copied by this seat from `boards/one-not.md` (the lines of 2026-11-24 named below),
`research/one-not/DEAD_ENDS.md` (family D) and the Lean files named. Lean checks only that the encoding is
a `Forms` and what follows from it. Clock times on that board mix time zones, so no times are
encoded, only "built using".

A refuted row of the board is split in two: its material (a definition) and its universal claim.
That split is this seat's modelling decision; the tree of `Unify.lean` had one node for both.

Rows:
* `mergeSet`: real merge sets `M_z(w)` (board, 09:15 to 10:15 lines; `W951/MergeSDR.lean`).
* `pureClass`: pure classes (board, 10:45 line; `W951/PureSDR.lean`).
* `pureSDRAll`: "PureSDR for every correct circuit", the official target of 10:47.
* `cxMUdd`: the circuit `cxMU_dd`, which refutes it (board, "12:20 TARGET WARNING").
* `mergePriceAll`: "the price inequality for real merge sets, with no minimality".
* `star4`: the circuit STAR4, which refutes it (board, 13:25 line; DEAD_ENDS family D).
* `liftClass`: lifted classes; pure classes and real merge sets are lifted classes
  (`W951/PureGP.lean::liftSDR_of_pureSDR`, `W951/PureLLift.lean::mergeSet_eq_lift`).
* `liftTarget`: LiftSDR / MUL as the official target (board, "OFFICIAL TARGET ... ~12:27"),
  adopted because of `cxMUdd`. Open.
* `f2Count`: the count over real-witness gates (board, "DECISION 12:46"); real merge sets lie in
  it (`F2Desc`, commit 7e0da84).
* `bottomPay`: the open statement at the end of the chain A4, A7, A10 (`boards/tasks/open-one-not.md`);
  the chain is one row here.
-/

/-- Ten rows of the one-NOT board (data). -/
inductive Row
  | mergeSet | pureClass | pureSDRAll | cxMUdd | mergePriceAll | star4
  | liftClass | liftTarget | f2Count | bottomPay
  deriving DecidableEq

namespace Row

instance : Fintype Row :=
  ⟨⟨[mergeSet, pureClass, pureSDRAll, cxMUdd, mergePriceAll, star4, liftClass, liftTarget,
    f2Count, bottomPay], by decide⟩, fun x => by cases x <;> decide⟩

/-- The recorded kind of a row (data). -/
inductive Kind | material | witness | refuted | stillOpen
  deriving DecidableEq

/-- Kind of each row, as recorded on the boards (data, not checked). -/
def kind : Row → Kind
  | mergeSet => .material | pureClass => .material | liftClass => .material
  | f2Count => .material
  | cxMUdd => .witness | star4 => .witness
  | pureSDRAll => .refuted | mergePriceAll => .refuted
  | liftTarget => .stillOpen | bottomPay => .stillOpen

/-- "Built using", immediate edges (data). Reading of an edge: the row's statement or
construction uses the parent as an ingredient, as a special case it generalises, or as the
counterexample it answers. -/
def parents : Row → List Row
  | mergeSet => [] | pureClass => []
  | pureSDRAll => [pureClass]
  | cxMUdd => [pureClass]
  | mergePriceAll => [mergeSet]
  | star4 => [mergeSet]
  | liftClass => [mergeSet, pureClass]
  | liftTarget => [liftClass, cxMUdd]
  | f2Count => [mergeSet]
  | bottomPay => [f2Count]

/-- `a` is reached from `b` in at most `n` parent steps. -/
def anc : ℕ → Row → Row → Bool
  | 0, a, b => decide (a = b)
  | n + 1, a, b => decide (a = b) || (parents b).any fun p => anc n a p

/-- "Built using", closed under composition (three steps suffice for this table). -/
def le (a b : Row) : Bool := anc 3 a b

/-- Recorded refutations: (counterexample, universal claim) (data). -/
def refutations : List (Row × Row) := [(cxMUdd, pureSDRAll), (star4, mergePriceAll)]

/-- Conflict generated by the recorded refutations: something built on a counterexample against
something built on the claim it refutes. -/
def clash (a b : Row) : Bool :=
  refutations.any fun r => (le r.1 a && le r.2 b) || (le r.2 a && le r.1 b)

end Row

/-- Encoding check: the table is a `Forms` (a partial order; conflict symmetric, irreflexive,
inherited). It would fail if any row were built on both a claim and its counterexample. -/
instance : Forms Row where
  le a b := Row.le a b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  conflict a b := Row.clash a b = true
  conflict_symm := by decide
  conflict_irrefl := by decide
  conflict_hered := by decide

instance : DecidableRel (α := Row) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (Row.le a b = true))

instance : DecidableRel (Forms.conflict (E := Row)) := fun a b =>
  inferInstanceAs (Decidable (Row.clash a b = true))

/-- Reading: the present of the board: every row not recorded as refuted. Encoding check: this is
a state, so nothing kept was built on a refuted claim and no two kept rows are in conflict. -/
def present : State Row where
  carrier := {e | e.kind ≠ .refuted}
  lower := by
    have : ∀ a b : Row, a ≤ b → b.kind ≠ .refuted → a.kind ≠ .refuted := by decide
    exact fun {a b} => this a b
  free := by
    have : ∀ a b : Row, a.kind ≠ .refuted → b.kind ≠ .refuted → ¬ conflict a b := by decide
    exact fun {a b} => this a b

/-- The real history is not a tree: the lifted classes have two unrelated parents, so no
`Fisher.Frame` structure exists on these rows with this order. -/
theorem history_not_tree : ¬ ∀ a b c : Row, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a := by decide

/-- Two open targets of the present are concurrent. In a tree one would be lost to the other. -/
theorem targets_concurrent : Concurrent Row.liftTarget Row.bottomPay :=
  ⟨by decide, by decide, by decide⟩

/-- The states of the history are not a Fisher frame either. -/
theorem history_states_not_tree :
    ¬ ∀ a b c : State Row, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a := fun h =>
  linear_past_iff_no_concurrent.1 h ⟨_, _, targets_concurrent⟩

/-- **The reconciliation, in the data.** The merge-set line and the pure-class line were lost to
each other, and both lie in the past of the lifted classes. So `lost_mono` is false for the
states of this history. -/
theorem lines_reconciled :
    Lost (cone Row.mergeSet) (cone Row.pureClass) ∧
      cone Row.mergeSet ≤ cone Row.liftClass ∧ cone Row.pureClass ≤ cone Row.liftClass ∧
      ¬ Lost (cone Row.liftClass) (cone Row.pureClass) := by
  refine ⟨lost_iff_incomparable.2 ⟨fun h => ?_, fun h => ?_⟩, cone_le_cone.2 (by decide),
    cone_le_cone.2 (by decide), fun h => h.2.2 (cone_le_cone.2 (by decide))⟩
  · exact absurd (cone_le_cone.1 h) (by decide)
  · exact absurd (cone_le_cone.1 h) (by decide)

theorem lost_mono_fails_on_history :
    ¬ ∀ m m' f : State Row, m ≤ m' → Lost m f → Lost m' f := fun h =>
  lines_reconciled.2.2.2 (h _ _ _ lines_reconciled.2.1 lines_reconciled.1)

/-- In the data, the rows closed to the present are exactly the rows recorded as refuted. The
left side is computed from the edges and the refutation list, the right side is the `kind`
column. -/
theorem closed_iff_refuted (e : Row) : ¬ Open present e ↔ e.kind = .refuted := by
  rw [open_iff]
  have : ∀ e : Row, (¬ ∀ a : Row, a.kind ≠ .refuted → ¬ conflict a e) ↔ e.kind = .refuted := by
    decide
  exact this e

/-- **What stays lost.** A refuted claim is in no later state of the present. General theory
(`open_iff`, heredity) applied to the data. -/
theorem refuted_never_returns {e : Row} (he : e.kind = .refuted) {x : State Row}
    (hx : present ≤ x) : e ∉ x.carrier := fun h =>
  (closed_iff_refuted e).2 he ⟨x, hx, cone_le_iff.2 h⟩

/-- The branch of each refuted claim is lost to the present for ever. -/
theorem refuted_branch_lost_forever {e : Row} (he : e.kind = .refuted) {x : State Row}
    (hx : present ≤ x) : Lost x (cone e) := by
  refine lost_iff_incomparable.2
    ⟨fun h => ?_, fun h => refuted_never_returns he hx (cone_le_iff.1 h)⟩
  have h1 : Row.mergeSet ≤ e := h (hx (by decide : Row.mergeSet.kind ≠ .refuted))
  have h2 : Row.cxMUdd ≤ e := h (hx (by decide : Row.cxMUdd.kind ≠ .refuted))
  have : ∀ e : Row, e.kind = .refuted → Row.mergeSet ≤ e → Row.cxMUdd ≤ e → False := by decide
  exact this e he h1 h2

/-- **What the join recovered.** From the branch of each refuted claim, the present can take over
exactly the material the claim was about. -/
theorem salvage_pure (e : Row) :
    e ∈ (salvage present (cone Row.pureSDRAll)).carrier ↔ e = Row.pureClass := by
  have : ∀ e : Row, (e ≤ Row.pureSDRAll ∧ ∀ a : Row, a.kind ≠ .refuted → ¬ conflict a e) ↔
      e = Row.pureClass := by decide
  exact this e

theorem salvage_merge (e : Row) :
    e ∈ (salvage present (cone Row.mergePriceAll)).carrier ↔ e = Row.mergeSet := by
  have : ∀ e : Row, (e ≤ Row.mergePriceAll ∧ ∀ a : Row, a.kind ≠ .refuted → ¬ conflict a e) ↔
      e = Row.mergeSet := by decide
  exact this e

/-- The material of both refuted claims is in the past of the lifted target. -/
theorem refuted_material_reused :
    Row.pureClass ≤ Row.liftTarget ∧ Row.mergeSet ≤ Row.liftTarget ∧
      Row.cxMUdd ≤ Row.liftTarget := by decide

/-- A shared choice can fail though each side has one: in the data, the state holding only
`cxMUdd` and the state holding only `star4` each still have a real choice, and their join has
none. -/
theorem sharedChoiceFails :
    ∃ h : ¬ Clash (cone Row.cxMUdd) (cone Row.star4),
      Choice (cone Row.cxMUdd) ∧ Choice (cone Row.star4) ∧
        ¬ Choice (join (cone Row.cxMUdd) (cone Row.star4) h) := by
  have hc : ¬ Clash (cone Row.cxMUdd) (cone Row.star4) :=
    rejoin_iff_not_clash.1 (cone_rejoin_of_not_conflict (by decide))
  have key : ∀ (c : Row) (e : Row), Open (cone c) e ↔ ¬ conflict c e := fun c e =>
    ⟨fun h hce => open_iff.1 h c (le_refl c) hce,
      fun h => cone_rejoin_of_not_conflict h⟩
  refine ⟨hc, ⟨Row.star4, Row.mergePriceAll, (key _ _).2 (by decide), (key _ _).2 (by decide),
    by decide⟩, ⟨Row.cxMUdd, Row.pureSDRAll, (key _ _).2 (by decide), (key _ _).2 (by decide),
    by decide⟩, ?_⟩
  rw [choice_join_iff]
  rintro ⟨e, e', ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
  rw [key] at h1 h2 h3 h4
  have : ∀ e e' : Row, ¬ conflict Row.cxMUdd e → ¬ conflict Row.star4 e →
      ¬ conflict Row.cxMUdd e' → ¬ conflict Row.star4 e' → ¬ conflict e e' := by decide
  exact this e e' h1 h2 h3 h4 h5

end PEqualNP.Philosophy.DAG
