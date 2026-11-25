import PEqualNP.Philosophy.Hegel
import PEqualNP.Philosophy.Camus
import PEqualNP.Philosophy.Beauvoir

/-!
# One frame: Fisher's branching time, enriched (philosophy-unification seat)

HONESTY. These are formal models of cited readings of Fisher, Deleuze, Hegel, Camus and Beauvoir.
They claim nothing about what any of them meant. The theorems are about orders, lists and sets.
They say nothing about circuits, and nothing here bears on P versus NP. The board section encodes
the names and the recorded status of seven board rows as data; it does not check those rows.

The frame. A search is a tree of decisions (`Hegel.Path`), which is a Fisher frame with a first
moment. In it:
* Fisher: a refuted or abandoned route is a lost future, and stays lost (`Fisher.lost_mono`);
* Deleuze: the past of the present is one chain (the actual), the whole tree is the virtual, and
  the chain does not determine the tree (`actual_does_not_determine_virtual`);
* Hegel: a lost route parts from the present at one determinate decision
  (`Hegel.determinate_negation`);
* Beauvoir: that parting point was a free moment, the lost route is the present's "barbarian",
  and the two cannot recognise each other inside a tree (`Beauvoir.barbarian_iff_lost`);
* Camus: while there is always another decision to take, the present starts an endless ascent
  that carries every ghost with it (`Camus.revolt`, `Camus.revolt_keeps_ghosts`).
All of this is one theorem, `unified`. The second result, `permanence_iff_no_reconciliation`, is
the price: in any partial order, loss is permanent exactly when lost pairs never meet again.

Sources are listed in the four imported files and in LITERATURE.md, section M5. Prose:
philosophy/UNIFY.md.
-/

namespace PEqualNP.Philosophy.Unify

open PEqualNP.Philosophy.Fisher PEqualNP.Philosophy.Hegel PEqualNP.Philosophy.Camus
open PEqualNP.Philosophy.Beauvoir

/-! ### 1. The frame of paths is absurd, in Camus's sense, when there is anything to decide -/

theorem path_absurd (α : Type*) [Nonempty α] : Absurd (Path α) := by
  intro m
  obtain ⟨x⟩ := ‹Nonempty α›
  refine not_isMax_iff.2 ⟨⟨m.steps ++ [x]⟩, lt_of_le_of_ne ?_ ?_⟩
  · exact Path.le_def.2 (List.prefix_append _ _)
  · intro e
    have := congrArg (fun p : Path α => p.steps.length) e
    simp at this

/-! ### 2. The unifying theorem -/

/-- **One lost route, five readings.** Let `f` be lost at the present `m` in a tree of decisions.
1. (Fisher, hauntology) `f` is lost at every later moment.
2. (Hegel, determinate negation) `m` and `f` share a part `a` and then differ by one pair of
   distinct decisions.
3. (Beauvoir, freedom) some moment of the present's past was free.
4. (Beauvoir's barbarians; Hegel, recognition) `f` is the present's other, and no moment holds
   both.
5. (Deleuze, the actual) the present's past is a single chain.
6. (Camus, revolt) if there is anything to decide, the present starts an endless strictly
   ascending history, and `f` is lost at every step of it. -/
theorem unified {α : Type*} {m f : Path α} (h : Lost m f) :
    (∀ m', m ≤ m' → Lost m' f) ∧
    (∃ (a : Path α) (x y : α), x ≠ y ∧ a ≤ m ∧ a ≤ f ∧
      (⟨a.steps ++ [x]⟩ : Path α) ≤ m ∧ (⟨a.steps ++ [y]⟩ : Path α) ≤ f) ∧
    (∃ a, a ≤ m ∧ Free a) ∧
    (Barbarian m f ∧ ¬ Recognise m f) ∧
    IsChain (· ≤ ·) (facticity m) ∧
    (Nonempty α → ∃ s : ℕ → Path α, s 0 = m ∧ StrictMono s ∧ ∀ n, Lost (s n) f) := by
  refine ⟨fun _ hm => lost_mono hm h, determinate_negation h, haunted_past_free ⟨f, h⟩,
    ⟨barbarian_iff_lost.2 h, no_recognition_between_barbarians (barbarian_iff_lost.2 h)⟩,
    facticity_isChain m, fun hne => ?_⟩
  obtain ⟨s, hs0, hs⟩ := revolt (path_absurd α) m
  exact ⟨s, hs0, hs, fun n => revolt_keeps_ghosts hs (hs0 ▸ h) n⟩

/-! ### 3. The price: permanence of loss against reconciliation -/

section Price

variable {P : Type*} [PartialOrder P]

/-- Fisher's `Lost`, stated for any partial order (no linear past assumed). -/
def LostP (m f : P) : Prop := (∃ m', m' ≤ m ∧ m' ≤ f) ∧ ¬ m ≤ f ∧ ¬ f ≤ m

/-- On a Fisher frame the two notions agree. -/
theorem lostP_iff_lost {M : Type*} [Frame M] {m f : M} : LostP m f ↔ Lost m f := Iff.rfl

/-- **Permanence if and only if no reconciliation.** In any partial order: lost futures stay
lost for ever exactly when no lost pair ever meets again in a later moment. Reading: Fisher's
irreversible cancellation and Hegel's recognition (Beauvoir's shared future) are the two sides of
one condition, and a world cannot have both. -/
theorem permanence_iff_no_reconciliation :
    (∀ m m' f : P, m ≤ m' → LostP m f → LostP m' f) ↔
      (∀ a b : P, LostP a b → ¬ ∃ w, a ≤ w ∧ b ≤ w) := by
  constructor
  · rintro hperm a b hab ⟨w, haw, hbw⟩
    exact (hperm a w b haw hab).2.2 hbw
  · rintro hno m m' f hmm' ⟨⟨a, ham, haf⟩, hmf, hfm⟩
    refine ⟨⟨a, ham.trans hmm', haf⟩, fun h => hmf (hmm'.trans h), fun h => ?_⟩
    exact hno m f ⟨⟨a, ham, haf⟩, hmf, hfm⟩ ⟨m', hmm', h⟩

/-- A world with a join: in the four-point diamond the two middle points lose each other, are
reconciled at the top, and the loss is undone there. Reading: a history with merges (the
repository's own commit history has them, and the board has a REOPENED section) is not a Fisher
frame, and its lost routes can come back. -/
theorem diamond_reconciles :
    LostP ((true, false) : Bool × Bool) (false, true) ∧
      ((true, false) : Bool × Bool) ≤ (true, true) ∧
      ¬ LostP ((true, true) : Bool × Bool) (false, true) := by
  refine ⟨⟨⟨(false, false), by decide, by decide⟩, by decide, by decide⟩, by decide, ?_⟩
  exact fun h => h.2.2 (by decide)

end Price

/-! ### 4. Deleuze: the actual does not determine the virtual -/

theorem unit_total : ∀ l₁ l₂ : List Unit, l₁ <+: l₂ ∨ l₂ <+: l₁
  | [], _ => Or.inl List.nil_prefix
  | _ :: _, [] => Or.inr List.nil_prefix
  | () :: s, () :: t =>
    (unit_total s t).imp (fun h => List.cons_prefix_cons.2 ⟨rfl, h⟩)
      (fun h => List.cons_prefix_cons.2 ⟨rfl, h⟩)

/-- **Same actual, different virtual.** Two presents whose pasts have the same shape (a chain of
the same length; by `Path.le_iff_take` the past of a path is its initial segments), one in a world
with nothing to choose and one in a world with a choice. The first is not haunted and the second
is. Reading: Deleuze's non-resemblance of actual and virtual (as in `Deleuze.lean` and in the
Bridge file's `corners_not_injective`): the line that was actualised does not tell which tree it
was drawn from. -/
theorem actual_does_not_determine_virtual :
    ∃ (m : Path Unit) (m' : Path Bool),
      m.steps.length = m'.steps.length ∧ ¬ Haunted m ∧ Haunted m' := by
  refine ⟨⟨[()]⟩, ⟨[true]⟩, rfl, ?_, ⟨⟨[false]⟩, lost_iff_other.2 ⟨by decide, by decide⟩⟩⟩
  rintro ⟨f, hf⟩
  exact not_lost_of_total (fun a b : Path Unit => unit_total a.steps b.steps) _ f hf

/-! ### 5. Levels joined by a projection: possibility and necessity -/

section Levels

variable {X Y : Type*}

/-- Along any map `f` from a lower level to an upper one, a property `S` of the lower level has
two opposite images above: "some preimage has `S`" (`f '' S`) and "every preimage has `S`"
(`Set.kernImage f S`). They are the two adjoints of pulling back. Reading: Lawvere, "Adjointness
in Foundations" (1969), quantifiers as adjoints; the level reading is ours. -/
theorem level_adjoints (f : X → Y) :
    GaloisConnection (Set.image f) (Set.preimage f) ∧
      GaloisConnection (Set.preimage f) (Set.kernImage f) :=
  ⟨Set.image_preimage, Set.preimage_kernImage⟩

/-- **The two images agree exactly when the projection forgets nothing.** Reading (Beauvoir's
ambiguity, between the levels): identifying what may hold above with what must hold above is
legitimate only for an injective projection. The Bridge file proves that the repository's
projection from the finite slack table to the polynomial `Φ` is not injective
(`virtualOf_not_injective`), so there the two never merge. -/
theorem collapse_iff_injective (f : X → Y) :
    (∀ S : Set X, f '' S ⊆ Set.kernImage f S) ↔ Function.Injective f := by
  constructor
  · intro h x₁ x₂ e
    have := h {x₁} ⟨x₁, rfl, rfl⟩ e.symm
    exact (Set.mem_singleton_iff.1 this).symm
  · rintro hf S y ⟨x, hx, rfl⟩ x' e
    exact hf e ▸ hx

/-- So a projection that forgets leaves a real gap: some property that may hold above without
having to. -/
theorem ambiguity_of_levels (f : X → Y) (hf : ¬ Function.Injective f) :
    ∃ S : Set X, ¬ f '' S ⊆ Set.kernImage f S := by
  by_contra h
  exact hf ((collapse_iff_injective f).1 fun S => not_not.1 fun hS => h ⟨S, hS⟩)

end Levels

/-! ### 6. The board's own history as a Fisher frame

Seven rows of the one-NOT board, as data. Names and statuses are copied from
`boards/tasks/open-one-not.md` and `boards/TREE.md` on 2026-11-25:
* `A4`  F2-transfer (reduced to DD-absorption);
* `A7`  DD-absorption (reduced to light absorption);
* `A10` light absorption (reduced to BOTTOM PAY);
* `BottomPay` the open statement at the end of that chain;
* `C2`  the one-point step for real-witness gates: refuted (finding `7dbb073c`, twin trees);
* `C4`  the witness count for any gate type: refuted (finding `f4704cc4`, four NOT gates);
* `L5`  monotone level means: refuted (finding `98a42596`, twin trees).
The tree shape (each refuted row a first step from the root, the reductions a single line) is our
encoding of that history, not a board fact.
-/

/-- Seven board rows. -/
inductive Row | A4 | A7 | A10 | BottomPay | C2 | C4 | L5
  deriving DecidableEq

instance : Nonempty Row := ⟨.A4⟩

/-- The recorded status of a row. -/
inductive Verdict | refuted | reduced | stillOpen
  deriving DecidableEq

/-- Status as recorded on the boards (data, not checked here). -/
def verdict : Row → Verdict
  | .A4 => .reduced | .A7 => .reduced | .A10 => .reduced
  | .BottomPay => .stillOpen
  | .C2 => .refuted | .C4 => .refuted | .L5 => .refuted

/-- The route to a row: the decisions that lead to it from the first statement. -/
def route : Row → Path Row
  | .A4 => ⟨[.A4]⟩
  | .A7 => ⟨[.A4, .A7]⟩
  | .A10 => ⟨[.A4, .A7, .A10]⟩
  | .BottomPay => ⟨[.A4, .A7, .A10, .BottomPay]⟩
  | .C2 => ⟨[.C2]⟩
  | .C4 => ⟨[.C4]⟩
  | .L5 => ⟨[.L5]⟩

/-- The present of the search. -/
def present : Path Row := route .BottomPay

/-- The reductions form one line: the actual history. -/
theorem live_line : route .A4 ≤ route .A7 ∧ route .A7 ≤ route .A10 ∧ route .A10 ≤ present := by
  decide

/-- Every refuted row is a lost future of the present. -/
theorem refuted_lost (r : Row) (h : verdict r = .refuted) : Lost present (route r) := by
  rw [lost_iff_other]
  cases r <;> first
    | exact absurd h (by decide)
    | exact ⟨by decide, by decide⟩

/-- **`lost_mono` on the board.** However the search continues from here, every refuted row stays
a lost future: it is never the present again and never ahead. It also never leaves the frame
(`Hegel.trichotomy`), which is the formal side of keeping refuted rows with their witnesses. -/
theorem refuted_lost_forever (r : Row) (h : verdict r = .refuted) {m : Path Row}
    (hm : present ≤ m) : Lost m (route r) :=
  lost_mono hm (refuted_lost r h)

/-- The present of the search is haunted. -/
theorem present_haunted : Haunted present := ⟨route .C2, refuted_lost .C2 rfl⟩

/-- Each refuted row parts from the present at a determinate decision. -/
theorem refuted_determinate (r : Row) (h : verdict r = .refuted) :
    ∃ (a : Path Row) (x y : Row), x ≠ y ∧ a ≤ present ∧ a ≤ route r ∧
      (⟨a.steps ++ [x]⟩ : Path Row) ≤ present ∧ (⟨a.steps ++ [y]⟩ : Path Row) ≤ route r :=
  determinate_negation (refuted_lost r h)

/-- **Capitalist realism on the board.** From the present, every reachable future passes through
`A4`: no alternative to that route is imaginable from here. Each refuted row is such an
alternative; it was possible from an earlier moment and is now lost. -/
theorem board_realism :
    ¬ Possible present (fun f => ¬ route .A4 ≤ f) ∧
      ∀ r, verdict r = .refuted →
        (∃ m', m' ≤ present ∧ Possible m' (fun f => ¬ route .A4 ≤ f)) ∧ Haunted present := by
  have hP : ∀ f, Reachable present f → route .A4 ≤ f := fun f hf =>
    le_trans (show route .A4 ≤ present by decide) hf
  obtain ⟨h1, h2⟩ := capitalist_realism (P := fun f => route .A4 ≤ f) hP
  refine ⟨h1, fun r hr => h2 (route r) (refuted_lost r hr) ?_⟩
  cases r <;> first
    | exact absurd hr (by decide)
    | decide

/-- The board's present is not final: the search can always take another step, and every refuted
row is lost along the whole of any continuation (Camus on the board). -/
theorem board_revolt :
    ∃ s : ℕ → Path Row, s 0 = present ∧ StrictMono s ∧
      ∀ r, verdict r = .refuted → ∀ n, Lost (s n) (route r) := by
  obtain ⟨s, hs0, hs⟩ := revolt (path_absurd Row) present
  exact ⟨s, hs0, hs, fun r hr n => revolt_keeps_ghosts hs (hs0 ▸ refuted_lost r hr) n⟩

end PEqualNP.Philosophy.Unify
