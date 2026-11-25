import PEqualNP.Philosophy.Hegel

/-!
# Ambiguity, freedom, and the barbarians (philosophy-unification seat)

HONESTY. This file contains formal models of cited readings. It claims nothing about what
Beauvoir meant. Nothing here is about circuits.

Readings followed.
* Simone de Beauvoir, *Pour une morale de l'ambiguïté* (1947; *The Ethics of Ambiguity*, tr.
  Frechtman 1948): a person is at once facticity (a given situation) and transcendence (an open
  project), and the ethical failure is to collapse one into the other; the "serious man" treats
  values as given; freedom wills an open future, for itself and for others. Cited from memory, in
  copyright, not quoted, not re-read for this file.
* Simone de Beauvoir, *Diary of a Philosophy Student, Volume 1, 1926-27* (ed. Klaw, Le Bon de
  Beauvoir, Simons; University of Illinois Press, 2006). CONFIRMED ONLY FROM SEARCH SUMMARIES of
  the edition's notes and of a review: in 1926 the young Beauvoir is reading Maurice Barrès,
  *Sous l'œil des barbares* (1888, first volume of *Le Culte du moi*), takes over his word
  "barbarians" for those who are not the self ("O you who are not me", as the review quotes the
  diary), and on 10 July 1927 names her philosophical problem "this opposition of self and
  other". The diary itself was not opened. See research/philosophy/UNIFY.md for what is and is not
  confirmed.

* Simone de Beauvoir, *L'Invitée* (1943; *She Came to Stay*). Its epigraph is Hegel's line,
  given in the scholarship as "Chaque conscience poursuit la mort de l'autre" (each consciousness
  seeks the death of the other), and the novel ends with Françoise killing Xavière. The Stanford
  Encyclopedia entry on Beauvoir (read as a search summary) adds that the murder destroys one
  particular other, not the other as such. Novel not opened; in copyright; plot from secondary
  sources.
* Hegel, *Phenomenology of Spirit*, "Lordship and Bondage": the struggle to the death defeats
  itself, since recognition needs the other to remain. Cited from memory.

The carrier is Fisher's branching frame. A situated self is a moment `m`.
-/

namespace PEqualNP.Philosophy.Beauvoir

open PEqualNP.Philosophy.Fisher PEqualNP.Philosophy.Hegel

variable {M : Type*} [Frame M]

/-! ### 1. Ambiguity: facticity and transcendence -/

/-- Facticity: the given past of a situation. Reading: *Ethics of Ambiguity*, part I. -/
def facticity (m : M) : Set M := Set.Iic m

/-- Transcendence: the open futures a situation can project itself into. Same reading. -/
def transcendence (m : M) : Set M := Set.Ici m

/-- Facticity is a single line: the past holds no alternatives. -/
theorem facticity_isChain (m : M) : IsChain (· ≤ ·) (facticity m) :=
  fun a ha b hb _ => Frame.linear_past a b m ha hb

/-- `Iic m ∩ Ici m = {m}` (antisymmetry). A general fact about partial orders; the labels
facticity and transcendence, and the name "ambiguity", are ours and do not recover Beauvoir's
account of the human being as both. -/
theorem ambiguity (m : M) : facticity m ∩ transcendence m = {m} := by
  ext x
  simp only [facticity, transcendence, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
    Set.mem_singleton_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-! ### 2. Freedom and seriousness -/

/-- `Free` is our definition: a moment opens at least two exclusive futures. It is not Beauvoir's
account of freedom (which is not indeterminism). -/
def Free (m : M) : Prop := ∃ f g, m ≤ f ∧ m ≤ g ∧ ¬ f ≤ g ∧ ¬ g ≤ f

/-- `Serious` is our definition: the future is one chain. Beauvoir's "serious man" treats values
as ready-made; that is not the same as a linearly ordered future. -/
def Serious (m : M) : Prop := IsChain (· ≤ ·) (transcendence m)

/-- `Serious` is defined as the negation of `Free` up to De Morgan; this iff unfolds those two
definitions and is not Beauvoir's account of either. -/
theorem serious_iff_not_free (m : M) : Serious m ↔ ¬ Free m := by
  constructor
  · rintro hs ⟨f, g, hf, hg, hfg, hgf⟩
    by_cases hne : f = g
    · exact hfg (hne ▸ le_rfl)
    · rcases hs hf hg hne with h | h
      · exact hfg h
      · exact hgf h
  · intro hn f hf g hg _
    by_contra hc
    exact hn ⟨f, g, hf, hg, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩

/-- Whichever of two exclusive futures is taken, the other is lost from then on: Fisher's
`haunted_of_branch`, stated from the branch point. -/
theorem free_act_haunts {m : M} (h : Free m) :
    ∃ f g, m ≤ f ∧ m ≤ g ∧ (∀ m', f ≤ m' → Lost m' g) ∧ (∀ m', g ≤ m' → Lost m' f) := by
  obtain ⟨f, g, hf, hg, hfg, hgf⟩ := h
  exact ⟨f, g, hf, hg, fun _ hm => haunted_of_branch hf hg hfg hgf hm,
    fun _ hm => haunted_of_branch hg hf hgf hfg hm⟩

/-- A haunted present has a `Free` moment in its past: where the lost future and the present
parted. -/
theorem haunted_past_free {m : M} (h : Haunted m) : ∃ a, a ≤ m ∧ Free a := by
  obtain ⟨f, ⟨a, ham, haf⟩, hmf, hfm⟩ := h
  exact ⟨a, ham, m, f, ham, haf, hmf, hfm⟩

/-- If every moment is `Serious`, no moment is `Haunted`. -/
theorem serious_world_unhaunted (hs : ∀ a : M, Serious a) (m : M) : ¬ Haunted m := fun h =>
  let ⟨a, _, ha⟩ := haunted_past_free h
  (serious_iff_not_free a).1 (hs a) ha

/-! ### 3. The barbarians -/

/-- A rename of `Other`: neither past nor possible future of `m`. The word follows Barrès's
"barbares" as the young Beauvoir takes them over (confirmed only as far as the header says).
Modelling another person as an unchosen branch of one timeline is our decision, and it settles by
fiat a question Beauvoir treats philosophically. -/
def Barbarian (m x : M) : Prop := Other m x

/-- `Other` is symmetric. (Our label: the 1927 "opposition of self and other"; nothing more of
Hegel's or Beauvoir's account is modelled.) -/
theorem barbarian_symm {m x : M} (h : Barbarian m x) : Barbarian x m := other_symm h

/-- A self is never its own barbarian, nor is its past or its possible future. -/
theorem not_barbarian_self (m : M) : ¬ Barbarian m m := fun h => h.1 le_rfl

/-- Self and barbarian share no possible future in a branching frame. -/
theorem barbarian_iff_no_common_future {m x : M} : Barbarian m x ↔ ¬ ∃ h, m ≤ h ∧ x ≤ h :=
  other_iff_no_common_future

/-- In a frame with a first moment, `Other` and `Lost` coincide (both mean incomparable). So in
this model other persons are unchosen branches of the self's own timeline; that is a modelling
decision, and the reading "hatred of the barbarians is self-hatred" is unconfirmed and not
modelled. -/
theorem barbarian_iff_lost [OrderBot M] {m x : M} : Barbarian m x ↔ Lost m x :=
  lost_iff_other.symm

/-- Each `Barbarian` has a `Free` moment in the self's past (where the two parted). -/
theorem barbarian_past_free [OrderBot M] {m x : M} (h : Barbarian m x) : ∃ a, a ≤ m ∧ Free a :=
  haunted_past_free ⟨x, barbarian_iff_lost.1 h⟩

/-- Holds by definition: `Barbarian m x` is a statement about order position only, so `(P → Q) ∧
(¬P → Q)` given `Q` for any predicate `Right`. Kept only to record that the model's `Barbarian`
does not depend on any property at `x` (the diary's "even if you might be right"). -/
theorem barbarian_independent_of_any_predicate {m x : M} (h : Barbarian m x) (Right : M → Prop) :
    (Right x → Barbarian m x) ∧ (¬ Right x → Barbarian m x) := ⟨fun _ => h, fun _ => h⟩

/-! ### 4. *She Came to Stay*: each consciousness seeks the death of the other -/

/-- `lost_mono` applied twice: between a self and its barbarian, every continuation of one has
the other `Lost`, both ways. "Death" here is only "becoming `Lost`" (incomparable); nothing in the
model kills anyone. Named as the epigraph of *L'Invitée* only by us. -/
theorem lost_both_ways [OrderBot M] {m x : M} (h : Barbarian m x) :
    (∀ m', m ≤ m' → Lost m' x) ∧ (∀ x', x ≤ x' → Lost x' m) :=
  ⟨fun _ hm => lost_mono hm (barbarian_iff_lost.1 h),
    fun _ hx => lost_mono hx (barbarian_iff_lost.1 (barbarian_symm h))⟩

/-- Comparable moments have a common upper bound. (Our label: a particular other, not the other
as such, after the SEP remark on the novel's ending.) -/
theorem not_every_other_dies {m x : M} (h : m ≤ x ∨ x ≤ m) : ∃ w, m ≤ w ∧ x ≤ w :=
  coactual_iff_comparable.2 h

/-- `Recognise` is our label for "a common future": a moment above both. It is not Hegel's mutual
acknowledgement of self-consciousnesses. -/
def Recognise (m x : M) : Prop := ∃ w, m ≤ w ∧ x ≤ w

/-- Incomparable moments have no common upper bound (by `linear_past`). Hegel's argument that a
fight to the death destroys the recognition it seeks is not modelled. `Unify.lean` shows that a
frame with joins gives up permanence of loss. -/
theorem no_recognition_between_barbarians {m x : M} (h : Barbarian m x) : ¬ Recognise m x :=
  barbarian_iff_no_common_future.1 h

/-- Recognition is exactly being on one line. -/
theorem recognise_iff_comparable {m x : M} : Recognise m x ↔ (m ≤ x ∨ x ≤ m) :=
  coactual_iff_comparable

end PEqualNP.Philosophy.Beauvoir
