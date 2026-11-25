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
  other". The diary itself was not opened. See philosophy/UNIFY.md for what is and is not
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

/-- **Ambiguity.** The present is the one moment that is both given and open, and it is the only
thing the two sides share: neither side contains the other's content. -/
theorem ambiguity (m : M) : facticity m ∩ transcendence m = {m} := by
  ext x
  simp only [facticity, transcendence, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
    Set.mem_singleton_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-! ### 2. Freedom and seriousness -/

/-- A situation is free when it opens at least two futures that exclude each other. Reading: a
choice is real only if something else could be chosen (our modelling choice). -/
def Free (m : M) : Prop := ∃ f g, m ≤ f ∧ m ≤ g ∧ ¬ f ≤ g ∧ ¬ g ≤ f

/-- The serious attitude: the future is read as already given, one line like the past. Reading:
Beauvoir's "serious man", who treats values as ready-made things. -/
def Serious (m : M) : Prop := IsChain (· ≤ ·) (transcendence m)

/-- Seriousness is exactly the denial of freedom: it reads transcendence as more facticity. -/
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

/-- **No free act without a ghost.** Whichever of two exclusive futures is taken, the other is
lost from then on. This is Fisher's `haunted_of_branch`, read from the side of the one who
chooses. -/
theorem free_act_haunts {m : M} (h : Free m) :
    ∃ f g, m ≤ f ∧ m ≤ g ∧ (∀ m', f ≤ m' → Lost m' g) ∧ (∀ m', g ≤ m' → Lost m' f) := by
  obtain ⟨f, g, hf, hg, hfg, hgf⟩ := h
  exact ⟨f, g, hf, hg, fun _ hm => haunted_of_branch hf hg hfg hgf hm,
    fun _ hm => haunted_of_branch hg hf hgf hfg hm⟩

/-- **Every ghost is the trace of a freedom.** A haunted present has a free moment in its past:
the place where the lost future and the present parted. -/
theorem haunted_past_free {m : M} (h : Haunted m) : ∃ a, a ≤ m ∧ Free a := by
  obtain ⟨f, ⟨a, ham, haf⟩, hmf, hfm⟩ := h
  exact ⟨a, ham, m, f, ham, haf, hmf, hfm⟩

/-- In a serious world nothing is ever lost and nobody is haunted. -/
theorem serious_world_unhaunted (hs : ∀ a : M, Serious a) (m : M) : ¬ Haunted m := fun h =>
  let ⟨a, _, ha⟩ := haunted_past_free h
  (serious_iff_not_free a).1 (hs a) ha

/-! ### 3. The barbarians -/

/-- A barbarian, relative to a self `m`: one who is not me, was never me, and whom I cannot
become. Reading: Barrès's "barbares" as the young Beauvoir takes them over, those who are not the
self (confirmed only as far as the header says). Reading "not me" as "not me at any time of my
line" is our modelling step. -/
def Barbarian (m x : M) : Prop := Other m x

/-- The opposition of self and other is mutual: I am the barbarian of my barbarian. Reading:
Hegel's recognition scene in its barest form, and Beauvoir's 1927 "opposition of self and
other". -/
theorem barbarian_symm {m x : M} (h : Barbarian m x) : Barbarian x m := other_symm h

/-- A self is never its own barbarian, nor is its past or its possible future. -/
theorem not_barbarian_self (m : M) : ¬ Barbarian m m := fun h => h.1 le_rfl

/-- Self and barbarian share no possible future in a branching frame. -/
theorem barbarian_iff_no_common_future {m x : M} : Barbarian m x ↔ ¬ ∃ h, m ≤ h ∧ x ≤ h :=
  other_iff_no_common_future

/-- **The barbarians are one's own lost futures.** In a frame with a first moment, the one who is
not me is exactly a future that was open to an earlier me and is now cancelled. So the other is
made of what the self gave up, which is the formal part of the reading "the hatred of the
barbarians is a relation to oneself". -/
theorem barbarian_iff_lost [OrderBot M] {m x : M} : Barbarian m x ↔ Lost m x :=
  lost_iff_other.symm

/-- Each barbarian marks a moment of the self's own past that was free. -/
theorem barbarian_past_free [OrderBot M] {m x : M} (h : Barbarian m x) : ∃ a, a ≤ m ∧ Free a :=
  haunted_past_free ⟨x, barbarian_iff_lost.1 h⟩

/-- Being a barbarian is settled by position alone: it is the same whatever is true at `x`
("even if you might be right", as the diary is quoted). In the model, any property at all may
hold at a barbarian. -/
theorem barbarian_whatever_is_right {m x : M} (h : Barbarian m x) (Right : M → Prop) :
    (Right x → Barbarian m x) ∧ (¬ Right x → Barbarian m x) := ⟨fun _ => h, fun _ => h⟩

/-! ### 4. *She Came to Stay*: each consciousness seeks the death of the other -/

/-- **The epigraph, in the frame.** Between a self and its barbarian, every continuation of the
one is a world from which the other is cancelled, and this holds in both directions. Reading: the
Hegel epigraph of *L'Invitée*; the two consciousnesses are Françoise and Xavière. -/
theorem each_seeks_the_death_of_the_other [OrderBot M] {m x : M} (h : Barbarian m x) :
    (∀ m', m ≤ m' → Lost m' x) ∧ (∀ x', x ≤ x' → Lost x' m) :=
  ⟨fun _ hm => lost_mono hm (barbarian_iff_lost.1 h),
    fun _ hx => lost_mono hx (barbarian_iff_lost.1 (barbarian_symm h))⟩

/-- A particular other, not the other as such: whoever lies on my own line shares a future with
me, and nothing of the kind follows for them. Reading: the SEP remark on the novel's ending. -/
theorem not_every_other_dies {m x : M} (h : m ≤ x ∨ x ≤ m) : ∃ w, m ≤ w ∧ x ≤ w :=
  coactual_iff_comparable.2 h

/-- Recognition between two selves: a moment that holds both. Reading: Hegel's mutual
recognition, in its barest form (our modelling choice). -/
def Recognise (m x : M) : Prop := ∃ w, m ≤ w ∧ x ≤ w

/-- **The struggle defeats itself.** In a branching frame, barbarians cannot recognise each
other: recognition would need a common moment, and linear past forbids one. So the frame that
makes loss permanent is the frame in which the opposition of self and other has no resolution;
`Unify.lean` shows that a frame with joins resolves it and gives up permanence. -/
theorem no_recognition_between_barbarians {m x : M} (h : Barbarian m x) : ¬ Recognise m x :=
  barbarian_iff_no_common_future.1 h

/-- Recognition is exactly being on one line. -/
theorem recognise_iff_comparable {m x : M} : Recognise m x ↔ (m ≤ x ∨ x ≤ m) :=
  coactual_iff_comparable

end PEqualNP.Philosophy.Beauvoir
