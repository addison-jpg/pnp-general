import Mathlib

/-!
# Hauntology as branching time (seat P4)

HONESTY. This file models a cited reading and claims nothing about what Fisher meant.

Readings followed: Mark Fisher, *Ghosts of My Life* (2014): hauntology, "the slow cancellation of the
future" (after Berardi), futures that were possible, exert pressure, and are no longer reachable.
Mark Fisher, *Capitalist Realism* (2009): "it is easier to imagine the end of the world than the
end of capitalism" (Fisher, after Jameson and Zizek). Source of the word: Derrida, *Specters of
Marx* (1993). The model captures only the modal half (cancelled possibility), not the affective
or ideological half. Pressure and slowness are not modelled: cancellation here is instantaneous
at a branch point and is a static fact about an order.
A lost future is read, as a remark and not a result, as a Deleuzian virtual no longer actualisable.
-/

namespace PEqualNP.Philosophy.Fisher

/-- A branching-time frame: moments with a partial order (earlier-than) whose past is linear
(the predecessors of any moment form a chain). (`IsHistory` below defines histories as maximal chains; no theorem uses it.) -/
class Frame (M : Type*) extends PartialOrder M where
  linear_past : ∀ a b c : M, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

variable {M : Type*} [Frame M]

/-- A history is a maximal chain. -/
def IsHistory (h : Set M) : Prop := IsChain (· ≤ ·) h ∧ ∀ c : Set M, IsChain (· ≤ ·) c → h ⊆ c → c = h

/-- Future `f` is reachable from `m`: it lies above `m`. -/
def Reachable (m f : M) : Prop := m ≤ f

/-- A modal definition read as Fisher's lost future: an untaken branch. `f` was reachable from some earlier moment `m' ≤ m`, yet is neither
reachable from `m` nor already past (a past moment is not a lost future). It cannot tell a lost
political future from an unchosen lunch: any branching makes a moment `Haunted`. -/
def Lost (m f : M) : Prop := (∃ m', m' ≤ m ∧ Reachable m' f) ∧ ¬ Reachable m f ∧ ¬ f ≤ m

/-- Some lost future exists at `m` (read as hauntology in Fisher; any branching suffices). -/
def Haunted (m : M) : Prop := ∃ f, Lost m f

/-- (1) Lost futures accumulate: once lost, lost at every later moment. Uses linearity of the
past; irreversibility is built into the static order, not derived. -/
theorem lost_mono {m m' f : M} (h : m ≤ m') (hl : Lost m f) : Lost m' f := by
  obtain ⟨⟨a, ha, haf⟩, hn, hp⟩ := hl
  refine ⟨⟨a, ha.trans h, haf⟩, fun hr => hn (h.trans hr), fun hf => ?_⟩
  rcases Frame.linear_past m f m' h hf with c | c
  · exact hn c
  · exact hp c

theorem haunted_mono {m m' : M} (h : m ≤ m') (hm : Haunted m) : Haunted m' :=
  hm.elim fun f hf => ⟨f, lost_mono h hf⟩

/-- (2) Branching: if the future splits at `m₀` into incomparable `b₁ b₂`, every moment above
`b₁` is haunted by `b₂`. -/
theorem haunted_of_branch {m₀ b₁ b₂ m : M} (h1 : m₀ ≤ b₁) (h2 : m₀ ≤ b₂)
    (hi : ¬ b₁ ≤ b₂) (hj : ¬ b₂ ≤ b₁) (hm : b₁ ≤ m) : Lost m b₂ := by
  refine ⟨⟨m₀, h1.trans hm, h2⟩, fun h => hi (hm.trans h), fun h => ?_⟩
  rcases Frame.linear_past b₁ b₂ m hm h with c | c
  · exact hi c
  · exact hj c

theorem haunted_of_branch' {m₀ b₁ b₂ m : M} (h1 : m₀ ≤ b₁) (h2 : m₀ ≤ b₂)
    (hi : ¬ b₁ ≤ b₂) (hj : ¬ b₂ ≤ b₁) (hm : b₁ ≤ m) : Haunted m :=
  ⟨b₂, haunted_of_branch h1 h2 hi hj hm⟩

/-- Possibly-`P` in the future-modal sense: some reachable future satisfies `P`. -/
def Possible (m : M) (P : M → Prop) : Prop := ∃ f, Reachable m f ∧ P f

/-- (3) `∀ → ¬∃¬` for reachable futures, plus an unfolding of `Lost`. If every reachable future
satisfies `P`, then `¬P` is not possible from `m`; and if `¬P` held at a lost future `g`, the
alternative was possible from an earlier moment. `P` is an arbitrary predicate; this does not model
ideology or imagination, and is read as Fisher's *Capitalist Realism* only by us. -/
theorem no_alternative_of_all_reachable {m : M} {P : M → Prop}
    (hP : ∀ f, Reachable m f → P f) :
    ¬ Possible m (fun f => ¬ P f) ∧
      ∀ g, Lost m g → ¬ P g →
        (∃ m', m' ≤ m ∧ Possible m' (fun f => ¬ P f)) ∧ Haunted m := by
  refine ⟨fun ⟨f, hr, hn⟩ => hn (hP f hr), fun g hg hn => ⟨?_, g, hg⟩⟩
  obtain ⟨⟨m', hm', hr⟩, _⟩ := hg
  exact ⟨m', hm', g, hr, hn⟩

/-- In a linear frame nothing is lost (a trivial fact; does not use `linear_past`). -/
theorem not_lost_of_total (htot : ∀ a b : M, a ≤ b ∨ b ≤ a) (m f : M) : ¬ Lost m f := by
  rintro ⟨_, hn, hp⟩
  rcases htot m f with c | c
  · exact hn c
  · exact hp c

/-! ### A tiny concrete frame: a root with two children, one of which has a child. -/

inductive N | root | a | b | c deriving DecidableEq

/-- `root ≤ everything`, `a ≤ c`, plus reflexivity. -/
def N.le : N → N → Prop
  | .root, _ => True
  | .a, .a => True | .a, .c => True
  | .b, .b => True | .c, .c => True
  | _, _ => False

instance : DecidableRel N.le := fun x y => by unfold N.le; cases x <;> cases y <;> infer_instance

instance : Frame N where
  le := N.le
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> simp [N.le]
  le_antisymm := by intro a b; cases a <;> cases b <;> simp [N.le]
  linear_past := by intro a b c; cases a <;> cases b <;> cases c <;> simp [N.le]

instance : DecidableRel (α := N) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (N.le x y))

example : Lost N.c N.b := haunted_of_branch (m₀ := N.root) (b₁ := N.a) (b₂ := N.b) (m := N.c)
  (by decide) (by decide) (by decide) (by decide) (by decide)

example : Haunted N.c := haunted_of_branch' (m₀ := N.root) (b₁ := N.a) (b₂ := N.b) (m := N.c)
  (by decide) (by decide) (by decide) (by decide) (by decide)

end PEqualNP.Philosophy.Fisher
