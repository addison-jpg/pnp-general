import PEqualNP.Philosophy.Fisher

/-!
# The absurd as a demand with no fixed point (philosophy-unification seat)

HONESTY. This file contains formal models of a cited reading. It claims nothing about what Camus
meant. Nothing here is about circuits, and nothing here bears on whether any open problem of this
repository has an answer.

Reading followed. Albert Camus, *Le Mythe de Sisyphe* (1942): the absurd is neither in the person
nor in the world but in their confrontation, the demand for a total and unified answer set against
a world that gives none; revolt is to keep the confrontation alive and continue. Cited from memory
of the O'Brien translation (in copyright; not quoted, not re-read for this file).

Three formal readings, each small:
1. no total answer: no family of answers indexed by the moments covers every question about the
   moments (Lawvere's fixed point theorem, in Cantor's case);
2. revolt: in a world without a last moment, every moment starts an endless strict ascent;
3. the reduction that never closes: a chain of reductions carries truth down to the first
   statement if it ever closes, and a chain that strictly lowers a natural number must stop.
-/

namespace PEqualNP.Philosophy.Camus

open PEqualNP.Philosophy.Fisher

/-! ### 1. No total answer -/

/-- Lawvere's fixed point theorem (F. W. Lawvere, "Diagonal arguments and cartesian closed
categories", 1969), in sets: if `A` parametrises every map `A → B`, every `g : B → B` has a fixed
point. -/
theorem lawvere_fixed_point {A B : Type*} (φ : A → A → B) (hφ : Function.Surjective φ)
    (g : B → B) : ∃ b, g b = b := by
  obtain ⟨a, ha⟩ := hφ (fun x => g (φ x x))
  exact ⟨φ a a, (congrFun ha a).symm⟩

/-- **The demand cannot be met.** A total answer would assign to each moment a verdict on every
moment, so that every question about moments is some moment's verdict. Negation has no fixed
point, so no such assignment exists. Reading: Camus's demand for unity, modelled as a demand for
self-coverage; the model choice is ours. -/
theorem no_total_answer (M : Type*) : ¬ ∃ φ : M → M → Prop, Function.Surjective φ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨b, hb⟩ := lawvere_fixed_point φ hφ Not
  have hnb : ¬ b := fun x => (hb.mpr x) x
  exact hnb (hb.mp hnb)

/-- A demand that always asks for more has no resting point. -/
theorem demand_no_fixed_point {M : Type*} [Preorder M] (D : M → M) (h : ∀ m, m < D m) (m : M) :
    D m ≠ m := fun e => absurd (h m) (by rw [e]; exact lt_irrefl m)

/-! ### 2. Revolt -/

variable {M : Type*} [Frame M]

/-- An absurd world: no moment is final. -/
def Absurd (M : Type*) [Frame M] : Prop := ∀ m : M, ¬ IsMax m

/-- **Revolt.** In an absurd world every moment begins an endless strictly ascending history.
Reading: Sisyphus continues; there is always a next step and never a last one. -/
theorem revolt (h : Absurd M) (m : M) : ∃ s : ℕ → M, s 0 = m ∧ StrictMono s := by
  choose next hnext using fun x : M => not_isMax_iff.1 (h x)
  refine ⟨fun n => next^[n] m, rfl, strictMono_nat_of_lt_succ fun n => ?_⟩
  rw [Function.iterate_succ_apply']
  exact hnext _

/-- Revolt does not undo loss: along any continuation, what was lost stays lost (Fisher's
`lost_mono`), so the ascent of Sisyphus carries its ghosts with it. -/
theorem revolt_keeps_ghosts {s : ℕ → M} (hs : StrictMono s) {f : M} (hl : Lost (s 0) f) (n : ℕ) :
    Lost (s n) f :=
  lost_mono (hs.monotone (Nat.zero_le n)) hl

/-! ### 3. Reductions that close, and reductions that do not -/

/-- A chain of reductions: statement `n + 1` implies statement `n`. If any stage is ever proved,
the first statement is proved. Reading: the board's chain A4 → A7 → A10 → BottomPay, where each
arrow is a checked implication and the last statement is open. -/
theorem chain_closes {P : ℕ → Prop} (red : ∀ n, P (n + 1) → P n) : ∀ n, P n → P 0
  | 0, h => h
  | n + 1, h => chain_closes red n (red n h)

/-- So an open first statement means every later stage is open too: the rock is the same rock at
every height. -/
theorem open_all_the_way {P : ℕ → Prop} (red : ∀ n, P (n + 1) → P n) (h0 : ¬ P 0) (n : ℕ) :
    ¬ P n := fun h => h0 (chain_closes red n h)

/-- The finite level is where the absurd stops: no sequence of natural numbers strictly descends
for ever. Reading: the repository's bottom level argues by a minimal counterexample; a reduction
that lowers a size must close. -/
theorem no_infinite_descent : ¬ ∃ f : ℕ → ℕ, StrictAnti f := by
  rintro ⟨f, hf⟩
  have key : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := hf (Nat.lt_add_one k)
      omega
  have := key (f 0 + 1)
  omega

end PEqualNP.Philosophy.Camus
