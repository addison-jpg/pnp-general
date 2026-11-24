import PEqualNP.Defs

/-!
# Boolean sums on the NOT gate ladder (rung `k`)

Card 2 of the board: state rung `k` of the NOT gate ladder in the form that L-meta-951 proves for
`k = 1`. The setting is that of `one-not/lean` (`bound_of_forall_not_minCE`), written with the
circuits of `Defs/CircuitLowerBounds.lean`:

* sets `S w ⊆ [n]` with `|S w| ≥ 2` and `|S a ∩ S b| ≤ 1` for `a ≠ b` (a (1,1)-disjoint Boolean
  sum);
* one list of gates of AND, OR, NOT, fan-in at most two, with one output wire `out w` per set,
  where wire `out w` computes `OR(S w)` (`Circuit.eval` of `⟨gates, out w⟩`);
* at most `k` NOT gates, counted as in `SIZENot` (`Defs/General.lean`).

`BoolSumNot k` says that every such circuit has at least `∑ w (|S w| - 1)` gates.

* `boolSumNot_anti`: allowing more NOT gates gives a stronger statement, so rung `k + 1` gives
  rung `k`.
* `notCount_le_one_iff`: at most one NOT gate in the count of `SIZENot` is the same as "two NOT
  gates are the same gate", the hypothesis `AtMostOneNot` of `one-not/lean`.

State of knowledge (not claimed here): `k = 0` is the monotone case, proved in `one-not/lean` as
`W951/LiftBound.bound_of_noNot` (same hypotheses, no NOT gate). `k = 1` is L-meta-951
(`one-not/lean`, `bound_of_forall_not_minCE`; open statement `no_minCE`). For larger `k` nothing is
claimed.
The wire values agree with `one-not/lean`: `(Circuit.mk gates o).eval (List.ofFn x)` is, by
definition, `val gates x o` there.
-/

namespace PEqualNP.General.BoolSum

open PEqualNP.CircuitLowerBounds

open Classical in
/-- The number of NOT gates of a gate list, counted as in `SIZENot`. -/
noncomputable def notCount (gates : List Gate) : ℕ :=
  (gates.filter fun g => g.op = GateOp.not).length

/-- **Rung `k` for Boolean sums.** Every circuit of AND, OR and NOT gates of fan-in at most two,
with at most `k` NOT gates, that computes a (1,1)-disjoint Boolean sum has at least
`∑ w (|S w| - 1)` gates. `k = 1` is L-meta-951. -/
def BoolSumNot (k : ℕ) : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)),
    (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List Gate) (out : Fin m → ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      notCount gates ≤ k →
      (∀ (w : Fin m) (x : Fin n → Bool),
        (Circuit.mk gates (out w)).eval (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
      ∑ i : Fin m, ((S i).card - 1) ≤ gates.length

/-- More NOT gates allowed: rung `k + 1` gives rung `k`. -/
theorem boolSumNot_anti {k k' : ℕ} (hkk : k ≤ k') (h : BoolSumNot k') : BoolSumNot k :=
  fun S h2 hS gates out hg hN hev => h S h2 hS gates out hg (hN.trans hkk) hev

open Classical in
/-- At most one gate of a list satisfies `p` iff two gates satisfying `p` sit at the same index. -/
theorem length_filter_le_one_iff {α : Type*} (p : α → Prop) (l : List α) :
    (l.filter fun a => p a).length ≤ 1 ↔
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), p (l[i]'hi) → p (l[j]'hj) → i = j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · rw [List.filter_cons_of_pos (by simpa using ha), List.length_cons]
      have key : (l.filter fun a => p a).length + 1 ≤ 1 ↔ ∀ x ∈ l, ¬ p x := by
        rw [show (l.filter fun a => p a).length + 1 ≤ 1 ↔ (l.filter fun a => p a).length = 0 by
          omega, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        simp
      rw [key]
      constructor
      · intro hnil i j hi hj hpi hpj
        rcases i with _ | i
        · rcases j with _ | j
          · rfl
          · exact absurd hpj (hnil _ (List.getElem_mem _))
        · exact absurd hpi (hnil _ (List.getElem_mem _))
      · intro H x hx hpx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        exact absurd (H 0 (j + 1) (by simp) (by simpa using hj) ha hpx) (by omega)
    · rw [List.filter_cons_of_neg (by simpa using ha), ih]
      constructor
      · intro H i j hi hj hpi hpj
        rcases i with _ | i
        · exact absurd hpi ha
        rcases j with _ | j
        · exact absurd hpj ha
        simp only [List.length_cons] at hi hj
        exact congrArg (· + 1) (H i j (by omega) (by omega) hpi hpj)
      · intro H i j hi hj hpi hpj
        have := H (i + 1) (j + 1) (by simpa using hi) (by simpa using hj) hpi hpj
        omega

/-- `notCount gates ≤ 1` is `one-not/lean`'s `AtMostOneNot gates`: two NOT gates are the same gate. -/
theorem notCount_le_one_iff (gates : List Gate) :
    notCount gates ≤ 1 ↔
      ∀ (i1 i2 : ℕ) (h1 : i1 < gates.length) (h2 : i2 < gates.length),
        (gates[i1]'h1).op = GateOp.not → (gates[i2]'h2).op = GateOp.not → i1 = i2 :=
  length_filter_le_one_iff (fun g : Gate => g.op = GateOp.not) gates

end PEqualNP.General.BoolSum
