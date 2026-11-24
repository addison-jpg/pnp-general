import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LiftBound

/-!
# The literal statement of `L_meta_951` is equivalent to `OneNotBound`

`LMeta951Statement` is the type of `PEqualNP.Outside.L_meta_951`, copied verbatim from Final.lean
(`example : LMeta951Statement := PEqualNP.Outside.L_meta_951` typechecks; it is not included here,
so that nothing in this file depends on `no_minCE`).

The two statements differ in two places.
* Evaluation: `Circuit.eval ⟨gates, out w⟩ (List.ofFn x)` against `val gates x (out w)`; these are
  equal by unfolding (`circuit_eval_eq_val`).
* At most one NOT: `∃ ι : Fin 1 → Fin gates.length, ...` against `AtMostOneNot gates`. For
  `gates ≠ []` they are equivalent (`ι_iff_atMostOneNot`). For `gates = []` there is no
  `ι : Fin 1 → Fin 0`, so the literal statement says nothing about the empty circuit, while
  `AtMostOneNot []` holds. `OneNotBound` is still true there: an empty circuit computes no
  `OR(S w)` with `2 ≤ |S w|` (`no_output_of_nil`), so `m = 0` and the sum is `0`
  (`oneNotBound_nil`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The statement (type) of `PEqualNP.Outside.L_meta_951`, verbatim. -/
def LMeta951Statement : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length

/-- `Circuit.eval` on `List.ofFn x` is `val`. -/
theorem circuit_eval_eq_val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (o : ℕ) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = val gates x o := rfl

/-- The converse of `hU_of_ι`, for a nonempty circuit. -/
theorem ι_of_atMostOneNot {gates : List Gate} (hne : gates ≠ []) (hU : AtMostOneNot gates) :
    ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
  have hpos : 0 < gates.length := List.length_pos_iff.mpr hne
  by_cases h : ∃ i : Fin gates.length, (gates.get i).op = GateOp.not
  · obtain ⟨i0, h0⟩ := h
    refine ⟨fun _ => i0, fun i hi => ⟨0, ?_⟩⟩
    exact Fin.ext (hU i0 i i0.2 i.2 (by simpa using h0) (by simpa using hi))
  · exact ⟨fun _ => ⟨0, hpos⟩, fun i hi => absurd ⟨i, hi⟩ h⟩

/-- For a nonempty circuit, the `ι` encoding is `AtMostOneNot`. -/
theorem ι_iff_atMostOneNot {gates : List Gate} (hne : gates ≠ []) :
    (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) ↔ AtMostOneNot gates :=
  ⟨hU_of_ι, ι_of_atMostOneNot hne⟩

/-- For the empty circuit the `ι` encoding is false (`Fin 1 → Fin 0` is empty)... -/
theorem not_ι_nil : ¬ ∃ ι : Fin 1 → Fin ([] : List Gate).length, ∀ i : Fin ([] : List Gate).length,
    (([] : List Gate).get i).op = GateOp.not → ∃ j : Fin 1, ι j = i :=
  fun ⟨ι, _⟩ => (ι 0).elim0

/-- ... while `AtMostOneNot []` is true. -/
theorem atMostOneNot_nil : AtMostOneNot ([] : List Gate) :=
  fun _ _ h1 => absurd h1 (by simp)

/-- The empty circuit computes no `OR(T)` with `2 ≤ |T|`, at any output wire `o` (an input, or out
of range, which reads `false`). -/
theorem no_output_of_nil {n : ℕ} (T : Finset (Fin n)) (hT : 2 ≤ T.card) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val [] x o = decide (∃ v ∈ T, x v = true)) : False := by
  by_cases h : o < n
  · obtain ⟨v, hv, hne⟩ : ∃ v ∈ T, v ≠ ⟨o, h⟩ := by
      by_contra hc
      push Not at hc
      have : T ⊆ {⟨o, h⟩} := fun v hv => Finset.mem_singleton.mpr (hc v hv)
      have := Finset.card_le_card this
      simp at this
      omega
    have := hev (fun u => decide (u = v))
    simp only [val_nil, h, ↓reduceDIte] at this
    have h1 : decide ((⟨o, h⟩ : Fin n) = v) = false := by simpa using fun e => hne e.symm
    rw [h1] at this
    have h2 : decide (∃ u ∈ T, decide (u = v) = true) = true := by simpa using hv
    rw [h2] at this
    exact Bool.false_ne_true this
  · obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    have := hev (fun _ => true)
    simp only [val_nil, h, ↓reduceDIte] at this
    exact Bool.false_ne_true (this.trans (decide_eq_true ⟨v, hv, trivial⟩))

/-- `OneNotBound` for the empty circuit: there is no output, so the sum is `0`. -/
theorem oneNotBound_nil {n m : ℕ} (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val [] x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ ([] : List Gate).length := by
  have : IsEmpty (Fin m) := ⟨fun w => no_output_of_nil (S w) (h2 w) (out w) (hev w)⟩
  simp

/-- The literal statement of `L_meta_951` implies `OneNotBound`. -/
theorem oneNotBound_of_lMeta951Statement (H : LMeta951Statement) : OneNotBound := by
  intro n m S h2 hS gates out hg hU hev
  by_cases hne : gates = []
  · subst hne
    exact oneNotBound_nil S h2 out hev
  · exact H n m S h2 hS gates out hg (ι_of_atMostOneNot hne hU) hev

/-- `OneNotBound` implies the literal statement of `L_meta_951`. -/
theorem lMeta951Statement_of_oneNotBound (H : OneNotBound) : LMeta951Statement := by
  intro n m S h2 hS gates out hg hι hev
  exact H n m S h2 hS gates out hg (hU_of_ι hι) hev

/-- The literal statement of `L_meta_951` is equivalent to `OneNotBound`. -/
theorem L_meta_951_iff_oneNotBound : LMeta951Statement ↔ OneNotBound :=
  ⟨oneNotBound_of_lMeta951Statement, lMeta951Statement_of_oneNotBound⟩

/-- The literal statement is also equivalent to `LiftedBound`. -/
theorem L_meta_951_iff_liftedBound : LMeta951Statement ↔ LiftedBound :=
  L_meta_951_iff_oneNotBound.trans liftedBound_iff_oneNotBound.symm

end PEqualNP.Outside.L_meta_951_aux
