import Mathlib
import PEqualNP.Defs
import PEqualNP.Kernel.GateShape

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Kernel

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ r, gs.foldl step w = w ++ r := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr]
    simp [step]

theorem val_append {n : ℕ} (A B : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : j < n + A.length) : val (A ++ B) x j = val A x j := by
  unfold val
  rw [List.foldl_append]
  obtain ⟨r, hr⟩ := fold_prefix B (A.foldl step (List.ofFn x))
  rw [hr]
  have hl : (A.foldl step (List.ofFn x)).length = n + A.length := by
    rw [fold_length]; simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  rcases GateShape.and_or_shape g hop hlen (f z) with ⟨ho, hi, hz⟩ | ⟨ho, hi, _⟩ | ⟨a, hi, hz⟩ |
      ⟨ho, a, b, hi, hz⟩ | ⟨ho, a, b, hi, hz⟩
  · right
    exact ⟨0, 0, fun h => by rw [hz] at h; exact absurd h (by simp)⟩
  · left
    intro y
    simp [hi, ho, GateOp.eval]
  · right
    refine ⟨a, a, fun h => ?_⟩
    rw [hz] at h
    refine ⟨h, h, fun y hy => Or.inl ?_⟩
    rcases hop with ho | ho <;> simpa [hi, ho, GateOp.eval] using hy
  · right
    rw [hz] at *
    by_cases h : f z a = false
    · refine ⟨a, a, fun _ => ⟨h, h, fun y hy => Or.inl ?_⟩⟩
      exact (by simpa [hi, ho, GateOp.eval] using hy : _ ∧ _).1
    · refine ⟨b, b, fun hzz => ?_⟩
      have hb : f z b = false := by
        cases ha : f z a <;> cases hb : f z b <;> simp_all
      refine ⟨hb, hb, fun y hy => Or.inl ?_⟩
      simp [hi, ho, GateOp.eval] at hy
      exact hy.2
  · right
    refine ⟨a, b, fun h => ?_⟩
    rw [hz] at h
    refine ⟨?_, ?_, fun y hy => ?_⟩
    · exact (by simpa using h : _ ∧ _).1
    · exact (by simpa using h : _ ∧ _).2
    · simpa [hi, ho, GateOp.eval] using hy

end PEqualNP.Outside.L_meta_951_aux
