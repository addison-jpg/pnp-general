import Mathlib
import PEqualNP.Defs.CircuitLowerBounds

/-!
# OR of `n` inputs needs `n - 1` AND/OR gates, with any number of NOT gates

Setting: the project's own `PEqualNP.CircuitLowerBounds.Circuit` (gates `and`, `or`, `not`, fan-in at
most two, wires that do not exist read `false`). NOT gates are unlimited and FREE: only AND/OR gates
are counted. Since the total gate count is at least the AND/OR count, the bound holds for the project's
`Circuit.size` as well.

Proof (structural, no enumeration). Keep a partition of the inputs, given by a colouring `c`. A NOT gate
and any gate reading at most one wire do not change it. An AND/OR gate reading two wires whose values
depend only on the colour classes `k1`, `k2` merges `k2` into `k1`: the number of classes drops by at
most one, and every earlier wire still depends on a single class. After `a` AND/OR gates there are at
least `n - a` classes and every wire depends on one class. The output of an OR depends on every input,
so there is one class: `n ≤ a + 1`. For `n = 4`: at least 3 gates.
-/

namespace PEqualNP.W951.Open.Or4ManyNot

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

/-- one gate appended to the wire list (the body of `Circuit.wires`) -/
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- the gates that are counted: everything except NOT -/
def counted (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

def Valid (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

/-- `f` depends only on the inputs of colour `k` -/
def DepIn (c : Fin n → ℕ) (k : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, c i = k → x i = y i) → f x = f y

def Inv (ws : (Fin n → Bool) → List Bool) (c : Fin n → ℕ) (L a : ℕ) : Prop :=
  (∀ x, (ws x).length = L) ∧ n ≤ (Finset.univ.image c).card + a ∧
    ∀ j, ∃ k, DepIn c k (fun x => (ws x).getD j false)

def mergeC (c : Fin n → ℕ) (k1 k2 : ℕ) : Fin n → ℕ := fun i => if c i = k2 then k1 else c i

theorem DepIn.merge {c : Fin n → ℕ} {k : ℕ} {f : (Fin n → Bool) → Bool} (h : DepIn c k f)
    (k1 k2 : ℕ) : DepIn (mergeC c k1 k2) (if k = k2 then k1 else k) f := by
  intro x y hxy
  apply h
  intro i hi
  apply hxy i
  simp [mergeC, hi]

theorem DepIn.const (c : Fin n → ℕ) (k : ℕ) (b : Bool) : DepIn c k (fun _ => b) :=
  fun _ _ _ => rfl

theorem card_merge (c : Fin n → ℕ) (k1 k2 : ℕ) :
    (Finset.univ.image c).card ≤ (Finset.univ.image (mergeC c k1 k2)).card + 1 := by
  have : Finset.univ.image c ⊆ insert k2 (Finset.univ.image (mergeC c k1 k2)) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    by_cases h : c i = k2
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [mergeC, h]⟩)
  exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)

theorem getD_stepW (w : List Bool) (g : Gate) (j : ℕ) :
    (stepW w g).getD j false =
      if j < w.length then w.getD j false
      else if j = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold stepW
  by_cases h1 : j < w.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · by_cases h2 : j = w.length
    · subst h2; simp
    · have h3 : w.length < j := by omega
      rw [if_neg h1, if_neg h2, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega)]
      rfl

/-- generic step: a new colouring that keeps every old wire inside one class, loses at most `b`
classes, and puts the new wire inside one class. -/
theorem step_inv {ws : (Fin n → Bool) → List Bool} {c : Fin n → ℕ} {L a : ℕ}
    (h : Inv ws c L a) (g : Gate) (c' : Fin n → ℕ) (b : ℕ)
    (hc' : ∀ j k, DepIn c k (fun x => (ws x).getD j false) →
      ∃ k', DepIn c' k' (fun x => (ws x).getD j false))
    (hcard : (Finset.univ.image c).card ≤ (Finset.univ.image c').card + b)
    (hv : ∃ k, DepIn c' k (fun x => g.op.eval (g.inputs.map fun i => (ws x).getD i false))) :
    Inv (fun x => stepW (ws x) g) c' (L + 1) (a + b) := by
  obtain ⟨hL, hn, hd⟩ := h
  refine ⟨?_, by omega, ?_⟩
  · intro x; simp [stepW, hL x]
  · intro j
    obtain ⟨k0, hk0⟩ := hv
    by_cases h1 : j < L
    · obtain ⟨k, hk⟩ := hd j
      obtain ⟨k', hk'⟩ := hc' j k hk
      refine ⟨k', fun x y hxy => ?_⟩
      have := hk' x y hxy
      simp only [getD_stepW, hL, h1, if_true]
      exact this
    · by_cases h2 : j = L
      · refine ⟨k0, fun x y hxy => ?_⟩
        simp only [getD_stepW, hL, h2, lt_irrefl, if_false, if_true]
        exact hk0 x y hxy
      · refine ⟨0, fun x y _ => ?_⟩
        have e : ∀ z, (stepW (ws z) g).getD j false = false := fun z => by
          rw [getD_stepW, hL]; simp [h1, h2]
        show (stepW (ws x) g).getD j false = (stepW (ws y) g).getD j false
        rw [e x, e y]

theorem binary_case {ws : (Fin n → Bool) → List Bool} {c : Fin n → ℕ} {L a : ℕ}
    (h : Inv ws c L a) (g : Gate) (i j : ℕ) (F : Bool → Bool → Bool)
    (hF : ∀ x, g.op.eval (g.inputs.map fun i => (ws x).getD i false)
      = F ((ws x).getD i false) ((ws x).getD j false)) :
    ∃ c', Inv (fun x => stepW (ws x) g) c' (L + 1) (a + 1) := by
  obtain ⟨k1, hk1⟩ := h.2.2 i
  obtain ⟨k2, hk2⟩ := h.2.2 j
  refine ⟨mergeC c k1 k2, step_inv h g _ 1 ?_ (card_merge c k1 k2) ?_⟩
  · intro j' k hk
    exact ⟨_, hk.merge k1 k2⟩
  · refine ⟨k1, fun x y hxy => ?_⟩
    have e1 : DepIn (mergeC c k1 k2) k1 (fun x => (ws x).getD i false) := by
      simpa using hk1.merge k1 k2
    have e2 : DepIn (mergeC c k1 k2) k1 (fun x => (ws x).getD j false) := by
      simpa using hk2.merge k1 k2
    have a1 := e1 x y hxy
    have a2 := e2 x y hxy
    simp only at a1 a2
    show g.op.eval (g.inputs.map fun i => (ws x).getD i false)
      = g.op.eval (g.inputs.map fun i => (ws y).getD i false)
    rw [hF x, hF y, a1, a2]

theorem step_valid {ws : (Fin n → Bool) → List Bool} {c : Fin n → ℕ} {L a : ℕ}
    (h : Inv ws c L a) (g : Gate) (hg : Valid g) :
    ∃ c', Inv (fun x => stepW (ws x) g) c' (L + 1) (a + if counted g then 1 else 0) := by
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with hop | hop | hop
  · -- AND
    have hc : counted g = true := by simp [counted, hop]
    rw [hc]; simp only [if_true]
    match hI : g.inputs, hlen with
    | [], _ => exact binary_case h g 0 0 (fun _ _ => true) (by intro x; simp [hop, GateOp.eval, hI])
    | [i], _ => exact binary_case h g i i (fun p _ => p) (by intro x; simp [hop, GateOp.eval, hI])
    | [i, j], _ =>
      exact binary_case h g i j (fun p q => p && q) (by intro x; simp [hop, GateOp.eval, hI])
  · -- OR
    have hc : counted g = true := by simp [counted, hop]
    rw [hc]; simp only [if_true]
    match hI : g.inputs, hlen with
    | [], _ => exact binary_case h g 0 0 (fun _ _ => false) (by intro x; simp [hop, GateOp.eval, hI])
    | [i], _ => exact binary_case h g i i (fun p _ => p) (by intro x; simp [hop, GateOp.eval, hI])
    | [i, j], _ =>
      exact binary_case h g i j (fun p q => p || q) (by intro x; simp [hop, GateOp.eval, hI])
  · -- NOT: nothing changes
    have hc : counted g = false := by simp [counted, hop]
    rw [hc]; simp only [Bool.false_eq_true, if_false, add_zero]
    refine ⟨c, step_inv h g c 0 (fun j k hk => ⟨k, hk⟩) (by omega) ?_⟩
    match hI : g.inputs with
    | [] => exact ⟨0, by simp [hop, GateOp.eval, hI]; exact DepIn.const _ _ _⟩
    | i :: rest =>
      obtain ⟨k, hk⟩ := h.2.2 i
      refine ⟨k, fun x y hxy => ?_⟩
      simp only [hop, GateOp.eval, hI, List.map_cons, List.headD_cons]
      have := hk x y hxy
      simp only at this
      rw [this]

theorem foldl_inv (gs : List Gate) (hv : ∀ g ∈ gs, Valid g) :
    ∀ (ws : (Fin n → Bool) → List Bool) (c : Fin n → ℕ) (L a : ℕ), Inv ws c L a →
      ∃ c' L', Inv (fun x => gs.foldl stepW (ws x)) c' L' (a + gs.countP counted) := by
  induction gs with
  | nil => intro ws c L a h; exact ⟨c, L, by simpa using h⟩
  | cons g gs ih =>
    intro ws c L a h
    obtain ⟨c1, h1⟩ := step_valid h g (hv g (List.mem_cons_self ..))
    obtain ⟨c2, L2, h2⟩ := ih (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')) _ c1 _ _ h1
    refine ⟨c2, L2, ?_⟩
    have e : a + (g :: gs).countP counted = a + (if counted g then 1 else 0) + gs.countP counted := by
      rw [List.countP_cons]; omega
    rw [e]
    simpa [List.foldl_cons] using h2

theorem init_inv : Inv (n := n) (fun x => List.ofFn x) (fun i => i.val) n 0 := by
  refine ⟨fun x => by simp, ?_, fun j => ?_⟩
  · have : (Finset.univ.image (fun i : Fin n => i.val)).card = n := by
      rw [Finset.card_image_of_injective _ Fin.val_injective]; simp
    omega
  · by_cases hj : j < n
    · refine ⟨j, fun x y hxy => ?_⟩
      have := hxy ⟨j, hj⟩ rfl
      simpa [List.getD_eq_getElem?_getD, hj] using this
    · exact ⟨0, fun x y _ => by simp [List.getD_eq_default, hj]⟩

/-- **OR of `n` inputs, any number of NOT gates.** A circuit of AND, OR and NOT gates of fan-in at most
two computing the OR of `n` inputs has at least `n - 1` AND/OR gates (NOT gates are free). -/
theorem or_needs_gates (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (hor : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i, x i = true)) :
    n ≤ C.gates.countP counted + 1 := by
  obtain ⟨c, L, hL, hn, hd⟩ := foldl_inv C.gates hv _ _ _ _ (init_inv (n := n))
  obtain ⟨k, hk⟩ := hd C.output
  have hw : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (C.gates.foldl stepW (List.ofFn x)).getD C.output false := by
    intro x; rfl
  have hall : ∀ i, c i = k := by
    intro i
    by_contra hne
    have := hk (fun _ => false) (fun j => decide (j = i)) (by
      intro j hj
      have : j ≠ i := fun e => hne (e ▸ hj)
      simp [this])
    have e1 := hor (fun _ => false)
    have e2 := hor (fun j => decide (j = i))
    simp only [← hw] at this
    rw [e1, e2] at this
    simp at this
  have : (Finset.univ.image c).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    rw [hall i, hall j]
  omega

/-- **OR of four inputs (one 4-set, base 3), any number of NOT gates: at least 3 gates.** -/
theorem or4_needs_three_andor (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (hor : ∀ x : List Bool, x.length = 4 → C.eval x = x.any id) :
    3 ≤ C.gates.countP counted := by
  have := or_needs_gates (n := 4) C hv (fun x => by
    rw [hor _ (by simp)]
    simp [Fin.exists_fin_succ])
  omega

/-- Total size (NOT gates included) is at least 3 as well. -/
theorem or4_size_ge_three (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (hor : ∀ x : List Bool, x.length = 4 → C.eval x = x.any id) : 3 ≤ C.size :=
  (or4_needs_three_andor C hv hor).trans List.countP_le_length

#print axioms or_needs_gates
#print axioms or4_needs_three_andor
#print axioms or4_size_ge_three

end PEqualNP.W951.Open.Or4ManyNot
