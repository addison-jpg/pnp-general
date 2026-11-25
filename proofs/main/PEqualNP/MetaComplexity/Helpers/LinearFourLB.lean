import Mathlib
import PEqualNP.Defs

/-!
# A `3m` lower bound for ORs over a linear 4-uniform family (weight ≤ 2 promise)

Let `S : Fin m → Finset (Fin n)` be a family of `m` four-element subsets of the `n` inputs
that pairwise share at most one point (a *linear* 4-uniform hypergraph), and assume `n ≤ 15`.
Any list of AND/OR gates of fan-in at most two with outputs `out w` that, on every input of
Hamming weight at most two, compute `⋁_{v ∈ S w} x v` for every `w`, has at least `3 * m`
gates (`linear_four_lb`).

This generalizes `PEqualNP.Outside.L_meta_667` (the 13 lines of the projective plane of order
three, recovered as `pg23_lb`). The proof is the same: every line owns at least two gates whose
weight-one support lies inside it, and a line with only two owned gates is additionally charged
to gates whose support strictly contains it.

The bound `n ≤ 15` enters only in `triple_split`: the three supersets of a "triple" have
pairwise disjoint excess outside the line, so with at most `11` points outside a line each
excess has size at most `5` and each superset has at most `9` points, and a set of at most `9`
points contains at most `3` lines (`lines_in_card_le9_le3`). For larger `n` the supersets can be
arbitrarily large and contain arbitrarily many lines, and this charging argument no longer
applies.
-/

namespace PEqualNP.MetaComplexity.LinearFour

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


section Plane

variable {n m : ℕ} {S : Fin m → Finset (Fin n)}

-- Combinatorics of a linear 4-uniform family `S`
lemma line_eq_of_subset_two
    (card_inter_line : ∀ w₁ w₂ : Fin m, w₁ ≠ w₂ → (S w₁ ∩ S w₂).card ≤ 1)
    {T : Finset (Fin n)} {w₁ w₂ : Fin m}
    (h1 : T ⊆ S w₁) (h2 : T ⊆ S w₂) (hc : 2 ≤ T.card) : w₁ = w₂ := by
  by_contra hne
  have hle := Finset.card_le_card (Finset.subset_inter h1 h2)
  have := card_inter_line w₁ w₂ hne
  omega

lemma line_eq_of_superset_le6 (card_line : ∀ w : Fin m, (S w).card = 4)
    (card_inter_line : ∀ w₁ w₂ : Fin m, w₁ ≠ w₂ → (S w₁ ∩ S w₂).card ≤ 1)
    {T : Finset (Fin n)} {w₁ w₂ : Fin m}
    (h1 : S w₁ ⊆ T) (h2 : S w₂ ⊆ T) (hc : T.card ≤ 6) : w₁ = w₂ := by
  by_contra hne
  have hle := Finset.card_le_card (Finset.union_subset h1 h2)
  have hci := Finset.card_union_add_card_inter (S w₁) (S w₂)
  have := card_inter_line w₁ w₂ hne
  have := card_line w₁
  have := card_line w₂
  omega

lemma lines_in_card_le9_le3 (card_line : ∀ w : Fin m, (S w).card = 4)
    (card_inter_line : ∀ w₁ w₂ : Fin m, w₁ ≠ w₂ → (S w₁ ∩ S w₂).card ≤ 1)
    (T : Finset (Fin n)) (hc : T.card ≤ 9) :
    (Finset.univ.filter (fun w : Fin m => S w ⊆ T)).card ≤ 3 := by
  set X := Finset.univ.filter (fun w : Fin m => S w ⊆ T)
  by_contra hgt
  obtain ⟨w₄, hw₄⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : 2 < (X.erase w₄).card := by rw [Finset.card_erase_of_mem hw₄]; omega
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hcard
  rw [Finset.mem_erase] at hw₁ hw₂ hw₃
  have hL : ∀ w ∈ X, S w ⊆ T := fun w hw => (Finset.mem_filter.mp hw).2
  have hun : ((S w₁ ∪ S w₂) ∪ S w₃) ∪ S w₄ ⊆ T :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset (hL _ hw₁.2) (hL _ hw₂.2))
      (hL _ hw₃.2)) (hL _ hw₄)
  have i12 := card_inter_line w₁ w₂ h12
  have i13 := card_inter_line w₁ w₃ h13
  have i23 := card_inter_line w₂ w₃ h23
  have i14 := card_inter_line w₁ w₄ hw₁.1
  have i24 := card_inter_line w₂ w₄ hw₂.1
  have i34 := card_inter_line w₃ w₄ hw₃.1
  have c2 := Finset.card_union_add_card_inter (S w₁) (S w₂)
  have c3 := Finset.card_union_add_card_inter (S w₁ ∪ S w₂) (S w₃)
  have c4 := Finset.card_union_add_card_inter ((S w₁ ∪ S w₂) ∪ S w₃) (S w₄)
  have d3 : ((S w₁ ∪ S w₂) ∩ S w₃).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have := Finset.card_union_le (S w₁ ∩ S w₃) (S w₂ ∩ S w₃); omega
  have d4 : (((S w₁ ∪ S w₂) ∪ S w₃) ∩ S w₄).card ≤ 3 := by
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
    have := Finset.card_union_le (S w₁ ∩ S w₄ ∪ S w₂ ∩ S w₄) (S w₃ ∩ S w₄)
    have := Finset.card_union_le (S w₁ ∩ S w₄) (S w₂ ∩ S w₄); omega
  have hle := Finset.card_le_card hun
  have := card_line w₁
  have := card_line w₂
  have := card_line w₃
  have := card_line w₄
  omega


-- Light inputs and monotonicity helpers
def e1 (v : Fin n) : Fin n → Bool := fun k => decide (k = v)
def e2 (a b : Fin n) : Fin n → Bool := fun k => decide (k = a ∨ k = b)

def WeightLe2 (x : Fin n → Bool) : Prop :=
  ∀ i j k : Fin n, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k

lemma e1_weightLe2 (v : Fin n) : WeightLe2 (e1 v) := by
  intro i j k hi hj hk
  simp only [e1, decide_eq_true_eq] at hi hj hk
  left; exact hi.trans hj.symm

lemma e2_weightLe2 (a b : Fin n) : WeightLe2 (e2 a b) := by
  intro i j k hi hj hk
  simp only [e2, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> tauto

def MonoFun (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ k, x k = true → y k = true) → f x = true → f y = true

def Safe (S : Fin m → Finset (Fin n)) (w : Fin m) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, WeightLe2 x → f x = true → ∃ v ∈ S w, x v = true

lemma prime_weight2 (w : Fin m) (f₁ f₂ : (Fin n → Bool) → Bool)
    (hm₁ : MonoFun f₁) (hm₂ : MonoFun f₂)
    (hs : Safe S w (fun x => f₁ x && f₂ x)) :
    (∀ v : Fin n, f₁ (e1 v) = true → v ∈ S w) ∨
    (∀ v : Fin n, f₂ (e1 v) = true → v ∈ S w) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨a, ha1, haL⟩, ⟨b, hb2, hbL⟩⟩ := h
  have h1 : f₁ (e2 a b) = true := hm₁ (e1 a) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk) ha1
  have h2 : f₂ (e2 a b) = true := hm₂ (e1 b) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk) hb2
  obtain ⟨v, hvL, hvx⟩ := hs (e2 a b) (e2_weightLe2 a b) (by simp [h1, h2])
  simp only [e2, decide_eq_true_eq] at hvx
  rcases hvx with rfl | rfl
  · exact haL hvL
  · exact hbL hvL

-- Wire evaluation and weight-1 support V
def wval (gates : List Gate) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD i false

def wvalAt (gates : List Gate) (k i : ℕ) (x : Fin n → Bool) : Bool :=
  if i < n + k then wval gates i x else false

def V (n : ℕ) (gates : List Gate) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => wval gates i (e1 v) = true)

def VAt (n : ℕ) (gates : List Gate) (k i : ℕ) : Finset (Fin n) :=
  if i < n + k then V n gates i else ∅

lemma mem_V (gates : List Gate) (i : ℕ) (v : Fin n) :
    v ∈ V n gates i ↔ wval gates i (e1 v) = true := by
  simp [V]

lemma mem_VAt (gates : List Gate) (k i : ℕ) (v : Fin n) :
    v ∈ VAt n gates k i ↔ wvalAt gates k i (e1 v) = true := by
  unfold VAt wvalAt
  split_ifs with h
  · exact mem_V (n := n) gates i v
  · simp

lemma wval_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ) :
    MonoFun (wval (n := n) gates i) := by
  intro x y hle hx
  apply wiresFrom_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp) _ i hx
  intro j hj
  by_cases hjlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

lemma wvalAt_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (k i : ℕ) :
    MonoFun (wvalAt (n := n) gates k i) := by
  intro x y hle hx
  unfold wvalAt at hx ⊢
  split_ifs at hx ⊢ with h
  exact wval_mono (n := n) gates hmono i x y hle hx

lemma wval_input (gates : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wval gates i x = x ⟨i, hi⟩ := by
  unfold wval
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [getD_wiresFrom_lt gates (List.ofFn x) i (by omega)]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_ofFn (f := x) (i := i) (by omega)

lemma V_input (gates : List Gate) (i : ℕ) (hi : i < n) :
    V n gates i = {⟨i, hi⟩} := by
  ext v
  rw [mem_V, wval_input (n := n) gates i hi, Finset.mem_singleton]
  simp [e1, Fin.ext_iff, eq_comm]

lemma card_V_input (gates : List Gate) (i : ℕ) (hi : i < n) :
    (V n gates i).card = 1 := by
  rw [V_input (n := n) gates i hi, Finset.card_singleton]

lemma V_ge_len (gates : List Gate) (i : ℕ) (hi : n + gates.length ≤ i) :
    V n gates i = ∅ := by
  ext v
  rw [mem_V]
  simp only [Finset.notMem_empty, iff_false]
  unfold wval
  rw [List.getD_eq_default]
  · simp
  · rw [length_wiresFrom, List.length_ofFn]; omega

lemma gate_idx_of_VAt_ge2 (gates : List Gate) (k i : ℕ) (hc : 2 ≤ (VAt n gates k i).card) :
    ∃ g' < k, i = n + g' := by
  unfold VAt at hc
  split_ifs at hc with hlt
  · have hge13 : n ≤ i := by
      by_contra h13
      have hcard := card_V_input (n := n) gates i (by omega)
      omega
    exact ⟨i - n, by omega, by omega⟩
  · simp at hc

lemma gate_idx_of_V_ge2 (gates : List Gate) (i : ℕ) (hc : 2 ≤ (V n gates i).card) :
    ∃ g < gates.length, i = n + g := by
  have hlt : i < n + gates.length := by
    by_contra hge
    have he := V_ge_len (n := n) gates i (by omega)
    rw [he] at hc; simp at hc
  have hge13 : n ≤ i := by
    by_contra h13
    have hcard := card_V_input (n := n) gates i (by omega)
    omega
  exact ⟨i - n, by omega, by omega⟩

lemma wval_gate_eq (gates : List Gate) (k : ℕ) (hk : k < gates.length) (x : Fin n → Bool) :
    wval gates (n + k) x =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => wvalAt gates k i x) := by
  have h := getD_wiresFrom_gate gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  exact h

lemma V_gate_nil_and (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = []) :
    V n gates (n + k) = Finset.univ := by
  ext v
  rw [mem_V, wval_gate_eq (n := n) gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_nil_or (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = []) :
    V n gates (n + k) = ∅ := by
  ext v
  rw [mem_V, wval_gate_eq (n := n) gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) (x : Fin n → Bool) :
    wval gates (n + k) x = wvalAt gates k a x := by
  rw [wval_gate_eq (n := n) gates k hk, hin]
  rcases hop with h | h <;> simp [h, GateOp.eval]

lemma wval_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) (x : Fin n → Bool) :
    wval gates (n + k) x = (wvalAt gates k a x && wvalAt gates k b x) := by
  rw [wval_gate_eq (n := n) gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) (x : Fin n → Bool) :
    wval gates (n + k) x = (wvalAt gates k a x || wvalAt gates k b x) := by
  rw [wval_gate_eq (n := n) gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) :
    V n gates (n + k) = VAt n gates k a := by
  ext v; rw [mem_V, mem_VAt, wval_gate_one (n := n) gates k hk a hop hin]

lemma V_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) :
    V n gates (n + k) = VAt n gates k a ∩ VAt n gates k b := by
  ext v; rw [mem_V, Finset.mem_inter, mem_VAt, mem_VAt, wval_gate_two_and (n := n) gates k hk a b hop hin]
  simp [Bool.and_eq_true]

lemma V_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) :
    V n gates (n + k) = VAt n gates k a ∪ VAt n gates k b := by
  ext v; rw [mem_V, Finset.mem_union, mem_VAt, mem_VAt, wval_gate_two_or (n := n) gates k hk a b hop hin]
  simp [Bool.or_eq_true]

-- A constant-true gate is never safe (it fires on the all-false input)
lemma not_safe_nil_and (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = []) (w : Fin m) :
    ¬ Safe S w (wval (n := n) gates (n + k)) := by
  intro hsafe
  have hval : wval (n := n) gates (n + k) (fun _ => false) = true := by
    rw [wval_gate_eq (n := n) gates k hk, hop, hin]; simp [GateOp.eval]
  obtain ⟨v, _, hv⟩ := hsafe (fun _ => false) (by intro i j k hi; simp at hi) hval
  simp at hv

-- Owned gate sets and triple-superset predicate
def GwUp (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) (g : ℕ) : Finset ℕ :=
  (Finset.range (g + 1)).filter (fun j => V n gates (n + j) ⊆ S w ∧ 2 ≤ (V n gates (n + j)).card)

def Gw (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => V n gates (n + j) ⊆ S w ∧ 2 ≤ (V n gates (n + j)).card)

def HasTriple (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) : Prop :=
  ∃ ga gb gc : ℕ,
    ga < gates.length ∧ gb < gates.length ∧ gc < gates.length ∧
    S w ⊂ V n gates (n + ga) ∧ S w ⊂ V n gates (n + gb) ∧ S w ⊂ V n gates (n + gc) ∧
    Disjoint (V n gates (n + ga) \ S w) (V n gates (n + gb) \ S w) ∧
    Disjoint (V n gates (n + ga) \ S w) (V n gates (n + gc) \ S w) ∧
    Disjoint (V n gates (n + gb) \ S w) (V n gates (n + gc) \ S w)

lemma GwUp_subset_Gw (gates : List Gate) (w : Fin m) (g : ℕ) (hg : g < gates.length) :
    GwUp S gates w g ⊆ Gw S gates w := by
  intro j hj
  simp only [GwUp, Gw, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma card_ge3_of_three {S : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac])]
    rw [Finset.card_insert_of_notMem (by simp [hbc])]
    simp
  linarith [Finset.card_le_card hsub]

lemma card_ge2_of_two {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    2 ≤ S.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab])]; simp
  linarith [Finset.card_le_card hsub]

lemma card_ge3_of_sub (gates : List Gate) (w : Fin m) (g' g : ℕ)
    (hlt : g' < g) (hg : g ∈ GwUp S gates w g) (h2 : 2 ≤ (GwUp S gates w g').card) :
    3 ≤ (GwUp S gates w g).card := by
  have hnot : g ∉ GwUp S gates w g' := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    omega
  have hsub : insert g (GwUp S gates w g') ⊆ GwUp S gates w g := by
    intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact hg
    · simp only [GwUp, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

-- Helper: any gate g' with V(n+g') ⊆ S w, card = 3, and Safe S w has an earlier gate in GwUp
lemma exists_child_of_card3 (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) (g' : ℕ) (hg' : g' < gates.length)
    (hsub : V n gates (n + g') ⊆ S w) (hcard : (V n gates (n + g')).card = 3)
    (hsafe : Safe S w (wval gates (n + g'))) :
    ∃ g'' < g', V n gates (n + g'') ⊆ S w ∧ 2 ≤ (V n gates (n + g'')).card := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  obtain ⟨hop, hlen⟩ := hvalid (gates[g']) (List.getElem_mem hg')
  match hin : (gates[g']).inputs with
  | [] =>
    rcases hop with h | h
    · exact absurd hsafe (not_safe_nil_and gates g' hg' h hin w)
    · have hV := V_gate_nil_or (n := n) gates g' hg' h hin
      rw [hV] at hcard; simp at hcard
  | [a] =>
    have hV := V_gate_one (n := n) gates g' hg' a hop hin
    have ha3 : (VAt n gates g' a).card = 3 := by rw [← hV]; exact hcard
    obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a (by omega)
    have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
    rw [hVeq] at hV ha3
    exact ⟨g'', hg''lt, by rw [← hV]; exact hsub, by omega⟩
  | [a, b] =>
    rcases hop with h | h
    · have hw : ∀ x : Fin n → Bool, wval gates (n + g') x = (wvalAt gates g' a x && wvalAt gates g' b x) :=
        wval_gate_two_and (n := n) gates g' hg' a b h hin
      have hsafe' : Safe S w (fun x => wvalAt gates g' a x && wvalAt gates g' b x) := by
        intro x hx hv; exact hsafe x hx (by rw [hw]; exact hv)
      have hV := V_gate_two_and (n := n) gates g' hg' a b h hin
      have hpr := prime_weight2 w (wvalAt gates g' a) (wvalAt gates g' b)
        (wvalAt_mono (n := n) gates hmono g' a) (wvalAt_mono (n := n) gates hmono g' b) hsafe'
      rcases hpr with haL | hbL
      · have hasub : VAt n gates g' a ⊆ S w := by
          intro v hv; exact haL v ((mem_VAt (n := n) gates g' a v).mp hv)
        have hge : 3 ≤ (VAt n gates g' a).card := by
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := VAt n gates g' a) (s₂ := VAt n gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a (by omega)
        have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
        rw [hVeq] at hasub hge
        exact ⟨g'', hg''lt, hasub, by omega⟩
      · have hbsub : VAt n gates g' b ⊆ S w := by
          intro v hv; exact hbL v ((mem_VAt (n := n) gates g' b v).mp hv)
        have hge : 3 ≤ (VAt n gates g' b).card := by
          have := Finset.card_le_card (Finset.inter_subset_right (s₁ := VAt n gates g' a) (s₂ := VAt n gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' b (by omega)
        have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
        rw [hVeq] at hbsub hge
        exact ⟨g'', hg''lt, hbsub, by omega⟩
    · have hV := V_gate_two_or (n := n) gates g' hg' a b h hin
      have hsum : 3 ≤ (VAt n gates g' a).card + (VAt n gates g' b).card := by
        have := Finset.card_union_le (VAt n gates g' a) (VAt n gates g' b)
        rw [← hV, hcard] at this; exact this
      by_cases ha2 : 2 ≤ (VAt n gates g' a).card
      · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a ha2
        have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
        have hasub : V n gates (n + g'') ⊆ S w := by
          rw [← hVeq]; exact Finset.subset_union_left.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hasub, by rw [← hVeq]; exact ha2⟩
      · have hb2 : 2 ≤ (VAt n gates g' b).card := by omega
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' b hb2
        have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
        have hbsub : V n gates (n + g'') ⊆ S w := by
          rw [← hVeq]; exact Finset.subset_union_right.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hbsub, by rw [← hVeq]; exact hb2⟩
  | _ :: _ :: _ :: _ =>
    rw [hin] at hlen; simp at hlen

-- Helper: symmetric core of the AND case when VAt g i = S w and S w ⊆ VAt g j
lemma and_case_core (card_line : ∀ w : Fin m, (S w).card = 4)
    (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) (g : ℕ) (hg : g < gates.length)
    (hVg : V n gates (n + g) = S w)
    (hsafe : Safe S w (wval gates (n + g)))
    (ih : ∀ m < g, V n gates (n + m) = S w → Safe S w (wval gates (n + m)) →
      3 ≤ (GwUp S gates w m).card ∨ (2 ≤ (GwUp S gates w m).card ∧ HasTriple S gates w))
    (i j : ℕ) (hwg : ∀ x : Fin n → Bool, wval gates (n + g) x = (wvalAt gates g i x && wvalAt gates g j x))
    (hVi : VAt n gates g i = S w) (hVj_sub : S w ⊆ VAt n gates g j) :
    3 ≤ (GwUp S gates w g).card ∨ (2 ≤ (GwUp S gates w g).card ∧ HasTriple S gates w) := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  have hgw : g ∈ GwUp S gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
  have hi2 : 2 ≤ (VAt n gates g i).card := by rw [hVi, card_line]; omega
  obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g i hi2
  have hVi_eq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
  rw [hVi_eq] at hVi
  have hg'w : g' ∈ GwUp S gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [hVi], by rw [hVi, card_line]; omega⟩
  -- Case 1: VAt g j = S w
  by_cases hVj_eq : VAt n gates g j = S w
  · by_cases hji : j = n + g'
    · subst hji
      have hsafe' : Safe S w (wval gates (n + g')) := by
        intro x hx hv
        have h1 : wvalAt gates g (n + g') x = true := by
          unfold wvalAt; rw [if_pos (by omega)]; exact hv
        exact hsafe x hx (by rw [hwg]; simp [h1])
      have hih := ih g' hg'lt hVi hsafe'
      have h2' : 2 ≤ (GwUp S gates w g').card := by
        rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    · have hj2 : 2 ≤ (VAt n gates g j).card := by rw [hVj_eq, card_line]; omega
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g j hj2
      have hVj_eq2 : VAt n gates g (n + g'') = V n gates (n + g'') := if_pos (by omega)
      rw [hVj_eq2] at hVj_eq
      have hg''w : g'' ∈ GwUp S gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hVj_eq], by rw [hVj_eq, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg'w hg''w hgw (by omega) (by omega) (by omega))
  -- Case 2: S w ⊂ VAt g j
  · have hVj_ssub : S w ⊂ VAt n gates g j := Finset.ssubset_iff_subset_ne.mpr ⟨hVj_sub, fun he => hVj_eq he.symm⟩
    have hj5 : 5 ≤ (VAt n gates g j).card := by
      have := Finset.card_lt_card hVj_ssub
      rw [card_line] at this; omega
    obtain ⟨gj, hgjlt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g j (by omega)
    have hVj_eq2 : VAt n gates g (n + gj) = V n gates (n + gj) := if_pos (by omega)
    rw [hVj_eq2] at hVj_ssub
    -- Now inspect gate g' (which has V n gates (n + g') = S w)
    have hg'_len : g' < gates.length := by omega
    obtain ⟨hop', hlen'⟩ := hvalid (gates[g']) (List.getElem_mem hg'_len)
    match hin' : (gates[g']).inputs with
    | [] =>
      rcases hop' with h | h
      · have hV := V_gate_nil_and (n := n) gates g' hg'_len h hin'
        rw [hV] at hVi
        have h1 := Finset.card_lt_card hVj_ssub
        have h2 := Finset.card_le_univ (V n gates (n + gj))
        rw [← hVi, Finset.card_univ] at h1
        omega
      · have hV := V_gate_nil_or (n := n) gates g' hg'_len h hin'
        rw [hV] at hVi
        have := congrArg Finset.card hVi
        rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one (n := n) gates g' hg'_len a hop' hin'
      rw [hVi] at hV
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a (by rw [← hV, card_line]; omega)
      have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
      rw [hVeq] at hV
      have hg''w : g'' ∈ GwUp S gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [← hV], by rw [← hV, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | [a, b] =>
      rcases hop' with h | h
      · have hV := V_gate_two_and (n := n) gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have ha_sub : S w ⊆ VAt n gates g' a := by
          rw [hV]; exact Finset.inter_subset_left
        have hb_sub : S w ⊆ VAt n gates g' b := by
          rw [hV]; exact Finset.inter_subset_right
        by_cases ha_eq : VAt n gates g' a = S w
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a (by rw [ha_eq, card_line]; omega)
          have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
          rw [hVeq] at ha_eq
          have hg''w : g'' ∈ GwUp S gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, by rw [ha_eq], by rw [ha_eq, card_line]; omega⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · by_cases hb_eq : VAt n gates g' b = S w
          · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' b (by rw [hb_eq, card_line]; omega)
            have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
            rw [hVeq] at hb_eq
            have hg''w : g'' ∈ GwUp S gates w g := by
              simp only [GwUp, Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by rw [hb_eq], by rw [hb_eq, card_line]; omega⟩
            exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
          · -- Strict supersets: ga, gb, gj!
            have ha_ssub : S w ⊂ VAt n gates g' a := Finset.ssubset_iff_subset_ne.mpr ⟨ha_sub, fun he => ha_eq he.symm⟩
            have hb_ssub : S w ⊂ VAt n gates g' b := Finset.ssubset_iff_subset_ne.mpr ⟨hb_sub, fun he => hb_eq he.symm⟩
            have ha5 : 5 ≤ (VAt n gates g' a).card := by
              have := Finset.card_lt_card ha_ssub; rw [card_line] at this; omega
            have hb5 : 5 ≤ (VAt n gates g' b).card := by
              have := Finset.card_lt_card hb_ssub; rw [card_line] at this; omega
            obtain ⟨ga, hgalt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a (by omega)
            obtain ⟨gb, hgblt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' b (by omega)
            have hVa_eq : VAt n gates g' (n + ga) = V n gates (n + ga) := if_pos (by omega)
            have hVb_eq : VAt n gates g' (n + gb) = V n gates (n + gb) := if_pos (by omega)
            rw [hVa_eq] at ha_ssub
            rw [hVb_eq] at hb_ssub
            rw [hVa_eq, hVb_eq] at hV
            have hdisj_ab : Disjoint (V n gates (n + ga) \ S w) (V n gates (n + gb) \ S w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpb
              rw [Finset.mem_sdiff] at hpa hpb
              have hp_in : p ∈ V n gates (n + ga) ∩ V n gates (n + gb) := Finset.mem_inter.mpr ⟨hpa.1, hpb.1⟩
              rw [← hV] at hp_in
              exact hpa.2 hp_in
            have hwg' : ∀ x : Fin n → Bool, wval gates (n + g') x = (wval gates (n + ga) x && wval gates (n + gb) x) := by
              intro x
              rw [wval_gate_two_and (n := n) gates g' hg'_len (n + ga) (n + gb) h hin']
              unfold wvalAt
              rw [if_pos (by omega), if_pos (by omega)]
            have hdisj_aj : Disjoint (V n gates (n + ga) \ S w) (V n gates (n + gj) \ S w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpj
              rw [Finset.mem_sdiff] at hpa hpj
              obtain ⟨q, hqb, hqL⟩ := Finset.exists_of_ssubset hb_ssub
              have h1 : wval gates (n + ga) (e2 p q) = true :=
                wval_mono (n := n) gates hmono (n + ga) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V (n := n) gates (n + ga) p).mp hpa.1)
              have h2 : wval gates (n + gb) (e2 p q) = true :=
                wval_mono (n := n) gates hmono (n + gb) (e1 q) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V (n := n) gates (n + gb) q).mp hqb)
              have h3 : wval gates (n + gj) (e2 p q) = true :=
                wval_mono (n := n) gates hmono (n + gj) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V (n := n) gates (n + gj) p).mp hpj.1)
              have hval : wval gates (n + g) (e2 p q) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 p q) (e2_weightLe2 p q) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hpa.2 hvL
              · exact hqL hvL
            have hdisj_bj : Disjoint (V n gates (n + gb) \ S w) (V n gates (n + gj) \ S w) := by
              rw [Finset.disjoint_left]
              intro p hpb hpj
              rw [Finset.mem_sdiff] at hpb hpj
              obtain ⟨q, hqa, hqL⟩ := Finset.exists_of_ssubset ha_ssub
              have h1 : wval gates (n + ga) (e2 q p) = true :=
                wval_mono (n := n) gates hmono (n + ga) (e1 q) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V (n := n) gates (n + ga) q).mp hqa)
              have h2 : wval gates (n + gb) (e2 q p) = true :=
                wval_mono (n := n) gates hmono (n + gb) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V (n := n) gates (n + gb) p).mp hpb.1)
              have h3 : wval gates (n + gj) (e2 q p) = true :=
                wval_mono (n := n) gates hmono (n + gj) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V (n := n) gates (n + gj) p).mp hpj.1)
              have hval : wval gates (n + g) (e2 q p) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 q p) (e2_weightLe2 q p) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hqL hvL
              · exact hpb.2 hvL
            exact Or.inr ⟨card_ge2_of_two hg'w hgw (by omega),
              ⟨ga, gb, gj, by omega, by omega, by omega,
                ha_ssub, hb_ssub, hVj_ssub, hdisj_ab, hdisj_aj, hdisj_bj⟩⟩
      · have hV := V_gate_two_or (n := n) gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have hsum : 4 ≤ (VAt n gates g' a).card + (VAt n gates g' b).card := by
          have := Finset.card_union_le (VAt n gates g' a) (VAt n gates g' b)
          rw [← hV, card_line] at this; exact this
        by_cases ha2 : 2 ≤ (VAt n gates g' a).card
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' a ha2
          have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
          have hasub : V n gates (n + g'') ⊆ S w := by
            rw [← hVeq, hV]; exact Finset.subset_union_left
          have hg''w : g'' ∈ GwUp S gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hasub, by rw [← hVeq]; exact ha2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · have hb2 : 2 ≤ (VAt n gates g' b).card := by omega
          obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g' b hb2
          have hVeq : VAt n gates g' (n + g'') = V n gates (n + g'') := if_pos (by omega)
          have hbsub : V n gates (n + g'') ⊆ S w := by
            rw [← hVeq, hV]; exact Finset.subset_union_right
          have hg''w : g'' ∈ GwUp S gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hbsub, by rw [← hVeq]; exact hb2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin'] at hlen'; simp at hlen'

-- Main per-line structural lemma by strong induction on gate index g
lemma line_structure (card_line : ∀ w : Fin m, (S w).card = 4)
    (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) :
    ∀ g : ℕ, g < gates.length → V n gates (n + g) = S w → Safe S w (wval gates (n + g)) →
      3 ≤ (GwUp S gates w g).card ∨ (2 ≤ (GwUp S gates w g).card ∧ HasTriple S gates w) := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg hVg hsafe
    have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
    have hgw : g ∈ GwUp S gates w g := by
      simp only [GwUp, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
    obtain ⟨hop, hlen⟩ := hvalid (gates[g]) (List.getElem_mem hg)
    match hin : (gates[g]).inputs with
    | [] =>
      rcases hop with h | h
      · exact absurd hsafe (not_safe_nil_and gates g hg h hin w)
      · have hV := V_gate_nil_or (n := n) gates g hg h hin
        rw [hV] at hVg
        have := congrArg Finset.card hVg; rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one (n := n) gates g hg a hop hin
      rw [hVg] at hV
      obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g a (by rw [← hV, card_line]; omega)
      have hVeq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
      rw [hVeq] at hV
      have hsafe' : Safe S w (wval gates (n + g')) := by
        intro x hx hv
        apply hsafe x hx
        rw [wval_gate_one (n := n) gates g hg (n + g') hop hin]
        unfold wvalAt; rw [if_pos (by omega)]; exact hv
      have hih := ih g' hg'lt (by omega) hV.symm hsafe'
      have h2' : 2 ≤ (GwUp S gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    | [i, j] =>
      rcases hop with h | h
      · -- AND gate
        have hwg := wval_gate_two_and (n := n) gates g hg i j h hin
        have hsafe' : Safe S w (fun x => wvalAt gates g i x && wvalAt gates g j x) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; exact hv)
        have hV := V_gate_two_and (n := n) gates g hg i j h hin
        rw [hVg] at hV
        have hpr := prime_weight2 w (wvalAt gates g i) (wvalAt gates g j)
          (wvalAt_mono (n := n) gates hmono g i) (wvalAt_mono (n := n) gates hmono g j) hsafe'
        have ih' : ∀ m < g, V n gates (n + m) = S w → Safe S w (wval gates (n + m)) →
            3 ≤ (GwUp S gates w m).card ∨ (2 ≤ (GwUp S gates w m).card ∧ HasTriple S gates w) :=
          fun m hm => ih m hm (by omega)
        rcases hpr with hiL | hjL
        · have hisub : VAt n gates g i ⊆ S w := fun v hv => hiL v ((mem_VAt (n := n) gates g i v).mp hv)
          have hVi : VAt n gates g i = S w :=
            Finset.Subset.antisymm hisub (by rw [hV]; exact Finset.inter_subset_left)
          have hVj_sub : S w ⊆ VAt n gates g j := by rw [hV]; exact Finset.inter_subset_right
          exact and_case_core card_line gates hvalid w g hg hVg hsafe ih' i j hwg hVi hVj_sub
        · have hjsub : VAt n gates g j ⊆ S w := fun v hv => hjL v ((mem_VAt (n := n) gates g j v).mp hv)
          have hVj : VAt n gates g j = S w :=
            Finset.Subset.antisymm hjsub (by rw [hV]; exact Finset.inter_subset_right)
          have hVi_sub : S w ⊆ VAt n gates g i := by rw [hV]; exact Finset.inter_subset_left
          have hwg_comm : ∀ x : Fin n → Bool, wval gates (n + g) x = (wvalAt gates g j x && wvalAt gates g i x) := by
            intro x; rw [hwg, Bool.and_comm]
          exact and_case_core card_line gates hvalid w g hg hVg hsafe ih' j i hwg_comm hVj hVi_sub
      · -- OR gate
        have hwg := wval_gate_two_or (n := n) gates g hg i j h hin
        have hV := V_gate_two_or (n := n) gates g hg i j h hin
        rw [hVg] at hV
        have hi_sub : VAt n gates g i ⊆ S w := by rw [hV]; exact Finset.subset_union_left
        have hj_sub : VAt n gates g j ⊆ S w := by rw [hV]; exact Finset.subset_union_right
        have hsafe_i : Safe S w (wvalAt gates g i) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hsafe_j : Safe S w (wvalAt gates g j) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hci_le : (VAt n gates g i).card ≤ 4 := by
          have := Finset.card_le_card hi_sub; rw [card_line] at this; exact this
        have hcj_le : (VAt n gates g j).card ≤ 4 := by
          have := Finset.card_le_card hj_sub; rw [card_line] at this; exact this
        have hsum : 4 ≤ (VAt n gates g i).card + (VAt n gates g j).card := by
          have := Finset.card_union_le (VAt n gates g i) (VAt n gates g j)
          rw [← hV, card_line] at this; exact this
        by_cases hi4 : (VAt n gates g i).card = 4
        · have hVi : VAt n gates g i = S w :=
            Finset.eq_of_subset_of_card_le hi_sub (by rw [card_line, hi4])
          obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g i (by omega)
          have hVeq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
          rw [hVeq] at hVi
          have hsafe' : Safe S w (wval gates (n + g')) := by
            intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
          have hih := ih g' hg'lt (by omega) hVi hsafe'
          have h2' : 2 ≤ (GwUp S gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
          exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
        · by_cases hj4 : (VAt n gates g j).card = 4
          · have hVj : VAt n gates g j = S w :=
              Finset.eq_of_subset_of_card_le hj_sub (by rw [card_line, hj4])
            obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g j (by omega)
            have hVeq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
            rw [hVeq] at hVj
            have hsafe' : Safe S w (wval gates (n + g')) := by
              intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
            have hih := ih g' hg'lt (by omega) hVj hsafe'
            have h2' : 2 ≤ (GwUp S gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
            exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
          · by_cases hi3 : (VAt n gates g i).card = 3
            · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g i (by omega)
              have hVeq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
              rw [hVeq] at hi_sub hi3
              have hsafe' : Safe S w (wval gates (n + g')) := by
                intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
              obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                exists_child_of_card3 gates hvalid w g' (by omega) hi_sub hi3 hsafe'
              have hg'w : g' ∈ GwUp S gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hi_sub, by omega⟩
              have hg''w : g'' ∈ GwUp S gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hsub'', hc''⟩
              exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
            · by_cases hj3 : (VAt n gates g j).card = 3
              · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g j (by omega)
                have hVeq : VAt n gates g (n + g') = V n gates (n + g') := if_pos (by omega)
                rw [hVeq] at hj_sub hj3
                have hsafe' : Safe S w (wval gates (n + g')) := by
                  intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
                obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                  exists_child_of_card3 gates hvalid w g' (by omega) hj_sub hj3 hsafe'
                have hg'w : g' ∈ GwUp S gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                have hg''w : g'' ∈ GwUp S gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hsub'', hc''⟩
                exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
              · -- Both have card = 2!
                have hi2 : (VAt n gates g i).card = 2 := by omega
                have hj2 : (VAt n gates g j).card = 2 := by omega
                have hij_ne : i ≠ j := by
                  intro he; subst he
                  rw [Finset.union_idempotent] at hV
                  have := congrArg Finset.card hV
                  rw [card_line, hi2] at this; omega
                obtain ⟨g₁, hg₁lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g i (by omega)
                obtain ⟨g₂, hg₂lt, rfl⟩ := gate_idx_of_VAt_ge2 (n := n) gates g j (by omega)
                have hV1 : VAt n gates g (n + g₁) = V n gates (n + g₁) := if_pos (by omega)
                have hV2 : VAt n gates g (n + g₂) = V n gates (n + g₂) := if_pos (by omega)
                rw [hV1] at hi_sub hi2
                rw [hV2] at hj_sub hj2
                have hg1w : g₁ ∈ GwUp S gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hi_sub, by omega⟩
                have hg2w : g₂ ∈ GwUp S gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                exact Or.inl (card_ge3_of_three hg1w hg2w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen; simp at hlen

-- From HasTriple, either some gate has card in {5, 6}, or all three have card in [7, 9] and are distinct
-- (this is where `n ≤ 15` is used: the three excesses are disjoint inside the `n - 4 ≤ 11` points
-- off the line, so if each has at least 3 points then each has at most 5)
def B56 (n : ℕ) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => 5 ≤ (V n gates (n + j)).card ∧ (V n gates (n + j)).card ≤ 6)

def B7 (n : ℕ) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => 7 ≤ (V n gates (n + j)).card ∧ (V n gates (n + j)).card ≤ 9)

lemma card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

lemma triple_split (card_line : ∀ w : Fin m, (S w).card = 4)
    (hn : n ≤ 15) (gates : List Gate) (w : Fin m) (ht : HasTriple S gates w) :
    (∃ j ∈ B56 n gates, S w ⊆ V n gates (n + j)) ∨
    3 ≤ ((B7 n gates).filter (fun j => S w ⊆ V n gates (n + j))).card := by
  obtain ⟨ga, gb, gc, ha_lt, hb_lt, hc_lt, ha_ss, hb_ss, hc_ss, hab, hac, hbc⟩ := ht
  set Da := V n gates (n + ga) \ S w
  set Db := V n gates (n + gb) \ S w
  set Dc := V n gates (n + gc) \ S w
  have ha_sub : S w ⊆ V n gates (n + ga) := ha_ss.subset
  have hb_sub : S w ⊆ V n gates (n + gb) := hb_ss.subset
  have hc_sub : S w ⊆ V n gates (n + gc) := hc_ss.subset
  have hra_pos : 1 ≤ Da.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset ha_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrb_pos : 1 ≤ Db.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hb_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrc_pos : 1 ≤ Dc.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hc_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hca : (V n gates (n + ga)).card = 4 + Da.card := by
    have hle := Finset.card_le_card ha_sub
    have hsd : Da.card = (V n gates (n + ga)).card - (S w).card := card_sdiff_eq ha_sub
    rw [card_line] at hsd hle; omega
  have hcb : (V n gates (n + gb)).card = 4 + Db.card := by
    have hle := Finset.card_le_card hb_sub
    have hsd : Db.card = (V n gates (n + gb)).card - (S w).card := card_sdiff_eq hb_sub
    rw [card_line] at hsd hle; omega
  have hcc : (V n gates (n + gc)).card = 4 + Dc.card := by
    have hle := Finset.card_le_card hc_sub
    have hsd : Dc.card = (V n gates (n + gc)).card - (S w).card := card_sdiff_eq hc_sub
    rw [card_line] at hsd hle; omega
  have hsum : Da.card + Db.card + Dc.card ≤ n - 4 := by
    have hsub : (Da ∪ Db) ∪ Dc ⊆ Finset.univ \ S w := by
      intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with (hx | hx) | hx
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hd_ab_c : Disjoint (Da ∪ Db) Dc := Finset.disjoint_union_left.mpr ⟨hac, hbc⟩
    have hc_u : ((Da ∪ Db) ∪ Dc).card = Da.card + Db.card + Dc.card := by
      rw [Finset.card_union_of_disjoint hd_ab_c, Finset.card_union_of_disjoint hab]
    have hc_comp : (Finset.univ \ S w).card = n - 4 := by
      rw [card_sdiff_eq (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, card_line]
    have := Finset.card_le_card hsub
    omega
  by_cases ha2 : Da.card ≤ 2
  · left
    exact ⟨ga, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, by omega, by omega⟩, ha_sub⟩
  · by_cases hb2 : Db.card ≤ 2
    · left
      exact ⟨gb, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, by omega, by omega⟩, hb_sub⟩
    · by_cases hc2 : Dc.card ≤ 2
      · left
        exact ⟨gc, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, by omega, by omega⟩, hc_sub⟩
      · right
        have ha7 : 7 ≤ (V n gates (n + ga)).card ∧ (V n gates (n + ga)).card ≤ 9 := ⟨by omega, by omega⟩
        have hb7 : 7 ≤ (V n gates (n + gb)).card ∧ (V n gates (n + gb)).card ≤ 9 := ⟨by omega, by omega⟩
        have hc7 : 7 ≤ (V n gates (n + gc)).card ∧ (V n gates (n + gc)).card ≤ 9 := ⟨by omega, by omega⟩
        have hne_ab : ga ≠ gb := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hab hp (by simpa [Da, Db, he] using hp)
        have hne_ac : ga ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hac hp (by simpa [Da, Dc, he] using hp)
        have hne_bc : gb ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hrb_pos
          exact Finset.disjoint_left.mp hbc hp (by simpa [Db, Dc, he] using hp)
        have hma : ga ∈ (B7 n gates).filter (fun j => S w ⊆ V n gates (n + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha7⟩, ha_sub⟩
        have hmb : gb ∈ (B7 n gates).filter (fun j => S w ⊆ V n gates (n + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, hb7⟩, hb_sub⟩
        have hmc : gc ∈ (B7 n gates).filter (fun j => S w ⊆ V n gates (n + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, hc7⟩, hc_sub⟩
        exact card_ge3_of_three hma hmb hmc hne_ab hne_ac hne_bc

theorem main_lb (card_line : ∀ w : Fin m, (S w).card = 4)
    (card_inter_line : ∀ w₁ w₂ : Fin m, w₁ ≠ w₂ → (S w₁ ∩ S w₂).card ≤ 1)
    (hn : n ≤ 15) (gates : List Gate) (out : Fin m → ℕ)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ (w : Fin m) (x : Fin n → Bool), WeightLe2 x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    3 * m ≤ gates.length := by
  -- Step 1: Every S w satisfies either 3 ≤ (Gw w).card or (2 ≤ (Gw w).card ∧ HasTriple w)
  have hline : ∀ w : Fin m,
      3 ≤ (Gw S gates w).card ∨ (2 ≤ (Gw S gates w).card ∧ HasTriple S gates w) := by
    intro w
    have hVout : V n gates (out w) = S w := by
      ext v
      rw [mem_V]
      have hc := hcomp w (e1 v) (e1_weightLe2 v)
      change wval gates (out w) (e1 v) = decide (∃ u ∈ S w, e1 v u = true) at hc
      rw [hc, decide_eq_true_eq]
      constructor
      · rintro ⟨u, huL, hu⟩
        simp only [e1, decide_eq_true_eq] at hu
        rwa [← hu]
      · intro hvL
        exact ⟨v, hvL, by simp [e1]⟩
    have hsafe_out : Safe S w (wval gates (out w)) := by
      intro x hx hv
      have hc := hcomp w x hx
      change wval gates (out w) x = decide (∃ u ∈ S w, x u = true) at hc
      rw [hc, decide_eq_true_eq] at hv
      exact hv
    obtain ⟨g, hglt, hgo⟩ := gate_idx_of_V_ge2 (n := n) gates (out w) (by rw [hVout, card_line]; omega)
    rw [hgo] at hVout hsafe_out
    have hsub := Finset.card_le_card (GwUp_subset_Gw (S := S) gates w g hglt)
    rcases line_structure card_line gates hvalid w g hglt hVout hsafe_out with h3 | ⟨h2, ht⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, ht⟩
  -- Step 2: Gw w (across all w), B56, B7 are pairwise disjoint subsets of range gates.length
  have hGw_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin m)) (Gw S gates) := by
    intro w₁ _ w₂ _ hne
    change Disjoint (Gw S gates w₁) (Gw S gates w₂)
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Gw, Finset.mem_filter] at hj₁ hj₂
    exact hne (line_eq_of_subset_two card_inter_line hj₁.2.1 hj₂.2.1 hj₁.2.2)
  set U := Finset.univ.biUnion (Gw S gates)
  have hU_card : U.card = ∑ w : Fin m, (Gw S gates w).card :=
    Finset.card_biUnion (fun w₁ _ w₂ _ hne => hGw_disj (Finset.mem_univ w₁) (Finset.mem_univ w₂) hne)
  have hU_disj_56 : Disjoint U (B56 n gates) := by
    rw [Finset.disjoint_left]
    intro j hjU hj56
    obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
    simp only [Gw, B56, Finset.mem_filter] at hjw hj56
    have hle := Finset.card_le_card hjw.2.1
    rw [card_line] at hle
    omega
  have hU_disj_7 : Disjoint U (B7 n gates) := by
    rw [Finset.disjoint_left]
    intro j hjU hj7
    obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
    simp only [Gw, B7, Finset.mem_filter] at hjw hj7
    have hle := Finset.card_le_card hjw.2.1
    rw [card_line] at hle
    omega
  have h56_disj_7 : Disjoint (B56 n gates) (B7 n gates) := by
    rw [Finset.disjoint_left]
    intro j hj56 hj7
    simp only [B56, B7, Finset.mem_filter] at hj56 hj7
    omega
  have htot_sub : (U ∪ B56 n gates) ∪ B7 n gates ⊆ Finset.range gates.length := by
    intro j hj
    simp only [Finset.mem_union] at hj
    rcases hj with (hjU | hj56) | hj7
    · obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
      exact (Finset.mem_filter.mp hjw).1
    · exact (Finset.mem_filter.mp hj56).1
    · exact (Finset.mem_filter.mp hj7).1
  have htot_le : (∑ w : Fin m, (Gw S gates w).card) + (B56 n gates).card + (B7 n gates).card ≤ gates.length := by
    have hc := Finset.card_le_card htot_sub
    rw [Finset.card_range] at hc
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hU_disj_7, h56_disj_7⟩),
        Finset.card_union_of_disjoint hU_disj_56, hU_card] at hc
    exact hc
  -- Step 3: Partition Fin n into W3, W56, W7
  set W3 := Finset.univ.filter (fun w : Fin m => 3 ≤ (Gw S gates w).card)
  set Wrem := Finset.univ \ W3
  set W56 := Wrem.filter (fun w : Fin m => ∃ j ∈ B56 n gates, S w ⊆ V n gates (n + j))
  set W7 := Wrem \ W56
  have hW56_sub : W56 ⊆ Wrem := Finset.filter_subset _ Wrem
  have h1_part : W56.card + W7.card = Wrem.card := by
    have hsd : W7.card = Wrem.card - W56.card := card_sdiff_eq hW56_sub
    have hle : W56.card ≤ Wrem.card := Finset.card_le_card hW56_sub
    omega
  have hpart : W3.card + W56.card + W7.card = m := by
    have hsd : Wrem.card = (Finset.univ : Finset (Fin m)).card - W3.card := card_sdiff_eq (Finset.subset_univ W3)
    have hle : W3.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ W3)
    rw [Finset.card_univ, Fintype.card_fin] at hsd hle
    omega
  -- Sum of |Gw w| >= 26 + W3.card = 3 * W3.card + 2 * W56.card + 2 * W7.card
  have hGw_sum : 3 * W3.card + 2 * W56.card + 2 * W7.card ≤ ∑ w : Fin m, (Gw S gates w).card := by
    have hge : ∀ w : Fin m, (if w ∈ W3 then 3 else 2) ≤ (Gw S gates w).card := by
      intro w
      split_ifs with hw
      · exact (Finset.mem_filter.mp hw).2
      · rcases hline w with h3 | ⟨h2, _⟩
        · omega
        · exact h2
    have hsum_le := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hge w)
    have hlhs : ∑ w : Fin m, (if w ∈ W3 then (3 : ℕ) else 2) = 3 * W3.card + 2 * Wrem.card := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      have hf1 : (Finset.univ.filter (fun w : Fin m => w ∈ W3)) = W3 := by
        ext x; simp
      have hf2 : (Finset.univ.filter (fun w : Fin m => w ∉ W3)) = Wrem := by
        ext x; simp [Wrem]
      rw [hf1, hf2]; ring
    omega
  -- Step 4: W56.card <= (B56 n gates).card via injection
  have hW56_le : W56.card ≤ (B56 n gates).card := by
    have hex : ∀ w ∈ W56, ∃ j ∈ B56 n gates, S w ⊆ V n gates (n + j) :=
      fun w hw => (Finset.mem_filter.mp hw).2
    choose f hf_mem hf_sub using hex
    have hinj : Set.InjOn (fun w => if hw : w ∈ W56 then f w hw else 0) W56 := by
      intro w₁ hw₁ w₂ hw₂ heq
      have hw₁' : w₁ ∈ W56 := Finset.mem_coe.mp hw₁
      have hw₂' : w₂ ∈ W56 := Finset.mem_coe.mp hw₂
      have hf_eq : f w₁ hw₁' = f w₂ hw₂' := by simpa [hw₁', hw₂'] using heq
      have h1 := hf_sub w₁ hw₁'
      have h2 := hf_sub w₂ hw₂'
      rw [← hf_eq] at h2
      have hc6 : (V n gates (n + f w₁ hw₁')).card ≤ 6 := (Finset.mem_filter.mp (hf_mem w₁ hw₁')).2.2
      exact line_eq_of_superset_le6 card_line card_inter_line h1 h2 hc6
    have hmap : ∀ w ∈ W56, (if hw : w ∈ W56 then f w hw else 0) ∈ B56 n gates := by
      intro w hw; simp [hw, hf_mem w hw]
    exact Finset.card_le_card_of_injOn _ hmap hinj
  -- Step 5: 3 * W7.card <= 3 * (B7 n gates).card via bipartite double counting
  have hW7_le : 3 * W7.card ≤ 3 * (B7 n gates).card := by
    set E := (W7 ×ˢ B7 n gates).filter (fun p => S p.1 ⊆ V n gates (n + p.2))
    have hleft : 3 * W7.card ≤ E.card := by
      have heq : E.card = ∑ w ∈ W7, ((B7 n gates).filter (fun j => S w ⊆ V n gates (n + j))).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.card_filter]
      rw [heq]
      have hge3 : ∀ w ∈ W7, 3 ≤ ((B7 n gates).filter (fun j => S w ⊆ V n gates (n + j))).card := by
        intro w hw
        have hwrem : w ∈ Wrem := (Finset.mem_sdiff.mp hw).1
        have hnot3 : ¬ (3 ≤ (Gw S gates w).card) := by
          intro h3
          exact (Finset.mem_sdiff.mp hwrem).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h3⟩)
        have hnot56 : ¬ (∃ j ∈ B56 n gates, S w ⊆ V n gates (n + j)) := by
          intro h56
          exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mpr ⟨hwrem, h56⟩)
        rcases hline w with h3 | ⟨_, ht⟩
        · exact absurd h3 hnot3
        · rcases triple_split card_line hn gates w ht with h56 | h3b
          · exact absurd h56 hnot56
          · exact h3b
      calc 3 * W7.card = ∑ _w ∈ W7, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ W7, ((B7 n gates).filter (fun j => S w ⊆ V n gates (n + j))).card :=
          Finset.sum_le_sum hge3
    have hright : E.card ≤ 3 * (B7 n gates).card := by
      have heq : E.card = ∑ j ∈ B7 n gates, (W7.filter (fun w => S w ⊆ V n gates (n + j))).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.card_filter]
      rw [heq]
      have hle2 : ∀ j ∈ B7 n gates, (W7.filter (fun w => S w ⊆ V n gates (n + j))).card ≤ 3 := by
        intro j hj
        have hc7 : (V n gates (n + j)).card ≤ 9 := (Finset.mem_filter.mp hj).2.2
        have hsub : W7.filter (fun w => S w ⊆ V n gates (n + j)) ⊆
            Finset.univ.filter (fun w : Fin m => S w ⊆ V n gates (n + j)) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, (Finset.mem_filter.mp hw).2⟩
        exact (Finset.card_le_card hsub).trans (lines_in_card_le9_le3 card_line card_inter_line _ hc7)
      calc ∑ j ∈ B7 n gates, (W7.filter (fun w => S w ⊆ V n gates (n + j))).card
          ≤ ∑ _j ∈ B7 n gates, 3 := Finset.sum_le_sum hle2
        _ = 3 * (B7 n gates).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  omega


end Plane


/-- **Main theorem.** For a linear 4-uniform family `S` of `m` lines on `n ≤ 15` points, any
AND/OR circuit of fan-in at most two whose outputs compute the OR over each line on all inputs of
weight at most two has at least `3 * m` gates. -/
theorem linear_four_lb {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ w, (S w).card = 4)
    (hlin : ∀ w₁ w₂, w₁ ≠ w₂ → (S w₁ ∩ S w₂).card ≤ 1)
    (hn : n ≤ 15)
    (gates : List Gate) (out : Fin m → ℕ)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ (w : Fin m) (x : Fin n → Bool),
      (∀ i j k : Fin n, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    3 * m ≤ gates.length :=
  main_lb hcard hlin hn gates out hvalid hcomp

/-- The projective plane of order three: the lines `{0, 1, 3, 9} + w` on `Fin 13`. -/
def pg23Line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

/-- The original instance `PEqualNP.Outside.L_meta_667`, re-derived from `linear_four_lb`. -/
theorem pg23_lb (gates : List Gate) (out : Fin 13 → ℕ)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) :
    39 ≤ gates.length :=
  linear_four_lb pg23Line (by decide) (by decide) (by norm_num) gates out hvalid hcomp

end PEqualNP.MetaComplexity.LinearFour
