import PEqualNP.Defs
import PEqualNP.Outside.L_meta_174
import PEqualNP.Outside.L_meta_716

/-!
# XOR with a fresh variable costs at least three gates more than both `f` and `¬f`

Circuits: AND, OR, NOT of fan-in at most two, every gate counted (`HasCircuitSize`).
For a non-constant `f` on `n` inputs and a fresh input `x`:

* `xor_lower`: a circuit with `s + 3` gates for `x ⊕ f` gives circuits with `s` gates for `f`
  AND for `¬f`. In words: `C(x ⊕ f) ≥ max (C f) (C ¬f) + 3`.
* `xor_exact`: if the sizes of `f` and `¬f` differ, then `C(x ⊕ f) = min (C f) (C ¬f) + 4`
  exactly (the upper bound is `L_meta_716`).

The proof counts, for each constant `c`, the gates that are redundant once `x := c`: a gate whose
restricted function is constant or equals the restricted function of an earlier wire. No
minimality of the circuit is used.
-/

namespace PEqualNP.General.XorExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_174

/-! ## Wires -/

lemma wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w = wiresFrom gs w ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  rw [wiresFrom_append]; rfl

/-- The value of wire `i` on the input `y`, with the last input set to `c`. -/
def val (n : ℕ) (gs : List Gate) (c : Bool) (i : ℕ) (y : Fin n → Bool) : Bool :=
  (wiresFrom gs (List.ofFn y ++ [c])).getD i false

lemma val_append_lt (n : ℕ) (gs gs' : List Gate) (c : Bool) (i : ℕ) (y : Fin n → Bool)
    (hi : i < n + 1 + gs.length) : val n (gs ++ gs') c i y = val n gs c i y := by
  unfold val
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simp [length_wiresFrom]; omega)]

lemma val_ge (n : ℕ) (gs : List Gate) (c : Bool) (i : ℕ) (y : Fin n → Bool)
    (hi : n + 1 + gs.length ≤ i) : val n gs c i y = false := by
  unfold val
  exact List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)

lemma val_lt (n : ℕ) (gs : List Gate) (c : Bool) (i : ℕ) (y : Fin n → Bool) (hi : i < n) :
    val n gs c i y = (List.ofFn y).getD i false := by
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using hi)]

lemma val_n (n : ℕ) (gs : List Gate) (c : Bool) (y : Fin n → Bool) : val n gs c n y = c := by
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  exact getD_snoc_len _ _ _ _ (by simp)

lemma val_snoc_eq (n : ℕ) (gs : List Gate) (g : Gate) (c : Bool) (y : Fin n → Bool) :
    val n (gs ++ [g]) c (n + 1 + gs.length) y =
      g.op.eval (g.inputs.map fun i => val n gs c i y) := by
  unfold val
  rw [wiresFrom_snoc]
  exact getD_snoc_len _ _ _ _ (by simp [length_wiresFrom])

/-- A default gate, read where a list of gates has no gate. -/
def dG : Gate := ⟨GateOp.and, []⟩

lemma val_gate (n : ℕ) (gs : List Gate) (c : Bool) (j : ℕ) (y : Fin n → Bool)
    (hj : j < gs.length) :
    val n gs c (n + 1 + j) y = (gs.getD j dG).op.eval ((gs.getD j dG).inputs.map fun i =>
      if i < n + 1 + j then val n gs c i y else false) := by
  have hl : (gs.take j).length = j := by simp; omega
  have hsplit : gs = (gs.take j ++ [gs.getD j dG]) ++ gs.drop (j + 1) := by
    rw [List.getD_eq_getElem _ _ hj]; simp
  have h1 : val n gs c (n + 1 + j) y = val n (gs.take j ++ [gs.getD j dG]) c (n + 1 + j) y := by
    conv_lhs => rw [hsplit]
    exact val_append_lt n _ _ c _ y (by simp; omega)
  have h2 := val_snoc_eq n (gs.take j) (gs.getD j dG) c y
  rw [hl] at h2
  rw [h1, h2]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + 1 + j
  · simp only [hi, ite_true]
    conv_rhs => rw [← List.take_append_drop j gs]
    exact (val_append_lt n _ _ c i y (by rw [hl]; exact hi)).symm
  · simp only [hi, ite_false]
    exact val_ge n _ c i y (by rw [hl]; omega)

lemma nok_getD (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (j : ℕ) : NOk (gs.getD j dG) := by
  by_cases hj : j < gs.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hnok _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨⟨Or.inl rfl, by simp [dG]⟩, by simp [dG]⟩

/-! ## The shape of one gate -/

lemma gate_cases (g : Gate) (h : NOk g) :
    (∃ b : Bool, ∀ a : ℕ → Bool, g.op.eval (g.inputs.map a) = b) ∨
    (∃ i, g.inputs = [i] ∧ ((∀ a : ℕ → Bool, g.op.eval (g.inputs.map a) = a i) ∨
        (∀ a : ℕ → Bool, g.op.eval (g.inputs.map a) = !a i))) ∨
    (∃ i k, g.inputs = [i, k] ∧
      ((∀ a : ℕ → Bool, g.op.eval (g.inputs.map a) = (a i && a k)) ∨
        (∀ a : ℕ → Bool, g.op.eval (g.inputs.map a) = (a i || a k)))) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨⟨hop, hlen⟩, hnot⟩ := h
  simp only at hop hlen hnot
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    rcases inputs with _ | ⟨i, _ | ⟨k, _ | ⟨l, r⟩⟩⟩
    · exact Or.inl ⟨true, fun a => by simp [GateOp.eval]⟩
    · exact Or.inr (Or.inl ⟨i, rfl, Or.inl fun a => by simp [GateOp.eval]⟩)
    · exact Or.inr (Or.inr ⟨i, k, rfl, Or.inl fun a => by simp [GateOp.eval]⟩)
    · simp at hlen
  · have : op = GateOp.or := h
    subst this
    rcases inputs with _ | ⟨i, _ | ⟨k, _ | ⟨l, r⟩⟩⟩
    · exact Or.inl ⟨false, fun a => by simp [GateOp.eval]⟩
    · exact Or.inr (Or.inl ⟨i, rfl, Or.inl fun a => by simp [GateOp.eval]⟩)
    · exact Or.inr (Or.inr ⟨i, k, rfl, Or.inr fun a => by simp [GateOp.eval]⟩)
    · simp at hlen
  · have : op = GateOp.not := h
    subst this
    rcases inputs with _ | ⟨i, _ | ⟨k, r⟩⟩
    · exact Or.inl ⟨true, fun a => by simp [GateOp.eval]⟩
    · exact Or.inr (Or.inl ⟨i, rfl, Or.inr fun a => by simp [GateOp.eval]⟩)
    · simp at hnot

/-- A gate with an input that is constant (over a family of inputs) is constant or copies one of
its inputs. -/
lemma gate_const_input (g : Gate) (h : NOk g) {ι : Type} (a : ℕ → ι → Bool) (i : ℕ)
    (hi : i ∈ g.inputs) (b : Bool) (hb : ∀ y, a i y = b) :
    (∃ b' : Bool, ∀ y, g.op.eval (g.inputs.map fun k => a k y) = b') ∨
    (∃ k ∈ g.inputs, ∀ y, g.op.eval (g.inputs.map fun k => a k y) = a k y) := by
  rcases gate_cases g h with ⟨b', hb'⟩ | ⟨i', hin, hc | hc⟩ | ⟨i', k', hin, hc | hc⟩
  · exact Or.inl ⟨b', fun y => hb' _⟩
  · rw [hin] at hi
    obtain rfl : i = i' := by simpa using hi
    exact Or.inl ⟨b, fun y => (hc _).trans (hb y)⟩
  · rw [hin] at hi
    obtain rfl : i = i' := by simpa using hi
    exact Or.inl ⟨!b, fun y => (hc _).trans (by rw [hb y])⟩
  · have hik : i = i' ∨ i = k' := by rw [hin] at hi; simpa using hi
    rcases hik with rfl | rfl
    · cases b
      · exact Or.inl ⟨false, fun y => (hc _).trans (by simp [hb y])⟩
      · exact Or.inr ⟨k', by simp [hin], fun y => (hc _).trans (by simp [hb y])⟩
    · cases b
      · exact Or.inl ⟨false, fun y => (hc _).trans (by simp [hb y])⟩
      · exact Or.inr ⟨i', by simp [hin], fun y => (hc _).trans (by simp [hb y])⟩
  · have hik : i = i' ∨ i = k' := by rw [hin] at hi; simpa using hi
    rcases hik with rfl | rfl
    · cases b
      · exact Or.inr ⟨k', by simp [hin], fun y => (hc _).trans (by simp [hb y])⟩
      · exact Or.inl ⟨true, fun y => (hc _).trans (by simp [hb y])⟩
    · cases b
      · exact Or.inr ⟨i', by simp [hin], fun y => (hc _).trans (by simp [hb y])⟩
      · exact Or.inl ⟨true, fun y => (hc _).trans (by simp [hb y])⟩

/-! ## Semantic elimination

Fix the last input to `c` and rebuild the circuit on the other `n` inputs. A gate is dropped
when its restricted function is constant or is already the function of a wire of the new
circuit. -/

/-- The function a status denotes on the new circuit `gs'`. -/
def sval (n : ℕ) (gs' : List Gate) (s : Stat) (y : Fin n → Bool) : Bool :=
  Stat.val (wiresFrom gs' (List.ofFn y)) s

/-- The wire a status names (`0` for a constant; never used for one). -/
def sidx : Stat → ℕ
  | Sum.inr k => k
  | Sum.inl _ => 0

open Classical in
/-- One step: process the gate `g`. -/
noncomputable def step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    List Stat × List Gate :=
  if h : ∃ b : Bool, ∀ y : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => sval n acc.2 (acc.1.getD i (Sum.inl false)) y) = b then
    (acc.1 ++ [Sum.inl (Classical.choose h)], acc.2)
  else if h' : ∃ k, k < n + acc.2.length ∧ ∀ y : Fin n → Bool,
      (wiresFrom acc.2 (List.ofFn y)).getD k false =
        g.op.eval (g.inputs.map fun i => sval n acc.2 (acc.1.getD i (Sum.inl false)) y) then
    (acc.1 ++ [Sum.inr (Classical.choose h')], acc.2)
  else
    (acc.1 ++ [Sum.inr (n + acc.2.length)],
      acc.2 ++ [⟨g.op, g.inputs.map fun i => sidx (acc.1.getD i (Sum.inl false))⟩])

/-- The whole elimination. -/
noncomputable def sem (n : ℕ) (c : Bool) (gs : List Gate) : List Stat × List Gate :=
  gs.foldl (step n) (initStats n c, [])

lemma sem_snoc (n : ℕ) (c : Bool) (gs : List Gate) (g : Gate) :
    sem n c (gs ++ [g]) = step n (sem n c gs) g := by
  simp [sem, List.foldl_append]

/-- The invariant: every old wire has a status, valid in the new circuit, with the same value. -/
def SInv (n : ℕ) (c : Bool) (gs : List Gate) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = n + 1 + gs.length ∧ (∀ g ∈ acc.2, Ok g) ∧
  ∀ i : ℕ, Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    ∀ y : Fin n → Bool, sval n acc.2 (acc.1.getD i (Sum.inl false)) y = val n gs c i y

lemma sinv_init (n : ℕ) (c : Bool) : SInv n c [] (initStats n c, []) := by
  refine ⟨by simp [initStats], by simp, fun i => ⟨?_, fun y => ?_⟩⟩
  · exact ((inv_init n c (fun _ => false)).2 i).1
  · exact ((inv_init n c y).2 i).2

lemma sinv_extend (n : ℕ) (c : Bool) (gs : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hinv : SInv n c gs acc) (s : Stat) (extra : List Gate) (hok : ∀ g' ∈ extra, Ok g')
    (hvalid : Stat.Valid (n + (acc.2 ++ extra).length) s)
    (hval : ∀ y : Fin n → Bool, sval n (acc.2 ++ extra) s y =
      val n (gs ++ [g]) c (n + 1 + gs.length) y) :
    SInv n c (gs ++ [g]) (acc.1 ++ [s], acc.2 ++ extra) := by
  obtain ⟨hl, hok0, hi⟩ := hinv
  refine ⟨by simp [hl]; omega, ?_, fun i => ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok0 g' h
    · exact hok g' h
  · show Stat.Valid (n + (acc.2 ++ extra).length) ((acc.1 ++ [s]).getD i (Sum.inl false)) ∧
      ∀ y : Fin n → Bool, sval n (acc.2 ++ extra) ((acc.1 ++ [s]).getD i (Sum.inl false)) y =
        val n (gs ++ [g]) c i y
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl]
      exact ⟨hvalid, hval⟩
    · rw [getD_snoc_ne _ _ _ _ hil]
      refine ⟨Stat.valid_mono (by simp) _ (hi i).1, fun y => ?_⟩
      have hv : sval n (acc.2 ++ extra) (acc.1.getD i (Sum.inl false)) y =
          sval n acc.2 (acc.1.getD i (Sum.inl false)) y := by
        unfold sval
        obtain ⟨t, ht, -⟩ := wiresFrom_prefix extra (wiresFrom acc.2 (List.ofFn y))
        rw [wiresFrom_append, ht]
        exact Stat.val_append _ _ _ (by rw [length_wiresFrom]; simpa using (hi i).1)
      rw [hv, (hi i).2 y]
      by_cases hlt : i < n + 1 + gs.length
      · exact (val_append_lt n gs [g] c i y hlt).symm
      · rw [val_ge n gs c i y (by omega), val_ge n (gs ++ [g]) c i y (by simp; omega)]

/-- The function of the gate about to be processed is the value of the new old-wire. -/
lemma step_fun (n : ℕ) (c : Bool) (gs : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hinv : SInv n c gs acc) (y : Fin n → Bool) :
    g.op.eval (g.inputs.map fun i => sval n acc.2 (acc.1.getD i (Sum.inl false)) y) =
      val n (gs ++ [g]) c (n + 1 + gs.length) y := by
  rw [val_snoc_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (hinv.2.2 i).2 y

lemma sinv_step (n : ℕ) (c : Bool) (gs : List Gate) (g : Gate) (hg : NOk g)
    (acc : List Stat × List Gate) (hinv : SInv n c gs acc) :
    SInv n c (gs ++ [g]) (step n acc g) := by
  classical
  have hf := step_fun n c gs g acc hinv
  unfold step
  split_ifs with h h'
  · have := sinv_extend n c gs g acc hinv (Sum.inl (Classical.choose h)) [] (by simp) trivial
      (fun y => by
        rw [← hf y, Classical.choose_spec h y]; rfl)
    simpa using this
  · have := sinv_extend n c gs g acc hinv (Sum.inr (Classical.choose h')) [] (by simp)
      (by simpa [Stat.Valid] using (Classical.choose_spec h').1)
      (fun y => by
        rw [← hf y, ← (Classical.choose_spec h').2 y, List.append_nil]; rfl)
    simpa using this
  · -- the gate is kept: every input status is a wire
    have hwire : ∀ i ∈ g.inputs, ∃ k, acc.1.getD i (Sum.inl false) = Sum.inr k := by
      intro i hi
      cases hst : acc.1.getD i (Sum.inl false) with
      | inr k => exact ⟨k, rfl⟩
      | inl b =>
        exfalso
        rcases gate_const_input g hg
          (fun k y => sval n acc.2 (acc.1.getD k (Sum.inl false)) y) i hi b
          (fun y => by
            show sval n acc.2 (acc.1.getD i (Sum.inl false)) y = b
            rw [hst]; rfl) with ⟨b', hb'⟩ | ⟨k, _, hk⟩
        · exact h ⟨b', hb'⟩
        · cases hsk : acc.1.getD k (Sum.inl false) with
          | inl b' => exact h ⟨b', fun y => by rw [hk y, hsk]; rfl⟩
          | inr k' =>
            apply h'
            refine ⟨k', ?_, fun y => ?_⟩
            · have := (hinv.2.2 k).1
              rw [hsk] at this
              exact this
            · rw [hk y, hsk]; rfl
    apply sinv_extend n c gs g acc hinv (Sum.inr (n + acc.2.length))
      [⟨g.op, g.inputs.map fun i => sidx (acc.1.getD i (Sum.inl false))⟩]
    · intro g' hg'
      obtain rfl := List.mem_singleton.1 hg'
      exact ⟨hg.1.1, by simpa using hg.1.2⟩
    · simp [Stat.Valid]
    · intro y
      rw [← hf y]
      unfold sval
      rw [wiresFrom_snoc]
      show (wiresFrom acc.2 (List.ofFn y) ++ [_]).getD (n + acc.2.length) false = _
      rw [getD_snoc_len _ _ _ _ (by simp [length_wiresFrom])]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨k, hk⟩ := hwire i hi
      simp only [Function.comp_apply, hk]
      rfl

/-- A gate that is redundant on side `c`: constant, or equal to an earlier wire. -/
def Red (n : ℕ) (gs : List Gate) (c : Bool) (j : ℕ) : Prop :=
  (∃ b : Bool, ∀ y : Fin n → Bool, val n gs c (n + 1 + j) y = b) ∨
    ∃ i, i < n + 1 + j ∧ ∀ y : Fin n → Bool, val n gs c i y = val n gs c (n + 1 + j) y

lemma red_snoc (n : ℕ) (gs : List Gate) (g : Gate) (c : Bool) (j : ℕ) (hj : j < gs.length) :
    Red n (gs ++ [g]) c j ↔ Red n gs c j := by
  have e : ∀ i, i ≤ n + 1 + j → ∀ y : Fin n → Bool, val n (gs ++ [g]) c i y = val n gs c i y :=
    fun i hi y => val_append_lt n gs [g] c i y (by omega)
  constructor
  · rintro (⟨b, hb⟩ | ⟨i, hi, he⟩)
    · exact Or.inl ⟨b, fun y => by rw [← e _ le_rfl y]; exact hb y⟩
    · exact Or.inr ⟨i, hi, fun y => by rw [← e _ le_rfl y, ← e i (by omega) y]; exact he y⟩
  · rintro (⟨b, hb⟩ | ⟨i, hi, he⟩)
    · exact Or.inl ⟨b, fun y => by rw [e _ le_rfl y]; exact hb y⟩
    · exact Or.inr ⟨i, hi, fun y => by rw [e _ le_rfl y, e i (by omega) y]; exact he y⟩

lemma step_len_le (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    (step n acc g).2.length ≤ acc.2.length + 1 := by
  classical
  unfold step
  split_ifs <;> simp

lemma step_red (n : ℕ) (c : Bool) (gs : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hinv : SInv n c gs acc) (hred : Red n (gs ++ [g]) c gs.length) :
    (step n acc g).2 = acc.2 := by
  classical
  have hf := step_fun n c gs g acc hinv
  unfold step
  split_ifs with h h'
  · rfl
  · rfl
  · exfalso
    rcases hred with ⟨b, hb⟩ | ⟨i, hi, he⟩
    · exact h ⟨b, fun y => by rw [hf y]; exact hb y⟩
    · have hvi : ∀ y : Fin n → Bool, sval n acc.2 (acc.1.getD i (Sum.inl false)) y =
          g.op.eval (g.inputs.map fun i => sval n acc.2 (acc.1.getD i (Sum.inl false)) y) := by
        intro y
        rw [hf y, ← he y, val_append_lt n gs [g] c i y hi]
        exact (hinv.2.2 i).2 y
      cases hsi : acc.1.getD i (Sum.inl false) with
      | inl b => exact h ⟨b, fun y => by rw [← hvi y, hsi]; rfl⟩
      | inr k =>
        apply h'
        refine ⟨k, ?_, fun y => ?_⟩
        · have := (hinv.2.2 i).1
          rw [hsi] at this
          exact this
        · rw [← hvi y, hsi]; rfl

lemma sem_main (n : ℕ) (c : Bool) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) :
    SInv n c gs (sem n c gs) ∧ ∀ S : Finset ℕ, (∀ j ∈ S, j < gs.length ∧ Red n gs c j) →
      (sem n c gs).2.length + S.card ≤ gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨sinv_init n c, fun S hS => ?_⟩
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by simpa using (hS j hj).1
    subst this
    simp [sem]
  | append_singleton gs g ih =>
    obtain ⟨hinv, hcount⟩ := ih (fun g' hg' => hnok g' (List.mem_append_left _ hg'))
    have hg : NOk g := hnok g (by simp)
    refine ⟨by rw [sem_snoc]; exact sinv_step n c gs g hg _ hinv, fun S hS => ?_⟩
    rw [sem_snoc]
    have hS' : ∀ j ∈ S.erase gs.length, j < gs.length ∧ Red n gs c j := by
      intro j hj
      obtain ⟨hne, hjS⟩ := Finset.mem_erase.1 hj
      have hlt : j < gs.length := by
        have := (hS j hjS).1
        simp at this
        omega
      exact ⟨hlt, (red_snoc n gs g c j hlt).1 (hS j hjS).2⟩
    have hc := hcount _ hS'
    by_cases hm : gs.length ∈ S
    · have h1 := step_red n c gs g _ hinv (hS _ hm).2
      have h2 := Finset.card_erase_add_one hm
      rw [h1]
      simp only [List.length_append, List.length_singleton]
      omega
    · have h1 := step_len_le n (sem n c gs) g
      rw [Finset.erase_eq_of_notMem hm] at hc
      simp only [List.length_append, List.length_singleton]
      omega

/-- Semantic elimination: every set of redundant gates is saved. -/
lemma se (n : ℕ) (c : Bool) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (out : ℕ)
    (hnc : ¬ ∃ b : Bool, ∀ y : Fin n → Bool, val n gs c out y = b)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < gs.length ∧ Red n gs c j) :
    ∃ C : Circuit, FanInTwo C ∧ C.size + S.card ≤ gs.length ∧
      ∀ y : Fin n → Bool, C.eval (List.ofFn y) = val n gs c out y := by
  obtain ⟨hinv, hcount⟩ := sem_main n c gs hnok
  cases hst : (sem n c gs).1.getD out (Sum.inl false) with
  | inl b =>
    exfalso
    apply hnc
    refine ⟨b, fun y => ?_⟩
    rw [← (hinv.2.2 out).2 y, hst]; rfl
  | inr k =>
    refine ⟨⟨(sem n c gs).2, k⟩, hinv.2.1, hcount S hS, fun y => ?_⟩
    rw [← (hinv.2.2 out).2 y, hst]; rfl

/-! ## Facts about one gate inside the circuit -/

/-- Wire `i` is constant on side `c`. -/
abbrev K (n : ℕ) (gs : List Gate) (c : Bool) (i : ℕ) : Prop :=
  ∃ b : Bool, ∀ y : Fin n → Bool, val n gs c i y = b

/-- Wire `i` takes different values on the two sides, at `y`. -/
abbrev Split (n : ℕ) (gs : List Gate) (i : ℕ) (y : Fin n → Bool) : Prop :=
  val n gs false i y ≠ val n gs true i y

/-- Gate `j` reads the (existing, earlier) wire `i`. -/
def reads (n : ℕ) (gs : List Gate) (j i : ℕ) : Prop :=
  i ∈ (gs.getD j dG).inputs ∧ i < n + 1 + j

lemma ne_not {a b : Bool} (h : a ≠ b) : b = !a := by cases a <;> cases b <;> simp_all

lemma kboth {n : ℕ} {gs : List Gate} {i : ℕ} (hs : ∀ y : Fin n → Bool, Split n gs i y) {c : Bool}
    (hk : K n gs c i) : ∀ c', K n gs c' i := by
  obtain ⟨b, hb⟩ := hk
  intro c'
  cases c <;> cases c'
  · exact ⟨b, hb⟩
  · exact ⟨!b, fun y => by rw [← hb y]; exact ne_not (hs y)⟩
  · exact ⟨!b, fun y => by rw [← hb y]; exact ne_not (Ne.symm (hs y))⟩
  · exact ⟨b, hb⟩

lemma red_of_reads (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (c : Bool) (j i : ℕ)
    (hj : j < gs.length) (hr : reads n gs j i) (hk : K n gs c i) : Red n gs c j := by
  obtain ⟨b, hb⟩ := hk
  rcases gate_const_input (gs.getD j dG) (nok_getD gs hnok j)
      (fun k (y : Fin n → Bool) => if k < n + 1 + j then val n gs c k y else false) i hr.1 b
      (fun y => by simp only [hr.2, ite_true]; exact hb y) with ⟨b', hb'⟩ | ⟨k, _, hk'⟩
  · exact Or.inl ⟨b', fun y => (val_gate n gs c j y hj).trans (hb' y)⟩
  · by_cases hlt : k < n + 1 + j
    · refine Or.inr ⟨k, hlt, fun y => ?_⟩
      have := (val_gate n gs c j y hj).trans (hk' y)
      simp only [hlt, ite_true] at this
      exact this.symm
    · refine Or.inl ⟨false, fun y => ?_⟩
      have := (val_gate n gs c j y hj).trans (hk' y)
      simp only [hlt, ite_false] at this
      exact this

lemma split_reads (n : ℕ) (gs : List Gate) (j : ℕ) (y : Fin n → Bool) (hj : j < gs.length)
    (hs : Split n gs (n + 1 + j) y) : ∃ i, reads n gs j i ∧ Split n gs i y := by
  by_contra hno
  apply hs
  rw [val_gate n gs false j y hj, val_gate n gs true j y hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hlt : i < n + 1 + j
  · simp only [hlt, ite_true]
    by_contra hne
    exact hno ⟨i, ⟨hi, hlt⟩, hne⟩
  · simp only [hlt, ite_false]

lemma K_of_all (n : ℕ) (gs : List Gate) (c : Bool) (j : ℕ) (hj : j < gs.length)
    (h : ∀ i, reads n gs j i → K n gs c i) : K n gs c (n + 1 + j) := by
  refine ⟨val n gs c (n + 1 + j) (fun _ => false), fun y => ?_⟩
  rw [val_gate n gs c j y hj, val_gate n gs c j _ hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hlt : i < n + 1 + j
  · obtain ⟨b, hb⟩ := h i ⟨hi, hlt⟩
    simp only [hlt, ite_true]
    rw [hb y, hb]
  · simp only [hlt, ite_false]

/-- A gate reading a wire that is the constant `p` on side `false` and `!p` on side `true` is
constant on one of the sides. -/
lemma anti (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (j i : ℕ) (hj : j < gs.length)
    (hr : reads n gs j i) (p : Bool) (h0 : ∀ y : Fin n → Bool, val n gs false i y = p)
    (h1 : ∀ y : Fin n → Bool, val n gs true i y = !p) :
    K n gs false (n + 1 + j) ∨ K n gs true (n + 1 + j) := by
  have hlt := hr.2
  have hi := hr.1
  rcases gate_cases (gs.getD j dG) (nok_getD gs hnok j) with
    ⟨b, hb⟩ | ⟨i', hin, hc | hc⟩ | ⟨i', k', hin, hc | hc⟩
  · exact Or.inl ⟨b, fun y => (val_gate n gs false j y hj).trans (hb _)⟩
  · rw [hin] at hi
    obtain rfl : i = i' := by simpa using hi
    exact Or.inl ⟨p, fun y => (val_gate n gs false j y hj).trans ((hc _).trans (by
      simp only [hlt, ite_true]; exact h0 y))⟩
  · rw [hin] at hi
    obtain rfl : i = i' := by simpa using hi
    exact Or.inl ⟨!p, fun y => (val_gate n gs false j y hj).trans ((hc _).trans (by
      simp only [hlt, ite_true]; rw [h0 y]))⟩
  · have hik : i = i' ∨ i = k' := by rw [hin] at hi; simpa using hi
    cases p
    · refine Or.inl ⟨false, fun y => (val_gate n gs false j y hj).trans ((hc _).trans ?_)⟩
      rcases hik with rfl | rfl <;> simp [hlt, h0 y]
    · refine Or.inr ⟨false, fun y => (val_gate n gs true j y hj).trans ((hc _).trans ?_)⟩
      rcases hik with rfl | rfl <;> simp [hlt, h1 y]
  · have hik : i = i' ∨ i = k' := by rw [hin] at hi; simpa using hi
    cases p
    · refine Or.inr ⟨true, fun y => (val_gate n gs true j y hj).trans ((hc _).trans ?_)⟩
      rcases hik with rfl | rfl <;> simp [hlt, h1 y]
    · refine Or.inl ⟨true, fun y => (val_gate n gs false j y hj).trans ((hc _).trans ?_)⟩
      rcases hik with rfl | rfl <;> simp [hlt, h0 y]

/-- If every split gate outside `B` reads no split wire of `B`, all split wires are in `B`. -/
lemma block (n : ℕ) (gs : List Gate) (y : Fin n → Bool) (B : ℕ → Prop) (hx : B n)
    (hB : ∀ j, j < gs.length → ¬ B (n + 1 + j) → Split n gs (n + 1 + j) y →
      ∀ i, reads n gs j i → B i → Split n gs i y → False) :
    ∀ i, Split n gs i y → B i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hs
    by_cases h1 : i < n
    · exact absurd (by rw [val_lt n gs false i y h1, val_lt n gs true i y h1]) hs
    · by_cases h2 : i = n
      · rw [h2]; exact hx
      · by_cases h3 : i < n + 1 + gs.length
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + 1 + j := ⟨i - (n + 1), by omega⟩
          by_contra hnB
          obtain ⟨i', hr, hs'⟩ := split_reads n gs j y (by omega) hs
          exact hB j (by omega) hnB hs i' hr (ih i' hr.2 hs') hs'
        · exact absurd (by
            rw [val_ge n gs false i y (by omega), val_ge n gs true i y (by omega)]) hs

lemma two_mem (l : List ℕ) (a b : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ x ∈ l, x = a ∨ x = b := by
  rcases l with _ | ⟨u, _ | ⟨v, _ | ⟨w, r⟩⟩⟩
  · simp at ha
  · simp at ha hb; omega
  · intro x hx; simp at ha hb hx; omega
  · simp at hl

/-! ## Counting -/

/-- There are `k` distinct gates that are redundant on side `c`. -/
def Has (n : ℕ) (gs : List Gate) (c : Bool) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = k ∧ ∀ j ∈ S, j < gs.length ∧ Red n gs c j

lemma has3 (n : ℕ) (gs : List Gate) (c : Bool) (a b d : ℕ) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (ha : a < gs.length ∧ Red n gs c a) (hb : b < gs.length ∧ Red n gs c b)
    (hd : d < gs.length ∧ Red n gs c d) : Has n gs c 3 :=
  ⟨{a, b, d}, Finset.card_eq_three.2 ⟨a, b, d, hab, had, hbd, rfl⟩, by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> assumption⟩

lemma has4 (n : ℕ) (gs : List Gate) (c : Bool) (a b d e : ℕ) (hab : a ≠ b) (had : a ≠ d)
    (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (ha : a < gs.length ∧ Red n gs c a) (hb : b < gs.length ∧ Red n gs c b)
    (hd : d < gs.length ∧ Red n gs c d) (he : e < gs.length ∧ Red n gs c e) : Has n gs c 4 :=
  ⟨{a, b, d, e}, by
    rw [Finset.card_insert_of_notMem (by simp [hab, had, hae]),
      Finset.card_eq_three.2 ⟨b, d, e, hbd, hbe, hde, rfl⟩], by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> assumption⟩

/-- Gate `j` reads the last input. -/
abbrev Rd (n : ℕ) (gs : List Gate) (j : ℕ) : Prop := j < gs.length ∧ reads n gs j n

lemma Kx (n : ℕ) (gs : List Gate) (c : Bool) : K n gs c n := ⟨c, fun y => val_n n gs c y⟩

lemma rd_red (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (j : ℕ) (h : Rd n gs j)
    (c : Bool) : j < gs.length ∧ Red n gs c j :=
  ⟨h.1, red_of_reads n gs hnok c j n h.1 h.2 (Kx n gs c)⟩

lemma rd_K (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (j : ℕ) (h : Rd n gs j) :
    K n gs false (n + 1 + j) ∨ K n gs true (n + 1 + j) :=
  anti n gs hnok j n h.1 h.2 false (fun y => val_n n gs false y) (fun y => val_n n gs true y)

/-- A set `B` of wires, each constant on some side, that no gate outside `B` reads: impossible,
because the output is split and constant on no side. -/
lemma dead (n : ℕ) (gs : List Gate) (out : ℕ) (hsens : ∀ y : Fin n → Bool, Split n gs out y)
    (hnc : ∀ c, ¬ K n gs c out) (B : ℕ → Prop) (hBK : ∀ i, B i → ∃ c, K n gs c i) (hx : B n)
    (hblk : ∀ j, j < gs.length → ¬ B (n + 1 + j) → ∀ i, reads n gs j i → B i → False) :
    False := by
  have hB := block n gs (fun _ => false) B hx
    (fun j hj hnB _ i hr hBi _ => hblk j hj hnB i hr hBi) out (hsens _)
  obtain ⟨c, hc⟩ := hBK out hB
  exact hnc c hc

/-- The same, used to show that a gate `g` is split at every `y`. -/
lemma strong (n : ℕ) (gs : List Gate) (out : ℕ) (hsens : ∀ y : Fin n → Bool, Split n gs out y)
    (hnc : ∀ c, ¬ K n gs c out) (B : ℕ → Prop) (hBK : ∀ i, B i → ∃ c, K n gs c i) (hx : B n)
    (g : ℕ)
    (hblk : ∀ y, ¬ Split n gs (n + 1 + g) y → ∀ j, j < gs.length → ¬ B (n + 1 + j) →
      Split n gs (n + 1 + j) y → ∀ i, reads n gs j i → B i → False) :
    ∀ y, Split n gs (n + 1 + g) y := by
  intro y
  by_cases hns : Split n gs (n + 1 + g) y
  · exact hns
  · exfalso
    have hB := block n gs y B hx
      (fun j hj hnB hsj i hr hBi _ => hblk y hns j hj hnB hsj i hr hBi) out (hsens y)
    obtain ⟨c, hc⟩ := hBK out hB
    exact hnc c hc

/-- One gate reads the last input. -/
lemma caseC (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (out : ℕ)
    (hsens : ∀ y : Fin n → Bool, Split n gs out y) (hnc : ∀ c, ¬ K n gs c out)
    (g1 : ℕ) (h1 : Rd n gs g1) (huniq : ∀ j, Rd n gs j → j = g1) :
    Has n gs false 3 ∧ Has n gs true 3 := by
  have hs1 : ∀ y, Split n gs (n + 1 + g1) y :=
    strong n gs out hsens hnc (fun i => i = n)
      (fun i hi => by rw [show i = n from hi]; exact ⟨false, Kx n gs false⟩) rfl g1
      (fun y hns j hj _ hsj i hr hBi => by
        rw [show i = n from hBi] at hr
        rw [huniq j ⟨hj, hr⟩] at hsj
        exact hns hsj)
  have hK1 : ∀ c, K n gs c (n + 1 + g1) := by
    rcases rd_K n gs hnok g1 h1 with h | h
    · exact kboth hs1 h
    · exact kboth hs1 h
  have hR1 := rd_red n gs hnok g1 h1
  by_cases hX2 : ∃ a b, a ≠ b ∧ (a < gs.length ∧ reads n gs a (n + 1 + g1)) ∧
      (b < gs.length ∧ reads n gs b (n + 1 + g1))
  · obtain ⟨a, b, hab, ⟨ha, hra⟩, ⟨hb, hrb⟩⟩ := hX2
    have h1a : g1 ≠ a := by have := hra.2; omega
    have h1b : g1 ≠ b := by have := hrb.2; omega
    exact ⟨has3 n gs false g1 a b h1a h1b hab (hR1 false)
        ⟨ha, red_of_reads n gs hnok false a _ ha hra (hK1 false)⟩
        ⟨hb, red_of_reads n gs hnok false b _ hb hrb (hK1 false)⟩,
      has3 n gs true g1 a b h1a h1b hab (hR1 true)
        ⟨ha, red_of_reads n gs hnok true a _ ha hra (hK1 true)⟩
        ⟨hb, red_of_reads n gs hnok true b _ hb hrb (hK1 true)⟩⟩
  · by_cases hX2' : ∃ a, a < gs.length ∧ reads n gs a (n + 1 + g1)
    · obtain ⟨g2, hg2, hr2⟩ := hX2'
      have uniq2 : ∀ j, j < gs.length → reads n gs j (n + 1 + g1) → j = g2 := by
        intro j hj hr
        by_contra hne
        exact hX2 ⟨j, g2, hne, ⟨hj, hr⟩, ⟨hg2, hr2⟩⟩
      have h12 : g1 ≠ g2 := by have := hr2.2; omega
      have hs2 : ∀ y, Split n gs (n + 1 + g2) y :=
        strong n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g1)
          (fun i hi => by
            rcases hi with e | e
            · rw [e]; exact ⟨false, Kx n gs false⟩
            · rw [e]; exact ⟨false, hK1 false⟩) (Or.inl rfl) g2
          (fun y hns j hj hnB hsj i hr hBi => by
            rcases hBi with e | e
            · rw [e] at hr
              exact hnB (Or.inr (by rw [huniq j ⟨hj, hr⟩]))
            · rw [e] at hr
              rw [uniq2 j hj hr] at hsj
              exact hns hsj)
      have hK2 : ∀ c, K n gs c (n + 1 + g2) := by
        obtain ⟨p, hp⟩ := hK1 false
        have hp1 : ∀ y : Fin n → Bool, val n gs true (n + 1 + g1) y = !p := fun y => by
          rw [← hp y]; exact ne_not (hs1 y)
        rcases anti n gs hnok g2 (n + 1 + g1) hg2 hr2 p hp hp1 with h | h
        · exact kboth hs2 h
        · exact kboth hs2 h
      by_cases hX3 : ∃ g3, g3 < gs.length ∧ reads n gs g3 (n + 1 + g2)
      · obtain ⟨g3, hg3, hr3⟩ := hX3
        have h23 : g2 ≠ g3 := by have := hr3.2; omega
        have h13 : g1 ≠ g3 := by have := hr3.2; have := hr2.2; omega
        exact ⟨has3 n gs false g1 g2 g3 h12 h13 h23 (hR1 false)
            ⟨hg2, red_of_reads n gs hnok false g2 _ hg2 hr2 (hK1 false)⟩
            ⟨hg3, red_of_reads n gs hnok false g3 _ hg3 hr3 (hK2 false)⟩,
          has3 n gs true g1 g2 g3 h12 h13 h23 (hR1 true)
            ⟨hg2, red_of_reads n gs hnok true g2 _ hg2 hr2 (hK1 true)⟩
            ⟨hg3, red_of_reads n gs hnok true g3 _ hg3 hr3 (hK2 true)⟩⟩
      · exfalso
        exact dead n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g1 ∨ i = n + 1 + g2)
          (fun i hi => by
            rcases hi with e | e | e
            · rw [e]; exact ⟨false, Kx n gs false⟩
            · rw [e]; exact ⟨false, hK1 false⟩
            · rw [e]; exact ⟨false, hK2 false⟩) (Or.inl rfl)
          (fun j hj hnB i hr hBi => by
            rcases hBi with e | e | e
            · rw [e] at hr
              exact hnB (Or.inr (Or.inl (by rw [huniq j ⟨hj, hr⟩])))
            · rw [e] at hr
              exact hnB (Or.inr (Or.inr (by rw [uniq2 j hj hr])))
            · rw [e] at hr
              exact hX3 ⟨j, hj, hr⟩)
    · exfalso
      exact dead n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g1)
        (fun i hi => by
          rcases hi with e | e
          · rw [e]; exact ⟨false, Kx n gs false⟩
          · rw [e]; exact ⟨false, hK1 false⟩) (Or.inl rfl)
        (fun j hj hnB i hr hBi => by
          rcases hBi with e | e
          · rw [e] at hr
            exact hnB (Or.inr (by rw [huniq j ⟨hj, hr⟩]))
          · rw [e] at hr
            exact hX2' ⟨j, hj, hr⟩)

/-- Two readers `g`, `g'`, both constant on side `c`; the one other gate `h` that reads them
reads `g` and not `g'`. -/
lemma b1_one (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (out : ℕ)
    (hsens : ∀ y : Fin n → Bool, Split n gs out y) (hnc : ∀ c, ¬ K n gs c out)
    (g g' : ℕ) (hg : Rd n gs g) (hg' : Rd n gs g') (huniq : ∀ j, Rd n gs j → j = g ∨ j = g')
    (c : Bool) (hKg : K n gs c (n + 1 + g)) (hKg' : K n gs c (n + 1 + g')) (h : ℕ)
    (hh : h < gs.length) (hhg : h ≠ g) (hhg' : h ≠ g') (hne : g ≠ g')
    (hr : reads n gs h (n + 1 + g)) (hnr : ¬ reads n gs h (n + 1 + g'))
    (hY : ∀ j, j < gs.length → j ≠ g → j ≠ g' →
      (reads n gs j (n + 1 + g) ∨ reads n gs j (n + 1 + g')) → j = h) :
    Has n gs false 3 ∧ Has n gs true 3 := by
  have hs : ∀ y, Split n gs (n + 1 + g) y :=
    strong n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g')
      (fun i hi => by
        rcases hi with e | e
        · rw [e]; exact ⟨c, Kx n gs c⟩
        · rw [e]; exact ⟨c, hKg'⟩) (Or.inl rfl) g
      (fun y hns j hj hnB hsj i hr' hBi => by
        have hjg : j ≠ g := fun e => by rw [e] at hsj; exact hns hsj
        have hjg' : j ≠ g' := fun e => hnB (Or.inr (by rw [e]))
        rcases hBi with e | e
        · rw [e] at hr'
          rcases huniq j ⟨hj, hr'⟩ with e' | e'
          · exact hjg e'
          · exact hjg' e'
        · rw [e] at hr'
          have := hY j hj hjg hjg' (Or.inr hr')
          rw [this] at hr'
          exact hnr hr')
  have hK : ∀ c', K n gs c' (n + 1 + g) := kboth hs hKg
  have hRg := rd_red n gs hnok g hg
  have hRg' := rd_red n gs hnok g' hg'
  exact ⟨has3 n gs false g g' h hne (Ne.symm hhg) (Ne.symm hhg') (hRg false) (hRg' false)
      ⟨hh, red_of_reads n gs hnok false h _ hh hr (hK false)⟩,
    has3 n gs true g g' h hne (Ne.symm hhg) (Ne.symm hhg') (hRg true) (hRg' true)
      ⟨hh, red_of_reads n gs hnok true h _ hh hr (hK true)⟩⟩

/-- Two readers `g`, `g'` with `g'` not constant on the side where `g` is: some other gate
reads `g`. -/
lemma b2_reader (n : ℕ) (gs : List Gate) (out : ℕ)
    (hsens : ∀ y : Fin n → Bool, Split n gs out y) (hnc : ∀ c, ¬ K n gs c out)
    (g g' : ℕ) (huniq : ∀ j, Rd n gs j → j = g ∨ j = g') (a b : Bool)
    (hKg : K n gs a (n + 1 + g)) (hKg' : K n gs b (n + 1 + g'))
    (hnot : ¬ K n gs a (n + 1 + g')) :
    ∃ r, r < gs.length ∧ r ≠ g ∧ r ≠ g' ∧ reads n gs r (n + 1 + g) := by
  by_contra hno
  have hs' : ∀ y, Split n gs (n + 1 + g') y :=
    strong n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g)
      (fun i hi => by
        rcases hi with e | e
        · rw [e]; exact ⟨a, Kx n gs a⟩
        · rw [e]; exact ⟨a, hKg⟩) (Or.inl rfl) g'
      (fun y hns j hj hnB hsj i hr hBi => by
        have hjg' : j ≠ g' := fun e => by rw [e] at hsj; exact hns hsj
        have hjg : j ≠ g := fun e => hnB (Or.inr (by rw [e]))
        rcases hBi with e | e
        · rw [e] at hr
          rcases huniq j ⟨hj, hr⟩ with e' | e'
          · exact hjg e'
          · exact hjg' e'
        · rw [e] at hr
          exact hno ⟨j, hj, hjg, hjg', hr⟩)
  exact hnot (kboth hs' hKg' a)

/-- Two gates read the last input. -/
lemma caseB (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (out : ℕ)
    (hsens : ∀ y : Fin n → Bool, Split n gs out y) (hnc : ∀ c, ¬ K n gs c out)
    (g1 g2 : ℕ) (hne : g1 ≠ g2) (h1 : Rd n gs g1) (h2 : Rd n gs g2)
    (huniq : ∀ j, Rd n gs j → j = g1 ∨ j = g2) :
    (∃ c, Has n gs c 4) ∨ (Has n gs false 3 ∧ Has n gs true 3) := by
  have hR1 := rd_red n gs hnok g1 h1
  have hR2 := rd_red n gs hnok g2 h2
  by_cases hB1 : ∃ c, K n gs c (n + 1 + g1) ∧ K n gs c (n + 1 + g2)
  · obtain ⟨c, hc1, hc2⟩ := hB1
    have hYred : ∀ j, j < gs.length →
        (reads n gs j (n + 1 + g1) ∨ reads n gs j (n + 1 + g2)) → Red n gs c j := by
      intro j hj hr
      rcases hr with hr | hr
      · exact red_of_reads n gs hnok c j _ hj hr hc1
      · exact red_of_reads n gs hnok c j _ hj hr hc2
    by_cases hone : ∃ h, h < gs.length ∧ h ≠ g1 ∧ h ≠ g2 ∧
        (reads n gs h (n + 1 + g1) ∨ reads n gs h (n + 1 + g2))
    · obtain ⟨h, hh, hh1, hh2, hhr⟩ := hone
      by_cases htwo : ∃ h', h' ≠ h ∧ h' < gs.length ∧ h' ≠ g1 ∧ h' ≠ g2 ∧
          (reads n gs h' (n + 1 + g1) ∨ reads n gs h' (n + 1 + g2))
      · obtain ⟨h', hne', hh', hh1', hh2', hhr'⟩ := htwo
        exact Or.inl ⟨c, has4 n gs c g1 g2 h h' hne (Ne.symm hh1) (Ne.symm hh1') (Ne.symm hh2)
          (Ne.symm hh2') (Ne.symm hne') (hR1 c) (hR2 c) ⟨hh, hYred h hh hhr⟩
          ⟨hh', hYred h' hh' hhr'⟩⟩
      · have hY : ∀ j, j < gs.length → j ≠ g1 → j ≠ g2 →
            (reads n gs j (n + 1 + g1) ∨ reads n gs j (n + 1 + g2)) → j = h := by
          intro j hj hj1 hj2 hr
          by_contra hjh
          exact htwo ⟨j, hjh, hj, hj1, hj2, hr⟩
        by_cases hboth : reads n gs h (n + 1 + g1) ∧ reads n gs h (n + 1 + g2)
        · have hKh : K n gs c (n + 1 + h) := by
            apply K_of_all n gs c h hh
            intro i hi
            have hlen : (gs.getD h dG).inputs.length ≤ 2 := (nok_getD gs hnok h).1.2
            have : i = n + 1 + g1 ∨ i = n + 1 + g2 :=
              two_mem _ _ _ hlen hboth.1.1 hboth.2.1 (by omega) i hi.1
            rcases this with e | e
            · rw [e]; exact hc1
            · rw [e]; exact hc2
          by_cases h3 : ∃ h3, h3 < gs.length ∧ h3 ≠ g1 ∧ h3 ≠ g2 ∧ reads n gs h3 (n + 1 + h)
          · obtain ⟨h3, hh3, h31, h32, hr3⟩ := h3
            have h3h : h ≠ h3 := by have := hr3.2; omega
            exact Or.inl ⟨c, has4 n gs c g1 g2 h h3 hne (Ne.symm hh1) (Ne.symm h31)
              (Ne.symm hh2) (Ne.symm h32) h3h (hR1 c) (hR2 c) ⟨hh, hYred h hh hhr⟩
              ⟨hh3, red_of_reads n gs hnok c h3 _ hh3 hr3 hKh⟩⟩
          · exfalso
            exact dead n gs out hsens hnc
              (fun i => i = n ∨ i = n + 1 + g1 ∨ i = n + 1 + g2 ∨ i = n + 1 + h)
              (fun i hi => by
                rcases hi with e | e | e | e
                · rw [e]; exact ⟨c, Kx n gs c⟩
                · rw [e]; exact ⟨c, hc1⟩
                · rw [e]; exact ⟨c, hc2⟩
                · rw [e]; exact ⟨c, hKh⟩) (Or.inl rfl)
              (fun j hj hnB i hr hBi => by
                have hj1 : j ≠ g1 := fun e => hnB (Or.inr (Or.inl (by rw [e])))
                have hj2 : j ≠ g2 := fun e => hnB (Or.inr (Or.inr (Or.inl (by rw [e]))))
                have hjh : j ≠ h := fun e => hnB (Or.inr (Or.inr (Or.inr (by rw [e]))))
                rcases hBi with e | e | e | e
                · rw [e] at hr
                  rcases huniq j ⟨hj, hr⟩ with e' | e'
                  · exact hj1 e'
                  · exact hj2 e'
                · rw [e] at hr
                  exact hjh (hY j hj hj1 hj2 (Or.inl hr))
                · rw [e] at hr
                  exact hjh (hY j hj hj1 hj2 (Or.inr hr))
                · rw [e] at hr
                  exact h3 ⟨j, hj, hj1, hj2, hr⟩)
        · right
          rcases hhr with hr | hr
          · have hnr : ¬ reads n gs h (n + 1 + g2) := fun h' => hboth ⟨hr, h'⟩
            exact b1_one n gs hnok out hsens hnc g1 g2 h1 h2 huniq c hc1 hc2 h hh hh1 hh2 hne
              hr hnr hY
          · have hnr : ¬ reads n gs h (n + 1 + g1) := fun h' => hboth ⟨h', hr⟩
            exact b1_one n gs hnok out hsens hnc g2 g1 h2 h1 (fun j hj => (huniq j hj).symm) c
              hc2 hc1 h hh hh2 hh1 (Ne.symm hne) hr hnr
              (fun j hj hj2 hj1 hr' => hY j hj hj1 hj2 hr'.symm)
    · exfalso
      exact dead n gs out hsens hnc (fun i => i = n ∨ i = n + 1 + g1 ∨ i = n + 1 + g2)
        (fun i hi => by
          rcases hi with e | e | e
          · rw [e]; exact ⟨c, Kx n gs c⟩
          · rw [e]; exact ⟨c, hc1⟩
          · rw [e]; exact ⟨c, hc2⟩) (Or.inl rfl)
        (fun j hj hnB i hr hBi => by
          have hj1 : j ≠ g1 := fun e => hnB (Or.inr (Or.inl (by rw [e])))
          have hj2 : j ≠ g2 := fun e => hnB (Or.inr (Or.inr (by rw [e])))
          rcases hBi with e | e | e
          · rw [e] at hr
            rcases huniq j ⟨hj, hr⟩ with e' | e'
            · exact hj1 e'
            · exact hj2 e'
          · rw [e] at hr
            exact hone ⟨j, hj, hj1, hj2, Or.inl hr⟩
          · rw [e] at hr
            exact hone ⟨j, hj, hj1, hj2, Or.inr hr⟩)
  · right
    have hno : ∀ c, K n gs c (n + 1 + g1) → ¬ K n gs c (n + 1 + g2) :=
      fun c hk1 hk2 => hB1 ⟨c, hk1, hk2⟩
    have key : ∀ a b : Bool, K n gs a (n + 1 + g1) → K n gs b (n + 1 + g2) →
        ¬ K n gs a (n + 1 + g2) → ¬ K n gs b (n + 1 + g1) → Has n gs a 3 ∧ Has n gs b 3 := by
      intro a b ka kb na nb
      obtain ⟨r1, hr1, hr11, hr12, hrr1⟩ :=
        b2_reader n gs out hsens hnc g1 g2 huniq a b ka kb na
      obtain ⟨r2, hr2, hr22, hr21, hrr2⟩ :=
        b2_reader n gs out hsens hnc g2 g1 (fun j hj => (huniq j hj).symm) b a kb ka nb
      exact ⟨has3 n gs a g1 g2 r1 hne (Ne.symm hr11) (Ne.symm hr12) (hR1 a) (hR2 a)
          ⟨hr1, red_of_reads n gs hnok a r1 _ hr1 hrr1 ka⟩,
        has3 n gs b g1 g2 r2 hne (Ne.symm hr21) (Ne.symm hr22) (hR1 b) (hR2 b)
          ⟨hr2, red_of_reads n gs hnok b r2 _ hr2 hrr2 kb⟩⟩
    rcases rd_K n gs hnok g1 h1 with k1 | k1 <;> rcases rd_K n gs hnok g2 h2 with k2 | k2
    · exact absurd k2 (hno _ k1)
    · exact key false true k1 k2 (hno _ k1) (fun k => hno _ k k2)
    · exact (key true false k1 k2 (hno _ k1) (fun k => hno _ k k2)).symm
    · exact absurd k2 (hno _ k1)

/-- The count: four redundant gates on one side, or three on each. -/
theorem count_main (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (out : ℕ)
    (hsens : ∀ y : Fin n → Bool, Split n gs out y) (hnc : ∀ c, ¬ K n gs c out) :
    (∃ c, Has n gs c 4) ∨ (Has n gs false 3 ∧ Has n gs true 3) := by
  by_cases h3 : ∃ a b d, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ Rd n gs a ∧ Rd n gs b ∧ Rd n gs d
  · obtain ⟨a, b, d, hab, had, hbd, ha, hb, hd⟩ := h3
    exact Or.inr ⟨has3 n gs false a b d hab had hbd (rd_red n gs hnok a ha false)
        (rd_red n gs hnok b hb false) (rd_red n gs hnok d hd false),
      has3 n gs true a b d hab had hbd (rd_red n gs hnok a ha true)
        (rd_red n gs hnok b hb true) (rd_red n gs hnok d hd true)⟩
  · by_cases h2 : ∃ a b, a ≠ b ∧ Rd n gs a ∧ Rd n gs b
    · obtain ⟨a, b, hab, ha, hb⟩ := h2
      exact caseB n gs hnok out hsens hnc a b hab ha hb (fun j hj => by
        by_contra hno
        push Not at hno
        exact h3 ⟨a, b, j, hab, Ne.symm hno.1, Ne.symm hno.2, ha, hb, hj⟩)
    · by_cases h1 : ∃ a, Rd n gs a
      · obtain ⟨a, ha⟩ := h1
        exact Or.inr (caseC n gs hnok out hsens hnc a ha (fun j hj => by
          by_contra hno
          exact h2 ⟨j, a, hno, hj, ha⟩))
      · exfalso
        exact dead n gs out hsens hnc (fun i => i = n)
          (fun i hi => by rw [show i = n from hi]; exact ⟨false, Kx n gs false⟩) rfl
          (fun j hj _ i hr hBi => by
            rw [show i = n from hBi] at hr
            exact h1 ⟨j, hj, hr⟩)

/-! ## The theorems -/

lemma not_gate (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun y : Fin n → Bool => !f y) (s + 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  refine ⟨⟨C.gates ++ [⟨GateOp.not, [C.output]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ok g hg
    · have he : g = ⟨GateOp.not, [C.output]⟩ := List.mem_singleton.1 hg
      subst g
      simp
  · simpa [Circuit.size] using Nat.add_le_add_right hsz 1
  · intro y
    show (wiresFrom (C.gates ++ [⟨GateOp.not, [C.output]⟩]) (List.ofFn y)).getD
      (n + C.gates.length) false = _
    rw [wiresFrom_snoc, getD_snoc_len _ _ _ _ (by simp [length_wiresFrom])]
    have : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    show (!(wiresFrom C.gates (List.ofFn y)).getD C.output false) = !f y
    rw [this]

lemma size_mono (n s s' : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s)
    (hs : s ≤ s') : HasCircuitSize n f s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  exact ⟨C, ok, le_trans hsz hs, hev⟩

/-- **Three gates.** If `F` changes whenever its last input is flipped, and is not constant once
that input is fixed, then fixing the last input (to either value) saves three gates. -/
theorem restrict_three (n s : ℕ) (F : (Fin (n + 1) → Bool) → Bool)
    (hsens : ∀ y : Fin n → Bool, F (Fin.snoc y false) ≠ F (Fin.snoc y true))
    (hnc : ∃ y y' : Fin n → Bool, F (Fin.snoc y true) ≠ F (Fin.snoc y' true))
    (h : HasCircuitSize (n + 1) F (s + 3)) (c : Bool) :
    HasCircuitSize n (fun y : Fin n → Bool => F (Fin.snoc y c)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz1 : C.gates.length ≤ s + 3 := hsz
  set gs := C.gates.map normGate with hgs
  have hlen : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hv : ∀ (c : Bool) (y : Fin n → Bool), val n gs c C.output y = F (Fin.snoc y c) := by
    intro c y
    unfold val
    rw [← ofFn_snoc, hgs, wiresFrom_norm, ← hev]; rfl
  have hsens' : ∀ y : Fin n → Bool, Split n gs C.output y := by
    intro y
    show val n gs false C.output y ≠ val n gs true C.output y
    rw [hv, hv]; exact hsens y
  have hF : ∀ (c : Bool) (y : Fin n → Bool), F (Fin.snoc y (!c)) = !F (Fin.snoc y c) := by
    intro c y
    cases c
    · exact ne_not (hsens y)
    · exact ne_not (Ne.symm (hsens y))
  have hnc' : ∀ c, ¬ K n gs c C.output := by
    rintro c ⟨b, hb⟩
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    cases c
    · have e1 := hF false y
      have e2 := hF false y'
      simp only [Bool.not_false] at e1 e2
      rw [e1, e2, ← hv false y, ← hv false y', hb y, hb y']
    · rw [← hv true y, ← hv true y', hb y, hb y']
  rcases count_main n gs hnok C.output hsens' hnc' with
    ⟨c0, S, hcard, hS⟩ | ⟨⟨S0, hc0, hS0⟩, ⟨S1, hc1, hS1⟩⟩
  · obtain ⟨C', ok', hsz', hev'⟩ := se n c0 gs hnok C.output (hnc' c0) S hS
    by_cases hcc : c = c0
    · subst hcc
      exact ⟨C', ok', by omega, fun y => by rw [hev' y, hv]⟩
    · have hc' : c = !c0 := by
        cases c <;> cases c0 <;> first | rfl | exact absurd rfl hcc
      have hbase : HasCircuitSize n (fun y : Fin n → Bool => F (Fin.snoc y c0)) (s - 1) :=
        ⟨C', ok', by omega, fun y => by rw [hev' y, hv]⟩
      have hn := not_gate n (s - 1) _ hbase
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1] at hn
      have e : (fun y : Fin n → Bool => F (Fin.snoc y c)) =
          fun y : Fin n → Bool => !F (Fin.snoc y c0) := by
        funext y; rw [hc']; exact hF c0 y
      rw [e]; exact hn
  · cases c
    · obtain ⟨C', ok', hsz', hev'⟩ := se n false gs hnok C.output (hnc' false) S0 hS0
      exact ⟨C', ok', by omega, fun y => by rw [hev' y, hv]⟩
    · obtain ⟨C', ok', hsz', hev'⟩ := se n true gs hnok C.output (hnc' true) S1 hS1
      exact ⟨C', ok', by omega, fun y => by rw [hev' y, hv]⟩

/-- **Lower bound.** For a non-constant `f`, a circuit with `s + 3` gates for `x ⊕ f` gives
circuits with `s` gates for `f` and for `¬f`: `C(x ⊕ f) ≥ max (C f) (C ¬f) + 3`. -/
theorem xor_lower (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc)))
      (s + 3)) :
    HasCircuitSize n f s ∧ HasCircuitSize n (fun y : Fin n → Bool => !f y) s := by
  have key := restrict_three n s _ (by intro y; simp)
    (by obtain ⟨y, y', hne⟩ := hf; exact ⟨y, y', by simpa using hne⟩) h
  have h0 := key false
  have h1 := key true
  simp only [Fin.snoc_last, Fin.snoc_castSucc, Bool.false_xor, Bool.true_xor] at h0 h1
  exact ⟨h0, h1⟩

/-- **Exact value when the two sizes differ.** If some size `s₀` is enough for exactly one of
`f`, `¬f`, then `x ⊕ f` has a circuit with `t + 4` gates exactly when `f` or `¬f` has one with
`t` gates: `C(x ⊕ f) = min (C f) (C ¬f) + 4`. -/
theorem xor_exact (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (s₀ : ℕ)
    (hdiff : (HasCircuitSize n f s₀ ∧ ¬ HasCircuitSize n (fun y : Fin n → Bool => !f y) s₀) ∨
      (HasCircuitSize n (fun y : Fin n → Bool => !f y) s₀ ∧ ¬ HasCircuitSize n f s₀))
    (t : ℕ) :
    HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc)))
        (t + 4) ↔
      (HasCircuitSize n f t ∨ HasCircuitSize n (fun y : Fin n → Bool => !f y) t) := by
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := xor_lower n (t + 1) f hf h
    rcases hdiff with ⟨hy, hn⟩ | ⟨hy, hn⟩
    · have : s₀ ≤ t := by
        by_contra hlt
        exact hn (size_mono n (t + 1) s₀ _ hB (by omega))
      exact Or.inl (size_mono n s₀ t f hy this)
    · have : s₀ ≤ t := by
        by_contra hlt
        exact hn (size_mono n (t + 1) s₀ _ hA (by omega))
      exact Or.inr (size_mono n s₀ t _ hy this)
  · rintro (h | h)
    · exact (PEqualNP.Outside.L_meta_716 n t f).1 h
    · exact (PEqualNP.Outside.L_meta_716 n t f).2 h

end PEqualNP.General.XorExtension
