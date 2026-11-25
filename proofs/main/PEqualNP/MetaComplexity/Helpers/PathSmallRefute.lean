import PEqualNP.Outside.L_meta_573

/-!
# The odd path bound of `L_meta_574` fails for `h = 1`

`L_meta_574` requires `3 ≤ h`. This file shows the same statement with `1 ≤ h` is false:
for `N = 2`, `g = x₀ xor x₁`, `u = 0`, `v = 1`, `h = 1` the function has a circuit of size 8,
while the conclusion would need a circuit of size at most 2 for xor or at most 5 for the
two-pendant function `xor(x₀,x₁) ∨ x₀y₀ ∨ x₁y₁` (whose size is 6 = 4 + 2).

The constant-propagation pass (`PathSmallGR`) is copied from `L_meta_574`, where it is private.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.MetaComplexity.PathSmallGR
-- The constant-propagation pass follows L_meta_468.

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

theorem elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

private lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

theorem assign_inputs {n m s : ℕ} {F : (Fin m → Bool) → Bool} {X : (Fin n → Bool) → Bool}
    (assign : Fin m → Bool ⊕ Fin n) (hc : HasCircuitSize m F s)
    (he : ∀ y : Fin n → Bool, F (fun j => (assign j).elim id y) = X y)
    (hnc : ∃ y y', X y ≠ X y') : HasCircuitSize n X s := by
  obtain ⟨C, hok, hsz, hev⟩ := hc
  let gs := C.gates.map normGate
  have hgood : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  let env (y : Fin n → Bool) (j : Fin m) : Bool := (assign j).elim id y
  let wire (j : Fin m) : Bool ⊕ ℕ := (assign j).map id Fin.val
  let init := List.ofFn wire
  let acc := elimPass n gs (init, [])
  have hinv (y : Fin n → Bool) :
      ElimInv n (List.ofFn y) (wiresFrom gs (List.ofFn (env y))) acc := by
    apply elimInv_pass n (List.ofFn y) gs _ (init, []) (fun g hg => (hgood g hg).1)
    refine ⟨by simp, by simp [init], ?_⟩
    intro i
    by_cases hi : i < m
    · change statValid _ ((List.ofFn wire).getD i _) ∧ _
      rw [ofFn_getD_lt _ _ _ hi]
      change statValid n (wire ⟨i,hi⟩) ∧ statVal (List.ofFn y) (wire ⟨i,hi⟩) = (List.ofFn (env y)).getD i false
      rw [ofFn_getD_lt _ _ _ hi]
      unfold wire env
      cases h : assign ⟨i,hi⟩ with
      | inl _ => exact ⟨trivial,rfl⟩
      | inr a => exact ⟨a.isLt, ofFn_getD_lt _ _ _ a.isLt⟩
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial,rfl⟩
  have hval (y : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (.inl false)) = X y := by
    rw [((hinv y).2.2 C.output).2]
    change (wiresFrom (C.gates.map normGate) _).getD _ false = _
    rw [wiresFrom_norm]
    exact (hev _).trans (he y)
  cases hout : acc.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x,y,hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [hout] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elimPass_ok n gs _ (by simp),?_,?_⟩
    · have hh := elimPass_len n gs (init,[])
      change acc.2.length ≤ s
      have hlen : gs.length = C.gates.length := by simp [gs]
      change acc.2.length ≤ [].length + gs.length at hh
      change C.gates.length ≤ s at hsz
      simpa using hh.trans (by simpa [hlen] using hsz)
    · intro x
      have hh := hval x
      rw [hout] at hh
      exact hh


end PEqualNP.MetaComplexity.PathSmallGR

namespace PEqualNP.MetaComplexity.PathSmall

/-- The statement of `L_meta_574` with `1 ≤ h` in place of `3 ≤ h`. -/
def PathLbAll : Prop :=
  ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), u ≠ v → 1 ≤ h → (∃ y y' : Fin N → Bool, g y ≠ g y') → g (fun _ : Fin N => false) = false → (∃ x : Fin N → Bool, x u = true ∧ g x = false) → (∃ x : Fin N → Bool, x v = true ∧ g x = false) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) s → ∃ s' : ℕ, (3 * h + s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize N g s') ∨ (3 * h + s' ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s')

/-- Two-input xor. -/
def gx : (Fin 2 → Bool) → Bool := fun y => xor (y 0) (y 1)

/-- An 8-gate circuit for `xor(x₀,x₁) ∨ x₀y₀ ∨ y₀y₁ ∨ y₁y₂ ∨ y₂x₁`:
`(x₀ ∨ x₁ ∨ y₁(y₀ ∨ y₂)) ∧ (y₀ ∨ y₂ ∨ ¬(x₀x₁))`. -/
def cex : Circuit :=
  ⟨[⟨GateOp.and, [0,1]⟩, ⟨GateOp.or, [0,1]⟩, ⟨GateOp.or, [2,4]⟩, ⟨GateOp.and, [3,7]⟩,
    ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [6,8]⟩, ⟨GateOp.or, [7,9]⟩, ⟨GateOp.and, [10,11]⟩], 12⟩

theorem cex_eval5 : ∀ a b c d e : Bool, cex.eval [a,b,c,d,e] =
    (xor a b || (a && c) || (c && d) || (d && e) || (e && b)) := by decide

theorem cex_has : HasCircuitSize (2 + (2 * 1 + 1)) (fun x : Fin (2 + 2 * 1 + 1) → Bool =>
    gx (fun i : Fin 2 => x (Fin.castAdd (2 * 1 + 1) i)) ||
    decide (∃ i : Fin (2 * 1 + 1), x (Fin.natAdd 2 i) = true ∧
      ((i.val = 0 ∧ x (Fin.castAdd (2 * 1 + 1) (0 : Fin 2)) = true) ∨
       (i.val + 1 = 2 * 1 + 1 ∧ x (Fin.castAdd (2 * 1 + 1) (1 : Fin 2)) = true) ∨
       ∃ j : Fin (2 * 1 + 1), j.val = i.val + 1 ∧ x (Fin.natAdd 2 j) = true))) 8 := by
  refine ⟨cex, ?_, by decide, ?_⟩
  · intro g hg
    simp only [cex, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · intro x
    have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by simp [List.ofFn_succ]
    rw [hl, cex_eval5]
    simp only [gx, Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp [Fin.natAdd, Fin.castAdd, Fin.castLE]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> rfl

theorem gx_parity : gx = fun x : Fin 2 → Bool =>
    decide ((Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1) := by
  funext y
  revert y
  decide

theorem gx_lb (s : ℕ) (h : HasCircuitSize 2 gx s) : 4 ≤ s := by
  rw [gx_parity] at h
  have := PEqualNP.MetaComplexity.Helpers573.parity_lower4 2 s h
  omega

/-- The two-pendant function for `gx`. -/
def G2 : (Fin (2 + 2) → Bool) → Bool := fun x =>
  gx (fun i : Fin 2 => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 (0 : Fin 2)) && x (Fin.natAdd 2 (0 : Fin 2))) ||
    (x (Fin.castAdd 2 (1 : Fin 2)) && x (Fin.natAdd 2 (1 : Fin 2)))

theorem G2_lb (s : ℕ) (h : HasCircuitSize (2 + 2) G2 s) : 6 ≤ s := by
  obtain ⟨h1, hs1⟩ := PathSmallGR.elim_one_var (F := G2) (3 : Fin 4) false h
    ⟨![true, true, false, false], by decide⟩
    ⟨![false, false, false, false], ![true, false, false, false], by decide⟩
  obtain ⟨h2, hs2⟩ := PathSmallGR.elim_one_var
    (F := fun x => G2 (Function.update x (3 : Fin 4) false)) (2 : Fin 4) false hs1
    ⟨![true, true, false, false], by decide⟩
    ⟨![false, false, false, false], ![true, false, false, false], by decide⟩
  let assn : Fin 4 → Bool ⊕ Fin 2 := fun j => if hj : j.val < 2 then .inr ⟨j.val, hj⟩ else .inl false
  have hx := PathSmallGR.assign_inputs (X := gx) assn hs2 (by
    intro y
    simp only [assn, G2, gx]
    decide +revert) ⟨![true, false], ![false, false], by decide⟩
  have := gx_lb _ hx
  omega

theorem path_lb_all_false : ¬ PathLbAll := by
  intro H
  obtain ⟨s', h | h⟩ := H 2 1 0 1 gx (by decide) le_rfl ⟨![true, false], ![false, false], by decide⟩
    (by decide) ⟨![true, true], rfl, by decide⟩ ⟨![true, true], rfl, by decide⟩ 8 cex_has
  · have := gx_lb s' h.2
    omega
  · have := G2_lb s' h.2
    omega

end PEqualNP.MetaComplexity.PathSmall
