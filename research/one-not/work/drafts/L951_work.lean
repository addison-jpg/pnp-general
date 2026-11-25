import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

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
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (Q : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ Q)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Good {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (rest : List Gate), gs = pre ++ g :: rest →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
      g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true ∨
      ∀ u : Fin n, g.op.eval (g.inputs.map fun j => val pre (eof u) j) = false

def Inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof Q) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ Q ∧ (u ∈ R → v ∈ R → l u = l v)

def Cnt {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof Q) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ u ∈ R ∧ v ∈ R ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt Q R gs i

theorem D_mono {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D Q R gs ⊆ D Q R (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, huR, hvR, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, huR, hvR, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) :
    ∃ l : Fin n → Fin n, Inv Q R gs l ∧ R.card ≤ (R.image l).card + (D Q R gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, fun _ _ => rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    have hgood' : Good Q gs := by
      intro pre g' rest h
      exact hgood pre g' (rest ++ [g]) (by rw [h]; simp)
    obtain ⟨l, hinv, hcard⟩ := ih hgood'
    have hg := hgood gs g [] (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    by_cases hPz : P (Zof Q) = true
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz
          rw [hPz] at hiz
          exact absurd hiz (by simp)
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono Q R gs g)
        omega
    have hPz' : P (Zof Q) = false := by simpa using hPz
    have key : ∀ u, P (eof u) = true →
        u ∈ Q ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → w ∈ R → w' ∈ R → l w = l w') ∧
          (∀ w w', B w → B w' → w ∈ R → w' ∈ R → l w = l w') := by
      intro u hu
      obtain ⟨hop, hlen⟩ : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        rcases hg with h | h | h
        · exact h
        · exact absurd h hPz
        · exact absurd hu (by rw [show P (eof u) = false from h u]; simp)
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof Q) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hPz'
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : ∃ u v, u ∈ R ∧ v ∈ R ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨u0, v0, hu0R, hv0R, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiu hiv
          obtain ⟨huQ, A, B, hAB, hA, hB⟩ := key u hiu
          refine ⟨huQ, fun huR hvR => ?_⟩
          have two : ∀ w, w ∈ R → P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwR hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0 hwR hu0R)
            · exact Or.inl (hA w u0 h h0 hwR hu0R)
            · exact Or.inr (hA w v0 h h1 hwR hv0R)
            · exact absurd (hB u0 v0 h0 h1 hu0R hv0R) hne
            · exact absurd (hA u0 v0 h0 h1 hu0R hv0R) hne
            · exact Or.inr (hB w v0 h h1 hwR hv0R)
            · exact Or.inl (hB w u0 h h0 hwR hu0R)
            · exact Or.inl (hB w u0 h h0 hwR hu0R)
          have red : ∀ w, w ∈ R → P (eof w) = true →
              (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwR hw
            rcases two w hwR hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u huR hiu, red v hvR hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huQ, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huQ, fun huR hvR => ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl huR hvR]
      · have himg : R.image l ⊆
            insert (l v0) (R.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (R.image l).card ≤
            (R.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D Q R (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, hu0R, hv0R, ?_, ?_⟩
          · rw [hnew]; exact hPz'
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D Q R gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D Q R gs).card + 1 ≤ (D Q R (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono Q R gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huQ, -⟩ := key u hiu
          refine ⟨huQ, fun huR hvR => ?_⟩
          by_contra hne
          exact hm ⟨u, v, huR, hvR, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono Q R gs g)
        omega

/-! ## Cleanup: deleting a gate that copies an earlier wire -/

def redir (p j i : ℕ) : ℕ := if i < p then i else if i = p then j else i - 1

def redirG (p j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redir p j)⟩

theorem getD_eraseIdx_redir (acc : List Bool) (p j i : ℕ) (hp : p < acc.length) (hj : j < p)
    (heq : acc.getD p false = acc.getD j false) :
    (acc.eraseIdx p).getD (redir p j i) false = acc.getD i false := by
  unfold redir
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases h1 : i < p
  · simp [h1]
  · by_cases h2 : i = p
    · subst h2
      simp only [List.getD_eq_getElem?_getD] at heq
      simp [hj, heq]
    · have h3 : ¬ (i - 1 < p) := by omega
      simp only [h1, h2, h3, if_false]
      congr 2
      omega

theorem eraseIdx_snoc (acc : List Bool) (b : Bool) (p : ℕ) (hp : p < acc.length) :
    (acc ++ [b]).eraseIdx p = acc.eraseIdx p ++ [b] := by
  rw [List.eraseIdx_append_of_lt_length hp]

theorem fold_redir (p j : ℕ) (hj : j < p) : ∀ (rest : List Gate) (acc : List Bool),
    p < acc.length → acc.getD p false = acc.getD j false →
    (rest.map (redirG p j)).foldl step (acc.eraseIdx p) = (rest.foldl step acc).eraseIdx p := by
  intro rest
  induction rest with
  | nil => intro acc _ _; simp
  | cons g rest ih =>
    intro acc hp heq
    simp only [List.map_cons, List.foldl_cons]
    have hstep : step (acc.eraseIdx p) (redirG p j g) = (step acc g).eraseIdx p := by
      unfold step redirG
      rw [eraseIdx_snoc _ _ _ hp]
      congr 2
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_eraseIdx_redir acc p j i hp hj heq
    rw [hstep]
    apply ih
    · unfold step; simp; omega
    · unfold step
      simp only [List.getD_eq_getElem?_getD] at heq ⊢
      rw [List.getElem?_append_left hp, List.getElem?_append_left (by omega)]
      exact heq

theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_erase (w : List Bool) (g : Gate) : (step w g).eraseIdx w.length = w := by
  unfold step
  rw [List.eraseIdx_append_of_length_le (le_refl _)]
  simp

def dropGate (gates : List Gate) (k j : ℕ) (n : ℕ) : List Gate :=
  gates.take k ++ (gates.drop (k + 1)).map (redirG (n + k) j)

theorem dropGate_length (gates : List Gate) (k j n : ℕ) (hk : k < gates.length) :
    (dropGate gates k j n).length + 1 = gates.length := by
  unfold dropGate; simp; omega

theorem val_dropGate {n : ℕ} (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hj : j < n + k) (hcopy : ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (x : Fin n → Bool) (i : ℕ) :
    val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i := by
  have hsplit : gates = gates.take k ++ gates[k] :: gates.drop (k + 1) := by
    simp
  set A := gates.take k with hA
  set B := gates.drop (k + 1) with hB
  set g := gates[k] with hg
  have hAl : A.length = k := by rw [hA]; simp; omega
  set acc0 := step (A.foldl step (List.ofFn x)) g with hacc0
  have hlA : (A.foldl step (List.ofFn x)).length = n + k := by
    rw [fold_length]; simp [hAl]
  have hl0 : acc0.length = n + k + 1 := by
    rw [hacc0, step_length, hlA]
  have hfull : gates.foldl step (List.ofFn x) = B.foldl step acc0 := by
    conv_lhs => rw [hsplit]
    simp [List.foldl_append, hacc0]
  have herase : acc0.eraseIdx (n + k) = A.foldl step (List.ofFn x) := by
    rw [hacc0, ← hlA]; exact step_erase _ _
  obtain ⟨r, hr⟩ := fold_prefix B acc0
  have heq0 : acc0.getD (n + k) false = acc0.getD j false := by
    have h := hcopy x
    unfold val at h
    rw [hfull, hr] at h
    simp only [List.getD_eq_getElem?_getD] at h ⊢
    rwa [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at h
  have hdrop : (dropGate gates k j n).foldl step (List.ofFn x) =
      (B.foldl step acc0).eraseIdx (n + k) := by
    unfold dropGate
    rw [List.foldl_append, ← herase]
    exact fold_redir (n + k) j hj B acc0 (by omega) heq0
  unfold val
  rw [hdrop, hfull]
  have hpB : n + k < (B.foldl step acc0).length := by rw [hr]; simp; omega
  have heqB : (B.foldl step acc0).getD (n + k) false = (B.foldl step acc0).getD j false := by
    simp only [List.getD_eq_getElem?_getD] at heq0 ⊢
    rw [hr, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact heq0
  exact getD_eraseIdx_redir _ _ _ _ hpB hj heqB

theorem getD_eraseIdx_ne (acc : List Bool) (p j i : ℕ) (hi : i ≠ p) :
    (acc.eraseIdx p).getD (redir p j i) false = acc.getD i false := by
  unfold redir
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases h1 : i < p
  · simp [h1]
  · have h3 : ¬ (i - 1 < p) := by omega
    simp only [h1, hi, h3, if_false]
    congr 2
    omega

theorem fold_redir_dead (p j : ℕ) : ∀ (rest : List Gate) (acc : List Bool),
    p < acc.length → (∀ g ∈ rest, p ∉ g.inputs) →
    (rest.map (redirG p j)).foldl step (acc.eraseIdx p) = (rest.foldl step acc).eraseIdx p := by
  intro rest
  induction rest with
  | nil => intro acc _ _; simp
  | cons g rest ih =>
    intro acc hp hno
    simp only [List.map_cons, List.foldl_cons]
    have hstep : step (acc.eraseIdx p) (redirG p j g) = (step acc g).eraseIdx p := by
      unfold step redirG
      rw [eraseIdx_snoc _ _ _ hp]
      congr 2
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hne : i ≠ p := fun h => hno g (by simp) (h ▸ hi)
      exact getD_eraseIdx_ne acc p j i hne
    rw [hstep]
    apply ih
    · unfold step; simp; omega
    · intro g' hg'; exact hno g' (by simp [hg'])

theorem val_dropDead {n : ℕ} (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hno : ∀ g ∈ gates, (n + k) ∉ g.inputs) (x : Fin n → Bool) (i : ℕ) (hi : i ≠ n + k) :
    val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i := by
  have hsplit : gates = gates.take k ++ gates[k] :: gates.drop (k + 1) := by simp
  set A := gates.take k with hA
  set B := gates.drop (k + 1) with hB
  set g := gates[k] with hg
  have hAl : A.length = k := by rw [hA]; simp; omega
  set acc0 := step (A.foldl step (List.ofFn x)) g with hacc0
  have hlA : (A.foldl step (List.ofFn x)).length = n + k := by
    rw [fold_length]; simp [hAl]
  have hl0 : acc0.length = n + k + 1 := by rw [hacc0, step_length, hlA]
  have hfull : gates.foldl step (List.ofFn x) = B.foldl step acc0 := by
    conv_lhs => rw [hsplit]
    simp [List.foldl_append, hacc0]
  have herase : acc0.eraseIdx (n + k) = A.foldl step (List.ofFn x) := by
    rw [hacc0, ← hlA]; exact step_erase _ _
  have hnoB : ∀ g' ∈ B, (n + k) ∉ g'.inputs := fun g' hg' => hno g' (List.mem_of_mem_drop hg')
  have hdrop : (dropGate gates k j n).foldl step (List.ofFn x) =
      (B.foldl step acc0).eraseIdx (n + k) := by
    unfold dropGate
    rw [List.foldl_append, ← herase]
    exact fold_redir_dead (n + k) j B acc0 (by omega) hnoB
  unfold val
  rw [hdrop, hfull]
  exact getD_eraseIdx_ne _ _ _ _ hi

/-! ## Generalised charging hypothesis -/

/-- THE ISOLATED HYPOTHESIS.  A family of zero sets `Q w ⊇ S w` such that the (unique) NOT gate
(and every other gate) is `Good` at the zero point `Zof (Q w)`, and the sets `D_w` of "counted
wires" (false at `Zof (Q w)`, true at two distinct `eof u`, `eof v`, `u v ∈ S w`) satisfy
`∑_w |D_w| ≤ #gates`. -/
def ChargeOK {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧ (∀ w, Good (Q w) gates) ∧
    ∑ w, (D (Q w) (S w) gates).card ≤ gates.length

theorem val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : n + gs.length ≤ j) : val gs x j = false := by
  unfold val
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [fold_length]; simp; omega)]
  rfl

theorem inv_mem {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) (i : ℕ)
    (u : Fin n) (hz : val gs (Zof Q) i = false) (hu : val gs (eof u) i = true) : u ∈ Q := by
  obtain ⟨l, hinv, -⟩ := main_inv Q ∅ gs hgood
  exact (hinv i u u hz hu hu).1

theorem zero_of_sub {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hSQ : ∀ w, S w ⊆ Q w) (w : Fin m) : val gates (Zof (Q w)) (out w) = false := by
  rw [hev, decide_eq_false_iff_not]
  rintro ⟨x, hx, hx'⟩
  simp [Zof, hSQ w hx] at hx'

theorem eof_true {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (w : Fin m) (u : Fin n) (hu : u ∈ S w) : val gates (eof u) (out w) = true := by
  rw [hev]
  simp only [decide_eq_true_eq]
  exact ⟨u, hu, by simp [eof]⟩

/-- Main conditional step: the charging hypothesis gives the bound. -/
theorem L951_core {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hc : ChargeOK S gates) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨Q, hSQ, hgood, hsum⟩ := hc
  choose l hinv hcard using fun o => main_inv (Q o) (S o) gates (hgood o)
  have hbound : ∀ w, (S w).card - 1 ≤ (D (Q w) (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (zero_of_sub S Q gates out hev hSQ w)
        (eof_true S gates out hev w u hu) (eof_true S gates out hev w v hv)).2 hu hv
    have := hcard w
    omega
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, (D (Q w) (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ ≤ gates.length := hsum

/-! ## Cone-restricted charging: gates outside a read-closed set `K` become constants -/

def mask (K : Finset ℕ) (gs : List Gate) : List Gate :=
  gs.mapIdx fun k g => if k ∈ K then g else ⟨GateOp.or, []⟩

theorem mask_snoc (K : Finset ℕ) (gs : List Gate) (g : Gate) :
    mask K (gs ++ [g]) = mask K gs ++ [if gs.length ∈ K then g else ⟨GateOp.or, []⟩] := by
  simp [mask, List.mapIdx_append]

theorem mask_length (K : Finset ℕ) (gs : List Gate) : (mask K gs).length = gs.length := by
  simp [mask]

theorem mask_range (gs : List Gate) (L : ℕ) (hL : gs.length ≤ L) :
    mask (Finset.range L) gs = gs := by
  induction gs using List.reverseRecOn with
  | nil => simp [mask]
  | append_singleton gs g ih =>
    rw [mask_snoc, ih (by simp at hL; omega)]
    have : gs.length ∈ Finset.range L := by simp at hL ⊢; omega
    simp [this]

/-- `K` is closed under reads (up to wire `n + L`). -/
def ReadClosed (n L : ℕ) (K : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), k ∈ K → ∀ i ∈ (gs[k]'hk).inputs, n ≤ i → i < n + L → i - n ∈ K

theorem val_mask {n : ℕ} (K : Finset ℕ) (L : ℕ) (x : Fin n → Bool) :
    ∀ gs : List Gate, gs.length ≤ L → ReadClosed n L K gs →
      ∀ i, (i < n ∨ i - n ∈ K ∨ n + gs.length ≤ i) → val (mask K gs) x i = val gs x i := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ i _
    simp [mask]
  | append_singleton gs g ih =>
    intro hL hcl i hi
    have hcl' : ReadClosed n L K gs := by
      intro k hk hkK j hj h1 h2
      have hk' : k < (gs ++ [g]).length := by simp; omega
      have := hcl k hk' hkK j (by rw [List.getElem_append_left hk]; exact hj) h1 h2
      exact this
    have ih' := ih (by simp at hL; omega) hcl'
    rw [mask_snoc, val_snoc, val_snoc, mask_length]
    split_ifs with h1 h2
    · -- the new gate is kept: same operation on the same input values
      congr 1
      apply List.map_congr_left
      intro j hj
      apply ih'
      by_cases hjn : j < n
      · exact Or.inl hjn
      · by_cases hjL : j < n + L
        · right; left
          have hk : gs.length < (gs ++ [g]).length := by simp
          have := hcl gs.length hk h2 j (by simp; exact hj) (by omega) hjL
          exact this
        · right; right
          have : (gs ++ [g]).length = gs.length + 1 := by simp
          omega
    · -- the new gate is masked: then i - n = gs.length must not be in K
      exfalso
      rcases hi with hi | hi | hi
      · omega
      · exact h2 (by rw [h1] at hi; simpa using hi)
      · simp at hi; omega
    · apply ih'
      rcases hi with hi | hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · right; right; simp at hi; omega

/-- Cone-restricted charging hypothesis: each set `w` uses a read-closed `K w` containing its
output and counts `D` in the circuit where gates outside `K w` are constants. -/
def ChargeOKc {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ (Q : Fin m → Finset (Fin n)) (K : Fin m → Finset ℕ), (∀ w, S w ⊆ Q w) ∧
    (∀ w, ReadClosed n gates.length (K w) gates) ∧
    (∀ w, out w < n ∨ out w - n ∈ K w ∨ n + gates.length ≤ out w) ∧
    (∀ w, Good (Q w) (mask (K w) gates)) ∧
    ∑ w, (D (Q w) (S w) (mask (K w) gates)).card ≤ gates.length

theorem L951_core_c {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hc : ChargeOKc S gates out) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨Q, K, hSQ, hcl, hout, hgood, hsum⟩ := hc
  have hevm : ∀ (w : Fin m) (x : Fin n → Bool),
      val (mask (K w) gates) x (out w) = decide (∃ v ∈ S w, x v = true) := by
    intro w x
    rw [val_mask (K w) gates.length x gates le_rfl (hcl w) (out w) (hout w)]
    exact hev w x
  have hbound : ∀ w, (S w).card - 1 ≤ (D (Q w) (S w) (mask (K w) gates)).card := by
    intro w
    obtain ⟨l, hinv, hcard⟩ := main_inv (Q w) (S w) (mask (K w) gates) (hgood w)
    have hz : val (mask (K w) gates) (Zof (Q w)) (out w) = false := by
      rw [hevm, decide_eq_false_iff_not]
      rintro ⟨v, hv, hv'⟩
      simp [Zof, hSQ w hv] at hv'
    have he : ∀ u ∈ S w, val (mask (K w) gates) (eof u) (out w) = true := by
      intro u hu
      rw [hevm]
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, by simp [eof]⟩
    have h1 : ((S w).image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv (out w) u v hz (he u hu) (he v hv)).2 hu hv
    omega
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, (D (Q w) (S w) (mask (K w) gates)).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ ≤ gates.length := hsum

theorem val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    val gs x (n + j) = (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => val (gs.take j) x i) := by
  have htk : gs.take (j + 1) = gs.take j ++ [gs[j]'hj] := List.take_succ_eq_append_getElem hj
  have hl : (gs.take j).length = j := by simp; omega
  have h := val_append (gs.take (j + 1)) (gs.drop (j + 1)) x (n + j)
    (by rw [htk]; simp; omega)
  rw [List.take_append_drop] at h
  rw [h, htk, val_snoc, if_pos (by rw [hl])]

theorem val_mask_out {n : ℕ} (K : Finset ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : j < gs.length) (hjK : j ∉ K) : val (mask K gs) x (n + j) = false := by
  have hj' : j < (mask K gs).length := by rw [mask_length]; exact hj
  rw [val_gate _ _ _ hj']
  have : (mask K gs)[j]'hj' = ⟨GateOp.or, []⟩ := by
    simp [mask, List.getElem_mapIdx, hjK]
  rw [this]
  simp [GateOp.eval]

theorem mem_mask {K : Finset ℕ} {gs : List Gate} {g : Gate} (h : g ∈ mask K gs) :
    ∃ (i : ℕ) (hi : i < gs.length), g = if i ∈ K then gs[i] else ⟨GateOp.or, []⟩ := by
  unfold mask at h
  obtain ⟨i, hi, hg⟩ := List.mem_mapIdx.mp h
  exact ⟨i, by simpa using hi, hg.symm⟩

/-- Masking away every NOT gate leaves only AND/OR gates, so every zero set is `Good`. -/
theorem good_mask_noNot {n : ℕ} (K : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hK : ∀ (i : ℕ) (hi : i < gs.length), i ∈ K → (gs[i]'hi).op ≠ GateOp.not)
    (Q : Finset (Fin n)) : Good Q (mask K gs) := by
  intro pre g rest hdec
  have hgm : g ∈ mask K gs := by rw [hdec]; simp
  left
  obtain ⟨i, hi, hgi⟩ := mem_mask hgm
  rw [hgi]
  split_ifs with h
  · have hm := hg (gs[i]'hi) (List.getElem_mem hi)
    rcases hm.1 with h1 | h1 | h1
    · exact ⟨Or.inl h1, hm.2⟩
    · exact ⟨Or.inr h1, hm.2⟩
    · exact absurd h1 (hK i hi h)
  · exact ⟨Or.inr rfl, by simp⟩

theorem mask_take (K : Finset ℕ) (gs : List Gate) (i : ℕ) :
    (mask K gs).take i = mask K (gs.take i) := by
  apply List.ext_getElem
  · simp [mask]
  · intro k h1 h2
    simp [mask, List.getElem_mapIdx]

theorem readClosed_take {n L : ℕ} {K : Finset ℕ} {gs : List Gate} (i : ℕ)
    (hcl : ReadClosed n L K gs) : ReadClosed n L K (gs.take i) := by
  intro k hk hkK j hj h1 h2
  have hk' : k < gs.length := by simp at hk; omega
  exact hcl k hk' hkK j (by simpa using hj) h1 h2

/-- Masking with a read-closed set keeps `Good`. -/
theorem good_mask_of_good {n : ℕ} (K : Finset ℕ) (gates : List Gate) (Q : Finset (Fin n))
    (hcl : ReadClosed n gates.length K gates) (hgood : Good Q gates) :
    Good Q (mask K gates) := by
  intro pre g rest hdec
  have hi : pre.length < gates.length := by
    have := congrArg List.length hdec; simp [mask_length] at this; omega
  have hpre : pre = mask K (gates.take pre.length) := by
    rw [← mask_take, hdec]; simp
  have hg : g = (mask K gates)[pre.length]'(by rw [mask_length]; exact hi) := by
    simp [hdec]
  have hgv : g = if pre.length ∈ K then gates[pre.length] else ⟨GateOp.or, []⟩ := by
    rw [hg]; simp [mask, List.getElem_mapIdx]
  by_cases hK : pre.length ∈ K
  · rw [if_pos hK] at hgv
    have hsplit : gates = gates.take pre.length ++ gates[pre.length] :: gates.drop (pre.length + 1) := by
      simp
    have horig := hgood _ _ _ hsplit
    have hmap : ∀ y : Fin n → Bool,
        (gates[pre.length].inputs.map fun j => val pre y j) =
          gates[pre.length].inputs.map fun j => val (gates.take pre.length) y j := by
      intro y
      apply List.map_congr_left
      intro j hj
      have e : val pre y j = val (mask K (gates.take pre.length)) y j :=
        congrArg (fun l => val l y j) hpre
      rw [e]
      apply val_mask K gates.length y (gates.take pre.length) (by simp) (readClosed_take _ hcl)
      by_cases hjn : j < n
      · exact Or.inl hjn
      · by_cases hjL : j < n + gates.length
        · exact Or.inr (Or.inl (hcl pre.length hi hK j hj (by omega) hjL))
        · right; right; simp; omega
    rw [hgv]
    rcases horig with h | h | h
    · exact Or.inl h
    · right; left; rw [hmap]; exact h
    · right; right; intro u; rw [hmap]; exact h u
  · rw [if_neg hK] at hgv
    rw [hgv]
    exact Or.inl ⟨Or.inr rfl, by simp⟩

/-- The cone of wire `o`: the intersection of all read-closed sets containing it. -/
noncomputable def coneOf (n : ℕ) (gates : List Gate) (o : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range gates.length).filter fun k => ∀ K : Finset ℕ,
    ReadClosed n gates.length K gates → (n ≤ o → o < n + gates.length → o - n ∈ K) → k ∈ K

theorem coneOf_closed (n : ℕ) (gates : List Gate) (o : ℕ) :
    ReadClosed n gates.length (coneOf n gates o) gates := by
  classical
  intro k hk hkK j hj h1 h2
  simp only [coneOf, Finset.mem_filter, Finset.mem_range] at hkK ⊢
  refine ⟨by omega, fun K hK ho => ?_⟩
  exact hK k hk (hkK.2 K hK ho) j hj h1 h2

theorem coneOf_out (n : ℕ) (gates : List Gate) (o : ℕ) :
    o < n ∨ o - n ∈ coneOf n gates o ∨ n + gates.length ≤ o := by
  classical
  by_cases h1 : o < n
  · exact Or.inl h1
  · by_cases h2 : o < n + gates.length
    · right; left
      simp only [coneOf, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, fun K _ ho => ho (by omega) h2⟩
    · right; right; omega

/-- Theorem X for cone-restricted charging. -/
theorem charge_of_pair_c {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (K : Fin m → Finset ℕ)
    (gates : List Gate) (out : Fin m → ℕ)
    (hSQ : ∀ w, S w ⊆ Q w) (hcl : ∀ w, ReadClosed n gates.length (K w) gates)
    (hout : ∀ w, out w < n ∨ out w - n ∈ K w ∨ n + gates.length ≤ out w)
    (hgood : ∀ w, Good (Q w) (mask (K w) gates))
    (hpair : ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1) :
    ChargeOKc S gates out := by
  classical
  refine ⟨Q, K, hSQ, hcl, hout, hgood, ?_⟩
  -- a counted wire of a masked circuit is a kept gate, where the mask agrees with the original
  have kept : ∀ w i, i ∈ D (Q w) (S w) (mask (K w) gates) →
      ∀ y : Fin n → Bool, val (mask (K w) gates) y i = val gates y i := by
    intro w i hi y
    simp only [D, Finset.mem_filter, Finset.mem_Ico, mask_length] at hi
    obtain ⟨⟨h1, h2⟩, -, u, -, -, -, -, hu, -⟩ := hi
    have hK : i - n ∈ K w := by
      by_contra hk
      have := val_mask_out (K w) gates (eof u) (i - n) (by omega) hk
      rw [show n + (i - n) = i by omega] at this
      rw [this] at hu
      exact absurd hu (by simp)
    exact val_mask (K w) gates.length y gates le_rfl (hcl w) i (Or.inr (Or.inl hK))
  have cross : ∀ a b : Fin m, ∀ i, i ∈ D (Q a) (S a) (mask (K a) gates) →
      i ∈ D (Q b) (S b) (mask (K b) gates) → 2 ≤ (S a ∩ Q b).card := by
    intro a b i hia hib
    have ka := kept a i hia
    have kb := kept b i hib
    simp only [D, Finset.mem_filter] at hia hib
    obtain ⟨-, -, u, v, huv, huR, hvR, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hu' : val (mask (K b) gates) (eof u) i = true := by rw [kb, ← ka]; exact hu
    have hv' : val (mask (K b) gates) (eof v) i = true := by rw [kb, ← ka]; exact hv
    have hub := inv_mem (Q b) _ (hgood b) i u hzb hu'
    have hvb := inv_mem (Q b) _ (hgood b) i v hzb hv'
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ Q b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huR, hub⟩
      · exact Finset.mem_inter.mpr ⟨hvR, hvb⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair huv] at this
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Q a) (S a) (mask (K a) gates)) (D (Q b) (S b) (mask (K b) gates)) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    have h1 := cross a b i hia hib
    have h2 := cross b a i hib hia
    rcases hpair a b hab with h | h <;> omega
  calc ∑ w, (D (Q w) (S w) (mask (K w) gates)).card
      = (Finset.univ.biUnion fun w => D (Q w) (S w) (mask (K w) gates)).card := by
        rw [Finset.card_biUnion hdisj]
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter, mask_length] at hw
        exact hw.1
    _ = gates.length := by simp

theorem chargeOKc_of {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hc : ChargeOK S gates) : ChargeOKc S gates out := by
  obtain ⟨Q, hSQ, hgood, hsum⟩ := hc
  have hm : mask (Finset.range gates.length) gates = gates := mask_range gates _ le_rfl
  refine ⟨Q, fun _ => Finset.range gates.length, hSQ, ?_, ?_, ?_, ?_⟩
  · intro w k hk _ i _ h1 h2
    simp; omega
  · intro w
    by_cases h : out w < n
    · exact Or.inl h
    · by_cases h' : out w < n + gates.length
      · right; left; simp; omega
      · right; right; omega
  · intro w; rw [hm]; exact hgood w
  · simpa [hm] using hsum

/-! ## Special case (b): every set is easy (`Good (S w) gates`) -/

theorem charge_of_good {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hgood : ∀ w, Good (S w) gates) : ChargeOK S gates := by
  classical
  refine ⟨S, fun _ => subset_rfl, hgood, ?_⟩
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false :=
    zero_of_sub S S gates out hev (fun _ => subset_rfl)
  have side : ∀ a b : Fin m, a ≠ b → ∀ i, i ∈ D (S a) (S a) gates →
      i ∈ D (S b) (S b) gates → False := by
    intro a b hab i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, huR, hvR, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hub := inv_mem (S b) gates (hgood b) i u hzb hu
    have hvb := inv_mem (S b) gates (hgood b) i v hzb hv
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huR, hub⟩
      · exact Finset.mem_inter.mpr ⟨hvR, hvb⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair huv] at this
    have := hS a b hab
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) (S a) gates) (D (S b) (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    exact side a b hab i hia hib
  calc ∑ w, (D (S w) (S w) gates).card
      = (Finset.univ.biUnion fun w => D (S w) (S w) gates).card := by
        rw [Finset.card_biUnion hdisj]
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp

/-! ## Reduction of `Good` to the NOT gates being true at the zero point -/

def NotQuiet {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ pre g rest, gs = pre ++ g :: rest → g.op = GateOp.not →
    g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true

theorem good_of_quiet {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hq : NotQuiet Q gs) : Good Q gs := by
  intro pre g rest h
  have hmem : g ∈ gs := by rw [h]; simp
  rcases (hg g hmem).1 with h1 | h1 | h1
  · exact Or.inl ⟨Or.inl h1, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr h1, (hg g hmem).2⟩
  · exact Or.inr (Or.inl (hq pre g rest h h1))

/-- Special case (a): every NOT gate reads a wire that does not exist yet (or nothing). -/
theorem notquiet_of_dangling {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate)
    (hd : ∀ pre g rest, gs = pre ++ g :: rest → g.op = GateOp.not →
      ∀ j, g.inputs.head? = some j → n + pre.length ≤ j) : NotQuiet Q gs := by
  intro pre g rest h hop
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons j r =>
    have hj := hd pre g rest h hop j (by simp [hi])
    simp [GateOp.eval, val_ge pre (Zof Q) j hj]

theorem mono_val {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    by_cases h : i < n
    · simp only [h, dite_true] at hi ⊢; exact hxy _ hi
    · simp [h] at hi
  | append_singleton gs g ih =>
    have hg' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hm => hg g' (List.mem_append_left _ hm)
    have ih' := ih hg'
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with h
    · rcases hg g (by simp) with ho | ho
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        exact fun j hj => ih' j (hi j hj)
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨j, hj, hv⟩ := hi
        exact ⟨j, hj, ih' j hv⟩
    · exact ih' i hi

def AtMostOneNot (gates : List Gate) : Prop :=
  ∀ (i1 i2 : ℕ) (h1 : i1 < gates.length) (h2 : i2 < gates.length),
    (gates[i1]'h1).op = GateOp.not → (gates[i2]'h2).op = GateOp.not → i1 = i2

theorem hU_of_ι {gates : List Gate}
    (hι : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) : AtMostOneNot gates := by
  obtain ⟨ι, hι⟩ := hι
  intro i1 i2 h1 h2 e1 e2
  obtain ⟨j1, hj1⟩ := hι ⟨i1, h1⟩ (by simpa using e1)
  obtain ⟨j2, hj2⟩ := hι ⟨i2, h2⟩ (by simpa using e2)
  have : j1 = j2 := Subsingleton.elim _ _
  subst this
  have := congrArg Fin.val (hj1.symm.trans hj2)
  simpa using this

theorem not_index {gates : List Gate} (hU : AtMostOneNot gates)
    (p1 r1 p2 r2 : List Gate) (g1 g2 : Gate) (h1 : gates = p1 ++ g1 :: r1)
    (h2 : gates = p2 ++ g2 :: r2) (hn1 : g1.op = GateOp.not) (hn2 : g2.op = GateOp.not) :
    p1.length = p2.length := by
  have l1 : p1.length < gates.length := by rw [h1]; simp
  have l2 : p2.length < gates.length := by rw [h2]; simp
  apply hU _ _ l1 l2
  · have : gates[p1.length]'l1 = g1 := by subst h1; simp
    rw [this]; exact hn1
  · have : gates[p2.length]'l2 = g2 := by subst h2; simp
    rw [this]; exact hn2

/-- If the NOT gate is false at the all-false input, it is false at every unit input, so every
zero set is `Good`. -/
theorem good_all_of_dead {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hdead : ¬ NotQuiet (Finset.univ : Finset (Fin n)) gates) (Q : Finset (Fin n)) :
    Good Q gates := by
  classical
  unfold NotQuiet at hdead
  push_neg at hdead
  obtain ⟨pre0, g0, rest0, h0, hn0, hz0⟩ := hdead
  have hz0' : g0.op.eval (g0.inputs.map fun j => val pre0 (Zof (Finset.univ : Finset (Fin n))) j)
      = false := by simpa using hz0
  -- every gate before the NOT is AND/OR
  have hpre : ∀ g' ∈ pre0, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
    intro g' hm
    obtain ⟨p1, r1, hp⟩ := List.append_of_mem hm
    have hmem : g' ∈ gates := by rw [h0]; exact List.mem_append_left _ hm
    rcases (hg g' hmem).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hl := not_index hU p1 (r1 ++ g0 :: rest0) pre0 rest0 g' g0
        (by rw [h0, hp]; simp) h0 h hn0
      have : pre0.length = p1.length + 1 + r1.length := by rw [hp]; simp; omega
      omega
  -- the NOT is false at every unit input
  have hdeadu : ∀ u : Fin n,
      g0.op.eval (g0.inputs.map fun j => val pre0 (eof u) j) = false := by
    intro u
    rw [hn0] at hz0' ⊢
    cases hin : g0.inputs with
    | nil => rw [hin] at hz0'; simp [GateOp.eval] at hz0'
    | cons j r =>
      rw [hin] at hz0'
      simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_false'] at hz0' ⊢
      exact mono_val pre0 hpre _ _ (fun c hc => by simp [Zof] at hc) j hz0'
  intro pre g rest h
  have hmem : g ∈ gates := by rw [h]; simp
  rcases (hg g hmem).1 with ho | ho | ho
  · exact Or.inl ⟨Or.inl ho, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr ho, (hg g hmem).2⟩
  · right; right
    have hl := not_index hU pre rest pre0 rest0 g g0 h h0 ho hn0
    have hh : pre ++ g :: rest = pre0 ++ g0 :: rest0 := h.symm.trans h0
    obtain ⟨hp, ht⟩ := List.append_inj hh hl
    subst hp
    have : g = g0 := (List.cons.inj ht).1
    subst this
    exact hdeadu

/-- Theorem X: enlarged zero sets `Q w ⊇ S w`, every `Q w` good, and for each pair one of the
two cross intersections has at most one point. -/
theorem charge_of_pair {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (gates : List Gate)
    (hSQ : ∀ w, S w ⊆ Q w) (hgood : ∀ w, Good (Q w) gates)
    (hpair : ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1) :
    ChargeOK S gates := by
  classical
  refine ⟨Q, hSQ, hgood, ?_⟩
  have cross : ∀ a b : Fin m, ∀ i, i ∈ D (Q a) (S a) gates → val gates (Zof (Q b)) i = false →
      2 ≤ (S a ∩ Q b).card := by
    intro a b i hia hzb
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia
    obtain ⟨-, -, u, v, huv, huR, hvR, hu, hv⟩ := hia
    have hub := inv_mem (Q b) gates (hgood b) i u hzb hu
    have hvb := inv_mem (Q b) gates (hgood b) i v hzb hv
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ Q b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huR, hub⟩
      · exact Finset.mem_inter.mpr ⟨hvR, hvb⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair huv] at this
  have side : ∀ a b : Fin m, a ≠ b → ∀ i, i ∈ D (Q a) (S a) gates →
      i ∈ D (Q b) (S b) gates → False := by
    intro a b hab i hia hib
    have hza : val gates (Zof (Q a)) i = false := by
      simp only [D, Finset.mem_filter] at hia; exact hia.2.1
    have hzb : val gates (Zof (Q b)) i = false := by
      simp only [D, Finset.mem_filter] at hib; exact hib.2.1
    have h1 := cross a b i hia hzb
    have h2 := cross b a i hib hza
    rcases hpair a b hab with h | h <;> omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Q a) (S a) gates) (D (Q b) (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    exact side a b hab i hia hib
  calc ∑ w, (D (Q w) (S w) gates).card
      = (Finset.univ.biUnion fun w => D (Q w) (S w) gates).card := by
        rw [Finset.card_biUnion hdisj]
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp

/-- At most one hard set: easy sets keep `Q = S`, the hard set takes `Q = univ`
(its zero point is the all-false input). -/
theorem charge_one_hard {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (w0 : Fin m) (heasy : ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hzero : NotQuiet (Finset.univ : Finset (Fin n)) gates) : ChargeOK S gates := by
  classical
  let Q : Fin m → Finset (Fin n) := fun w => if w = w0 then Finset.univ else S w
  refine charge_of_pair S Q gates ?_ ?_ ?_
  · intro w
    by_cases h : w = w0
    · simp [Q, h]
    · simp [Q, h]
  · intro w
    by_cases h : w = w0
    · simp only [Q, h, if_true]; exact good_of_quiet _ _ hg hzero
    · simp only [Q, h, if_false]; exact good_of_quiet _ _ hg (heasy w h)
  · intro a b hab
    by_cases hb : b = w0
    · -- b is the hard set: use S b ∩ Q a = S b ∩ S a
      right
      have ha : a ≠ w0 := fun h => hab (h.trans hb.symm)
      simp only [Q, ha, if_false]
      exact hS b a (fun h => hab h.symm)
    · -- b is easy: S a ∩ Q b = S a ∩ S b
      left
      simp only [Q, hb, if_false]
      exact hS a b hab

def constNot (b : GateOp) : Gate → Gate
  | ⟨GateOp.not, _⟩ => ⟨b, []⟩
  | g => g

/-- The hard branch, unproved: some NOT gate is false at some zero point `Zof (S w)`. -/
theorem charge_hard {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates)
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1)) : False := by
  sorry -- THE OPEN COMBINATORIAL LEMMA (charging with enlarged zero sets Q_w ⊋ S_w)

theorem charge_ok {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) 
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs) 
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1)) : ChargeOKc S gates out := by
  by_cases hq : ∀ w, NotQuiet (S w) gates
  · exact chargeOKc_of S gates out (charge_of_good S gates out hS hev fun w => good_of_quiet _ _ hg (hq w))
  · by_cases hz : NotQuiet (Finset.univ : Finset (Fin n)) gates
    · by_cases h1 : ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates
      · obtain ⟨w0, he⟩ := h1
        exact chargeOKc_of S gates out (charge_one_hard S gates hS hg w0 he hz)
      · by_cases hC : ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
            (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
            ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1
        · obtain ⟨Q, hSQ, hG, hP⟩ := hC
          exact charge_of_pair_c S Q (fun w => coneOf n gates (out w)) gates out hSQ
            (fun w => coneOf_closed n gates (out w)) (fun w => coneOf_out n gates (out w)) hG hP
        · by_cases h1N : ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
              i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates
          · exfalso
            apply hC
            classical
            obtain ⟨w0, hw0⟩ := h1N
            refine ⟨fun w => if w = w0 then Finset.univ else S w, ?_, ?_, ?_⟩
            · intro w; by_cases h : w = w0 <;> simp [h]
            · intro w
              by_cases h : w = w0
              · simp only [h, if_true]
                exact good_mask_of_good _ _ _ (coneOf_closed n gates (out w0))
                  (good_of_quiet _ _ hg hz)
              · simp only [h, if_false]
                rcases hw0 w h with hno | hq'
                · exact good_mask_noNot _ _ hg hno _
                · exact good_mask_of_good _ _ _ (coneOf_closed n gates (out w))
                    (good_of_quiet _ _ hg hq')
            · intro a b hab
              by_cases hb : b = w0
              · right
                have ha : a ≠ w0 := fun h => hab (h.trans hb.symm)
                simp only [ha, if_false]
                exact hS b a (fun h => hab h.symm)
              · left
                simp only [hb, if_false]
                exact hS a b hab
          · exact (charge_hard S h2 hS gates out hg hU hev hq hz h1 hclean hC0 hC1 hlive hC h1N hlt).elim
    · exact chargeOKc_of S gates out (charge_of_good S gates out hS hev fun w => good_all_of_dead gates hg hU hz (S w))

theorem dropGate_get (gates : List Gate) (k j n : ℕ) (hk : k < gates.length) (i : ℕ)
    (hi : i < (dropGate gates k j n).length) :
    ∃ (i0 : ℕ) (h0 : i0 < gates.length), (i < k → i0 = i) ∧ (k ≤ i → i0 = i + 1) ∧
      ((dropGate gates k j n)[i]'hi).op = (gates[i0]'h0).op ∧
      ((dropGate gates k j n)[i]'hi).inputs.length = (gates[i0]'h0).inputs.length := by
  have hlen := dropGate_length gates k j n hk
  by_cases hik : i < k
  · refine ⟨i, by omega, fun _ => rfl, fun h => absurd h (by omega), ?_, ?_⟩ <;>
      simp [dropGate, List.getElem_append_left (show i < (gates.take k).length by simp; omega)]
  · refine ⟨i + 1, by omega, fun h => absurd h hik, fun _ => rfl, ?_, ?_⟩ <;>
    · have hl : (gates.take k).length = k := by simp; omega
      have hge : ¬ i < (gates.take k).length := by rw [hl]; exact hik
      simp only [dropGate, List.getElem_append, hge, dite_false, List.getElem_map,
        List.getElem_drop, redirG, List.length_map]
      congr 2
      first
        | (rw [hl]; omega)
        | (congr 1; rw [hl]; omega)

theorem constNot_mono (b : GateOp) (hb : b = GateOp.and ∨ b = GateOp.or) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ gates.map (constNot b), (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg'
  obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg'
  have hop := (hg g0 h0).1
  have hlen := (hg g0 h0).2
  cases g0 with
  | mk op ins =>
    simp only at hop hlen
    rcases hop with rfl | rfl | rfl
    · simp [constNot, hlen]
    · simp [constNot, hlen]
    · rcases hb with rfl | rfl <;> simp [constNot]

theorem good_of_mono {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Q : Finset (Fin n)) : Good Q gs := by
  intro pre g rest h
  exact Or.inl (hm g (by rw [h]; simp))

theorem bound_const {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (b : GateOp) (hb : b = GateOp.and ∨ b = GateOp.or)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot b)) x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  have h := L951_core S (gates.map (constNot b)) out hev
    (charge_of_good S (gates.map (constNot b)) out hS hev
      (fun w => good_of_mono _ (constNot_mono b hb gates hg) (S w)))
  simpa using h

theorem bound_all : ∀ (L n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ), gates.length = L →
    (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) → AtMostOneNot gates →
    (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) →
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro n m S gates out hL h2 hS hg hU hev
  by_cases hdead : ∃ k : ℕ, k < gates.length ∧ (∀ w, out w ≠ n + k) ∧
      ∀ g ∈ gates, (n + k) ∉ g.inputs
  · obtain ⟨k, hk, hout, hno⟩ := hdead
    have hlen := dropGate_length gates k 0 n hk
    have hg' : ∀ g ∈ dropGate gates k 0 n,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
      intro g hg0
      simp only [dropGate, List.mem_append, List.mem_map] at hg0
      rcases hg0 with h | ⟨g0, h0, rfl⟩
      · exact hg g (List.mem_of_mem_take h)
      · have := hg g0 (List.mem_of_mem_drop h0)
        simpa [redirG] using this
    have hU' : AtMostOneNot (dropGate gates k 0 n) := by
      intro i1 i2 hi1 hi2 e1 e2
      obtain ⟨a1, ha1, c1, d1, o1, -⟩ := dropGate_get gates k 0 n hk i1 hi1
      obtain ⟨a2, ha2, c2, d2, o2, -⟩ := dropGate_get gates k 0 n hk i2 hi2
      have := hU a1 a2 ha1 ha2 (o1 ▸ e1) (o2 ▸ e2)
      by_cases q1 : i1 < k <;> by_cases q2 : i2 < k
      · have := c1 q1; have := c2 q2; omega
      · have := c1 q1; have := d2 (by omega); omega
      · have := d1 (by omega); have := c2 q2; omega
      · have := d1 (by omega); have := d2 (by omega); omega
    have hev' : ∀ (w : Fin m) (x : Fin n → Bool),
        val (dropGate gates k 0 n) x (redir (n + k) 0 (out w)) =
          decide (∃ v ∈ S w, x v = true) := by
      intro w x
      rw [val_dropDead gates k 0 hk hno x (out w) (hout w)]
      exact hev w x
    have := ih (dropGate gates k 0 n).length (by omega) n m S (dropGate gates k 0 n)
      (fun w => redir (n + k) 0 (out w)) rfl h2 hS hg' hU' hev'
    omega
  by_cases hc : ∃ k j : ℕ, k < gates.length ∧ j < n + k ∧
      ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j
  · obtain ⟨k, j, hk, hj, hcopy⟩ := hc
    have hlen := dropGate_length gates k j n hk
    have hg' : ∀ g ∈ dropGate gates k j n,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
      intro g hg0
      simp only [dropGate, List.mem_append, List.mem_map] at hg0
      rcases hg0 with h | ⟨g0, h0, rfl⟩
      · exact hg g (List.mem_of_mem_take h)
      · have := hg g0 (List.mem_of_mem_drop h0)
        simpa [redirG] using this
    have hU' : AtMostOneNot (dropGate gates k j n) := by
      intro i1 i2 hi1 hi2 e1 e2
      obtain ⟨a1, ha1, c1, d1, o1, -⟩ := dropGate_get gates k j n hk i1 hi1
      obtain ⟨a2, ha2, c2, d2, o2, -⟩ := dropGate_get gates k j n hk i2 hi2
      have := hU a1 a2 ha1 ha2 (o1 ▸ e1) (o2 ▸ e2)
      by_cases q1 : i1 < k <;> by_cases q2 : i2 < k
      · have := c1 q1; have := c2 q2; omega
      · have := c1 q1; have := d2 (by omega); omega
      · have := d1 (by omega); have := c2 q2; omega
      · have := d1 (by omega); have := d2 (by omega); omega
    have hev' : ∀ (w : Fin m) (x : Fin n → Bool),
        val (dropGate gates k j n) x (redir (n + k) j (out w)) =
          decide (∃ v ∈ S w, x v = true) := by
      intro w x
      rw [val_dropGate gates k j hk hj hcopy x (out w)]
      exact hev w x
    have := ih (dropGate gates k j n).length (by omega) n m S (dropGate gates k j n)
      (fun w => redir (n + k) j (out w)) rfl h2 hS hg' hU' hev'
    omega
  · have hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
        ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j :=
      fun k j hk hj h => hc ⟨k, j, hk, hj, h⟩
    by_cases hC0 : ∀ (w : Fin m) (x : Fin n → Bool),
        val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true)
    · exact bound_const S gates out GateOp.or (Or.inr rfl) hS hg hC0
    by_cases hC1 : ∀ (w : Fin m) (x : Fin n → Bool),
        val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true)
    · exact bound_const S gates out GateOp.and (Or.inl rfl) hS hg hC1
    have hlive : ∀ k : ℕ, k < gates.length →
        (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs := by
      intro k hk
      by_contra hne
      push_neg at hne
      exact hdead ⟨k, hk, hne.1, hne.2⟩
    by_contra hlt
    push_neg at hlt
    have := L951_core_c S gates out hev (charge_ok S h2 hS gates out hg hU hev hclean hC0 hC1 hlive hlt)
    omega

end PEqualNP.Outside.L_meta_951_aux

open PEqualNP.Outside.L_meta_951_aux in
theorem PEqualNP.Outside.L_meta_951 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact bound_all gates.length n m S gates out rfl h2 hS hg (hU_of_ι hι) hev
