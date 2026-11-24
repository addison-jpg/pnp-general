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
      g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true

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
    have hopl : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      rcases hg with h | h
      · exact h
      · exact absurd h hPz
    obtain ⟨hop, hlen⟩ := hopl
    have key : ∀ u, P (eof u) = true →
        u ∈ Q ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → w ∈ R → w' ∈ R → l w = l w') ∧
          (∀ w w', B w → B w' → w ∈ R → w' ∈ R → l w = l w') := by
      intro u hu
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
  · exact Or.inr (hq pre g rest h h1)

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

/-- The hard branch, unproved: some NOT gate is false at some zero point `Zof (S w)`. -/
theorem charge_hard {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hι : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates) : ChargeOK S gates := by
  sorry -- THE OPEN COMBINATORIAL LEMMA (charging with enlarged zero sets Q_w ⊋ S_w)

theorem charge_ok {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hι : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) : ChargeOK S gates := by
  by_cases hq : ∀ w, NotQuiet (S w) gates
  · exact charge_of_good S gates out hS hev fun w => good_of_quiet _ _ hg (hq w)
  · exact charge_hard S h2 hS gates out hg hι hev hq

end PEqualNP.Outside.L_meta_951_aux

open PEqualNP.Outside.L_meta_951_aux in
theorem PEqualNP.Outside.L_meta_951 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact L951_core S gates out hev (charge_ok S h2 hS gates out hg hι hev)
