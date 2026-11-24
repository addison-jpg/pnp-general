import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LemmaK
import PEqualNP.Kernel.W951Cube

/-!
# The resolution gadget (general form), and its MinCE consequences

Scaffold's "resolution gadget" (board agents/scaffold-core-sat.md 08:25, f15/HARD4.md): when a hard set
`S_w` has fewer than `d_w = |S_w| - 1` class wires, the missing merges come from an AND gate whose two
inputs are both "polluted" off `S_w`. The STRICT shape `(A ∨ y) ∧ (A ∨ ¬y)` with `y = h` restricted to
`x_S = 0` is false in general (referee dwV8p, REPORT2.md §2: cxstar5, cfgI, ...). This file proves the
GENERAL form, for every circuit (no minimality, any number of NOT gates for the count):

* `Clean Q gs c` : wire `c` is below `OR Q` (false on the cube `{x | x|_Q = 0}`).
* `ResAt Q gs k` : gate `k` is clean and is either a NOT gate or a *resolution AND* `a ∧ b` whose two
  inputs are both NOT clean (each is true somewhere on the cube, so `a ∧ b = 0` on the cube although
  `a, b ≠ 0` there: "`(A ∨ p) ∧ (A ∨ q)` with `p ∧ q = 0` off `Q`").
* **`gadget_count`** (union-find on units over clean wires): for a wire computing `OR Q`,
  `|Q| ≤ 1 + |Dr Q| + ∑_{k resolution} (|units_Q(k)| - 2)`.
  Theorem E (`easy_card`) is the special case without resolution gates.
* `gadget_exists` : `|Dr Q| + 1 < |Q|` ⇒ a resolution gate with at least 3 units of `Q`.
* `resAt_and` : with at most one NOT, such a gate is an AND (a clean NOT wire has no unit).
* `res_polluted` : one of the two inputs `t` of a resolution AND is true at a cube point where its
  `C0` value (NOT := false) is false: it is true there only thanks to the NOT ("¬h-polluted").
* **`MinCE.gadget`** : in a minimal counterexample, `(base - s) + 1 ≤ ∑_w excess_w` (so `≥ 2`), and
  some hard set `w` with `|Dr (S w)| < d_w` has a resolution AND gate with `≥ 3` units of `S w`, whose
  inputs are both unclean and one of which is NOT-polluted on the cube.

Strict forms that are only conjectured are stated as `Prop`s (`StrictGadget`, `PartialOrGadget`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Kernel

/-- Wire `c` is below `OR Q`: false on the cube `x|_Q = 0`. (`DrP Q gs c` is `Clean Q gs c` plus two
units.) -/
def Clean {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (c : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val gs x c = true → ∃ v ∈ Q, x v = true

/-- The units of `Q` on which wire `c` is true. -/
noncomputable def unitsIn {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (c : ℕ) : Finset (Fin n) :=
  Q.filter fun u => val gs (eof u) c = true

/-- Gate `k` is an uncovered clean gate: clean, and a NOT gate or a resolution AND (two inputs, both
not clean in the prefix the gate reads). -/
def ResAt {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (k : ℕ) : Prop :=
  ∃ hk : k < gs.length, Clean Q gs (n + k) ∧
    ((gs[k]'hk).op = GateOp.not ∨ ((gs[k]'hk).op = GateOp.and ∧ ∃ a b, (gs[k]'hk).inputs = [a, b] ∧
      ¬ Clean Q (gs.take k) a ∧ ¬ Clean Q (gs.take k) b))

open Classical in
/-- The excess of the resolution gates: `∑_k (|units| - 2)` over the `ResAt` gates. -/
noncomputable def resExcess {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : ℕ :=
  ∑ k ∈ Finset.range gs.length, if ResAt Q gs k then (unitsIn Q gs (n + k)).card - 2 else 0

/-- Invariant of the union-find run: the units of a clean wire carry one label. -/
def GInv {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ c, Clean Q gs c → ∀ u ∈ Q, ∀ v ∈ Q, val gs (eof u) c = true → val gs (eof v) c = true →
    l u = l v

section Snoc

variable {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (g : Gate)

theorem val_snoc_old (x : Fin n → Bool) (i : ℕ) (hi : i ≠ n + gs.length) :
    val (gs ++ [g]) x i = val gs x i := by
  rw [val_snoc]; simp [hi]

theorem val_snoc_new (x : Fin n → Bool) :
    val (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map fun j => val gs x j) := by
  rw [val_snoc]; simp

theorem clean_snoc_old (i : ℕ) (hi : i ≠ n + gs.length) :
    Clean Q (gs ++ [g]) i ↔ Clean Q gs i := by
  unfold Clean
  constructor
  · intro h x hx; exact h x (by rw [val_snoc_old gs g x i hi]; exact hx)
  · intro h x hx; exact h x (by rw [← val_snoc_old gs g x i hi]; exact hx)

theorem unitsIn_snoc_old (i : ℕ) (hi : i ≠ n + gs.length) :
    unitsIn Q (gs ++ [g]) i = unitsIn Q gs i := by
  unfold unitsIn
  congr 1
  funext u
  rw [val_snoc_old gs g _ i hi]

theorem resAt_snoc_old (k : ℕ) (hk : k < gs.length) :
    ResAt Q (gs ++ [g]) k ↔ ResAt Q gs k := by
  have hk' : k < (gs ++ [g]).length := by simp; omega
  have hget : (gs ++ [g])[k]'hk' = gs[k]'hk := List.getElem_append_left hk
  have htake : (gs ++ [g]).take k = gs.take k := List.take_append_of_le_length (by omega)
  have hc := clean_snoc_old Q gs g (n + k) (by omega)
  unfold ResAt
  constructor
  · rintro ⟨_, h1, h2⟩
    rw [hget, htake] at h2
    exact ⟨hk, hc.mp h1, h2⟩
  · rintro ⟨_, h1, h2⟩
    refine ⟨hk', hc.mpr h1, ?_⟩
    rw [hget, htake]
    exact h2

theorem resAt_snoc_new :
    ResAt Q (gs ++ [g]) gs.length ↔ Clean Q (gs ++ [g]) (n + gs.length) ∧
      (g.op = GateOp.not ∨ (g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧
        ¬ Clean Q gs a ∧ ¬ Clean Q gs b)) := by
  have hk' : gs.length < (gs ++ [g]).length := by simp
  have hget : (gs ++ [g])[gs.length]'hk' = g := by simp
  have htake : (gs ++ [g]).take gs.length = gs := by simp
  unfold ResAt
  constructor
  · rintro ⟨_, h1, h2⟩
    rw [hget, htake] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hk', h1, ?_⟩
    rw [hget, htake]
    exact h2

open Classical in
theorem resExcess_snoc :
    resExcess Q (gs ++ [g]) = resExcess Q gs +
      (if ResAt Q (gs ++ [g]) gs.length then
        (unitsIn Q (gs ++ [g]) (n + gs.length)).card - 2 else 0) := by
  unfold resExcess
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [unitsIn_snoc_old Q gs g (n + k) (by omega)]
  simp only [resAt_snoc_old Q gs g k hk']

open Classical in
theorem dr_snoc_le :
    (Dr Q gs).card + (if DrP Q (gs ++ [g]) (n + gs.length) then 1 else 0) ≤
      (Dr Q (gs ++ [g])).card := by
  classical
  have hsub : Dr Q gs ⊆ Dr Q (gs ++ [g]) := by
    intro c hc
    simp only [Dr, Finset.mem_filter, Finset.mem_Ico] at hc ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have hne : c ≠ n + gs.length := by omega
    refine ⟨⟨h1, by simp; omega⟩, ?_⟩
    have hv : ∀ x : Fin n → Bool, val (gs ++ [g]) x c = val gs x c :=
      fun x => val_snoc_old gs g x c hne
    unfold DrP at h3 ⊢
    simp only [hv]
    exact h3
  split_ifs with hd
  · have hnot : n + gs.length ∉ Dr Q gs := by
      simp [Dr, Finset.mem_filter, Finset.mem_Ico]
    have hins : insert (n + gs.length) (Dr Q gs) ⊆ Dr Q (gs ++ [g]) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · simp only [Dr, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by simp⟩, hd⟩
      · exact hsub hc
    have := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hnot] at this
    exact this
  · simpa using Finset.card_le_card hsub

end Snoc

/-- Labels on a set whose members share a label: at most one label. -/
theorem image_card_le_one {n : ℕ} (A : Finset (Fin n)) (l : Fin n → Fin n)
    (h : ∀ u ∈ A, ∀ v ∈ A, l u = l v) : (A.image l).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  exact h u hu v hv

/-- Collapsing the labels in `T ⊆ Q.image l` onto one label `l u0 ∈ T` loses at most `|T| - 1`
classes. -/
theorem collapse_card {n : ℕ} (Q : Finset (Fin n)) (l : Fin n → Fin n) (T : Finset (Fin n))
    (hT : T ⊆ Q.image l) (u0 : Fin n) (hu0 : u0 ∈ Q) (hl0 : l u0 ∈ T) :
    (Q.image l).card + 1 ≤
      (Q.image fun u => if l u ∈ T then l u0 else l u).card + T.card := by
  classical
  set l' : Fin n → Fin n := fun u => if l u ∈ T then l u0 else l u
  have hsub : insert (l u0) (Q.image l \ T) ⊆ Q.image l' := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.mem_image.mpr ⟨u0, hu0, by simp [l']⟩
    · obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.mp ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht1
      exact Finset.mem_image.mpr ⟨u, hu, by simp [l', ht2]⟩
  have hnm : l u0 ∉ Q.image l \ T := fun h => (Finset.mem_sdiff.mp h).2 hl0
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnm] at h1
  have h2 : (Q.image l).card ≤ (Q.image l \ T).card + T.card := by
    have := Finset.card_sdiff_add_card_eq_card hT
    omega
  omega

/-- The union-find run over clean wires: one label per clean wire, and the number of classes drops
by at most one per `Dr` wire, plus `|units| - 2` per resolution gate. -/
theorem gadget_run {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, GInv Q gs l ∧
      Q.card ≤ (Q.image l).card + (Dr Q gs).card + resExcess Q gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, ?_⟩
    · intro c _ u _ v _ hu hv
      rw [val_nil] at hu hv
      split_ifs at hu hv with hc
      · simp only [eof, decide_eq_true_eq] at hu hv
        exact hu.symm.trans hv
    · simp [Dr, resExcess]
  | append_singleton gs g ih =>
    have hg' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2 := fun g' hm => hg g' (by simp [hm])
    have hgg := hg g (by simp)
    obtain ⟨l, hinv, hcnt⟩ := ih hg'
    have hDr := dr_snoc_le Q gs g
    have hEx := resExcess_snoc Q gs g
    set N := n + gs.length with hN
    -- old wires keep their label property
    have hold : ∀ c, c ≠ N → Clean Q (gs ++ [g]) c → ∀ u ∈ Q, ∀ v ∈ Q,
        val (gs ++ [g]) (eof u) c = true → val (gs ++ [g]) (eof v) c = true → l u = l v := by
      intro c hc hcl u hu v hv h1 h2
      rw [val_snoc_old gs g _ c hc] at h1 h2
      exact hinv c ((clean_snoc_old Q gs g c hc).mp hcl) u hu v hv h1 h2
    by_cases hcl : Clean Q (gs ++ [g]) N
    swap
    · refine ⟨l, fun c hc u hu v hv h1 h2 => ?_, ?_⟩
      · by_cases hcN : c = N
        · exact absurd (hcN ▸ hc) hcl
        · exact hold c hcN hc u hu v hv h1 h2
      · split_ifs at hDr hEx <;> omega
    set U := unitsIn Q (gs ++ [g]) N with hU
    set T := U.image l with hT
    have hUQ : U ⊆ Q := Finset.filter_subset _ _
    have hTsub : T ⊆ Q.image l := Finset.image_subset_image hUQ
    -- the cost bound
    have hcost : T.card ≤ 1 + (if DrP Q (gs ++ [g]) N then 1 else 0) +
        (if ResAt Q (gs ++ [g]) gs.length then U.card - 2 else 0) := by
      have hTU : T.card ≤ U.card := Finset.card_image_le
      by_cases hU2 : U.card ≤ 1
      · omega
      push Not at hU2
      have hdr : DrP Q (gs ++ [g]) N := by
        obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp hU2
        simp only [hU, unitsIn, Finset.mem_filter] at hu hu'
        exact ⟨hcl, u, hu.1, u', hu'.1, hne, hu.2, hu'.2⟩
      simp only [hdr, ↓reduceIte]
      by_cases hres : ResAt Q (gs ++ [g]) gs.length
      · simp only [hres, ↓reduceIte]; omega
      simp only [hres, ↓reduceIte]
      rw [resAt_snoc_new] at hres
      have hres' : ¬ (g.op = GateOp.not ∨ (g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧
          ¬ Clean Q gs a ∧ ¬ Clean Q gs b)) := fun h => hres ⟨hcl, h⟩
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hgg.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (Or.inl h) hres'
      have hval : ∀ x, val (gs ++ [g]) x N = g.op.eval (g.inputs.map fun j => val gs x j) :=
        fun x => val_snoc_new gs g x
      -- membership in U
      have hmemU : ∀ u, u ∈ U ↔ u ∈ Q ∧ g.op.eval (g.inputs.map fun j => val gs (eof u) j) = true := by
        intro u
        simp only [hU, unitsIn, Finset.mem_filter, hval]
      -- a wire whose units contain U and that is clean in gs: one class
      have one_class : ∀ a, Clean Q gs a → (∀ u ∈ U, val gs (eof u) a = true) → T.card ≤ 1 := by
        intro a ha hsub
        apply image_card_le_one
        intro u hu v hv
        have hu' := hsub u hu
        have hv' := hsub v hv
        exact hinv a ha u (hUQ hu) v (hUQ hv) hu' hv'
      rcases GateShape.and_or_shape g hop hgg.2 (fun _ => false) with
        ⟨ho, hi, -⟩ | ⟨ho, hi, -⟩ | ⟨a, hi, -⟩ | ⟨ho, a, b, hi, -⟩ | ⟨ho, a, b, hi, -⟩
      · -- AND of nothing: constantly true, not clean
        exfalso
        obtain ⟨v, -, hv⟩ := hcl (fun _ => false) (by rw [hval]; simp [hi, ho, GateOp.eval])
        exact absurd hv (by simp)
      · -- OR of nothing: no unit
        exfalso
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
        have := ((hmemU u).mp hu).2
        simp [hi, ho, GateOp.eval] at this
      · -- copy of `a`
        have hcp : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = val gs x a := by
          intro x
          rw [hval]
          rcases hop with ho | ho <;> simp [hi, ho, GateOp.eval]
        have ha : Clean Q gs a := fun x hx => hcl x (by rw [hcp]; exact hx)
        have := one_class a ha fun u hu => by
          have := ((hmemU u).mp hu).2
          rcases hop with ho | ho <;> simpa [hi, ho, GateOp.eval] using this
        omega
      · -- AND of `a, b` with a clean input
        have hab : Clean Q gs a ∨ Clean Q gs b := by
          by_contra hno
          push Not at hno
          exact hres' (Or.inr ⟨ho, a, b, hi, hno.1, hno.2⟩)
        have hv : ∀ u ∈ U, val gs (eof u) a = true ∧ val gs (eof u) b = true := by
          intro u hu
          have := ((hmemU u).mp hu).2
          simpa [hi, ho, GateOp.eval] using this
        rcases hab with ha | hb
        · have := one_class a ha fun u hu => (hv u hu).1
          omega
        · have := one_class b hb fun u hu => (hv u hu).2
          omega
      · -- OR of `a, b`: both clean, two classes
        have hc2 : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = (val gs x a || val gs x b) := by
          intro x
          rw [hval]
          simp [hi, ho, GateOp.eval]
        have ha : Clean Q gs a := fun x hx => hcl x (by rw [hc2, hx]; rfl)
        have hb : Clean Q gs b := fun x hx => hcl x (by rw [hc2, hx]; simp)
        let Ua := U.filter fun u => val gs (eof u) a = true
        let Ub := U.filter fun u => val gs (eof u) b = true
        have hUab : U ⊆ Ua ∪ Ub := by
          intro u hu
          have := ((hmemU u).mp hu).2
          simp only [hi, ho, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, Bool.or_false, id] at this
          simp only [Finset.mem_union, Finset.mem_filter, Ua, Ub]
          cases h1 : val gs (eof u) a
          · rw [h1, Bool.false_or] at this; exact Or.inr ⟨hu, this⟩
          · exact Or.inl ⟨hu, rfl⟩
        have hla : (Ua.image l).card ≤ 1 := image_card_le_one _ _ fun u hu v hv => by
          simp only [Ua, Finset.mem_filter] at hu hv
          exact hinv a ha u (hUQ hu.1) v (hUQ hv.1) hu.2 hv.2
        have hlb : (Ub.image l).card ≤ 1 := image_card_le_one _ _ fun u hu v hv => by
          simp only [Ub, Finset.mem_filter] at hu hv
          exact hinv b hb u (hUQ hu.1) v (hUQ hv.1) hu.2 hv.2
        have hTs : T ⊆ Ua.image l ∪ Ub.image l := by
          rw [← Finset.image_union]
          exact Finset.image_subset_image hUab
        have := (Finset.card_le_card hTs).trans (Finset.card_union_le _ _)
        omega
    -- the new labelling
    by_cases hne : U.Nonempty
    · obtain ⟨u0, hu0⟩ := hne
      have hl0 : l u0 ∈ T := Finset.mem_image_of_mem l hu0
      refine ⟨fun u => if l u ∈ T then l u0 else l u, ?_, ?_⟩
      · intro c hc u hu v hv h1 h2
        by_cases hcN : c = N
        · subst hcN
          have hu' : l u ∈ T := Finset.mem_image_of_mem l
            (by simp only [hU, unitsIn, Finset.mem_filter]; exact ⟨hu, h1⟩)
          have hv' : l v ∈ T := Finset.mem_image_of_mem l
            (by simp only [hU, unitsIn, Finset.mem_filter]; exact ⟨hv, h2⟩)
          simp only [hu', hv', ↓reduceIte]
        · have := hold c hcN hc u hu v hv h1 h2
          simp only [this]
      · have hcol := collapse_card Q l T hTsub u0 (hUQ hu0) hl0
        split_ifs at hDr hEx hcost <;> omega
    · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      refine ⟨l, ?_, ?_⟩
      · intro c hc u hu v hv h1 h2
        by_cases hcN : c = N
        · subst hcN
          have : u ∈ U := by simp only [hU, unitsIn, Finset.mem_filter]; exact ⟨hu, h1⟩
          rw [hU0] at this
          simp at this
        · exact hold c hcN hc u hu v hv h1 h2
      · split_ifs at hDr hEx <;> omega

/-- **Gadget count.** For any circuit with AND/OR/NOT gates of fan-in `≤ 2` and a wire `o` computing
`OR Q`: `|Q| ≤ 1 + |Dr Q| + ∑_{resolution gates k} (|units_Q(k)| - 2)`. -/
theorem gadget_count {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (o : ℕ) (ho : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ Q, x v = true)) :
    Q.card ≤ 1 + (Dr Q gates).card + resExcess Q gates := by
  obtain ⟨l, hinv, hcnt⟩ := gadget_run Q gates hg
  have hcl : Clean Q gates o := fun x hx => by rw [ho] at hx; simpa using hx
  have hun : ∀ u ∈ Q, val gates (eof u) o = true := fun u hu => by
    rw [ho]; simpa using ⟨u, hu, eof_self3 u⟩
  have h1 := image_card_le_one Q l fun u hu v hv =>
    hinv o hcl u hu v hv (hun u hu) (hun v hv)
  omega

/-- A deficit of `Dr` wires forces a resolution gate with at least three units. -/
theorem gadget_exists {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (o : ℕ) (ho : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ Q, x v = true))
    (hdef : (Dr Q gates).card + 1 < Q.card) :
    ∃ k, ResAt Q gates k ∧ 3 ≤ (unitsIn Q gates (n + k)).card := by
  classical
  have h := gadget_count Q gates hg o ho
  have hpos : resExcess Q gates ≠ 0 := by omega
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  by_cases hr : ResAt Q gates k
  · simp only [hr, ↓reduceIte] at hk
    exact ⟨k, hr, by omega⟩
  · simp only [hr, ↓reduceIte] at hk
    exact absurd rfl hk

/-- With at most one NOT, a resolution gate with a unit is a resolution AND: a clean NOT wire is
antitone and false at `0`, hence has no unit. -/
theorem resAt_and {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (k : ℕ) (hr : ResAt Q gates k) (hu : 1 ≤ (unitsIn Q gates (n + k)).card) :
    ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.and ∧ ∃ a b,
      (gates[k]'hk).inputs = [a, b] ∧
      ¬ Clean Q (gates.take k) a ∧ ¬ Clean Q (gates.take k) b := by
  obtain ⟨hk, hcl, hor⟩ := hr
  refine ⟨hk, ?_⟩
  rcases hor with hn | h
  · exfalso
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (unitsIn Q gates (n + k)).card)
    simp only [unitsIn, Finset.mem_filter] at hu
    have h0 := notWire_antitone gates hg hU (n + k) (mem_notWires gates k hk hn)
      (fun _ => false) (eof u) (by simp) hu.2
    obtain ⟨v, -, hv⟩ := hcl _ h0
    exact absurd hv (by simp)
  · exact h

/-- **Pollution.** In a resolution AND `a ∧ b` (clean, both inputs unclean): the inputs are
disjoint on the cube `x|_Q = 0`, each is true somewhere on it, and one of them is true at a cube point
where its `C0` value (every NOT := false) is false. -/
theorem res_polluted {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gates.length) (hand : (gates[k]'hk).op = GateOp.and) (a b : ℕ)
    (hin : (gates[k]'hk).inputs = [a, b]) (hcl : Clean Q gates (n + k))
    (ha : ¬ Clean Q (gates.take k) a) (hb : ¬ Clean Q (gates.take k) b) :
    (∀ x : Fin n → Bool, (∀ v ∈ Q, x v = false) →
        ¬ (val (gates.take k) x a = true ∧ val (gates.take k) x b = true)) ∧
    (∃ x : Fin n → Bool, (∀ v ∈ Q, x v = false) ∧ val (gates.take k) x a = true) ∧
    (∃ x : Fin n → Bool, (∀ v ∈ Q, x v = false) ∧ val (gates.take k) x b = true) ∧
    ∃ t ∈ [a, b], ∃ x : Fin n → Bool, (∀ v ∈ Q, x v = false) ∧
      val (gates.take k) x t = true ∧ val (C0 (gates.take k)) x t = false := by
  have hcube : ∀ x : Fin n → Bool, (∀ v ∈ Q, x v = false) →
      ¬ (val (gates.take k) x a = true ∧ val (gates.take k) x b = true) := by
    rintro x hx ⟨h1, h2⟩
    have : val gates x (n + k) = true := by
      rw [val_gate gates x k hk, hin, hand]
      simp [GateOp.eval, h1, h2]
    obtain ⟨v, hv, hxv⟩ := hcl x this
    rw [hx v hv] at hxv
    exact absurd hxv (by simp)
  have unc : ∀ t, ¬ Clean Q (gates.take k) t →
      ∃ x : Fin n → Bool, (∀ v ∈ Q, x v = false) ∧ val (gates.take k) x t = true := by
    intro t ht
    unfold Clean at ht
    push Not at ht
    obtain ⟨x, hx, hno⟩ := ht
    exact ⟨x, fun v hv => by
      cases h : x v
      · rfl
      · exact absurd h (by simp [hno v hv]), hx⟩
  obtain ⟨xa, hxa, hva⟩ := unc a ha
  obtain ⟨xb, hxb, hvb⟩ := unc b hb
  refine ⟨hcube, ⟨xa, hxa, hva⟩, ⟨xb, hxb, hvb⟩, ?_⟩
  by_contra hno
  push Not at hno
  have hgk : ∀ g ∈ gates.take k, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := fun g hm => hg g (List.mem_of_mem_take hm)
  have hmono : ∀ g ∈ C0 (gates.take k), g.op = GateOp.and ∨ g.op = GateOp.or := fun g hm =>
    (constNot_mono GateOp.or (Or.inr rfl) (gates.take k) hgk g hm).1
  let xs : Fin n → Bool := fun i => xa i || xb i
  have hxs : ∀ v ∈ Q, xs v = false := fun v hv => by simp [xs, hxa v hv, hxb v hv]
  have up : ∀ t (y : Fin n → Bool), (∀ i, y i = true → xs i = true) →
      val (C0 (gates.take k)) y t = true → val (gates.take k) xs t = true := by
    intro t y hy h0
    have := mono_val (C0 (gates.take k)) hmono y xs hy t h0
    exact ((sandwich (gates.take k) (fun g hm => (hgk g hm).1) xs) t).1 this
  have ha0 : val (C0 (gates.take k)) xa a = true := by
    cases h : val (C0 (gates.take k)) xa a
    · exact absurd (hno a (by simp) xa hxa hva) (by rw [h]; simp)
    · rfl
  have hb0 : val (C0 (gates.take k)) xb b = true := by
    cases h : val (C0 (gates.take k)) xb b
    · exact absurd (hno b (by simp) xb hxb hvb) (by rw [h]; simp)
    · rfl
  exact hcube xs hxs ⟨up a xa (fun i h => by simp [xs, h]) ha0,
    up b xb (fun i h => by simp [xs, h]) hb0⟩

/-! ## Minimal counterexamples -/

/-- The `Dr` classes of distinct sets are disjoint and avoid the NOT wires, so
`#NOT + ∑_w |Dr (S w)| ≤ s` (any correct circuit with at most one NOT). -/
theorem notWires_add_sum_dr_le {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates) :
    (notWires n gates).card + ∑ w : Fin m, (Dr (S w) gates).card ≤ gates.length := by
  classical
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (Dr (S a) gates) (Dr (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro c hca hcb
    exact hab (sec_unique3 S h2 hS gates a b c (Or.inl (Finset.mem_filter.mp hca).2)
      (Or.inl (Finset.mem_filter.mp hcb).2))
  set C := Finset.univ.biUnion fun w => Dr (S w) gates
  have hC : ∑ w, (Dr (S w) gates).card = C.card := (Finset.card_biUnion hdisj).symm
  have hAC : Disjoint (notWires n gates) C := by
    rw [Finset.disjoint_left]
    intro c hcA hcC
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hcC
    exact notWire_not_ded S gates hg hU w c hcA (Finset.mem_filter.mp hw).2
  have hsub : notWires n gates ∪ C ⊆ Finset.Ico n (n + gates.length) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact (Finset.mem_filter.mp hc).1
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hc
      exact (Finset.mem_filter.mp hw).1
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hAC] at this
  simp at this
  omega

/-- **The resolution gadget in a minimal counterexample.**
(i) `(base - s) + 1 ≤ ∑_w resExcess (S w)`, so the resolution excess is at least `2`;
(ii) some HARD set `w` has `|Dr (S w)| < d_w` and a resolution AND gate `a ∧ b` with at least three
units of `S w`: the gate is below `OR (S w)`, `a` and `b` are both true somewhere on the cube
`x|_{S w} = 0` (never together), and one of them is true at a cube point where its `C0` value is
false. -/
theorem MinCE.gadget {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) :
    (∑ w : Fin m, ((S w).card - 1) - gates.length) + 1 ≤
        ∑ w : Fin m, resExcess (S w) gates ∧
    ∃ w : Fin m, ¬ NotQuiet (S w) gates ∧ (Dr (S w) gates).card + 1 < (S w).card ∧
      ∃ k, ∃ hk : k < gates.length, Clean (S w) gates (n + k) ∧
        3 ≤ (unitsIn (S w) gates (n + k)).card ∧
        (gates[k]'hk).op = GateOp.and ∧ ∃ a b, (gates[k]'hk).inputs = [a, b] ∧
        ¬ Clean (S w) (gates.take k) a ∧ ¬ Clean (S w) (gates.take k) b ∧
        ∃ t ∈ [a, b], ∃ x : Fin n → Bool, (∀ v ∈ S w, x v = false) ∧
          val (gates.take k) x t = true ∧ val (C0 (gates.take k)) x t = false := by
  classical
  have C := M.ce
  have hlt := C.hlt
  have hcount : ∀ w, (S w).card ≤ 1 + (Dr (S w) gates).card + resExcess (S w) gates :=
    fun w => gadget_count (S w) gates C.hg (out w) (C.hev w)
  have hsum := notWires_add_sum_dr_le S C.h2 C.hS gates C.hg C.hU
  -- there is a NOT gate
  have hnot : 1 ≤ (notWires n gates).card := by
    by_contra h0
    push Not at h0
    have hno : ∀ g ∈ gates, g.op ≠ GateOp.not := by
      intro g hgm hop
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
      have := Finset.card_pos.mpr ⟨n + p, mem_notWires gates p hp hop⟩
      omega
    have he : ∀ w, (S w).card - 1 ≤ (Dr (S w) gates).card := fun w =>
      easy_card (S w) gates (out w) C.hg
        (fun pre g rest h hop => absurd hop (hno g (by rw [h]; simp))) (C.hev w)
    have := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => he w
    omega
  refine ⟨?_, ?_⟩
  · have h1 : ∑ w : Fin m, ((S w).card - 1) ≤
        ∑ w : Fin m, ((Dr (S w) gates).card + resExcess (S w) gates) :=
      Finset.sum_le_sum fun w _ => by have := hcount w; omega
    rw [Finset.sum_add_distrib] at h1
    omega
  · have hlt' : ∑ w : Fin m, (Dr (S w) gates).card < ∑ w : Fin m, ((S w).card - 1) := by omega
    obtain ⟨w, -, hw⟩ := Finset.exists_lt_of_sum_lt hlt'
    have hdef : (Dr (S w) gates).card + 1 < (S w).card := by omega
    have hhard : ¬ NotQuiet (S w) gates := fun hq => by
      have := easy_card (S w) gates (out w) C.hg hq (C.hev w)
      omega
    obtain ⟨k, hr, h3⟩ := gadget_exists (S w) gates C.hg (out w) (C.hev w) hdef
    obtain ⟨hk, hand, a, b, hin, ha, hb⟩ := resAt_and (S w) gates C.hg C.hU k hr (by omega)
    have hcl : Clean (S w) gates (n + k) := hr.2.1
    obtain ⟨-, -, -, hpol⟩ := res_polluted (S w) gates C.hg k hk hand a b hin hcl ha hb
    exact ⟨w, hhard, hdef, k, hk, hcl, h3, hand, a, b, hin, ha, hb, hpol⟩

/-! ## Conjectured strict forms (NOT theorems; false without minimality, see STATEMENT.md) -/

/-- A resolution AND for set `Q` at gate `k` with inputs `a, b` (the shape found by `MinCE.gadget`). -/
def ResAnd {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate) (k a b : ℕ) : Prop :=
  ∃ hk : k < gates.length, Clean Q gates (n + k) ∧ (gates[k]'hk).op = GateOp.and ∧
    (gates[k]'hk).inputs = [a, b] ∧ ¬ Clean Q (gates.take k) a ∧ ¬ Clean Q (gates.take k) b

/-- CONJECTURE (scaffold's STRICT shape), meant only under a minimality hypothesis: every resolution
AND `A = a ∧ b` with at least three units has `{a, b} = {A ∨ y, A ∨ ¬y}` where `y(x) = h(x|_{Q := 0})`
and `h` is the input of the NOT gate at `p` (so `y = ¬ N(x|_{Q:=0})`).
FALSE for general circuits: referee dwV8p, cfgI set {0,1,2,3}: `(A ∨ (x7 ∧ h)) ∧ (A ∨ ¬h)`;
cxstar5: `¬x0 ∧ (x0 ∨ A)` (a Shannon split; `¬x0` is not above `A`). Not known for `MinCE`. -/
def StrictGadget {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∀ (w : Fin m) (k a b : ℕ), ResAnd (S w) gates k a b →
    3 ≤ (unitsIn (S w) gates (n + k)).card →
    ∃ p, ∃ hp : p < gates.length, (gates[p]'hp).op = GateOp.not ∧
      ((∀ x, val (gates.take k) x a = (val gates x (n + k) || !val gates (zeroOn (S w) x) (n + p)) ∧
             val (gates.take k) x b = (val gates x (n + k) || val gates (zeroOn (S w) x) (n + p))) ∨
       (∀ x, val (gates.take k) x b = (val gates x (n + k) || !val gates (zeroOn (S w) x) (n + p)) ∧
             val (gates.take k) x a = (val gates x (n + k) || val gates (zeroOn (S w) x) (n + p))))

/-- CONJECTURE ("A is a partial OR of S_w"), meant only under a minimality hypothesis: a resolution
AND with at least three units computes exactly the OR of its units.
FALSE for general circuits: n = 5, gates `x0|x2, x3|x4, ¬x0, copy, (x0|x2)|(x3|x4), AND(g9, g8), x2|g6`
(`Q = {2,3,4}`, output wire 11): gate 10 = `¬x0 ∧ (x2 ∨ x3 ∨ x4)` is a resolution AND with units
`{2,3,4}`, but it is not `x2 ∨ x3 ∨ x4`. -/
def PartialOrGadget {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∀ (w : Fin m) (k a b : ℕ), ResAnd (S w) gates k a b →
    3 ≤ (unitsIn (S w) gates (n + k)).card →
    ∀ x, val gates x (n + k) = decide (∃ u ∈ unitsIn (S w) gates (n + k), x u = true)

end PEqualNP.Outside.L_meta_951_aux
