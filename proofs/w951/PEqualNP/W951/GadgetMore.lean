import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LemmaK
import PEqualNP.Kernel.W951Cube
import PEqualNP.W951.PairLemma
import PEqualNP.W951.Peel
import PEqualNP.Kernel.W951Minimal

section Gadget

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

end Gadget

section Heredity

/-!
# Heredity (pairrule_log.md §0)

From a circuit for `F - b` (the sets `S i \ {b}`) one gets a circuit for `F` by adding one gate
`o_S := o_{S-b} ∨ x_b` per set `S ∋ b` with `|S| ≥ 2` (for `S = {b}` the output is the wire `x_b`,
no gate).  The number of added gates is `base(F) - base(F - b)` (`= deg b` when all `|S| ≥ 2`).

* `heredity_step` : one point, gate count `#{i | b ∈ S i, 2 ≤ |S i|}`.
* `base_erase`, `base_erase_deg` : `base(F) = base(F - b) + #{…}` (`= base(F - b) + deg b`).
* `heredity` : one point, all `|S i| ≥ 2`: size `t + deg b`.
* `heredity_multi` : any point set `Z`: `s + base(F - Z) = t + base(F)`.
* `bound_sdiff` : bound(F) ⇒ bound(F - Z).
* `MinCE.min_circuit`, `MinCE.heredity`, `MinCE.heredity_multi` : in a minimal counterexample,
  `s ≤ t + deg b` resp. `s + base(F - Z) ≤ t + base(F)` for every one-NOT circuit of `F - b` resp.
  `F - Z` of size `t`.

Sets that become empty carry no requirement (their outputs may be anything).  No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section heredity
variable {n m : ℕ}

/-- A wire computing the OR of a nonempty set is an existing wire. -/
theorem lt_of_ev (gates : List Gate) (T : Finset (Fin n)) (o : ℕ) (hT : T.Nonempty)
    (h : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ T, x v = true)) :
    o < n + gates.length := by
  by_contra hge
  have := h (fun _ => true)
  rw [val_ge _ _ _ (by omega)] at this
  obtain ⟨v, hv⟩ := hT
  simp at this
  exact this v hv

theorem hU_snoc (gates : List Gate) (hU : AtMostOneNot gates) (g : Gate)
    (hgn : g.op ≠ GateOp.not) : AtMostOneNot (gates ++ [g]) := by
  intro i1 i2 h1 h2 e1 e2
  have key : ∀ (i : ℕ) (h : i < (gates ++ [g]).length),
      ((gates ++ [g])[i]'h).op = GateOp.not →
      ∃ h' : i < gates.length, (gates[i]'h').op = GateOp.not := by
    intro i h e
    by_cases hi : i < gates.length
    · rw [List.getElem_append_left hi] at e
      exact ⟨hi, e⟩
    · rw [List.getElem_append_right (by omega)] at e
      simp at e
      exact absurd e hgn
  obtain ⟨h1', e1'⟩ := key i1 h1 e1
  obtain ⟨h2', e2'⟩ := key i2 h2 e2
  exact hU i1 i2 h1' h2' e1' e2'

theorem or_erase (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) (x : Fin n → Bool) :
    (decide (∃ v ∈ T.erase b, x v = true) || x b) = decide (∃ v ∈ T, x v = true) := by
  classical
  by_cases h : ∃ v ∈ T, x v = true
  · rw [decide_eq_true h]
    obtain ⟨v, hv, hx⟩ := h
    by_cases hvb : v = b
    · subst hvb; rw [hx]; simp
    · have h1 : ∃ v ∈ T.erase b, x v = true := ⟨v, Finset.mem_erase.mpr ⟨hvb, hv⟩, hx⟩
      rw [decide_eq_true h1]; rfl
  · rw [decide_eq_false h]
    have h1 : ¬ ∃ v ∈ T.erase b, x v = true := fun ⟨v, hv, hx⟩ =>
      h ⟨v, Finset.mem_of_mem_erase hv, hx⟩
    have h2 : x b = false := by
      cases hxb : x b
      · rfl
      · exact absurd ⟨b, hb, hxb⟩ h
    rw [decide_eq_false h1, h2]; rfl

/-- Heredity, one point: from a circuit for `F - b` a circuit for `F` with one more OR gate per set
`S ∋ b`, `|S| ≥ 2`. -/
theorem heredity_step (S : Fin m → Finset (Fin n)) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, ((S i).erase b).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length +
        (Finset.univ.filter fun i : Fin m => b ∈ S i ∧ 2 ≤ (S i).card).card ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  classical
  set B := Finset.univ.filter fun i : Fin m => b ∈ S i with hB
  have main : ∀ A : Finset (Fin m), A ⊆ B → ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length + (A.filter fun i : Fin m => 2 ≤ (S i).card).card ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      (∀ i ∈ A, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true)) ∧
      (∀ i ∉ A, ((S i).erase b).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ (S i).erase b, x v = true)) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨gates', out', by simp, hg, hU, by simp, fun i _ => hev i⟩
    | insert a A ha ih =>
      intro hsub
      obtain ⟨gates, out, hlen, hg1, hU1, hin, hnin⟩ :=
        ih ((Finset.subset_insert a A).trans hsub)
      have hba : b ∈ S a := by
        have := hsub (Finset.mem_insert_self a A)
        simpa [hB] using this
      by_cases hc : 2 ≤ (S a).card
      · have hne : ((S a).erase b).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hba]; omega
        have hoa := hnin a ha hne
        have hlt := lt_of_ev gates _ (out a) hne hoa
        refine ⟨gates ++ [⟨GateOp.or, [out a, (b : ℕ)]⟩],
          Function.update out a (n + gates.length), ?_, ?_, ?_, ?_, ?_⟩
        · rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem
            (fun h => ha (Finset.mem_of_mem_filter a h))]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro g hgm
          rcases List.mem_append.mp hgm with h | h
          · exact hg1 g h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨Or.inr (Or.inl rfl), by simp⟩
        · exact hU_snoc gates hU1 _ (by simp)
        · intro i hi hSi x
          by_cases hia : i = a
          · subst hia
            rw [Function.update_self, val_snoc, if_pos rfl]
            simp only [List.map_cons, List.map_nil]
            rw [hoa x, val_inp _ _ _ b.2, ← or_erase (S i) b hba x]
            simp [GateOp.eval]
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hia
            have hl := lt_of_ev gates _ (out i) hSi (hin i hiA hSi)
            rw [Function.update_of_ne hia, val_snoc, if_neg (by omega)]
            exact hin i hiA hSi x
        · intro i hi hSi x
          have hia : i ≠ a := fun e => hi (e ▸ Finset.mem_insert_self a A)
          have hiA : i ∉ A := fun h => hi (Finset.mem_insert_of_mem h)
          have hl := lt_of_ev gates _ (out i) hSi (hnin i hiA hSi)
          rw [Function.update_of_ne hia, val_snoc, if_neg (by omega)]
          exact hnin i hiA hSi x
      · refine ⟨gates, Function.update out a (b : ℕ), ?_, hg1, hU1, ?_, ?_⟩
        · rw [Finset.filter_insert, if_neg hc]; exact hlen
        · intro i hi hSi x
          by_cases hia : i = a
          · subst hia
            have hSb : S i = {b} := by
              symm
              apply Finset.eq_of_subset_of_card_le (by simpa using hba)
              simp only [Finset.card_singleton]; omega
            rw [Function.update_self, val_inp _ _ _ b.2, hSb]
            simp
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hia
            rw [Function.update_of_ne hia]
            exact hin i hiA hSi x
        · intro i hi hSi x
          have hia : i ≠ a := fun e => hi (e ▸ Finset.mem_insert_self a A)
          have hiA : i ∉ A := fun h => hi (Finset.mem_insert_of_mem h)
          rw [Function.update_of_ne hia]
          exact hnin i hiA hSi x
  obtain ⟨gates, out, hlen, hg1, hU1, hin, hnin⟩ := main B (Finset.Subset.refl _)
  refine ⟨gates, out, ?_, hg1, hU1, fun i hSi x => ?_⟩
  · rw [hlen, hB, Finset.filter_filter]
  · by_cases hi : i ∈ B
    · exact hin i hi hSi x
    · have hb : b ∉ S i := by simpa [hB] using hi
      have := hnin i hi (by rw [Finset.erase_eq_of_notMem hb]; exact hSi) x
      rw [Finset.erase_eq_of_notMem hb] at this
      exact this

/-- `base(F) = base(F - b) + #{i | b ∈ S i, 2 ≤ |S i|}`. -/
theorem base_erase (S : Fin m → Finset (Fin n)) (b : Fin n) :
    baseOf S = baseOf (fun i => (S i).erase b) +
      (Finset.univ.filter fun i : Fin m => b ∈ S i ∧ 2 ≤ (S i).card).card := by
  classical
  unfold baseOf
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  beta_reduce
  by_cases hb : b ∈ S i
  · rw [Finset.card_erase_of_mem hb]
    by_cases hc : 2 ≤ (S i).card
    · rw [if_pos ⟨hb, hc⟩]; omega
    · rw [if_neg (fun h => hc h.2)]; omega
  · rw [Finset.erase_eq_of_notMem hb, if_neg (fun h => hb h.1)]; rfl

/-- `base(F) = base(F - b) + deg b` when every set has at least two points. -/
theorem base_erase_deg (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (b : Fin n) : baseOf S = baseOf (fun i => (S i).erase b) + degOf S b := by
  rw [base_erase S b]
  unfold degOf
  congr 2
  ext i
  simp [h2 i]

/-- Heredity (§0): from a one-NOT circuit of size `t` for `F - b` a one-NOT circuit of size
`t + deg b` for `F`. -/
theorem heredity (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length + degOf S b ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ (i : Fin m) (x : Fin n → Bool), val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  obtain ⟨gates, out, hlen, hg1, hU1, hev1⟩ :=
    heredity_step S b gates' out' hg hU (fun i _ => hev i)
  refine ⟨gates, out, ?_, hg1, hU1, fun i => hev1 i (Finset.card_pos.mp (by have := h2 i; omega))⟩
  have h1 := base_erase S b
  have h2' := base_erase_deg S h2 b
  omega

/-- Heredity for a point set `Z`: from a one-NOT circuit of size `t` for `F - Z` a one-NOT circuit
for `F` of size `s` with `s + base(F - Z) = t + base(F)`. -/
theorem heredity_multi (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n)) :
    ∀ (gates' : List Gate) (out' : Fin m → ℕ),
    (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    AtMostOneNot gates' →
    (∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) →
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length + baseOf (fun i => S i \ Z) = gates'.length + baseOf S ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    intro gates' out' hg hU hev
    exact ⟨gates', out', by simp, hg, hU, fun i hi x => by simpa using hev i (by simpa using hi) x⟩
  | insert b Z hb ih =>
    intro gates' out' hg hU hev
    have hfam : ∀ i, S i \ insert b Z = (S i \ Z).erase b := fun i => Finset.sdiff_insert _ _ _
    obtain ⟨g1, o1, hlen1, hg1, hU1, hev1⟩ :=
      heredity_step (fun i => S i \ Z) b gates' out' hg hU (fun i hi x => by
        have := hev i (by rw [hfam]; exact hi) x
        rw [this]; simp only [hfam])
    obtain ⟨g2, o2, hlen2, hg2, hU2, hev2⟩ := ih g1 o1 hg1 hU1 hev1
    refine ⟨g2, o2, ?_, hg2, hU2, hev2⟩
    have hbase := base_erase (fun i => S i \ Z) b
    have : baseOf (fun i => S i \ insert b Z) = baseOf (fun i => (S i \ Z).erase b) := by
      unfold baseOf; simp only [hfam]
    omega

/-- bound(F) ⇒ bound(F - Z): if every one-NOT circuit for `F` has at least `base(F)` gates, then
every one-NOT circuit for `F - Z` has at least `base(F - Z)` gates. -/
theorem bound_sdiff (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n))
    (hF : ∀ (gates : List Gate) (out : Fin m → ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true)) → baseOf S ≤ gates.length)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) :
    baseOf (fun i => S i \ Z) ≤ gates'.length := by
  obtain ⟨gates, out, hlen, hg1, hU1, hev1⟩ := heredity_multi S Z gates' out' hg hU hev
  have := hF gates out hg1 hU1 hev1
  omega

end heredity

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- The circuit of a minimal counterexample is a minimum one-NOT circuit for its sets. -/
theorem min_circuit (M : MinCE S gates out) (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ S i, x v = true)) :
    gates.length ≤ gates'.length := by
  by_contra hlt
  push Not at hlt
  have C := M.ce
  exact M.min n m S gates' out' ⟨C.h2, C.hS, hg, hU, hev, lt_trans hlt C.hlt⟩ (Or.inl hlt)

/-- Heredity in a minimal counterexample: `s(F) + base(F - Z) ≤ s(F - Z) + base(F)` for every
one-NOT circuit of `F - Z` (so `F - Z` is short of its base by at most `σ`). -/
theorem heredity_multi (M : MinCE S gates out) (Z : Finset (Fin n))
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) :
    gates.length + baseOf (fun i => S i \ Z) ≤ gates'.length + baseOf S := by
  have C := M.ce
  obtain ⟨g1, o1, hlen, hg1, hU1, hev1⟩ :=
    PEqualNP.Outside.L_meta_951_aux.heredity_multi S Z gates' out' hg hU hev
  have := M.min_circuit g1 o1 hg1 hU1
    (fun i => hev1 i (Finset.card_pos.mp (by have := C.h2 i; omega)))
  omega

/-- Heredity in a minimal counterexample, one point: `s(F) ≤ s(F - b) + deg b`. -/
theorem heredity (M : MinCE S gates out) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    gates.length ≤ gates'.length + degOf S b := by
  have C := M.ce
  obtain ⟨g1, o1, hlen, hg1, hU1, hev1⟩ :=
    PEqualNP.Outside.L_meta_951_aux.heredity S C.h2 b gates' out' hg hU hev
  have := M.min_circuit g1 o1 hg1 hU1 hev1
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux

end Heredity

section Peel2

/-!
# Peel2: exact G1.9 for tight points, the G1.3 / G1.6 degree corollaries, and G1.3 (iii)

Source: front's `g1_fable.md` (G1.3, G1.6, G1.9).  Notation as in `PairLemma.lean` / `Peel.lean`:
`σ = base - s ≥ 1`, `V1` = points with exactly one reader, `B` = points with at least two.

* Level 1 (exact G1.9 equality case).  `MinCE.pairGate_unique` (cleanliness: at most one gate is
  `x_u ∨ x_w`), `IsPairGate.reader_left/right`, `MinCE.pairReaders_le` (the pair-gate readers of
  `x_u` are at most `p(u)`), and `MinCE.tight_exact`: for a tight `u` every pair partner `w` has
  exactly one pair gate `x_u ∨ x_w`, `#readers(u) = nonpair(u) + p(u)`, no single-reader point uses
  `u` as singleton (`Users = ∅`, in particular `kL(u) = 0`), and `nonpair(u) = l(u) - σ`
  (additively `base + nonpair(u) = s + l(u)`).
* Level 2 (G1.3 (ii) / G1.6 corollaries, from `MinCE.capacity`): `MinCE.peel_deg`,
  `MinCE.peel_deg_B` (`u ∈ B` used as singleton: `deg u ≥ 3 + σ`), `MinCE.peel_deg_V1`
  (`u ∈ V1`: `deg u ≥ 2 + σ`), `MinCE.capacity_B`, `MinCE.capacity_V1`.
* Level 3 (G1.3 (iii), two-point form).  Kernel part (restriction `x_Z := 0` for a point SET `Z`,
  the set version of `Kernel.list_restrictVar` / `restrictVar_bound`): `Kernel.zeroOn`,
  `Dag.val_restrictZero`, `deadZ`, `list_restrictZero`, `restrictZero_bound`.  W951 part: `DCZ Z`
  (gates dead under `x_Z := 0`), `MinCE.deadBoundSet` (N2 for point sets:
  `base + #DCZ(Z) ≤ s + ∑_{u ∈ Z} deg u`), `MinCE.peel_two` (G1.3 (iii), any `σ`, no tightness:
  `base + #(R_u1 ∪ R_u2) + 1 + [c ∉ R_u1 ∪ R_u2] ≤ s + deg u1 + deg u2`), `MinCE.peel_two_tight`
  (`u1, u2` tight and `σ = 1`: `c` reads `x_u1` or `x_u2`, or the gate `x_u1 ∨ x_u2` exists).
No sorry.
-/

-- The kernel part (`zeroOn`, `Dag.val_restrictZero`, `deadZ`, `list_restrictZero`,
-- `restrictZero_bound`, ...) now lives in `Kernel/W951Cube.lean`: it is the case `ρ = 0`
-- of the cube restriction.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Level 1: the exact G1.9 equality case -/

/-- A pair gate `x_u ∨ x_w` is a reader of `x_u`. -/
theorem IsPairGate.reader_left {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : k ∈ Readers u gates := by
  classical
  obtain ⟨hk, hop, hin⟩ := h
  simp only [Readers, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk, hk, Or.inl ⟨Or.inr hop, ?_⟩⟩
  rcases hin with hin | hin <;> rw [hin] <;> simp

/-- A pair gate `x_u ∨ x_w` is a reader of `x_w`. -/
theorem IsPairGate.reader_right {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : k ∈ Readers w gates := by
  classical
  obtain ⟨hk, hop, hin⟩ := h
  simp only [Readers, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk, hk, Or.inl ⟨Or.inr hop, ?_⟩⟩
  rcases hin with hin | hin <;> rw [hin] <;> simp

theorem IsPairGate.symm {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : IsPairGate gates k w u := by
  obtain ⟨hk, hop, hin⟩ := h
  exact ⟨hk, hop, hin.symm⟩

theorem pair_right_inj {n : ℕ} {u w w' : Fin n} (huw : u ≠ w)
    (h : ({u, w} : Finset (Fin n)) = {u, w'}) : w = w' := by
  have : w ∈ ({u, w'} : Finset (Fin n)) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact absurd e.symm huw
  · exact e

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- No duplicate pair gates (cleanliness): at most one gate is `x_u ∨ x_w`. -/
theorem pairGate_unique (M : MinCE S gates out) (u w : Fin n) (k k' : ℕ)
    (h : IsPairGate gates k u w) (h' : IsPairGate gates k' u w) : k = k' := by
  have key : ∀ a b : ℕ, IsPairGate gates a u w → IsPairGate gates b u w → ¬ a < b := by
    intro a b ha hb hlt
    have hbl : b < gates.length := by obtain ⟨hbl, -⟩ := hb; exact hbl
    exact M.clean b (n + a) hbl (by omega) fun x => by
      rw [val_pairGate gates b u w hb, val_pairGate gates a u w ha]
  rcases lt_trichotomy k k' with hlt | he | hlt
  · exact absurd hlt (key k k' h h')
  · exact he
  · exact absurd hlt (key k' k h' h)

open Classical in
/-- The readers of `x_u` that are pair gates `x_u ∨ x_w` of pair-sets `{u, w}` are at most `p(u)`
(one per pair-set, by cleanliness). -/
theorem pairReaders_le (M : MinCE S gates out) (u : Fin n) :
    ((Readers u gates).filter
      fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card ≤ pairDeg S u := by
  have C := M.ce
  set PS := Finset.univ.filter fun i : Fin m => u ∈ S i ∧ (S i).card = 2 with hPS
  let g : Fin m → ℕ := fun i =>
    if h : ∃ k w, S i = {u, w} ∧ IsPairGate gates k u w then h.choose else 0
  have hsub : (Readers u gates).filter
      (fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) ⊆ PS.image g := by
    intro k hk
    obtain ⟨-, w, ⟨i, hi⟩, hpg⟩ := Finset.mem_filter.mp hk
    have huw : u ≠ w := by
      intro e; have := C.h2 i; rw [hi, e] at this; simp at this
    have hex : ∃ k w, S i = {u, w} ∧ IsPairGate gates k u w := ⟨k, w, hi, hpg⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · simp only [hPS, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
      exact ⟨by simp, Finset.card_pair huw⟩
    · have hg : g i = hex.choose := by simp only [g]; rw [dif_pos hex]
      obtain ⟨w', hi', hpg'⟩ := hex.choose_spec
      have hww : w = w' := pair_right_inj huw (hi.symm.trans hi')
      rw [hg]
      exact M.pairGate_unique u w _ _ (hww ▸ hpg') hpg
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A point of some set has a gate dead under `x_u := 0`. -/
theorem dc_pos (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i) :
    1 ≤ (DC u gates).card := by
  have C := M.ce
  have hc := pair_count S gates out C.h2 C.hS C.hev C.hg u
  have hd := deg_split S C.h2 u
  have hdeg : 1 ≤ degOf S u := by
    obtain ⟨i, hi⟩ := hu
    unfold degOf
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  by_cases hp : 1 ≤ pairDeg S u
  · omega
  · have := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u (by omega)
    omega

open Classical in
/-- **G1.9, exact equality case.**  Let `u` be tight (`#readers(u) = deg u - σ`).  Then
1. every pair partner `w` (`{u, w}` a set) has exactly one pair gate `x_u ∨ x_w` (existence by
   G1.9, uniqueness by cleanliness);
2. the pair-gate readers of `x_u` are exactly `p(u)` many, and `#readers(u) = nonpair(u) + p(u)`;
3. no single-reader point uses `u` as singleton: `Users = ∅`, in particular `kL(u) = 0`;
4. `nonpair(u) = l(u) - σ`, additively `base + nonpair(u) = s + l(u)`;
5. `#readers(u) = deg u - σ` exactly, additively `s + deg u = base + #readers(u)`. -/
theorem tight_exact (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (ht : Tight S gates u) :
    (∀ (w : Fin n) (i : Fin m), S i = {u, w} → ∃! k, IsPairGate gates k u w) ∧
    ((Readers u gates).filter
      fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card = pairDeg S u ∧
    (Readers u gates).card = nonpair S gates u + pairDeg S u ∧
    Users S gates u = ∅ ∧ LineUsers S gates u = ∅ ∧
    baseOf S + nonpair S gates u = gates.length + lineDeg S u ∧
    gates.length + degOf S u = baseOf S + (Readers u gates).card := by
  have C := M.ce
  obtain ⟨heq, hnp⟩ := M.tight_readers u hu ht
  obtain ⟨-, hdb, hrp⟩ := M.rule_p u hu
  have hle := M.pairReaders_le u
  have hsplit := Finset.card_filter_add_card_filter_not (s := Readers u gates)
    (fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w)
  have hnpdef : nonpair S gates u = ((Readers u gates).filter
      fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card := rfl
  have hd := deg_split S C.h2 u
  have hpos := M.dc_pos u hu
  rw [← heq] at hpos hdb
  have hcap := (M.capacity u hpos).2
  have hkL := (M.rule_p_kL u hu).2
  unfold Tight at ht
  refine ⟨fun w i hi => ?_, by omega, by omega, ?_, ?_, by omega, by omega⟩
  · obtain ⟨k, hk⟩ := M.pairGate_of_tight u w i hi ht
    exact ⟨k, hk, fun k' hk' => M.pairGate_unique u w k' k hk' hk⟩
  · exact Finset.card_eq_zero.mp (by omega)
  · exact Finset.card_eq_zero.mp (by omega)

/-! ## Level 2: the G1.3 (ii) / G1.6 corollary forms -/

/-- G1.3 (ii), general form: if a single-reader point `v` uses `u` as the only earlier point of
one of its sets and `x_u` has a reader, then `dead0(u) ≥ #readers(u) + 1` and
`deg u ≥ #readers(u) + 1 + σ`. -/
theorem peel_deg (M : MinCE S gates out) (u : Fin n) (hU : (Users S gates u).Nonempty)
    (hr : 1 ≤ (Readers u gates).card) :
    (Readers u gates).card + 1 ≤ (DC u gates).card ∧
    baseOf S + (Readers u gates).card + 1 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.capacity u hr
  have := Finset.card_pos.mpr hU
  exact ⟨by omega, by omega⟩

/-- G1.3 (ii) for `u ∈ B` (at least two readers): a point of `B` used as the only earlier point
by some single-reader point has `dead0(u) ≥ 3` and `deg u ≥ 3 + σ`. -/
theorem peel_deg_B (M : MinCE S gates out) (u : Fin n) (hB : 2 ≤ (Readers u gates).card)
    (hU : (Users S gates u).Nonempty) :
    3 ≤ (DC u gates).card ∧ baseOf S + 3 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.peel_deg u hU (by omega)
  exact ⟨by omega, by omega⟩

/-- G1.3 (ii) for `u ∈ V1` (exactly one reader): `dead0(u) ≥ 2` and `deg u ≥ 2 + σ`. -/
theorem peel_deg_V1 (M : MinCE S gates out) (u : Fin n) (hV : (Readers u gates).card = 1)
    (hU : (Users S gates u).Nonempty) :
    2 ≤ (DC u gates).card ∧ baseOf S + 2 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.peel_deg u hU (by omega)
  exact ⟨by omega, by omega⟩

/-- The same two corollaries stated with one user: `v` single-reader, `u` the only point of
`S i` other than `v` with a reader below the reader of `v`. -/
theorem peel_deg_of_uses (M : MinCE S gates out) (u v : Fin n) (i : Fin m)
    (h : UsesVia S gates u v i) :
    (2 ≤ (Readers u gates).card → baseOf S + 3 ≤ gates.length + degOf S u) ∧
    ((Readers u gates).card = 1 → baseOf S + 2 ≤ gates.length + degOf S u) := by
  classical
  have hU : (Users S gates u).Nonempty :=
    ⟨v, by simp only [Users, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  exact ⟨fun hB => (M.peel_deg_B u hB hU).2, fun hV => (M.peel_deg_V1 u hV hU).2⟩

/-- G1.6 for `u ∈ B`: `#Users(u) ≤ deg u - σ - 2`. -/
theorem capacity_B (M : MinCE S gates out) (u : Fin n) (hB : 2 ≤ (Readers u gates).card) :
    baseOf S + 2 + (Users S gates u).card ≤ gates.length + degOf S u := by
  have := (M.capacity u (by omega)).2
  omega

/-- G1.6 for `u ∈ V1`: `#Users(u) ≤ deg u - σ - 1`. -/
theorem capacity_V1 (M : MinCE S gates out) (u : Fin n) (hV : (Readers u gates).card = 1) :
    baseOf S + 1 + (Users S gates u).card ≤ gates.length + degOf S u := by
  have := (M.capacity u (by omega)).2
  omega

end MinCE

/-! ## Level 3: G1.3 (iii), the two-point form -/

open Classical in
/-- The gates dead under the restriction `x_Z := 0` (`Z` a point set): on `{x | x = 0 on Z}` the
gate equals an earlier wire, or is constant. -/
noncomputable def DCZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k =>
    (∃ j, j < n + k ∧ ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) →
      val gates x (n + k) = val gates x j) ∨
    ∃ c : Bool, ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) → val gates x (n + k) = c

/-- Dead under `x_u := 0` implies dead under `x_Z := 0` for `u ∈ Z`. -/
theorem DC_sub_DCZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) (u : Fin n) (hu : u ∈ Z) :
    DC u gates ⊆ DCZ Z gates := by
  classical
  intro k hk
  simp only [DC, Finset.mem_filter, Finset.mem_range] at hk
  simp only [DCZ, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk.1, ?_⟩
  rcases hk.2 with ⟨j, hj, h⟩ | h
  · exact Or.inl ⟨j, hj, fun x hx => h x (hx u hu)⟩
  · exact Or.inr ⟨true, fun x hx => h x (hx u hu)⟩

theorem DCZ_sub_deadZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) (O : Finset ℕ) :
    DCZ Z gates ⊆ Kernel.deadZ gates Z O := by
  classical
  intro k hk
  simp only [DCZ, Finset.mem_filter, Finset.mem_range] at hk
  rcases hk.2 with ⟨j, hj, h⟩ | ⟨c, h⟩
  · exact Kernel.mem_deadZ_of_copy gates Z O k hk.1 j hj h
  · exact Kernel.mem_deadZ_of_const gates Z O k hk.1 c h

/-- An OR gate of fan-in `≤ 2` reading both `x_u1` and `x_u2` (`u1 ≠ u2`) is the pair gate. -/
theorem isPairGate_of_readers {n : ℕ} (gates : List Gate) (u1 u2 : Fin n) (h12 : u1 ≠ u2)
    (k : ℕ) (hk : k < gates.length) (hop : (gates[k]'hk).op = GateOp.or)
    (hlen : (gates[k]'hk).inputs.length ≤ 2)
    (h1 : k ∈ Readers u1 gates) (h2 : k ∈ Readers u2 gates) : IsPairGate gates k u1 u2 := by
  classical
  rw [readers_eq_wreaders] at h1 h2
  obtain ⟨_, h1⟩ := (mem_wreaders _ _ _).mp h1
  obtain ⟨_, h2⟩ := (mem_wreaders _ _ _).mp h2
  have hne : (u1 : ℕ) ≠ (u2 : ℕ) := Fin.val_ne_of_ne h12
  have m1 : (u1 : ℕ) ∈ (gates[k]'hk).inputs := by
    rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [hop] at h; cases h
  have m2 : (u2 : ℕ) ∈ (gates[k]'hk).inputs := by
    rcases h2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [hop] at h; cases h
  refine ⟨hk, hop, ?_⟩
  generalize (gates[k]'hk).inputs = l at hlen m1 m2
  match l, hlen with
  | [], _ => simp at m1
  | [a], _ =>
    simp only [List.mem_singleton] at m1 m2
    exact absurd (m1.trans m2.symm) hne
  | [a, b], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2
    rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left; rw [← e1, ← e2]
    · right; rw [← e1, ← e2]
    · exact absurd (e1.trans e2.symm) hne
  | _ :: _ :: _ :: _, h => simp at h

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- **N2 for point sets**: in a minimal counterexample, for every point set `Z` with at least one
gate dead under `x_Z := 0`, `base + #dead(Z := 0) ≤ s + ∑_{u ∈ Z} deg u`. -/
theorem deadBoundSet (M : MinCE S gates out) (Z : Finset (Fin n))
    (hd : 1 ≤ (DCZ Z gates).card) :
    baseOf S + (DCZ Z gates).card ≤ gates.length + ∑ u ∈ Z, degOf S u := by
  classical
  have C := M.ce
  have hsub := Finset.card_le_card (DCZ_sub_deadZ Z gates (Finset.univ.image out))
  have h := Kernel.restrictZero_bound S gates out C.hS C.hg C.hU C.hev
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) Z (by omega)
  set I := Finset.univ.filter (fun w : Fin m => 2 ≤ (S w \ Z).card)
  have key : ∀ w : Fin m, (S w).card - 1 ≤
      (if w ∈ I then (S w \ Z).card - 1 else 0) + (S w ∩ Z).card := by
    intro w
    have h1 := Finset.card_sdiff_add_card_inter (S w) Z
    by_cases hI : w ∈ I
    · rw [if_pos hI]; omega
    · rw [if_neg hI]
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hI
      omega
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => key w
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hsum
  have hdeg : ∑ w : Fin m, (S w ∩ Z).card = ∑ u ∈ Z, degOf S u := by
    have e1 : ∀ w : Fin m, (S w ∩ Z).card = ∑ u ∈ Z, (if u ∈ S w then 1 else 0) := by
      intro w
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    have e2 : ∀ u : Fin n, degOf S u = ∑ w : Fin m, (if u ∈ S w then 1 else 0) := by
      intro u
      unfold degOf
      rw [Finset.card_filter]
    rw [Finset.sum_congr rfl (fun w _ => e1 w), Finset.sum_comm,
      Finset.sum_congr rfl (fun u _ => e2 u)]
  unfold baseOf
  omega

open Classical in
/-- **G1.3 (iii), two-point form (general: any `σ`, no tightness).**  Let `v` be a single-reader
point with reader `r`, `S i ∋ v`, and let `u1 ≠ u2` (both `≠ v`) be such that no point of `S i`
other than `u1, u2` has a reader below `r` (`S i ∩ A_j ⊆ {u1, u2}`).  Then the other input of `r`
is a gate `c < r`, and under `x_u1 = x_u2 = 0` the readers of `x_u1`, of `x_u2`, the gate `r`
(which is no reader of either) and the gate `c` all die:
`base + #(R_u1 ∪ R_u2) + 1 + [c ∉ R_u1 ∪ R_u2] ≤ s + deg u1 + deg u2`. -/
theorem peel_two (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r})
    (i : Fin m) (hvi : v ∈ S i) (u1 u2 : Fin n) (h12 : u1 ≠ u2) (hv1 : u1 ≠ v) (hv2 : u2 ≠ v)
    (hA : ∀ t ∈ S i, t ≠ u1 → t ≠ u2 → ∀ k ∈ Readers t gates, r ≤ k) :
    ∃ c, c < r ∧ (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = n + c) ∧
      r ∉ Readers u1 gates ∪ Readers u2 gates ∧
      baseOf S + (Readers u1 gates ∪ Readers u2 gates).card + 1 +
        (if c ∈ Readers u1 gates ∪ Readers u2 gates then 0 else 1) ≤
          gates.length + degOf S u1 + degOf S u2 := by
  have C := M.ce
  obtain ⟨c, b, hc1, hc2, hr, hnu, hW, -, hcore⟩ := M.single_core2 v r hR
  set Z : Finset (Fin n) := {u1, u2} with hZ
  set R := Readers u1 gates ∪ Readers u2 gates with hRdef
  have hx : ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) →
      val gates x c = b ∧ val gates x (n + r) = x v := by
    intro x hxZ
    refine hcore i hvi x fun t ht hex => ?_
    by_cases ht1 : t = u1
    · rw [ht1]; exact hxZ u1 (by simp [hZ])
    · by_cases ht2 : t = u2
      · rw [ht2]; exact hxZ u2 (by simp [hZ])
      · obtain ⟨k, hk, hlt⟩ := hex
        exact absurd hlt (by have := hA t ht ht1 ht2 k hk; omega)
  have hrR : r ∉ R := by
    simp only [hRdef, Finset.mem_union, not_or]
    exact ⟨hnu u1 hv1, hnu u2 hv2⟩
  have hRsub : R ⊆ DCZ Z gates := by
    refine Finset.union_subset ?_ ?_
    · exact (readers_sub_DC u1 gates C.hg).trans (DC_sub_DCZ Z gates u1 (by simp [hZ]))
    · exact (readers_sub_DC u2 gates C.hg).trans (DC_sub_DCZ Z gates u2 (by simp [hZ]))
  have hrD : r ∈ DCZ Z gates := by
    simp only [DCZ, Finset.mem_filter, Finset.mem_range]
    exact ⟨hr, Or.inl ⟨v, by have := v.2; omega, fun x hxZ => by
      rw [(hx x hxZ).2, val_inp _ _ _ v.2]⟩⟩
  have hcD : c - n ∈ DCZ Z gates := by
    simp only [DCZ, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inr ⟨b, fun x hxZ => by
      rw [show n + (c - n) = c by omega]; exact (hx x hxZ).1⟩⟩
  refine ⟨c - n, by omega, fun p hp => ?_, hrR, ?_⟩
  · rw [show n + (c - n) = c by omega]; exact hW p hp
  have hins : insert (c - n) (insert r R) ⊆ DCZ Z gates :=
    Finset.insert_subset hcD (Finset.insert_subset hrD hRsub)
  have hcard := Finset.card_le_card hins
  have hcr : c - n ∉ insert r R ↔ c - n ∉ R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hb := M.deadBoundSet Z (by have := Finset.card_pos.mpr ⟨r, hrD⟩; omega)
  have hsumZ : ∑ u ∈ Z, degOf S u = degOf S u1 + degOf S u2 := Finset.sum_pair h12
  have h1 : (insert r R).card = R.card + 1 := Finset.card_insert_of_notMem hrR
  by_cases hcR : c - n ∈ R
  · rw [if_pos hcR]
    have := Finset.card_le_card (Finset.insert_subset hrD hRsub)
    omega
  · rw [if_neg hcR]
    rw [Finset.card_insert_of_notMem (hcr.mpr hcR), h1] at hcard
    omega

/-- **G1.3 (iii) as stated in the notes** (`u1, u2` tight, `σ = 1`): the other input `c` of the
reader `r` of `v` is a direct reader of `x_u1` or of `x_u2`, or the gate `x_u1 ∨ x_u2` exists. -/
theorem peel_two_tight (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r})
    (i : Fin m) (hvi : v ∈ S i) (u1 u2 : Fin n) (h12 : u1 ≠ u2) (hv1 : u1 ≠ v) (hv2 : u2 ≠ v)
    (hA : ∀ t ∈ S i, t ≠ u1 → t ≠ u2 → ∀ k ∈ Readers t gates, r ≤ k)
    (ht1 : Tight S gates u1) (ht2 : Tight S gates u2) (hσ : baseOf S = gates.length + 1) :
    ∃ c, c < r ∧ (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = n + c) ∧
      (c ∈ Readers u1 gates ∨ c ∈ Readers u2 gates ∨ ∃ k, IsPairGate gates k u1 u2) := by
  classical
  have C := M.ce
  obtain ⟨c, hcr, hW, -, hb⟩ := M.peel_two v r hR i hvi u1 u2 h12 hv1 hv2 hA
  refine ⟨c, hcr, hW, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hc2, hnp⟩ := hne
  have hcR : c ∉ Readers u1 gates ∪ Readers u2 gates := by
    simp only [Finset.mem_union, not_or]; exact ⟨hc1, hc2⟩
  rw [if_neg hcR] at hb
  have hint : Readers u1 gates ∩ Readers u2 gates = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_inter.mp hk
    have hkl : k < gates.length := by
      have := Finset.mem_filter.mp hk1
      exact Finset.mem_range.mp this.1
    exact hnp k (isPairGate_of_readers gates u1 u2 h12 k hkl (M.tight_or u1 ht1 k hkl hk1)
      (C.hg _ (List.getElem_mem hkl)).2 hk1 hk2)
  have hu := Finset.card_union_add_card_inter (Readers u1 gates) (Readers u2 gates)
  rw [hint, Finset.card_empty] at hu
  unfold Tight at ht1 ht2
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux

end Peel2
