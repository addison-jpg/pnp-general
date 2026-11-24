import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Eval
import PEqualNP.Kernel.W951Extra
import PEqualNP.Kernel.MultiBase

/-!
# W951/LiftCount: lifted counting (Lemma S2.1) for monotone circuits

A generic lemma about MONOTONE gate lists (every gate AND or OR, fan-in `≤ 2`), on `N` inputs
(wires `0..N-1`), gate `j` producing wire `N + j` (see `Eval.lean`). No NOT-gate machinery.

* `MonoList gs`: every gate is AND/OR with at most two inputs.
* `val_le_of_le`, `val_false_of_le`: every wire of an AND/OR list is monotone
  (from `Kernel.listVal_le`).
* `atomsAt gs a i` (`B(i)`): the atoms `a t` (`t : Fin k`) at which wire `i` is true.
* `IsOrAt gs j`: gate `j` is an OR gate.
* `liftCl gs Z a` (`cl(Z,a)`): gate indices `j` with wire `N + j` false on all of `Z` and true at
  `≥ 2` atoms; `liftClOr gs Z a`: its OR gates.
* `lift_run` (one zero point `z`): an explicit union-find run, modelled on `main_invT`
  (`Count.lean`): a labelling `l` and a merge set `M` of OR gates in `cl`, with
  `k ≤ |l(univ)| + |M|` and, for EVERY set `P` of atom indices,
  `|l(P)| + #{j ∈ M : B(N + j) ⊆ P} ≤ |P|` (the pair-budget form used by S2.2).
* **Lemma S2.1** (`lift_merges`, `lift_count`, `lift_count_family`): `Z` a nonempty join-closed
  Finset of points with the output `o` false on `Z`, atoms `a t` with `o` true, and (L): every
  input vanishing on `Z` is true at `≤ 1` atom. Then `cl(Z,a)` contains `≥ k − 1` OR gates;
  in fact there is a merge set `M ⊆ liftClOr gs Z a`, `k − 1 ≤ |M|`, with
  `#{j ∈ M : B(N + j) ⊆ P} ≤ |P| − 1` for every `P`.
* **Lemma S2.2** (`blockP` = `P(a|b)`; `atomsAt_subset_blockP`, `lift_pair_budget`,
  `lift_merges_blocked`, `liftCl_disjoint`, `liftClOr_disjoint`): a wire vanishing on `Zb` is true
  only at atoms of `P(a|b)`; at most `|P(a|b)| − 1` merge gates of `a` vanish on `Zb`; and
  `|P(a|b)| ≤ 1` or `|P(b|a)| ≤ 1` gives `cl_a ∩ cl_b = ∅`. (Blocking form only: no per-cube
  multi-base strengthening, which is false for AND/OR.)
* **Assembly** (`lift_family_bound`, `lift_family_le_length`): a pairwise blocked family of
  configurations gives `Σ_w (k w − 1) ≤ |⋃ cl_OR| ≤ gs.length`.

Proof idea: `Z` is join-closed and finite, so it has a largest point `z* = Z.sup id ∈ Z`; by
monotonicity a wire vanishes on `Z` iff it is false at `z*`, and an input vanishes on `Z` iff it
is false at `z*`. So everything reduces to the single zero point `z*`. There, an OR gate false at
`z*` has both inputs false at `z*`, and an AND gate false at `z*` has one input false at `z*` that
covers it; a merge (two atoms with different labels both true at a gate false at `z*`) therefore
happens only at OR gates, and joins exactly the two labels of its two inputs.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section LiftCount

variable {N k : ℕ}

/-! ## Monotone gate lists -/

/-- A monotone fan-in-2 gate list: every gate is an AND or an OR with at most two inputs. -/
def MonoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem MonoList.of_append {gs : List Gate} {g : Gate} (h : MonoList (gs ++ [g])) :
    MonoList gs :=
  fun g' hg' => h g' (List.mem_append_left _ hg')

theorem MonoList.andOr {gs : List Gate} (h : MonoList gs) :
    ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
  fun g hg => (h g hg).1

/-- Every wire of an AND/OR gate list is monotone (any fan-in). -/
theorem val_le_of_le (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : Fin N → Bool} (hxy : x ≤ y) (i : ℕ) : val gs x i ≤ val gs y i := by
  have h := PEqualNP.Kernel.listVal_le gs id id x y
    (fun c hc => Bool.le_iff_imp.mp (hxy c) hc)
    (fun a ha _ _ hv => PEqualNP.Kernel.listOp_mono (hg a ha) _ hv) i
  simp only [List.map_id] at h
  exact Bool.le_iff_imp.mpr h

/-- A wire false at `y` is false at every `x ≤ y`. -/
theorem val_false_of_le (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : Fin N → Bool} (hxy : x ≤ y) {i : ℕ} (h : val gs y i = false) :
    val gs x i = false := by
  have := val_le_of_le gs hg hxy i
  rw [h] at this
  cases hx : val gs x i
  · rfl
  · rw [hx] at this
    exact absurd this (by decide)

/-! ## Traces, OR gates, classes -/

/-- `B(i)`: the indices of the atoms at which wire `i` is true. -/
def atomsAt (gs : List Gate) (a : Fin k → Fin N → Bool) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun t => val gs (a t) i = true

theorem mem_atomsAt {gs : List Gate} {a : Fin k → Fin N → Bool} {i : ℕ} {t : Fin k} :
    t ∈ atomsAt gs a i ↔ val gs (a t) i = true := by
  simp [atomsAt]

theorem atomsAt_snoc (gs : List Gate) (g : Gate) (a : Fin k → Fin N → Bool) {i : ℕ}
    (hi : i ≠ N + gs.length) : atomsAt (gs ++ [g]) a i = atomsAt gs a i := by
  ext t
  simp only [mem_atomsAt, val_snoc, if_neg hi]

/-- Gate number `j` of `gs` (wire `N + j`) is an OR gate. -/
def IsOrAt (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ g.op = GateOp.or

theorem isOrAt_snoc {gs : List Gate} {g : Gate} {j : ℕ} (hj : j < gs.length)
    (h : IsOrAt gs j) : IsOrAt (gs ++ [g]) j := by
  obtain ⟨g', hg', hop⟩ := h
  exact ⟨g', by rw [List.getElem?_append_left hj]; exact hg', hop⟩

open Classical in
/-- OR gates of `cl` for a single zero point `z`: gate indices `j` (wire `N + j`) of OR gates
false at `z` and true at two or more atoms. -/
noncomputable def orClz (gs : List Gate) (z : Fin N → Bool) (a : Fin k → Fin N → Bool) :
    Finset ℕ :=
  (Finset.range gs.length).filter fun j =>
    IsOrAt gs j ∧ val gs z (N + j) = false ∧ 1 < (atomsAt gs a (N + j)).card

theorem mem_orClz {gs : List Gate} {z : Fin N → Bool} {a : Fin k → Fin N → Bool} {j : ℕ} :
    j ∈ orClz gs z a ↔ j < gs.length ∧ IsOrAt gs j ∧ val gs z (N + j) = false ∧
      1 < (atomsAt gs a (N + j)).card := by
  simp [orClz]

theorem orClz_snoc (gs : List Gate) (g : Gate) (z : Fin N → Bool) (a : Fin k → Fin N → Bool) :
    orClz gs z a ⊆ orClz (gs ++ [g]) z a := by
  intro j hj
  obtain ⟨hlt, hor, hz, hc⟩ := mem_orClz.mp hj
  have hne : N + j ≠ N + gs.length := by omega
  refine mem_orClz.mpr ⟨by simp; omega, isOrAt_snoc hlt hor, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [atomsAt_snoc gs g a hne]; exact hc

open Classical in
/-- `cl(Z, a)`: gate indices `j` (wire `N + j`) false on all of `Z` and true at two or more
atoms. -/
noncomputable def liftCl (gs : List Gate) (Z : Finset (Fin N → Bool)) (a : Fin k → Fin N → Bool) :
    Finset ℕ :=
  (Finset.range gs.length).filter fun j =>
    (∀ x ∈ Z, val gs x (N + j) = false) ∧ 1 < (atomsAt gs a (N + j)).card

open Classical in
/-- The OR gates of `cl(Z, a)`. -/
noncomputable def liftClOr (gs : List Gate) (Z : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) : Finset ℕ :=
  (liftCl gs Z a).filter fun j => IsOrAt gs j

theorem mem_liftCl {gs : List Gate} {Z : Finset (Fin N → Bool)} {a : Fin k → Fin N → Bool}
    {j : ℕ} : j ∈ liftCl gs Z a ↔ j < gs.length ∧ (∀ x ∈ Z, val gs x (N + j) = false) ∧
      1 < (atomsAt gs a (N + j)).card := by
  simp [liftCl]

theorem mem_liftClOr {gs : List Gate} {Z : Finset (Fin N → Bool)} {a : Fin k → Fin N → Bool}
    {j : ℕ} : j ∈ liftClOr gs Z a ↔ j < gs.length ∧ IsOrAt gs j ∧
      (∀ x ∈ Z, val gs x (N + j) = false) ∧ 1 < (atomsAt gs a (N + j)).card := by
  simp only [liftClOr, Finset.mem_filter, mem_liftCl]
  tauto

theorem liftClOr_subset (gs : List Gate) (Z : Finset (Fin N → Bool)) (a : Fin k → Fin N → Bool) :
    liftClOr gs Z a ⊆ liftCl gs Z a := by
  intro j hj
  obtain ⟨h1, -, h3, h4⟩ := mem_liftClOr.mp hj
  exact mem_liftCl.mpr ⟨h1, h3, h4⟩

/-! ## The union-find run at one zero point -/

/-- The union-find invariant: atoms true at a common wire that is false at `z` share a label. -/
def LInv (gs : List Gate) (z : Fin N → Bool) (a : Fin k → Fin N → Bool) (l : Fin k → Fin k) :
    Prop :=
  ∀ i s t, val gs z i = false → val gs (a s) i = true → val gs (a t) i = true → l s = l t

/-- An AND/OR gate with at most two inputs that is false at `z` is either never true, or covered by
two of its inputs that are false at `z`; for an AND gate, by one. -/
theorem gate_cover {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X)
    (hz : g.op.eval (g.inputs.map (f z)) = false) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
      ∃ c d, f z c = false ∧ f z d = false ∧ (g.op = GateOp.and → c = d) ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y c = true ∨ f y d = true := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · simp [GateOp.eval] at hz
    · left
      simp [GateOp.eval]
  | [c], _ =>
    right
    refine ⟨c, c, ?_, ?_, fun _ => rfl, ?_⟩ <;>
      rcases hop with rfl | rfl <;> simp_all [GateOp.eval]
  | [c, d], _ =>
    right
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id_eq, Bool.and_eq_true] at hz ⊢
      by_cases h : f z c = false
      · exact ⟨c, c, h, h, fun _ => rfl, fun y hy => Or.inl hy.1⟩
      · have hd : f z d = false := by
          cases hc : f z c <;> cases hd : f z d <;> simp_all
        exact ⟨d, d, hd, hd, fun _ => rfl, fun y hy => Or.inl hy.2⟩
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff] at hz ⊢
      exact ⟨c, d, hz.1, hz.2, fun (h : GateOp.or = GateOp.and) => GateOp.noConfusion h,
        fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

theorem card_image_relabel_le (l : Fin k → Fin k) (P : Finset (Fin k)) (s0 t0 : Fin k) :
    (P.image fun w => if l w = l t0 then l s0 else l w).card ≤ (P.image l).card := by
  have : (P.image fun w => if l w = l t0 then l s0 else l w) =
      (P.image l).image fun y => if y = l t0 then l s0 else y := by
    rw [Finset.image_image]
    rfl
  rw [this]
  exact Finset.card_image_le

theorem card_image_relabel_lt (l : Fin k → Fin k) (P : Finset (Fin k)) {s0 t0 : Fin k}
    (hs : s0 ∈ P) (ht : t0 ∈ P) (hne : l s0 ≠ l t0) :
    (P.image fun w => if l w = l t0 then l s0 else l w).card + 1 ≤ (P.image l).card := by
  have hsub : (P.image fun w => if l w = l t0 then l s0 else l w) ⊆ (P.image l).erase (l t0) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    by_cases h : l w = l t0
    · rw [if_pos h]
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem l hs⟩
    · rw [if_neg h]
      exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem l hw⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem l ht)] at h1
  have hpos : 0 < (P.image l).card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem l ht⟩
  omega

theorem card_image_le_relabel (l : Fin k → Fin k) (P : Finset (Fin k)) (s0 t0 : Fin k) :
    (P.image l).card ≤ (P.image fun w => if l w = l t0 then l s0 else l w).card + 1 := by
  have himg : P.image l ⊆ insert (l t0) (P.image fun w => if l w = l t0 then l s0 else l w) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    by_cases h : l w = l t0
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
      rw [if_neg h]
  exact (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)

/-- **The union-find run (one zero point).** Under (L) at `z`, there is a labelling `l` of the
atoms and a set `M` of OR gates of `cl(z, a)` (the merges) with
`k ≤ |l(univ)| + |M|` and, for every set `P` of atoms, `|l(P)| + #{j ∈ M : B(N+j) ⊆ P} ≤ |P|`. -/
theorem lift_run (gs : List Gate) (hm : MonoList gs) (z : Fin N → Bool)
    (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, z c = false → ∀ s t, a s c = true → a t c = true → s = t) :
    ∃ (l : Fin k → Fin k) (M : Finset ℕ), LInv gs z a l ∧ M ⊆ orClz gs z a ∧
      k ≤ (Finset.univ.image l).card + M.card ∧
      ∀ P : Finset (Fin k),
        (P.image l).card + (M.filter fun j => atomsAt gs a (N + j) ⊆ P).card ≤ P.card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ∅, ?_, by simp, by simp, by simp⟩
    intro i s t hz hs ht
    rw [val_nil] at hz hs ht
    by_cases h : i < N
    · simp only [h, dite_true] at hz hs ht
      exact hL ⟨i, h⟩ hz s t hs ht
    · simp [h] at hs
  | append_singleton gs g ih =>
    obtain ⟨l, M, hinv, hM, hk, hP⟩ := ih hm.of_append
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    have hnew : ∀ x : Fin N → Bool, val (gs ++ [g]) x (N + gs.length) =
        g.op.eval (g.inputs.map fun j => val gs x j) := fun x => by
      rw [val_snoc, if_pos rfl]
    have hold : ∀ (x : Fin N → Bool) (i : ℕ), i ≠ N + gs.length →
        val (gs ++ [g]) x i = val gs x i := fun x i hi => by
      rw [val_snoc, if_neg hi]
    have hMlt : ∀ j ∈ M, j < gs.length := fun j hj => (mem_orClz.mp (hM hj)).1
    have hMsub : M ⊆ orClz (gs ++ [g]) z a := hM.trans (orClz_snoc gs g z a)
    have hfilt : ∀ P : Finset (Fin k),
        (M.filter fun j => atomsAt (gs ++ [g]) a (N + j) ⊆ P) =
          M.filter fun j => atomsAt gs a (N + j) ⊆ P := by
      intro P
      apply Finset.filter_congr
      intro j hj
      rw [atomsAt_snoc gs g a (by have := hMlt j hj; omega)]
    by_cases hmerge : ∃ s0 t0, val (gs ++ [g]) (a s0) (N + gs.length) = true ∧
        val (gs ++ [g]) (a t0) (N + gs.length) = true ∧
        val (gs ++ [g]) z (N + gs.length) = false ∧ l s0 ≠ l t0
    swap
    · -- no merge: keep the labelling and the merge set
      refine ⟨l, M, ?_, hMsub, hk, fun P => by rw [hfilt]; exact hP P⟩
      intro i s t hz hs ht
      by_cases hi : i = N + gs.length
      · rw [hi] at hz hs ht
        by_contra hne
        exact hmerge ⟨s, t, hs, ht, hz, hne⟩
      · rw [hold _ _ hi] at hz hs ht
        exact hinv i s t hz hs ht
    obtain ⟨s0, t0, hs0, ht0, hz0, hne⟩ := hmerge
    rw [hnew] at hs0 ht0 hz0
    rcases gate_cover g hop hlen (fun x j => val gs x j) z hz0 with hall | ⟨c, d, hc, hd, hand, hcov⟩
    · exact absurd hs0 (by rw [hall (a s0)]; simp)
    have two : ∀ w, g.op.eval (g.inputs.map fun j => val gs (a w) j) = true →
        l w = l s0 ∨ l w = l t0 := by
      intro w hw
      rcases hcov _ hw with h | h <;> rcases hcov _ hs0 with h0 | h0 <;>
        rcases hcov _ ht0 with h1 | h1
      all_goals first
        | exact Or.inl (hinv c w s0 hc h h0)
        | exact Or.inl (hinv d w s0 hd h h0)
        | exact Or.inr (hinv c w t0 hc h h1)
        | exact Or.inr (hinv d w t0 hd h h1)
        | exact absurd (hinv c s0 t0 hc h0 h1) hne
        | exact absurd (hinv d s0 t0 hd h0 h1) hne
    have hor : g.op = GateOp.or := by
      rcases hop with h | h
      · exfalso
        have hcd := hand h
        subst hcd
        rcases hcov _ hs0 with h1 | h1 <;> rcases hcov _ ht0 with h2 | h2 <;>
          exact hne (hinv c s0 t0 hc h1 h2)
      · exact h
    have hst : s0 ≠ t0 := fun e => hne (by rw [e])
    have hBs : s0 ∈ atomsAt (gs ++ [g]) a (N + gs.length) := by
      rw [mem_atomsAt, hnew]; exact hs0
    have hBt : t0 ∈ atomsAt (gs ++ [g]) a (N + gs.length) := by
      rw [mem_atomsAt, hnew]; exact ht0
    have hnotin : gs.length ∉ M := fun h => by have := hMlt _ h; omega
    refine ⟨fun w => if l w = l t0 then l s0 else l w, insert gs.length M, ?_, ?_, ?_, ?_⟩
    · -- the invariant
      intro i s t hz hs ht
      by_cases hi : i = N + gs.length
      · rw [hi, hnew] at hs ht
        have red : ∀ w, g.op.eval (g.inputs.map fun j => val gs (a w) j) = true →
            (if l w = l t0 then l s0 else l w) = l s0 := by
          intro w hw
          rcases two w hw with h | h
          · split_ifs
            · rfl
            · exact h
          · rw [if_pos h]
        show (if l s = l t0 then l s0 else l s) = (if l t = l t0 then l s0 else l t)
        rw [red s hs, red t ht]
      · rw [hold _ _ hi] at hz hs ht
        have hl := hinv i s t hz hs ht
        show (if l s = l t0 then l s0 else l s) = (if l t = l t0 then l s0 else l t)
        rw [hl]
    · -- the merge set
      refine Finset.insert_subset_iff.mpr ⟨mem_orClz.mpr ⟨by simp, ⟨g, by simp, hor⟩, ?_, ?_⟩, hMsub⟩
      · rw [hnew]; exact hz0
      · exact Finset.one_lt_card.mpr ⟨s0, hBs, t0, hBt, hst⟩
    · -- the global count
      have h1 := card_image_le_relabel l Finset.univ s0 t0
      rw [Finset.card_insert_of_notMem hnotin]
      omega
    · -- the budget
      intro P
      rw [Finset.filter_insert]
      by_cases hBP : atomsAt (gs ++ [g]) a (N + gs.length) ⊆ P
      · rw [if_pos hBP, Finset.card_insert_of_notMem (fun h => hnotin (Finset.mem_of_mem_filter _ h)),
          hfilt]
        have h1 := card_image_relabel_lt l P (hBP hBs) (hBP hBt) hne
        have h2 := hP P
        omega
      · rw [if_neg hBP, hfilt]
        have h1 := card_image_relabel_le l P s0 t0
        have h2 := hP P
        omega

/-- S2.1 at one zero point, with the pair-budget refinement. -/
theorem lift_merges_pt (gs : List Gate) (hm : MonoList gs) (z : Fin N → Bool)
    (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, z c = false → ∀ s t, a s c = true → a t c = true → s = t)
    (o : ℕ) (hzo : val gs z o = false) (hao : ∀ t, val gs (a t) o = true) :
    ∃ M : Finset ℕ, M ⊆ orClz gs z a ∧ k - 1 ≤ M.card ∧
      ∀ P : Finset (Fin k), (M.filter fun j => atomsAt gs a (N + j) ⊆ P).card ≤ P.card - 1 := by
  classical
  obtain ⟨l, M, hinv, hM, hk, hP⟩ := lift_run gs hm z a hL
  refine ⟨M, hM, ?_, ?_⟩
  · have h1 : (Finset.univ.image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
      exact hinv o s t hzo (hao s) (hao t)
    omega
  · intro P
    rcases P.eq_empty_or_nonempty with rfl | hPne
    · have h0 : (M.filter fun j => atomsAt gs a (N + j) ⊆ (∅ : Finset (Fin k))) = ∅ := by
        apply Finset.filter_false_of_mem
        intro j hj hsub
        have h2 := (mem_orClz.mp (hM hj)).2.2.2
        rw [Finset.subset_empty.mp hsub] at h2
        simp at h2
      rw [h0]
      simp
    · have h1 := hP P
      have h2 : 0 < (P.image l).card := Finset.card_pos.mpr (hPne.image l)
      omega

/-! ## Join-closed zero sets -/

theorem le_sup_of_mem {Z : Finset (Fin N → Bool)} {x : Fin N → Bool} (hx : x ∈ Z) :
    x ≤ Z.sup id :=
  Finset.le_sup (f := id) hx

theorem sup_mem_of_join {Z : Finset (Fin N → Bool)} (hZ : Z.Nonempty)
    (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z) : Z.sup id ∈ Z :=
  SupClosed.finsetSup_mem (s := (Z : Set (Fin N → Bool)))
    (fun x hx y hy => hjoin x hx y hy) hZ (fun _ hi => hi)

/-- On a monotone list, a wire vanishes on a join-closed nonempty `Z` iff it is false at the
largest point `Z.sup id`. -/
theorem vanish_iff_sup (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {Z : Finset (Fin N → Bool)} (hZ : Z.Nonempty) (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z)
    (i : ℕ) : (∀ x ∈ Z, val gs x i = false) ↔ val gs (Z.sup id) i = false :=
  ⟨fun h => h _ (sup_mem_of_join hZ hjoin),
    fun h x hx => val_false_of_le gs hg (le_sup_of_mem hx) h⟩

theorem liftClOr_eq_orClz (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {Z : Finset (Fin N → Bool)} (hZ : Z.Nonempty) (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z)
    (a : Fin k → Fin N → Bool) : liftClOr gs Z a = orClz gs (Z.sup id) a := by
  ext j
  rw [mem_liftClOr, mem_orClz, vanish_iff_sup gs hg hZ hjoin]

/-- **Lemma S2.1 (lifted counting), with the merge set.** `M` monotone (AND/OR, fan-in `≤ 2`),
`Z` a nonempty join-closed set of points with the output `o` false on `Z`, atoms `a t`
(`t : Fin k`) with `o` true, and (L): every input vanishing on `Z` is true at `≤ 1` atom. Then
there is a set `M` of OR gates of `cl(Z, a)` with `k − 1 ≤ |M|`, and for every set `P` of atoms at
most `|P| − 1` gates `j ∈ M` have `B(N + j) ⊆ P`. -/
theorem lift_merges (gs : List Gate) (hm : MonoList gs) (Z : Finset (Fin N → Bool))
    (hZ : Z.Nonempty) (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z) (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, (∀ x ∈ Z, x c = false) → ∀ s t, a s c = true → a t c = true → s = t)
    (o : ℕ) (hZo : ∀ x ∈ Z, val gs x o = false) (hao : ∀ t, val gs (a t) o = true) :
    ∃ M : Finset ℕ, M ⊆ liftClOr gs Z a ∧ k - 1 ≤ M.card ∧
      ∀ P : Finset (Fin k), (M.filter fun j => atomsAt gs a (N + j) ⊆ P).card ≤ P.card - 1 := by
  have hL' : ∀ c : Fin N, Z.sup id c = false → ∀ s t, a s c = true → a t c = true → s = t := by
    intro c hc
    apply hL c
    intro x hx
    have h1 : x c ≤ Z.sup id c := le_sup_of_mem hx c
    rw [hc, Bool.le_iff_imp] at h1
    cases hxc : x c
    · rfl
    · exact absurd (h1 hxc) (by simp)
  rw [liftClOr_eq_orClz gs hm.andOr hZ hjoin]
  exact lift_merges_pt gs hm (Z.sup id) a hL' o (hZo _ (sup_mem_of_join hZ hjoin)) hao

/-- **Lemma S2.1 (lifted counting).** Under the hypotheses of `lift_merges`, `cl(Z, a)` contains
at least `k − 1` OR gates. -/
theorem lift_count (gs : List Gate) (hm : MonoList gs) (Z : Finset (Fin N → Bool))
    (hZ : Z.Nonempty) (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z) (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, (∀ x ∈ Z, x c = false) → ∀ s t, a s c = true → a t c = true → s = t)
    (o : ℕ) (hZo : ∀ x ∈ Z, val gs x o = false) (hao : ∀ t, val gs (a t) o = true) :
    k - 1 ≤ (liftClOr gs Z a).card := by
  obtain ⟨M, hM, hk, -⟩ := lift_merges gs hm Z hZ hjoin a hL o hZo hao
  exact hk.trans (Finset.card_le_card hM)

/-- **Lemma S2.1, family form.** An injective family of `k − 1` OR gates (gate indices) of
`cl(Z, a)`: each `f i` is the index of an OR gate of `gs` whose wire `N + f i` vanishes on `Z` and
is true at two or more atoms. -/
theorem lift_count_family (gs : List Gate) (hm : MonoList gs) (Z : Finset (Fin N → Bool))
    (hZ : Z.Nonempty) (hjoin : ∀ x ∈ Z, ∀ y ∈ Z, x ⊔ y ∈ Z) (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, (∀ x ∈ Z, x c = false) → ∀ s t, a s c = true → a t c = true → s = t)
    (o : ℕ) (hZo : ∀ x ∈ Z, val gs x o = false) (hao : ∀ t, val gs (a t) o = true) :
    ∃ f : Fin (k - 1) → ℕ, Function.Injective f ∧ ∀ i, f i ∈ liftClOr gs Z a := by
  have h := lift_count gs hm Z hZ hjoin a hL o hZo hao
  refine ⟨fun i => (liftClOr gs Z a).orderEmbOfFin rfl (Fin.castLE h i), ?_, fun i =>
    Finset.orderEmbOfFin_mem _ rfl _⟩
  intro i j hij
  exact Fin.castLE_injective h (((liftClOr gs Z a).orderEmbOfFin rfl).injective hij)

/-! ## Lemma S2.2: blocking and the pair budget -/

open Classical in
/-- `P(a|b)`: the atoms of configuration `a` that are not below any point of `Zb`. -/
noncomputable def blockP (Zb : Finset (Fin N → Bool)) (a : Fin k → Fin N → Bool) :
    Finset (Fin k) :=
  Finset.univ.filter fun t => ∀ y ∈ Zb, ¬ a t ≤ y

theorem mem_blockP {Zb : Finset (Fin N → Bool)} {a : Fin k → Fin N → Bool} {t : Fin k} :
    t ∈ blockP Zb a ↔ ∀ y ∈ Zb, ¬ a t ≤ y := by
  simp [blockP]

/-- **S2.2, trace form.** A wire vanishing on `Zb` is true only at atoms of `P(a|b)`. -/
theorem atomsAt_subset_blockP (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (Zb : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) {i : ℕ} (hi : ∀ y ∈ Zb, val gs y i = false) :
    atomsAt gs a i ⊆ blockP Zb a := by
  intro t ht
  rw [mem_blockP]
  intro y hy hle
  have h1 := val_false_of_le gs hg hle (hi y hy)
  rw [mem_atomsAt.mp ht] at h1
  exact Bool.noConfusion h1

/-- **S2.2, pair budget.** If the merge set `M` of configuration `a` satisfies the budget of
`lift_merges`, then at most `|P(a|b)| − 1` of its gates vanish on `Zb`. -/
theorem lift_pair_budget (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (Zb : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) (M : Finset ℕ)
    (hM : ∀ P : Finset (Fin k),
      (M.filter fun j => atomsAt gs a (N + j) ⊆ P).card ≤ P.card - 1) :
    (M.filter fun j => ∀ y ∈ Zb, val gs y (N + j) = false).card ≤ (blockP Zb a).card - 1 := by
  classical
  refine (Finset.card_le_card ?_).trans (hM (blockP Zb a))
  intro j hj
  obtain ⟨hjM, hjz⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hjM, atomsAt_subset_blockP gs hg Zb a hjz⟩

/-- **S2.2, combined with S2.1.** Under the hypotheses of `lift_merges` for `(Za, a)`, there is a
merge set `M` of `k − 1` or more OR gates of `cl(Za, a)` of which at most `|P(a|b)| − 1` vanish on
`Zb` (for every `Zb` simultaneously). -/
theorem lift_merges_blocked (gs : List Gate) (hm : MonoList gs) (Za : Finset (Fin N → Bool))
    (hZ : Za.Nonempty) (hjoin : ∀ x ∈ Za, ∀ y ∈ Za, x ⊔ y ∈ Za) (a : Fin k → Fin N → Bool)
    (hL : ∀ c : Fin N, (∀ x ∈ Za, x c = false) → ∀ s t, a s c = true → a t c = true → s = t)
    (o : ℕ) (hZo : ∀ x ∈ Za, val gs x o = false) (hao : ∀ t, val gs (a t) o = true) :
    ∃ M : Finset ℕ, M ⊆ liftClOr gs Za a ∧ k - 1 ≤ M.card ∧
      ∀ Zb : Finset (Fin N → Bool),
        (M.filter fun j => ∀ y ∈ Zb, val gs y (N + j) = false).card ≤
          (blockP Zb a).card - 1 := by
  obtain ⟨M, hM, hk, hP⟩ := lift_merges gs hm Za hZ hjoin a hL o hZo hao
  exact ⟨M, hM, hk, fun Zb => lift_pair_budget gs hm.andOr Zb a M hP⟩

/-- A gate of `cl(Za, a)` vanishing on `Zb` forces `2 ≤ |P(a|b)|`. -/
theorem two_le_blockP_of_mem (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (Za Zb : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) {j : ℕ} (hj : j ∈ liftCl gs Za a)
    (hb : ∀ y ∈ Zb, val gs y (N + j) = false) : 2 ≤ (blockP Zb a).card :=
  (mem_liftCl.mp hj).2.2.trans_le (Finset.card_le_card (atomsAt_subset_blockP gs hg Zb a hb))

/-- **Lemma S2.2 (blocking).** Two configurations `(Za, a)`, `(Zb, b)` of an AND/OR list. If
`|P(a|b)| ≤ 1` or `|P(b|a)| ≤ 1`, the classes `cl(Za, a)` and `cl(Zb, b)` are disjoint. -/
theorem liftCl_disjoint {k' : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (Za Zb : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) (b : Fin k' → Fin N → Bool)
    (h : (blockP Zb a).card ≤ 1 ∨ (blockP Za b).card ≤ 1) :
    Disjoint (liftCl gs Za a) (liftCl gs Zb b) := by
  rw [Finset.disjoint_left]
  intro j hja hjb
  have h1 := two_le_blockP_of_mem gs hg Za Zb a hja (mem_liftCl.mp hjb).2.1
  have h2 := two_le_blockP_of_mem gs hg Zb Za b hjb (mem_liftCl.mp hja).2.1
  omega

/-- **Lemma S2.2 (blocking), OR-gate classes.** -/
theorem liftClOr_disjoint {k' : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (Za Zb : Finset (Fin N → Bool))
    (a : Fin k → Fin N → Bool) (b : Fin k' → Fin N → Bool)
    (h : (blockP Zb a).card ≤ 1 ∨ (blockP Za b).card ≤ 1) :
    Disjoint (liftClOr gs Za a) (liftClOr gs Zb b) :=
  Finset.disjoint_of_subset_left (liftClOr_subset gs Za a)
    (Finset.disjoint_of_subset_right (liftClOr_subset gs Zb b)
      (liftCl_disjoint gs hg Za Zb a b h))

/-! ## Assembly: a pairwise blocked family of configurations -/

/-- **Assembly (S2.1 + S2.2).** A monotone list `gs`, a finite family `T` of outputs `o w`, each
with a configuration `(Z w, a w)` (`k w` atoms) satisfying the hypotheses of S2.1, pairwise
blocked (`|P(a|b)| ≤ 1` or `|P(b|a)| ≤ 1` for `a ≠ b` in `T`). Then
`Σ_{w ∈ T} (k w − 1) ≤ |⋃_w cl_OR(Z w, a w)| ≤ gs.length`. -/
theorem lift_family_bound {ι : Type*} (gs : List Gate) (hm : MonoList gs) (T : Finset ι)
    (k : ι → ℕ) (Z : ι → Finset (Fin N → Bool)) (a : ∀ w, Fin (k w) → Fin N → Bool) (o : ι → ℕ)
    (hZ : ∀ w ∈ T, (Z w).Nonempty) (hjoin : ∀ w ∈ T, ∀ x ∈ Z w, ∀ y ∈ Z w, x ⊔ y ∈ Z w)
    (hL : ∀ w ∈ T, ∀ c : Fin N, (∀ x ∈ Z w, x c = false) →
      ∀ s t, a w s c = true → a w t c = true → s = t)
    (hZo : ∀ w ∈ T, ∀ x ∈ Z w, val gs x (o w) = false)
    (hao : ∀ w ∈ T, ∀ t, val gs (a w t) (o w) = true)
    (hblock : ∀ u ∈ T, ∀ v ∈ T, u ≠ v →
      (blockP (Z v) (a u)).card ≤ 1 ∨ (blockP (Z u) (a v)).card ≤ 1) :
    ∑ w ∈ T, (k w - 1) ≤ (T.biUnion fun w => liftClOr gs (Z w) (a w)).card ∧
      (T.biUnion fun w => liftClOr gs (Z w) (a w)).card ≤ gs.length := by
  refine ⟨PEqualNP.Kernel.sum_le_card_biUnion_of_classes T _ _
    (fun w hw => lift_count gs hm (Z w) (hZ w hw) (hjoin w hw) (a w) (hL w hw) (o w)
      (hZo w hw) (hao w hw))
    (fun u hu v hv huv => liftClOr_disjoint gs hm.andOr (Z u) (Z v) (a u) (a v)
      (hblock u hu v hv huv)), ?_⟩
  have hsub : (T.biUnion fun w => liftClOr gs (Z w) (a w)) ⊆ Finset.range gs.length := by
    intro j hj
    obtain ⟨w, -, hjw⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_range.mpr (mem_liftClOr.mp hjw).1
  simpa using Finset.card_le_card hsub

/-- **Assembly, size form.** `Σ_{w ∈ T} (k w − 1) ≤ gs.length`. -/
theorem lift_family_le_length {ι : Type*} (gs : List Gate) (hm : MonoList gs) (T : Finset ι)
    (k : ι → ℕ) (Z : ι → Finset (Fin N → Bool)) (a : ∀ w, Fin (k w) → Fin N → Bool) (o : ι → ℕ)
    (hZ : ∀ w ∈ T, (Z w).Nonempty) (hjoin : ∀ w ∈ T, ∀ x ∈ Z w, ∀ y ∈ Z w, x ⊔ y ∈ Z w)
    (hL : ∀ w ∈ T, ∀ c : Fin N, (∀ x ∈ Z w, x c = false) →
      ∀ s t, a w s c = true → a w t c = true → s = t)
    (hZo : ∀ w ∈ T, ∀ x ∈ Z w, val gs x (o w) = false)
    (hao : ∀ w ∈ T, ∀ t, val gs (a w t) (o w) = true)
    (hblock : ∀ u ∈ T, ∀ v ∈ T, u ≠ v →
      (blockP (Z v) (a u)).card ≤ 1 ∨ (blockP (Z u) (a v)).card ≤ 1) :
    ∑ w ∈ T, (k w - 1) ≤ gs.length :=
  (lift_family_bound gs hm T k Z a o hZ hjoin hL hZo hao hblock).1.trans
    (lift_family_bound gs hm T k Z a o hZ hjoin hL hZo hao hblock).2

end LiftCount



end PEqualNP.Outside.L_meta_951_aux
