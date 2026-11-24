import PEqualNP.Kernel.AndReplace

/-!
# Kernel/MultiBase: multi-base-point Nechiporuk (Wegener 6.2 with per-output cubes)

Each output `o w` (`w ∈ T`) computes its Boolean sum `OR (S w)` only on its OWN cube
`{x ≥ z w}`, with `z w` missing `S w`.

**Main observation (collapse).** "Missing a set" is a per-variable condition, so the pairwise
compatibility hypothesis (`z a ⊔ z b` misses `S a ∪ S b` for `a ≠ b`) is equivalent to
*cross-avoidance* (`z b` misses `S a` for all `a b ∈ T`), which in turn says exactly that the
single point `T.sup z` misses every `S w`. On the common cube `{x ≥ T.sup z}` all outputs are
exact sums simultaneously, so the multi-base theorem is the single-base theorem
`Dag.sum_card_sub_one_le_andOr` at base `T.sup z`. No per-cube AND-replacement is needed.

* `orOf_finsetSup_eq_false`: `OR S` vanishes at `T.sup z` iff it vanishes at every `z w`.
* `crossAvoid_of_pairwise`: pairwise compatibility + self-avoidance ⟹ cross-avoidance.
* `Dag.sum_card_sub_one_le_andOr_commonBase`: any common upper bound `z'` of the `z w` missing
  all `S w` gives the bound (the most general form).
* `Dag.sum_card_sub_one_le_andOr_crossAvoid`: the bound under cross-avoidance.
* `Dag.sum_card_sub_one_le_andOr_multiBase`: **the target statement** (pairwise compatibility).
* `Dag.sum_card_sub_one_le_gates_multiBase`: OR-only version, with the merging-gate count at
  the common base `T.sup z` (the "coverage + privacy" half).

* `sum_card_sub_one_le_of_classes`: the abstract ASSEMBLY (classes `M w` of gates with
  (i) `|S w| − 1 ≤ |M w|`, (ii) pairwise disjoint ⟹ `Σ (|S w| − 1) ≤ |⋃ M w| ≤ s`);
  `Dag.CompatFamily`: the pairwise compatible family condition.
* `Dag.sum_card_sub_one_le_gates_ownBase`: for `{∨}`-dags, (i)/(ii) hold with
  `M w = merge (z w) (o w)` at each output's OWN base, with NO compatibility hypothesis
  (`OrOnly.val_sup`, `OrOnly.supp_subset_supp`, `merge_disjoint_multiBase`).
* `Dag.multiBase_without_compat_false`: for AND/OR dags the statement WITHOUT compatibility is
  false (`K_{2,2}`: 4 inputs, 3 gates, sum `4`).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open Function (update)

/-! ## The abstract counting skeleton (assembly) -/

/-- **Counting skeleton.** Pairwise disjoint classes `M w` (`w ∈ T`) with `d w ≤ |M w|`:
`Σ_{w ∈ T} d w ≤ |⋃ M w|`. -/
theorem sum_le_card_biUnion_of_classes {ι α : Type*} [DecidableEq α] (T : Finset ι) (d : ι → ℕ)
    (M : ι → Finset α) (hcount : ∀ w ∈ T, d w ≤ (M w).card)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (M a) (M b)) :
    ∑ w ∈ T, d w ≤ (T.biUnion M).card := by
  rw [Finset.card_biUnion fun a ha b hb hab => hdisj a ha b hb hab]
  exact Finset.sum_le_sum hcount

/-- **Assembly.** If every output `w ∈ T` owns a class `M w` of gates (indices in `Fin s`) with
`|S w| − 1 ≤ |M w|` (hypothesis (i), "coverage") and the classes are pairwise disjoint on `T`
(hypothesis (ii), "privacy"), then `Σ_{w ∈ T} (|S w| − 1) ≤ |⋃ M w| ≤ s`. -/
theorem sum_card_sub_one_le_of_classes {n s : ℕ} {ι : Type*} (T : Finset ι)
    (S : ι → Finset (Fin n)) (M : ι → Finset (Fin s))
    (hcount : ∀ w ∈ T, (S w).card - 1 ≤ (M w).card)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (M a) (M b)) :
    ∑ w ∈ T, ((S w).card - 1) ≤ (T.biUnion M).card ∧ (T.biUnion M).card ≤ s :=
  ⟨sum_le_card_biUnion_of_classes T _ M hcount hdisj,
    by simpa using Finset.card_le_univ (T.biUnion M)⟩

namespace Dag

variable {n s : ℕ}

/-- **Pairwise compatible family** of per-output cubes: output `o w` computes `OR (S w)` on its
own cube `{x ≥ z w}`, `z w` misses `S w`, the sums pairwise share at most one variable, and for
`a ≠ b` the point `z a ⊔ z b` misses `S a ∪ S b`. -/
structure CompatFamily (D : Dag n s) {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n)) (z : ι → Fin n → Bool) : Prop where
  disj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1
  computes : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x
  avoid : ∀ w ∈ T, orOf (S w) (z w) = false
  compat : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → orOf (S a ∪ S b) (z a ⊔ z b) = false

/-- **Assembly for a family**: a compatible family together with any system of pairwise
disjoint gate classes of the right sizes gives the bound. (The family itself is not used by the
count; it is what the classes are to be extracted from.) -/
theorem CompatFamily.sum_le_of_classes {D : Dag n s} {ι : Type*} {T : Finset ι}
    {o : ι → Fin (n + s)} {S : ι → Finset (Fin n)} {z : ι → Fin n → Bool}
    (_hF : D.CompatFamily T o S z) (M : ι → Finset (Fin s))
    (hcount : ∀ w ∈ T, (S w).card - 1 ≤ (M w).card)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (M a) (M b)) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s :=
  (sum_card_sub_one_le_of_classes T S M hcount hdisj).1.trans
    (sum_card_sub_one_le_of_classes T S M hcount hdisj).2

/-! ## Common base -/

/-- `OR S` vanishes at a finite sup of points iff it vanishes at each of them. -/
theorem orOf_finsetSup_eq_false {ι : Type*} (S : Finset (Fin n)) (T : Finset ι)
    (z : ι → Fin n → Bool) :
    orOf S (T.sup z) = false ↔ ∀ w ∈ T, orOf S (z w) = false := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    simp [orOf]
  | insert a T _ ih =>
    rw [Finset.sup_insert, orOf_sup, Bool.or_eq_false_iff, ih]
    simp

/-- Each base point lies below the common base. -/
theorem le_finsetSup_base {ι : Type*} (T : Finset ι) (z : ι → Fin n → Bool) {w : ι}
    (hw : w ∈ T) : z w ≤ T.sup z := Finset.le_sup hw

/-- **Pairwise compatibility is cross-avoidance.** If each `z w` misses `S w` and, for `a ≠ b`,
`z a ⊔ z b` misses `S a ∪ S b`, then every `z b` misses every `S a`. -/
theorem crossAvoid_of_pairwise {ι : Type*} (T : Finset ι) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool) (hz : ∀ w ∈ T, orOf (S w) (z w) = false)
    (hcompat : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → orOf (S a ∪ S b) (z a ⊔ z b) = false) :
    ∀ a ∈ T, ∀ b ∈ T, orOf (S a) (z b) = false := by
  intro a ha b hb
  by_cases hab : a = b
  · subst hab; exact hz a ha
  · have h := hcompat a ha b hb hab
    simp only [orOf, decide_eq_false_iff_not, not_exists, not_and] at h ⊢
    intro v hv hzv
    exact h v (Finset.mem_union_left _ hv) (by simp [hzv])

/-- Conversely, cross-avoidance gives pairwise compatibility: the two notions coincide. -/
theorem pairwise_of_crossAvoid {ι : Type*} (T : Finset ι) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool) (hav : ∀ a ∈ T, ∀ b ∈ T, orOf (S a) (z b) = false) :
    ∀ a ∈ T, ∀ b ∈ T, orOf (S a ∪ S b) (z a ⊔ z b) = false := by
  intro a ha b hb
  have h1 := hav a ha a ha
  have h2 := hav a ha b hb
  have h3 := hav b hb a ha
  have h4 := hav b hb b hb
  simp only [orOf, decide_eq_false_iff_not, not_exists, not_and] at h1 h2 h3 h4 ⊢
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have := h1 v hv; have := h2 v hv
    simp_all
  · have := h3 v hv; have := h4 v hv
    simp_all

/-- **Common-base form.** If some point `z'` above all the per-output bases `z w` still misses
every `S w`, the Nechiporuk bound holds (single-base theorem at `z'`). -/
theorem sum_card_sub_one_le_andOr_commonBase (D : Dag n s)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2)
    {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool) (z' : Fin n → Bool)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x)
    (hle : ∀ w ∈ T, z w ≤ z') (hz' : ∀ w ∈ T, orOf (S w) z' = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s :=
  D.sum_card_sub_one_le_andOr hD hfan z' T o S hdisj
    (fun w hw x hx => ho w hw x ((hle w hw).trans hx)) hz'

/-- **Multi-base Nechiporuk under cross-avoidance**: every base point `z b` misses every sum
`S a`. -/
theorem sum_card_sub_one_le_andOr_crossAvoid (D : Dag n s)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2)
    {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x)
    (hav : ∀ a ∈ T, ∀ b ∈ T, orOf (S a) (z b) = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s :=
  D.sum_card_sub_one_le_andOr_commonBase hD hfan T o S z (T.sup z) hdisj ho
    (fun _ hw => le_finsetSup_base T z hw)
    (fun w hw => (orOf_finsetSup_eq_false (S w) T z).mpr (hav w hw))

/-- **Multi-base-point Nechiporuk (Wegener 6.2 with per-output cubes).** An AND/OR dag of
fan-in `≤ 2`; each output `o w` (`w ∈ T`) computes `OR (S w)` on its own cube `{x ≥ z w}`, with
`z w` missing `S w`; the sums pairwise share at most one variable; and the base points are
pairwise compatible: `z a ⊔ z b` misses `S a ∪ S b`. Then the dag has at least
`Σ_{w ∈ T} (|S w| − 1)` gates. -/
theorem sum_card_sub_one_le_andOr_multiBase (D : Dag n s)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2)
    {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) (z w) = false)
    (hcompat : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → orOf (S a ∪ S b) (z a ⊔ z b) = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s :=
  D.sum_card_sub_one_le_andOr_crossAvoid hD hfan T o S z hdisj ho
    (crossAvoid_of_pairwise T S z hz hcompat)

/-- **OR-only multi-base bound with the merging-gate count** ("coverage + privacy"): for a
`{∨}`-dag the sum is bounded by the number of merging gates of the outputs, measured at the
common base `T.sup z`. -/
theorem sum_card_sub_one_le_gates_multiBase (D : Dag n s) (hD : D.OrOnly)
    (hfan : ∀ i, (D.gate i).inputs.length ≤ 2)
    {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) (z w) = false)
    (hcompat : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → orOf (S a ∪ S b) (z a ⊔ z b) = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ (T.biUnion fun w => D.merge (T.sup z) (o w)).card ∧
      (T.biUnion fun w => D.merge (T.sup z) (o w)).card ≤ s :=
  D.sum_card_sub_one_le_gates hD hfan (T.sup z) T o S hdisj
    (fun w hw x hx => ho w hw x ((le_finsetSup_base T z hw).trans hx))
    (fun w hw => (orOf_finsetSup_eq_false (S w) T z).mpr
      (crossAvoid_of_pairwise T S z hz hcompat w hw))

/-- The family version of the multi-base theorem. -/
theorem CompatFamily.sum_card_sub_one_le {D : Dag n s} {ι : Type*} {T : Finset ι}
    {o : ι → Fin (n + s)} {S : ι → Finset (Fin n)} {z : ι → Fin n → Bool}
    (hF : D.CompatFamily T o S z)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s :=
  D.sum_card_sub_one_le_andOr_multiBase hD hfan T o S z hF.disj hF.computes hF.avoid hF.compat

/-! ## OR-only dags: per-output bases, NO compatibility needed

In a `{∨}`-dag every wire is a join-homomorphism, so the support of a wire does not depend on
the base point as long as the wire vanishes there. Hence the merging classes
`M w = merge (z w) (o w)`, each measured at its OWN base, are pairwise disjoint, and hypotheses
(i)/(ii) of the assembly hold without any compatibility between the base points. -/

/-- An OR gate commutes with binary joins of its input values. -/
theorem _root_.PEqualNP.Kernel.KGate.eval_or_sup {k : ℕ} {g : KGate k}
    (hg : g.op = GateOp.or) (v v' : Fin k → Bool) :
    g.eval (fun a => v a || v' a) = (g.eval v || g.eval v') := by
  rw [KGate.eval_def, KGate.eval_def, KGate.eval_def, hg]
  show (g.inputs.map (Src.eval fun a => v a || v' a)).any id =
    ((g.inputs.map (Src.eval v)).any id || (g.inputs.map (Src.eval v')).any id)
  induction g.inputs with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.any_cons, ih, id]
    cases p with
    | wire a =>
      simp only [Src.eval_wire]
      cases v a <;> cases v' a <;> simp
    | const b =>
      simp only [Src.eval_const]
      cases b <;> simp

/-- **Wires of a `{∨}`-dag are join-homomorphisms.** -/
theorem OrOnly.val_sup {D : Dag n s} (hD : D.OrOnly) (x y : Fin n → Bool) :
    ∀ w, D.val (x ⊔ y) w = (D.val x w || D.val y w) := by
  refine wire_induction (fun j => by simp) (fun i ih => ?_)
  rw [val_natAdd, val_natAdd, val_natAdd, ← KGate.eval_or_sup (hD i)]
  exact congrArg (fun v => (D.gate i).eval v) (funext ih)

/-- **Base-independence of supports in `{∨}`-dags.** A variable in the support of `w` at base
`z` is in the support of `w` at any base `z'` where `w` vanishes. -/
theorem OrOnly.supp_subset_supp {D : Dag n s} (hD : D.OrOnly) {z z' : Fin n → Bool}
    {w : Fin (n + s)} (hz' : D.val z' w = false) : D.supp z w ⊆ D.supp z' w := by
  intro v hv
  obtain ⟨_, h1, h0⟩ := mem_supp.mp hv
  set e : Fin n → Bool := update (fun _ => false) v true with he
  have hsup : update z v true = z ⊔ e := by
    funext k
    by_cases hk : k = v
    · subst hk; simp [he]
    · simp [he, Function.update_of_ne hk]
  have hev : D.val e w = true := by
    rw [hsup, hD.val_sup, h0] at h1
    simpa using h1
  have hle : ∀ y : Fin n → Bool, y v = true → e ≤ y := by
    intro y hy k
    by_cases hk : k = v
    · subst hk; simp [he, hy]
    · simp [he, Function.update_of_ne hk]
  have hup : ∀ y : Fin n → Bool, y v = true → D.val y w = true := fun y hy =>
    Bool.le_iff_imp.mp (D.val_mono hD.mono (hle y hy) w) hev
  refine mem_supp.mpr ⟨?_, hup _ (by simp), hz'⟩
  by_contra hne
  have := hup z' (by simpa using hne)
  rw [hz'] at this
  exact absurd this (by simp)

/-- **Hypothesis (ii) for `{∨}`-dags, per-output bases.** Merging gates of two different
outputs, each measured at its own base, are different. No compatibility is needed. -/
theorem merge_disjoint_multiBase (D : Dag n s) (hD : D.OrOnly) {ι : Type*}
    (o : ι → Fin (n + s)) (S : ι → Finset (Fin n)) (z : ι → Fin n → Bool) {a b : ι}
    (hdisj : (S a ∩ S b).card ≤ 1)
    (ha : ∀ x, z a ≤ x → D.val x (o a) = orOf (S a) x) (hza : orOf (S a) (z a) = false)
    (hb : ∀ x, z b ≤ x → D.val x (o b) = orOf (S b) x) (hzb : orOf (S b) (z b) = false) :
    Disjoint (D.merge (z a) (o a)) (D.merge (z b) (o b)) := by
  classical
  rw [Finset.disjoint_left]
  intro i hia hib
  obtain ⟨hra, hca⟩ := mem_merge.mp hia
  obtain ⟨hrb, hcb⟩ := mem_merge.mp hib
  have hsa : D.supp (z a) (Fin.natAdd n i) ⊆ S a :=
    D.supp_subset_of_le (z a) ha hza fun x _ => hD.val_le hra x
  have hsb : D.supp (z b) (Fin.natAdd n i) ⊆ S b :=
    D.supp_subset_of_le (z b) hb hzb fun x _ => hD.val_le hrb x
  have hvb : D.val (z b) (Fin.natAdd n i) = false := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (D.supp (z b) (Fin.natAdd n i)).card)
    exact (mem_supp.mp hv).2.2
  have hab : D.supp (z a) (Fin.natAdd n i) ⊆ S a ∩ S b :=
    Finset.subset_inter hsa ((hD.supp_subset_supp hvb).trans hsb)
  have := Finset.card_le_card hab
  omega

/-- **Hypothesis (i) for monotone dags of fan-in `≤ 2`, at the output's own base**: the cone of
an output computing `OR S` on `{x ≥ z}` contains at least `|S| − 1` merging gates. -/
theorem card_sub_one_le_card_merge (D : Dag n s) (hD : D.Mono)
    (hfan : ∀ i, (D.gate i).inputs.length ≤ 2) (z : Fin n → Bool) {o : Fin (n + s)}
    {S : Finset (Fin n)} (ho : ∀ x, z ≤ x → D.val x o = orOf S x) (hz : orOf S z = false) :
    S.card - 1 ≤ (D.merge z o).card :=
  (D.card_sub_one_le_merge hD z ho hz).trans (D.sum_wt_le_card hfan _)

/-- **Multi-base Nechiporuk for `{∨}`-dags, WITHOUT compatibility.** A `{∨}`-dag of fan-in
`≤ 2`; each output `o w` computes `OR (S w)` on its own cube `{x ≥ z w}`, `z w` missing `S w`;
the sums pairwise share at most one variable. Then
`Σ_{w ∈ T} (|S w| − 1) ≤ |⋃_w merge (z w) (o w)| ≤ s`. Obtained from the assembly
`sum_card_sub_one_le_of_classes` with `M w = merge (z w) (o w)`. -/
theorem sum_card_sub_one_le_gates_ownBase (D : Dag n s) (hD : D.OrOnly)
    (hfan : ∀ i, (D.gate i).inputs.length ≤ 2)
    {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (z : ι → Fin n → Bool)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) (z w) = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ (T.biUnion fun w => D.merge (z w) (o w)).card ∧
      (T.biUnion fun w => D.merge (z w) (o w)).card ≤ s :=
  sum_card_sub_one_le_of_classes T S (fun w => D.merge (z w) (o w))
    (fun w hw => D.card_sub_one_le_card_merge hD.mono hfan (z w) (ho w hw) (hz w hw))
    (fun a ha b hb hab => D.merge_disjoint_multiBase hD o S z (hdisj a ha b hb hab)
      (ho a ha) (hz a ha) (ho b hb) (hz b hb))

/-! ## Sharpness: for AND/OR dags compatibility cannot be dropped

Keep `hz` (each `z w` misses its own `S w`) but drop `hcompat`. Take `n = 4`, the four sums
`{0,2}, {0,3}, {1,2}, {1,3}` (the edges of `K_{2,2}`; pairwise intersections `≤ 1`), `z w` the
indicator of the complement of `S w`, and ALL four outputs equal to the single wire
`(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)` (3 gates). On `{x ≥ z {i,j}}` this wire is `x_i ∨ x_j`, but
`Σ (|S w| − 1) = 4 > 3`. (In general `K_{p,q}`: `p + q − 1` gates against `p q`.)
By `sum_card_sub_one_le_gates_ownBase` such a counterexample must use an AND gate. -/

/-- `(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)` with three gates (wires 4, 5, 6). -/
def cexDag : Dag 4 3 :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨GateOp.and, [Src.wire ⟨0, by omega⟩, Src.wire ⟨1, by omega⟩]⟩
    | ⟨1, _⟩ => ⟨GateOp.and, [Src.wire ⟨2, by omega⟩, Src.wire ⟨3, by omega⟩]⟩
    | ⟨2, _⟩ => ⟨GateOp.or, [Src.wire ⟨4, by show 4 < 4 + 2; omega⟩,
        Src.wire ⟨5, by show 5 < 4 + 2; omega⟩]⟩⟩

def cexS : Fin 4 → Finset (Fin 4) := ![{0, 2}, {0, 3}, {1, 2}, {1, 3}]
def cexZ (w : Fin 4) : Fin 4 → Bool := fun v => decide (v ∉ cexS w)

theorem cex_val (x : Fin 4 → Bool) :
    cexDag.val x ⟨6, by omega⟩ = ((x 0 && x 1) || (x 2 && x 3)) := by
  have g0 : cexDag.val x (Fin.natAdd 4 (0 : Fin 3)) = (x 0 && x 1) := by
    rw [val_natAdd]
    show (GateOp.and).eval [cexDag.val x (Fin.castAdd 3 0), cexDag.val x (Fin.castAdd 3 1)] = _
    rw [val_castAdd, val_castAdd]
    simp [GateOp.eval]
  have g1 : cexDag.val x (Fin.natAdd 4 (1 : Fin 3)) = (x 2 && x 3) := by
    rw [val_natAdd]
    show (GateOp.and).eval [cexDag.val x (Fin.castAdd 3 2), cexDag.val x (Fin.castAdd 3 3)] = _
    rw [val_castAdd, val_castAdd]
    simp [GateOp.eval]
  show cexDag.val x (Fin.natAdd 4 (2 : Fin 3)) = _
  rw [val_natAdd]
  show (GateOp.or).eval [cexDag.val x (Fin.natAdd 4 (0 : Fin 3)),
    cexDag.val x (Fin.natAdd 4 (1 : Fin 3))] = _
  rw [g0, g1]
  simp [GateOp.eval]

theorem cex_gates (j : Fin 3) :
    ((cexDag.gate j).op = GateOp.and ∨ (cexDag.gate j).op = GateOp.or) ∧
      (cexDag.gate j).inputs.length ≤ 2 := by
  fin_cases j <;> simp [cexDag]

theorem cex_disj : ∀ a b : Fin 4, a ≠ b → (cexS a ∩ cexS b).card ≤ 1 := by decide

theorem cex_avoid : ∀ w : Fin 4, orOf (cexS w) (cexZ w) = false := by decide

theorem cex_computes (w : Fin 4) (x : Fin 4 → Bool) (hx : cexZ w ≤ x) :
    cexDag.val x ⟨6, by omega⟩ = orOf (cexS w) x := by
  rw [cex_val]
  have h : ∀ v, v ∉ cexS w → x v = true := fun v hv =>
    le_antisymm (Bool.le_true _) (le_trans (by simp [cexZ, hv]) (hx v))
  fin_cases w
  · have h1 := h 1 (by decide); have h3 := h 3 (by decide)
    simp [orOf, cexS, h1, h3]
  · have h1 := h 1 (by decide); have h3 := h 2 (by decide)
    simp [orOf, cexS, h1, h3]
  · have h1 := h 0 (by decide); have h3 := h 3 (by decide)
    simp [orOf, cexS, h1, h3]
  · have h1 := h 0 (by decide); have h3 := h 2 (by decide)
    simp [orOf, cexS, h1, h3]

/-- **Compatibility cannot be dropped for AND/OR dags.** -/
theorem multiBase_without_compat_false :
    ∃ (D : Dag 4 3) (o : Fin 4 → Fin (4 + 3)) (S : Fin 4 → Finset (Fin 4))
      (z : Fin 4 → Fin 4 → Bool),
      (∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or) ∧
      (∀ j, (D.gate j).inputs.length ≤ 2) ∧
      (∀ a ∈ (Finset.univ : Finset (Fin 4)), ∀ b ∈ (Finset.univ : Finset (Fin 4)),
        a ≠ b → (S a ∩ S b).card ≤ 1) ∧
      (∀ w ∈ (Finset.univ : Finset (Fin 4)), ∀ x, z w ≤ x → D.val x (o w) = orOf (S w) x) ∧
      (∀ w ∈ (Finset.univ : Finset (Fin 4)), orOf (S w) (z w) = false) ∧
      ¬ (∑ w ∈ (Finset.univ : Finset (Fin 4)), ((S w).card - 1) ≤ 3) :=
  ⟨cexDag, fun _ => ⟨6, by omega⟩, cexS, cexZ, fun j => (cex_gates j).1,
    fun j => (cex_gates j).2, fun a _ b _ => cex_disj a b, fun w _ => cex_computes w,
    fun w _ => cex_avoid w, by decide⟩

end Dag

end PEqualNP.Kernel
