import PEqualNP.Kernel.Circuit

/-!
# Kernel/Privacy: Wegener's Lemma 6.1 machinery at a base point

Wegener, *The Complexity of Boolean Functions*, §6.6, Lemma 6.1 (the Nechiporuk–Mehlhorn bound
for `(h, k)`-disjoint Boolean sums), here for `(1, 1)`-disjoint sums, generically over
`Dag n s` and relative to an arbitrary base point `z : Fin n → Bool` (the subcube `{x ≥ z}`;
`z = 0` is the classical case).

* `supp D z w` (written `I_z(w)` in the comments): the inputs `i` with `z i = false` whose single
  flip `z ↦ update z i true` switches wire `w` on (and `w` is off at `z`).
  - inputs: `card_supp_castAdd_le` (`|I_z(x_j)| ≤ 1`);
  - any monotone gate: `supp_natAdd_subset` (`I_z(g) ⊆ ⋃_{a read} I_z(a)`);
  - AND: `supp_and_subset` (`I_z(g) ⊆ I_z(a)` for every read `a` off at `z`, so
    `I_z(g) ⊆ ⋂_{a off at z} I_z(a)`);
  - OR: `subset_supp_or` (`I_z(a) ⊆ I_z(g)` for every read `a`, when `g` is off at `z`) and
    `supp_eq_empty_of_val` (`I_z(w) = ∅` when `w` is on at `z`);
  - restriction: `supp_restrictGE` (same support at `z` in `D.restrictGE z`) and
    `supp_restrictGE_zero` (the support of a gate of `D.restrictGE z` at base `0` is `I_z`).
* Boolean sums: `supp_eq_of_computes` (`I_z(o) = S` when `o = OR S` on `{x ≥ z}`, `S ∩ z = ∅`),
  `supp_subset_of_le` (`g ≤ o` on `{x ≥ z}` gives `I_z(g) ⊆ S`).
* **Privacy**: `privacy_of_le` (semantic), `privacy_of_readsOr` (structural: `g` below both
  outputs along OR gates), `privacy_orOnly` (OR-only dag, `g` in both cones): a wire with
  `|I_z(g)| ≥ 2` lies below at most one output of a `(1,1)`-disjoint Boolean sum.
* **Merge count**: `card_biUnion_supp_le` (union-find form, any monotone dag, any fan-in):
  `|⋃_{u ∈ F} I_z(u)| ≤ |F| + Σ_{i ∈ ⋃_{u∈F} merge u} (fanin i − 1)`, where `merge z u` is the
  set of gates in the cone of `u` with `|I_z| ≥ 2`. Per output: `card_sub_one_le_merge`.
* **Total**: `sum_card_sub_one_le` (monotone dag, counted gates below their outputs),
  `sum_card_sub_one_le_orOnly` and, with fan-in `≤ 2`, `sum_card_sub_one_le_gates`:
  `Σ_w (s_w − 1) ≤ s`.
* Wegener's (6.7) (`c = a ∨ b`): `boolSum_and_split`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open Function (update)

namespace KGate

variable {k : ℕ}

/-- A read of an OR gate is below the gate. -/
theorem le_eval_or {g : KGate k} (hg : g.op = GateOp.or) (v : Fin k → Bool) {a : Fin k}
    (ha : a ∈ g.reads) : v a ≤ g.eval v := by
  rw [Bool.le_iff_imp]
  intro hv
  rw [eval_def, hg]
  show (g.inputs.map (Src.eval v)).any id = true
  exact List.any_eq_true.mpr ⟨v a, List.mem_map.mpr ⟨Src.wire a, mem_reads.mp ha, rfl⟩, hv⟩

/-- An AND gate is below each of its reads. -/
theorem eval_and_le {g : KGate k} (hg : g.op = GateOp.and) (v : Fin k → Bool) {a : Fin k}
    (ha : a ∈ g.reads) : g.eval v ≤ v a := by
  rw [Bool.le_iff_imp]
  intro h
  rw [eval_def, hg] at h
  change (g.inputs.map (Src.eval v)).all id = true at h
  exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨Src.wire a, mem_reads.mp ha, rfl⟩)

end KGate

namespace Dag

variable {n s : ℕ}

/-! ## Boolean sums -/

theorem orOf_sup {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) :
    orOf S (x ⊔ y) = (orOf S x || orOf S y) := by
  rw [Bool.eq_iff_iff]
  simp only [orOf, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    have h' : (x v || y v) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h | h
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr ⟨v, hv, h⟩
  · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
    · exact ⟨v, hv, show (x v || y v) = true by simp [h]⟩
    · exact ⟨v, hv, show (x v || y v) = true by simp [h]⟩

/-- **Wegener (6.7), the `c = a ∨ b` argument.** On a set `A` of inputs closed under `⊔`, if a
Boolean sum `f = OR S` equals `(s ∧ t) ∨ h` with `s`, `t` monotone on `A`, then already
`f = s ∨ h` on `A` or `f = t ∨ h` on `A`. -/
theorem boolSum_and_split {n : ℕ} {A : (Fin n → Bool) → Prop}
    (hA : ∀ x y, A x → A y → A (x ⊔ y)) {S : Finset (Fin n)}
    {f s t h : (Fin n → Bool) → Bool} (hf : ∀ x, A x → f x = orOf S x)
    (hfst : ∀ x, A x → f x = ((s x && t x) || h x))
    (hs : ∀ x y, A x → A y → x ≤ y → s x ≤ s y) (ht : ∀ x y, A x → A y → x ≤ y → t x ≤ t y) :
    (∀ x, A x → f x = (s x || h x)) ∨ (∀ x, A x → f x = (t x || h x)) := by
  by_contra H
  push Not at H
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ := H
  have ka : s a = true ∧ f a = false := by
    rw [hfst a ha] at hfa ⊢
    revert hfa
    cases s a <;> cases t a <;> cases h a <;> decide
  have kb : t b = true ∧ f b = false := by
    rw [hfst b hb] at hfb ⊢
    revert hfb
    cases s b <;> cases t b <;> cases h b <;> decide
  have hc := hA a b ha hb
  have sc : s (a ⊔ b) = true :=
    Bool.le_iff_imp.mp (hs a _ ha hc le_sup_left) ka.1
  have tc : t (a ⊔ b) = true :=
    Bool.le_iff_imp.mp (ht b _ hb hc le_sup_right) kb.1
  have h1 := hfst _ hc
  rw [sc, tc, hf _ hc, orOf_sup, ← hf a ha, ← hf b hb, ka.2, kb.2] at h1
  simp at h1


/-! ## Semantic support at a base point -/

/-- `I_z(w)`: the inputs `i` off in `z` whose flip switches `w` on from `z`. -/
def supp (D : Dag n s) (z : Fin n → Bool) (w : Fin (n + s)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    z i = false ∧ D.val (update z i true) w = true ∧ D.val z w = false

theorem mem_supp {D : Dag n s} {z : Fin n → Bool} {w : Fin (n + s)} {i : Fin n} :
    i ∈ D.supp z w ↔
      z i = false ∧ D.val (update z i true) w = true ∧ D.val z w = false := by
  simp [supp]

theorem le_update (z : Fin n → Bool) (i : Fin n) : z ≤ update z i true := by
  intro j
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne h]

/-- A wire that is on at `z` has empty support. -/
theorem supp_eq_empty_of_val (D : Dag n s) (z : Fin n → Bool) (w : Fin (n + s))
    (hw : D.val z w = true) : D.supp z w = ∅ := by
  ext i
  simp [mem_supp, hw]

/-- An input wire has support at most itself. -/
theorem supp_castAdd_subset (D : Dag n s) (z : Fin n → Bool) (j : Fin n) :
    D.supp z (Fin.castAdd s j) ⊆ {j} := by
  intro i hi
  rw [mem_supp, val_castAdd, val_castAdd] at hi
  rw [Finset.mem_singleton]
  by_contra h
  have e : update z i true j = z j := Function.update_of_ne (Ne.symm h) _ _
  have := hi.2.1.symm.trans (e.trans hi.2.2)
  exact absurd this (by decide)

theorem card_supp_castAdd_le (D : Dag n s) (z : Fin n → Bool) (j : Fin n) :
    (D.supp z (Fin.castAdd s j)).card ≤ 1 :=
  (Finset.card_le_card (D.supp_castAdd_subset z j)).trans (Finset.card_singleton j).le

/-- **Monotone gates.** The support of a monotone gate is contained in the union of the
supports of the wires it reads. -/
theorem supp_natAdd_subset (D : Dag n s) (z : Fin n → Bool) (i : Fin s)
    (hi : OpMono (D.gate i).op) :
    D.supp z (Fin.natAdd n i) ⊆
      (D.gate i).reads.toFinset.biUnion fun a => D.supp z (lift i a) := by
  intro j hj
  rw [mem_supp] at hj
  obtain ⟨hzj, h1, h0⟩ := hj
  by_contra hne
  rw [Finset.mem_biUnion] at hne
  push Not at hne
  have hle : (D.gate i).eval (fun a => D.val (update z j true) (lift i a)) ≤
      (D.gate i).eval fun a => D.val z (lift i a) := by
    refine KGate.eval_mono hi fun a ha => ?_
    have := hne a (List.mem_toFinset.mpr ha)
    rw [mem_supp] at this
    rw [Bool.le_iff_imp]
    intro h
    by_contra h'
    exact this ⟨hzj, h, by simpa using h'⟩
  rw [val_natAdd] at h1 h0
  rw [h1, h0] at hle
  exact absurd hle (by decide)

/-- **AND gates.** The support of an AND gate is contained in the support of each read that is
off at `z` (so in their intersection). No monotonicity is needed. -/
theorem supp_and_subset (D : Dag n s) (z : Fin n → Bool) (i : Fin s)
    (hand : (D.gate i).op = GateOp.and) {a : Fin (n + i)} (ha : a ∈ (D.gate i).reads)
    (hza : D.val z (lift i a) = false) :
    D.supp z (Fin.natAdd n i) ⊆ D.supp z (lift i a) := by
  intro j hj
  rw [mem_supp] at hj ⊢
  refine ⟨hj.1, ?_, hza⟩
  have h1 := hj.2.1
  rw [val_natAdd] at h1
  exact Bool.le_iff_imp.mp (KGate.eval_and_le hand _ ha) h1

/-- **OR gates.** If an OR gate is off at `z`, the support of each read is contained in its
support (together with `supp_natAdd_subset`: the support is exactly the union). -/
theorem subset_supp_or (D : Dag n s) (z : Fin n → Bool) (i : Fin s)
    (hor : (D.gate i).op = GateOp.or) {a : Fin (n + i)} (ha : a ∈ (D.gate i).reads)
    (hz : D.val z (Fin.natAdd n i) = false) :
    D.supp z (lift i a) ⊆ D.supp z (Fin.natAdd n i) := by
  intro j hj
  rw [mem_supp] at hj ⊢
  refine ⟨hj.1, ?_, hz⟩
  rw [val_natAdd]
  exact Bool.le_iff_imp.mp (KGate.le_eval_or hor _ ha) hj.2.1

/-- The support at `z` is the same in `D.restrictGE z` (it only looks at the cube `{x ≥ z}`). -/
theorem supp_restrictGE (D : Dag n s) (z : Fin n → Bool) (w : Fin (n + s)) :
    (D.restrictGE z).supp z w = D.supp z w := by
  ext i
  simp only [mem_supp, D.val_restrictGE z _ (le_update z i), D.val_restrictGE z z le_rfl]

/-- **Two worlds.** The support at base `0` of a gate of `D.restrictGE z` is the support of
the gate of `D` at base `z`. -/
theorem supp_restrictGE_zero (D : Dag n s) (z : Fin n → Bool) (i : Fin s) :
    (D.restrictGE z).supp (fun _ => false) (Fin.natAdd n i) = D.supp z (Fin.natAdd n i) := by
  ext j
  have e1 : update (fun _ => false) j true ⊔ z = update z j true := by
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  have e0 : (fun _ : Fin n => false) ⊔ z = z := by funext k; simp
  simp only [mem_supp, val_restrictGE_gate, e1, e0, true_and]
  constructor
  · rintro ⟨h1, h0⟩
    refine ⟨?_, h1, h0⟩
    by_contra hz
    have : update z j true = z := by
      funext k
      by_cases h : k = j
      · subst h; simpa using hz
      · simp [Function.update_of_ne h]
    rw [this, h0] at h1
    exact absurd h1 (by decide)
  · exact fun h => h.2

/-! ## Boolean sums and the semantic privacy lemma -/

/-- If `o` computes `OR S` on `{x ≥ z}` and `S` misses `z`, the support of `o` is `S`. -/
theorem supp_eq_of_computes (D : Dag n s) (z : Fin n → Bool) {o : Fin (n + s)}
    {S : Finset (Fin n)} (ho : ∀ x, z ≤ x → D.val x o = orOf S x) (hz : orOf S z = false) :
    D.supp z o = S := by
  simp only [orOf, decide_eq_false_iff_not, not_exists, not_and] at hz
  ext i
  rw [mem_supp, ho _ (le_update z i), ho _ le_rfl]
  constructor
  · rintro ⟨_, h1, _⟩
    simp only [orOf, decide_eq_true_eq] at h1
    obtain ⟨v, hv, hxv⟩ := h1
    by_cases hvi : v = i
    · exact hvi ▸ hv
    · rw [Function.update_of_ne hvi] at hxv
      exact absurd hxv (hz v hv)
  · intro hi
    have hzi : z i = false := by simpa using hz i hi
    refine ⟨hzi, ?_, ?_⟩
    · simp only [orOf, decide_eq_true_eq]
      exact ⟨i, hi, by simp⟩
    · simpa [orOf] using hz

/-- **Semantic inclusion.** If `g ≤ o` on `{x ≥ z}`, `o = OR S` there and `S` misses `z`, then
`I_z(g) ⊆ S`. -/
theorem supp_subset_of_le (D : Dag n s) (z : Fin n → Bool) {g o : Fin (n + s)}
    {S : Finset (Fin n)} (ho : ∀ x, z ≤ x → D.val x o = orOf S x) (hz : orOf S z = false)
    (hle : ∀ x, z ≤ x → D.val x g ≤ D.val x o) : D.supp z g ⊆ S := by
  rw [← D.supp_eq_of_computes z ho hz]
  intro i hi
  rw [mem_supp] at hi ⊢
  refine ⟨hi.1, Bool.le_iff_imp.mp (hle _ (le_update z i)) hi.2.1, ?_⟩
  rw [ho _ le_rfl, hz]

/-- **Privacy (semantic form).** Outputs `o a` computing `OR (S a)` on `{x ≥ z}`, with
`S a` missing `z` and `|S a ∩ S b| ≤ 1` for `a ≠ b`. A wire `g` with `|I_z(g)| ≥ 2` that is below
two outputs on `{x ≥ z}` is below one output only (`a = b`). -/
theorem privacy_of_le (D : Dag n s) (z : Fin n → Bool) {ι : Type*} (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n)) (hdisj : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    {g : Fin (n + s)} (hg : 2 ≤ (D.supp z g).card) {a b : ι}
    (ha : ∀ x, z ≤ x → D.val x (o a) = orOf (S a) x) (hza : orOf (S a) z = false)
    (hb : ∀ x, z ≤ x → D.val x (o b) = orOf (S b) x) (hzb : orOf (S b) z = false)
    (hla : ∀ x, z ≤ x → D.val x g ≤ D.val x (o a))
    (hlb : ∀ x, z ≤ x → D.val x g ≤ D.val x (o b)) : a = b := by
  by_contra hab
  have h := Finset.card_le_card
    (Finset.subset_inter (D.supp_subset_of_le z ha hza hla) (D.supp_subset_of_le z hb hzb hlb))
  have := hdisj a b hab
  omega

/-! ## Below an output along OR gates -/

/-- `u` is an OR gate reading `v`. -/
def ReadsOr (D : Dag n s) (u v : Fin (n + s)) : Prop :=
  ∃ i : Fin s, u = Fin.natAdd n i ∧ (D.gate i).op = GateOp.or ∧
    ∃ a ∈ (D.gate i).reads, v = lift i a

/-- A wire reached from `u` along OR gates is below `u`, at every input. -/
theorem val_le_of_readsOr {D : Dag n s} {u v : Fin (n + s)}
    (h : Relation.ReflTransGen D.ReadsOr u v) (x : Fin n → Bool) : D.val x v ≤ D.val x u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨i, rfl, hor, a, ha, rfl⟩ := hbc
    refine le_trans ?_ ih
    rw [val_natAdd]
    exact KGate.le_eval_or hor (fun a => D.val x (lift i a)) ha

/-- **Privacy (OR paths).** A wire with `|I_z| ≥ 2` reached along OR gates from two outputs of a
`(1,1)`-disjoint Boolean sum (on `{x ≥ z}`) is reached from one output only. -/
theorem privacy_of_readsOr (D : Dag n s) (z : Fin n → Bool) {ι : Type*} (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n)) (hdisj : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    {g : Fin (n + s)} (hg : 2 ≤ (D.supp z g).card) {a b : ι}
    (ha : ∀ x, z ≤ x → D.val x (o a) = orOf (S a) x) (hza : orOf (S a) z = false)
    (hb : ∀ x, z ≤ x → D.val x (o b) = orOf (S b) x) (hzb : orOf (S b) z = false)
    (hpa : Relation.ReflTransGen D.ReadsOr (o a) g)
    (hpb : Relation.ReflTransGen D.ReadsOr (o b) g) : a = b :=
  D.privacy_of_le z o S hdisj hg ha hza hb hzb (fun x _ => val_le_of_readsOr hpa x)
    (fun x _ => val_le_of_readsOr hpb x)

/-- An OR-only dag (Wegener's `{∨}`-circuits). -/
def OrOnly (D : Dag n s) : Prop := ∀ i, (D.gate i).op = GateOp.or

theorem OrOnly.mono {D : Dag n s} (hD : D.OrOnly) : D.Mono :=
  fun i => hD i ▸ opMono_or

theorem OrOnly.readsOr {D : Dag n s} (hD : D.OrOnly) {u v : Fin (n + s)}
    (h : Relation.ReflTransGen D.Reads u v) : Relation.ReflTransGen D.ReadsOr u v :=
  Relation.ReflTransGen.mono (fun _ _ ⟨i, hu, a, ha, hv⟩ => ⟨i, hu, hD i, a, ha, hv⟩) _ _ h

/-- In an OR-only dag, everything in the cone of `o` is below `o`. -/
theorem OrOnly.val_le {D : Dag n s} (hD : D.OrOnly) {u v : Fin (n + s)}
    (h : Relation.ReflTransGen D.Reads u v) (x : Fin n → Bool) : D.val x v ≤ D.val x u :=
  val_le_of_readsOr (hD.readsOr h) x

/-- **Privacy (Wegener, Lemma 6.1, `(1,1)`-disjoint, at base `z`).** In an OR-only dag, a wire
with `|I_z| ≥ 2` lies in the cone of at most one output. -/
theorem privacy_orOnly (D : Dag n s) (hD : D.OrOnly) (z : Fin n → Bool) {ι : Type*}
    (o : ι → Fin (n + s)) (S : ι → Finset (Fin n)) (hdisj : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    {g : Fin (n + s)} (hg : 2 ≤ (D.supp z g).card) {a b : ι}
    (ha : ∀ x, z ≤ x → D.val x (o a) = orOf (S a) x) (hza : orOf (S a) z = false)
    (hb : ∀ x, z ≤ x → D.val x (o b) = orOf (S b) x) (hzb : orOf (S b) z = false)
    (hca : D.cone (· = o a) g) (hcb : D.cone (· = o b) g) : a = b := by
  obtain ⟨_, rfl, hra⟩ := hca
  obtain ⟨_, rfl, hrb⟩ := hcb
  exact D.privacy_of_readsOr z o S hdisj hg ha hza hb hzb (hD.readsOr hra) (hD.readsOr hrb)

/-! ## The merge count -/

theorem reads_le {D : Dag n s} {u v : Fin (n + s)} (h : Relation.ReflTransGen D.Reads u v) :
    v.1 ≤ u.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨i, rfl, a, _, rfl⟩ := hbc
    have := a.2
    simp only [lift_val, Fin.val_natAdd] at ih ⊢
    omega

open Classical in
/-- The merging gates of `w`: gates in the cone of `w` whose support has at least two
elements. -/
noncomputable def merge (D : Dag n s) (z : Fin n → Bool) (w : Fin (n + s)) : Finset (Fin s) :=
  Finset.univ.filter fun i =>
    Relation.ReflTransGen D.Reads w (Fin.natAdd n i) ∧ 2 ≤ (D.supp z (Fin.natAdd n i)).card

theorem mem_merge {D : Dag n s} {z : Fin n → Bool} {w : Fin (n + s)} {i : Fin s} :
    i ∈ D.merge z w ↔
      Relation.ReflTransGen D.Reads w (Fin.natAdd n i) ∧ 2 ≤ (D.supp z (Fin.natAdd n i)).card := by
  classical
  unfold merge
  rw [Finset.mem_filter]
  simp

/-- The weight of a gate: its fan-in minus one. -/
def wt (D : Dag n s) (i : Fin s) : ℕ := (D.gate i).inputs.length - 1

/-- A wire with support of size at least two is a gate wire. -/
theorem exists_natAdd_of_two_le (D : Dag n s) (z : Fin n → Bool) {w : Fin (n + s)}
    (hw : 2 ≤ (D.supp z w).card) : ∃ i : Fin s, w = Fin.natAdd n i := by
  by_cases hn : n ≤ w.1
  · exact ⟨⟨w.1 - n, by omega⟩, Fin.ext (by simp; omega)⟩
  · have e : w = Fin.castAdd s ⟨w.1, by omega⟩ := Fin.ext rfl
    have := D.card_supp_castAdd_le z ⟨w.1, by omega⟩
    rw [← e] at this
    omega

/-- **Merge count (union-find form).** In a monotone dag (any fan-in), for every finite set `F`
of wires: `|⋃_{u ∈ F} I_z(u)| ≤ |F| + Σ_{i ∈ ⋃_{u ∈ F} merge u} (fanin i − 1)`. -/
theorem card_biUnion_supp_le (D : Dag n s) (hD : D.Mono) (z : Fin n → Bool) :
    ∀ F : Finset (Fin (n + s)),
      (F.biUnion (D.supp z)).card ≤ F.card + ∑ i ∈ F.biUnion (D.merge z), D.wt i := by
  suffices key : ∀ m : ℕ, ∀ F : Finset (Fin (n + s)), (∀ u ∈ F, u.1 < m) →
      (F.biUnion (D.supp z)).card ≤ F.card + ∑ i ∈ F.biUnion (D.merge z), D.wt i from
    fun F => key (n + s) F fun u _ => u.2
  intro m
  induction m with
  | zero =>
    intro F hF
    have : F = ∅ := Finset.eq_empty_of_forall_notMem fun u hu => absurd (hF u hu) (by omega)
    subst this
    simp
  | succ m ih =>
    intro F hF
    by_cases hw : ∃ w ∈ F, w.1 = m
    swap
    · push Not at hw
      exact ih F fun u hu => lt_of_le_of_ne (Nat.lt_succ_iff.mp (hF u hu)) (hw u hu)
    obtain ⟨w, hwF, hwm⟩ := hw
    set F0 := F.erase w with hF0def
    have hF0 : ∀ u ∈ F0, u.1 < m := by
      intro u hu
      rw [Finset.mem_erase] at hu
      have := hF u hu.2
      refine lt_of_le_of_ne (Nat.lt_succ_iff.mp this) fun e => hu.1 (Fin.ext (e.trans hwm.symm))
    have hFeq : F = insert w F0 := (Finset.insert_erase hwF).symm
    have hcardF : F0.card + 1 = F.card := Finset.card_erase_add_one hwF
    have hψF0 : ∑ i ∈ F0.biUnion (D.merge z), D.wt i ≤ ∑ i ∈ F.biUnion (D.merge z), D.wt i :=
      Finset.sum_le_sum_of_subset
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset w F))
    by_cases hc : (D.supp z w).card ≤ 1
    · have h1 : (F.biUnion (D.supp z)).card ≤ (D.supp z w).card + (F0.biUnion (D.supp z)).card := by
        rw [hFeq, Finset.biUnion_insert]
        exact Finset.card_union_le _ _
      have := ih F0 hF0
      omega
    push Not at hc
    obtain ⟨i, rfl⟩ := D.exists_natAdd_of_two_le z hc
    have hm : n + i.1 = m := by simpa using hwm
    set R : Finset (Fin (n + s)) := (D.gate i).reads.toFinset.image (lift i) with hRdef
    have hR : ∀ u ∈ R, u.1 < m := by
      intro u hu
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      have := a.2
      simp only [lift_val]
      omega
    have hF' : ∀ u ∈ F0 ∪ R, u.1 < m := by
      intro u hu
      rcases Finset.mem_union.mp hu with h | h
      · exact hF0 u h
      · exact hR u h
    have hIH := ih (F0 ∪ R) hF'
    have hsub := D.supp_natAdd_subset z i (hD i)
    -- the supports only grow
    have h1 : F.biUnion (D.supp z) ⊆ (F0 ∪ R).biUnion (D.supp z) := by
      rw [hFeq, Finset.biUnion_insert]
      refine Finset.union_subset ?_ ?_
      · intro j hj
        obtain ⟨a, ha, hj⟩ := Finset.mem_biUnion.mp (hsub hj)
        exact Finset.mem_biUnion.mpr
          ⟨lift i a, Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha), hj⟩
      · exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
    -- the new frontier is not much larger
    have hreads : (D.gate i).reads.length ≤ (D.gate i).inputs.length :=
      List.length_filterMap_le _ _
    have h2 : (F0 ∪ R).card ≤ F0.card + (D.gate i).inputs.length :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left
        ((Finset.card_image_le).trans ((List.toFinset_card_le _).trans hreads)) _)
    have h3 : 1 ≤ (D.gate i).inputs.length := by
      by_contra h0
      have hnil : (D.gate i).reads = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil] at hsub
      have := Finset.card_le_card hsub
      simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.card_empty] at this
      omega
    -- the merging gate `i` is consumed
    have h5 : i ∈ F.biUnion (D.merge z) :=
      Finset.mem_biUnion.mpr ⟨_, hwF, mem_merge.mpr ⟨Relation.ReflTransGen.refl, hc⟩⟩
    have h4 : (F0 ∪ R).biUnion (D.merge z) ⊆ (F.biUnion (D.merge z)).erase i := by
      intro j hj
      obtain ⟨u, hu, hj⟩ := Finset.mem_biUnion.mp hj
      have hj' := mem_merge.mp hj
      have hlt := reads_le hj'.1
      rcases Finset.mem_union.mp hu with h | h
      · have hu' := hF0 u h
        refine Finset.mem_erase.mpr ⟨fun e => ?_, Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_of_mem_erase h, hj⟩⟩
        subst e
        simp only [Fin.val_natAdd] at hlt
        omega
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
        have hread : D.Reads (Fin.natAdd n i) (lift i a) :=
          ⟨i, rfl, a, List.mem_toFinset.mp ha, rfl⟩
        have := a.2
        refine Finset.mem_erase.mpr ⟨fun e => ?_, Finset.mem_biUnion.mpr
          ⟨_, hwF, mem_merge.mpr ⟨Relation.ReflTransGen.head hread hj'.1, hj'.2⟩⟩⟩
        subst e
        simp only [Fin.val_natAdd, lift_val] at hlt
        omega
    have h6 := Finset.add_sum_erase (F.biUnion (D.merge z)) D.wt h5
    have h7 : ∑ j ∈ (F0 ∪ R).biUnion (D.merge z), D.wt j ≤
        ∑ j ∈ (F.biUnion (D.merge z)).erase i, D.wt j := Finset.sum_le_sum_of_subset h4
    have h8 := Finset.card_le_card h1
    have hwi : D.wt i = (D.gate i).inputs.length - 1 := rfl
    omega

/-- **Per-output merge count.** In a monotone dag, `|I_z(w)| ≤ 1 + Σ_{i ∈ merge w} (fanin i − 1)`. -/
theorem card_supp_le (D : Dag n s) (hD : D.Mono) (z : Fin n → Bool) (w : Fin (n + s)) :
    (D.supp z w).card ≤ 1 + ∑ i ∈ D.merge z w, D.wt i := by
  simpa using D.card_biUnion_supp_le hD z {w}

/-- **Per-output merge count for a Boolean sum.** If `o` computes `OR S` on `{x ≥ z}` and `S`
misses `z`: `|S| − 1 ≤ Σ_{i ∈ merge o} (fanin i − 1)` (with fan-in `≤ 2`: at least `|S| − 1`
merging gates in the cone of `o`). -/
theorem card_sub_one_le_merge (D : Dag n s) (hD : D.Mono) (z : Fin n → Bool) {o : Fin (n + s)}
    {S : Finset (Fin n)} (ho : ∀ x, z ≤ x → D.val x o = orOf S x) (hz : orOf S z = false) :
    S.card - 1 ≤ ∑ i ∈ D.merge z o, D.wt i := by
  have := D.card_supp_le hD z o
  rw [D.supp_eq_of_computes z ho hz] at this
  omega

/-- Merging gates of two different outputs of a `(1,1)`-disjoint Boolean sum are different,
as soon as every merging gate is below its output on `{x ≥ z}`. -/
theorem merge_disjoint (D : Dag n s) (z : Fin n → Bool) {ι : Type*} (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n)) (hdisj : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) {a b : ι}
    (ha : ∀ x, z ≤ x → D.val x (o a) = orOf (S a) x) (hza : orOf (S a) z = false)
    (hb : ∀ x, z ≤ x → D.val x (o b) = orOf (S b) x) (hzb : orOf (S b) z = false)
    (hla : ∀ i ∈ D.merge z (o a), ∀ x, z ≤ x → D.val x (Fin.natAdd n i) ≤ D.val x (o a))
    (hlb : ∀ i ∈ D.merge z (o b), ∀ x, z ≤ x → D.val x (Fin.natAdd n i) ≤ D.val x (o b))
    (hab : a ≠ b) : Disjoint (D.merge z (o a)) (D.merge z (o b)) := by
  rw [Finset.disjoint_left]
  intro i hia hib
  exact hab (D.privacy_of_le z o S hdisj (mem_merge.mp hia).2 ha hza hb hzb (hla i hia)
    (hlb i hib))

/-- **Wegener, Lemma 6.1 (`h = k = 1`), at base `z`, monotone form.** A monotone dag (any
fan-in) whose outputs `o w` (`w ∈ T`) compute a `(1,1)`-disjoint Boolean sum `OR (S w)` on
`{x ≥ z}` (each `S w` missing `z`), each merging gate being below its output on `{x ≥ z}`:
`Σ_{w ∈ T} (|S w| − 1) ≤ Σ_{i merging} (fanin i − 1)`. -/
theorem sum_card_sub_one_le (D : Dag n s) (hD : D.Mono) (z : Fin n → Bool) {ι : Type*}
    (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) z = false)
    (hle : ∀ w ∈ T, ∀ i ∈ D.merge z (o w), ∀ x, z ≤ x →
      D.val x (Fin.natAdd n i) ≤ D.val x (o w)) :
    ∑ w ∈ T, ((S w).card - 1) ≤ ∑ i ∈ T.biUnion fun w => D.merge z (o w), D.wt i := by
  classical
  have hpd : (T : Set ι).PairwiseDisjoint fun w => D.merge z (o w) := by
    intro a ha b hb hab
    have := D.merge_disjoint z (fun w : T => o w) (fun w : T => S w)
      (fun a b h => hdisj a a.2 b b.2 fun e => h (Subtype.ext e))
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (ho a ha) (hz a ha) (ho b hb) (hz b hb) (hle a ha)
      (hle b hb) fun e => hab (congrArg Subtype.val e)
    exact this
  rw [Finset.sum_biUnion hpd]
  exact Finset.sum_le_sum fun w hw => D.card_sub_one_le_merge hD z (ho w hw) (hz w hw)

/-- **Lemma 6.1 for `{∨}`-dags at base `z`.** -/
theorem sum_card_sub_one_le_orOnly (D : Dag n s) (hD : D.OrOnly) (z : Fin n → Bool) {ι : Type*}
    (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) z = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ ∑ i ∈ T.biUnion fun w => D.merge z (o w), D.wt i :=
  D.sum_card_sub_one_le hD.mono z T o S hdisj ho hz fun _ _ _ hi x _ =>
    hD.val_le (mem_merge.mp hi).1 x

/-- With fan-in at most two, the weighted count is at most the number of merging gates. -/
theorem sum_wt_le_card (D : Dag n s) (hfan : ∀ i, (D.gate i).inputs.length ≤ 2)
    (B : Finset (Fin s)) : ∑ i ∈ B, D.wt i ≤ B.card := by
  have : ∑ i ∈ B, D.wt i ≤ ∑ _i ∈ B, 1 :=
    Finset.sum_le_sum fun i _ => by unfold wt; have := hfan i; omega
  simpa using this

/-- **The exact Nechiporuk bound for `(1,1)`-disjoint Boolean sums**, at base `z`, for
`{∨}`-dags of fan-in `≤ 2`: `Σ_{w ∈ T} (|S w| − 1) ≤ s`, indeed `≤` the number of merging gates
of the outputs. -/
theorem sum_card_sub_one_le_gates (D : Dag n s) (hD : D.OrOnly)
    (hfan : ∀ i, (D.gate i).inputs.length ≤ 2) (z : Fin n → Bool) {ι : Type*}
    (T : Finset ι) (o : ι → Fin (n + s)) (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) z = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ (T.biUnion fun w => D.merge z (o w)).card ∧
      (T.biUnion fun w => D.merge z (o w)).card ≤ s := by
  classical
  refine ⟨(D.sum_card_sub_one_le_orOnly hD z T o S hdisj ho hz).trans
    (D.sum_wt_le_card hfan _), ?_⟩
  simpa using Finset.card_le_univ (T.biUnion fun w => D.merge z (o w))

/-! ## Restriction to the cube -/

theorem restrictGE_orOnly (D : Dag n s) (z : Fin n → Bool) (hD : D.OrOnly) :
    (D.restrictGE z).OrOnly := fun i => hD i

@[simp] theorem wt_restrictGE (D : Dag n s) (z : Fin n → Bool) (i : Fin s) :
    (D.restrictGE z).wt i = D.wt i := by
  simp [wt, restrictGE, KGate.subst]

theorem reads_restrictGE {D : Dag n s} {z : Fin n → Bool} {u v : Fin (n + s)}
    (h : Relation.ReflTransGen (D.restrictGE z).Reads u v) : Relation.ReflTransGen D.Reads u v :=
  Relation.ReflTransGen.mono
    (fun _ _ ⟨i, hu, a, ha, hv⟩ => ⟨i, hu, a, (KGate.mem_reads_subst ha).2, hv⟩) _ _ h

/-- The merging gates of `D.restrictGE z` (at base `z`) are merging gates of `D`: the cone only
shrinks and the supports agree. -/
theorem merge_restrictGE_subset (D : Dag n s) (z : Fin n → Bool) (w : Fin (n + s)) :
    (D.restrictGE z).merge z w ⊆ D.merge z w := by
  intro i hi
  rw [mem_merge, supp_restrictGE] at hi
  exact mem_merge.mpr ⟨reads_restrictGE hi.1, hi.2⟩

end Dag

end PEqualNP.Kernel
