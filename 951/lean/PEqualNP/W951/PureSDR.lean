import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.CanonOneNot
import PEqualNP.W951.MergeRunT
import PEqualNP.W951.LiftFrac
import PEqualNP.W951.MinCE

/-!
# PureSDR: pure interval classes with pairwise disjoint merge sets close 951

The reduction for the candidate target PureSDR (board integrator 483ab00,
`951/PROOF_PLAN_SUGGESTIONS.md` §0 "Second run"; coord 10:42). A one-NOT circuit `gates` on `n`
inputs, NOT gate at position `p`, is lifted to the monotone list `lift n p gates` on `n + 1`
inputs (`Lift.lean`; the last input `y = Fin.last n` is the value of the NOT gate). `C_1` is the
lift at `y = 1`, `C_0` the lift at `y = 0`. For a set `R = S_w`:

* **I1** (`pureI1 gates p R Z`, world 1): the merge set of the union-find run of Lemma M
  (`runMT`) in the lift, zero point `(Z, 1)`, atom of `u ∈ R` the point `(e_u, 1)`. VALID when `Z`
  vanishes on `R` and `h(Z) = 0` (the NOT gate is `1` at `Z`). Neither maximality of `Z` nor
  `Z ∈ D` beyond `h(Z) = 0` is needed.
* **I0** (`pureI0 gates p R m`, world 0): zero point `(top_w, 0)`, atom of `u ∈ R` the point
  `(m_u ∪ {u}, 0)`, one point `m_u` per atom. VALID when `m_u ∩ R ⊆ {u}` and `h(m_u) = 1` (the
  NOT gate is `0` at `m_u`; `m_u` need not be a minterm, and `h(top_w) = 1` is not needed).

`PureSDR S gates p`: every set picks a valid pure option and the chosen classes are pairwise
disjoint. These are the classes `merges(W1, …)` / `merges(W0, …)` of `tools/kill_tests/ext.py`,
in LIFTED wire numbers (the lifted gate `j` is wire `n + 1 + j`; `realWire` of CanonOneNot maps it
to the real wire).

* `card_pureI1`, `card_pureI0` (GM in the lift, `merge_countT`): every valid class has at least
  `d_w = |S_w| - 1` merges. Uses correctness of the output through `val_lift` / `lift_exact`.
* `pureCls_subset`: every class lies in the `gates.length - 1` gate wires of the lift.
* Disjointness of the merge sets themselves (`runMT_disjoint_of_le`, D for any monotone list):
  `disjoint_pureI1_pureI1` (W1), `disjoint_pureI0_pureI0` (W0), `disjoint_pureI0_pureI1` (D across
  worlds), with explicit pair conditions, and `disjoint_pureI1_top`, `disjoint_pureI0_avoid`, `disjoint_pureI0_top` for
  `|S_w ∩ S_w'| ≤ 1`.
* `bound_of_pureSDR`: PureSDR ⇒ `∑ (|S_w| - 1) ≤ gates.length - 1`.
* `no_minCE_of_pureSDR`: PureSDR at every minimal counterexample closes `no_minCE`;
  `no_minCE_of_pureSDR'`: the same with PureSDR for the (unique) NOT gate.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureSDR

variable {n : ℕ}

/-! ## Test points -/

/-- World-1 atoms: the atom of the lifted coordinate `c` is `{c, y}` (so `(e_u, 1)` for
`c = u`). -/
def atom1 (c : Fin (n + 1)) : Fin (n + 1) → Bool := canonPt {c, Fin.last n}

/-- World-0 atoms for the points `m u`: the atom of the lifted coordinate `u` is `(m_u ∪ {u}, 0)`
(the atom of `y` itself is never used). -/
def atom0 (m : Fin n → Finset (Fin n)) (c : Fin (n + 1)) : Fin (n + 1) → Bool :=
  if h : c = Fin.last n then canonPt ∅ else canonPt (insert c (liftSet (m (c.castPred h))))

theorem atom1_castSucc (u : Fin n) : atom1 (Fin.castSucc u) = ext (canonPt {u}) true := by
  rw [atom1, ← atom1_eq]

theorem atom0_castSucc (m : Fin n → Finset (Fin n)) (u : Fin n) :
    atom0 m (Fin.castSucc u) = ext (canonPt (insert u (m u))) false := by
  rw [atom0, dite_eq_right (Fin.castSucc_ne_last u), Fin.castPred_castSucc, atom0_eq]

theorem mem_liftSet_iff {R : Finset (Fin n)} {c : Fin (n + 1)} :
    c ∈ liftSet R ↔ ∃ u ∈ R, Fin.castSucc u = c := by
  simp [liftSet]

theorem card_liftSet (R : Finset (Fin n)) : (liftSet R).card = R.card := by
  rw [liftSet, Finset.card_map]

/-! ## The classes -/

/-- **I1**: the merge set (lifted wires) at zero point `(Z, 1)`, atoms `(e_u, 1)`, `u ∈ R`. -/
noncomputable def pureI1 (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (Z : Fin n → Bool) :
    Finset ℕ :=
  runMT (ext Z true) atom1 (liftSet R) (lift n p gates) (lift n p gates).length

/-- **I0**: the merge set (lifted wires) at zero point `(top_w, 0)`, atoms `(m_u ∪ {u}, 0)`. -/
noncomputable def pureI0 (gates : List Gate) (p : ℕ) (R : Finset (Fin n))
    (m : Fin n → Finset (Fin n)) : Finset ℕ :=
  runMT (ext (Zof R) false) (atom0 m) (liftSet R) (lift n p gates) (lift n p gates).length

/-- A pure option: world 1 with zero point `Z`, or world 0 with atom points `m`. -/
inductive PureOpt (n : ℕ) where
  | one (Z : Fin n → Bool)
  | zero (m : Fin n → Finset (Fin n))

/-- The class of a pure option. -/
noncomputable def pureCls (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) : PureOpt n → Finset ℕ
  | .one Z => pureI1 gates p R Z
  | .zero m => pureI0 gates p R m

/-- Validity of a pure option for the set `R` (NOT gate at `p`, wire `n + p`). -/
def PureValid (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) : PureOpt n → Prop
  | .one Z => (∀ v ∈ R, Z v = false) ∧ val gates Z (n + p) = true
  | .zero m => (∀ u ∈ R, ∀ v ∈ m u, v ∈ R → v = u) ∧ ∀ u ∈ R, val gates (canonPt (m u)) (n + p) = false

/-- **PureSDR** (for the NOT gate at `p`): every set picks a valid pure option, and the chosen
classes are pairwise disjoint. -/
def PureSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) : Prop :=
  ∃ c : Fin m → PureOpt n, (∀ w, PureValid gates p (S w) (c w)) ∧
    ∀ w w', w ≠ w' → Disjoint (pureCls gates p (S w) (c w)) (pureCls gates p (S w') (c w'))

/-! ## Sizes (GM in the lift) -/

theorem goodT_of_monoList {N : ℕ} (z : Fin N → Bool) (q : Fin N → Fin N → Bool)
    (R : Finset (Fin N)) (gs : List Gate) (hm : MonoList gs) : GoodT z q R gs := by
  intro pre g rest h
  left
  exact hm g (by rw [h]; simp)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **I1 size.** `Z` vanishing on `R`, NOT gate `1` at `Z`, `o` computing `OR_R`: at least
`|R| - 1` merges. -/
theorem card_pureI1 (R : Finset (Fin n)) (Z : Fin n → Bool) (hZR : ∀ v ∈ R, Z v = false)
    (hZ : val gates Z (n + p) = true) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) :
    R.card - 1 ≤ (pureI1 gates p R Z).card := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hT : ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom1 c c' = true → ext Z true c' = false →
      c' = c := by
    intro c _ c' h1 h2
    rw [atom1, canonPt_eq_true, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact h1
    · rw [h1, ext_last] at h2
      exact absurd h2 (by decide)
  have hz : val (lift n p gates) (ext Z true) (liftWire n p o) = false := by
    have hl := val_lift (n := n) gates p hp Z o
    rw [hZ, hev] at hl
    rw [← hl]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    rw [hZR v hv] at hzv
    exact absurd hzv (by decide)
  have hao : ∀ c ∈ liftSet R, val (lift n p gates) (atom1 c) (liftWire n p o) = true := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    rw [atom1_castSucc]
    refine (lift_exact (n := n) gates p hp hg hU hN (canonPt {u}) o).2.1 ?_
    rw [hev]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_singleton_self _)⟩
  have := merge_countT (ext Z true) atom1 (liftSet R) (lift n p gates) hT
    (goodT_of_monoList _ _ _ _ hm) (liftWire n p o) hz hao
  rwa [card_liftSet] at this

include hg hU hN in
/-- **I0 size.** `m_u ∩ R ⊆ {u}` and NOT gate `0` at every `m_u`, `o` computing `OR_R`: at least
`|R| - 1` merges. -/
theorem card_pureI0 (R : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (hmR : ∀ u ∈ R, ∀ v ∈ m u, v ∈ R → v = u)
    (hmN : ∀ u ∈ R, val gates (canonPt (m u)) (n + p) = false) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) :
    R.card - 1 ≤ (pureI0 gates p R m).card := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hT : ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom0 m c c' = true →
      ext (Zof R) false c' = false → c' = c := by
    intro c hc c' h1 h2
    obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    rw [atom0_castSucc] at h1
    induction c' using Fin.lastCases with
    | last => rw [ext_last] at h1; exact absurd h1 (by decide)
    | cast v =>
      rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
      rw [ext_castSucc] at h2
      have hvR : v ∈ R := by simpa [Zof] using h2
      rcases h1 with rfl | h1
      · rfl
      · rw [hmR u hu v h1 hvR]
  have hz : val (lift n p gates) (ext (Zof R) false) (liftWire n p o) = false := by
    have h1 := (lift_exact (n := n) gates p hp hg hU hN (Zof R) o).1
    cases hv : val (lift n p gates) (ext (Zof R) false) (liftWire n p o)
    · rfl
    · have := h1 hv
      rw [hev] at this
      simp [Zof] at this
  have hao : ∀ c ∈ liftSet R, val (lift n p gates) (atom0 m c) (liftWire n p o) = true := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    rw [atom0_castSucc]
    have hle : canonPt (m u) ≤ canonPt (insert u (m u)) := by
      intro c
      refine Bool.le_iff_imp.mpr fun hc => ?_
      exact canonPt_eq_true.mpr (Finset.mem_insert_of_mem (canonPt_eq_true.mp hc))
    have hν := not_false_of_le gates p hp hg hU hN hle (hmN u hu)
    have hl := val_lift (n := n) gates p hp (canonPt (insert u (m u))) o
    rw [hν] at hl
    rw [← hl, hev]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_insert_self _ _)⟩
  have := merge_countT (ext (Zof R) false) (atom0 m) (liftSet R) (lift n p gates) hT
    (goodT_of_monoList _ _ _ _ hm) (liftWire n p o) hz hao
  rwa [card_liftSet] at this

include hg hU hN in
/-- Every valid pure class has at least `|R| - 1` merges. -/
theorem card_pureCls (R : Finset (Fin n)) (c : PureOpt n) (hc : PureValid gates p R c) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) :
    R.card - 1 ≤ (pureCls gates p R c).card := by
  cases c with
  | one Z => exact card_pureI1 gates p hp hg hU hN R Z hc.1 hc.2 o hev
  | zero m => exact card_pureI0 gates p hp hg hU hN R m hc.1 hc.2 o hev

/-- Every class lies in the gate wires of the lift. -/
theorem pureCls_subset (R : Finset (Fin n)) (c : PureOpt n) :
    pureCls gates p R c ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
  classical
  intro i hi
  have hsub : ∀ {z : Fin (n + 1) → Bool} {q : Fin (n + 1) → Fin (n + 1) → Bool},
      i ∈ runMT z q (liftSet R) (lift n p gates) (lift n p gates).length →
        i ∈ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
    intro z q h
    have := run_sub_DT z q (liftSet R) (lift n p gates) _ h
    rw [DT, Finset.mem_filter] at this
    exact this.1
  cases c with
  | one Z => exact hsub hi
  | zero m => exact hsub hi

/-! ## Disjointness of pure classes (W0, W1, D across worlds, for the merge sets themselves) -/

/-- **D for merge sets** (any monotone list): if of any two atoms of the first system one lies
below the zero point of the second, the two merge sets are disjoint. A wire in both is false at
`z'`, true at two atoms of the first system, and monotone. -/
theorem runMT_disjoint_of_le {N : ℕ} (gs : List Gate) (hm : MonoList gs) (z z' : Fin N → Bool)
    (q q' : Fin N → Fin N → Bool) (R R' : Finset (Fin N))
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → q u ≤ z' ∨ q v ≤ z') :
    Disjoint (runMT z q R gs gs.length) (runMT z' q' R' gs gs.length) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hi'
  have h1 := run_sub_DT z q R gs _ hi
  have h2 := run_sub_DT z' q' R' gs _ hi'
  rw [DT, Finset.mem_filter] at h1 h2
  obtain ⟨-, -, u, v, huv, hu, hv, hui, hvi⟩ := h1
  have hz' := h2.2.1
  rcases h u hu v hv huv with hle | hle
  · have := val_le_of_le gs hm.andOr hle i
    rw [hui, hz'] at this
    exact absurd this (by decide)
  · have := val_le_of_le gs hm.andOr hle i
    rw [hvi, hz'] at this
    exact absurd this (by decide)

theorem ext_le_of_le {x x' : Fin n → Bool} {b b' : Bool} (hx : x ≤ x') (hb : b ≤ b') :
    ext x b ≤ ext x' b' := by
  intro c
  induction c using Fin.lastCases with
  | last => rw [ext_last, ext_last]; exact hb
  | cast c => rw [ext_castSucc, ext_castSucc]; exact hx c

theorem canonPt_le {A : Finset (Fin n)} {x : Fin n → Bool} (h : ∀ c ∈ A, x c = true) :
    canonPt A ≤ x := by
  intro c
  refine Bool.le_iff_imp.mpr fun hc => h c (canonPt_eq_true.mp hc)

theorem canonPt_le_Zof {A R' : Finset (Fin n)} (h : Disjoint A R') : canonPt A ≤ Zof R' :=
  canonPt_le fun c hc => by simpa [Zof] using Finset.disjoint_left.mp h hc

/-- Pairs of distinct lifted coordinates of `liftSet R` come from pairs of distinct points of `R`. -/
theorem liftSet_pairs {R : Finset (Fin n)} {P : Fin (n + 1) → Prop}
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → P (Fin.castSucc u) ∨ P (Fin.castSucc v)) :
    ∀ c ∈ liftSet R, ∀ c' ∈ liftSet R, c ≠ c' → P c ∨ P c' := by
  intro c hc c' hc' hcc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp hc'
  exact h u hu v hv fun huv => hcc (huv ▸ rfl)

include hg hU hN in
/-- **W1 for pure classes.** `I1(R, Z) ∩ I1(R', Z') = ∅` when `Z'` is true at one of any two
points of `R`. -/
theorem disjoint_pureI1_pureI1 (R R' : Finset (Fin n)) (Z Z' : Fin n → Bool)
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → Z' u = true ∨ Z' v = true) :
    Disjoint (pureI1 gates p R Z) (pureI1 gates p R' Z') := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  rw [atom1_castSucc, atom1_castSucc]
  rcases h u hu v hv huv with h1 | h1
  · exact Or.inl (ext_le_of_le (canonPt_le fun c hc => by rw [Finset.mem_singleton.mp hc]; exact h1)
      le_rfl)
  · exact Or.inr (ext_le_of_le (canonPt_le fun c hc => by rw [Finset.mem_singleton.mp hc]; exact h1)
      le_rfl)

include hg hU hN in
/-- **D across worlds for pure classes.** `I0(R, m) ∩ I1(R', Z') = ∅` when `Z'` is true on one of
`m_u ∪ {u}`, `m_v ∪ {v}` for any two points `u ≠ v` of `R`. -/
theorem disjoint_pureI0_pureI1 (R R' : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (Z' : Fin n → Bool)
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v →
      (∀ c ∈ insert u (m u), Z' c = true) ∨ ∀ c ∈ insert v (m v), Z' c = true) :
    Disjoint (pureI0 gates p R m) (pureI1 gates p R' Z') := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  rw [atom0_castSucc, atom0_castSucc]
  rcases h u hu v hv huv with h1 | h1
  · exact Or.inl (ext_le_of_le (canonPt_le h1) (by decide))
  · exact Or.inr (ext_le_of_le (canonPt_le h1) (by decide))

include hg hU hN in
/-- **W0 for pure classes.** `I0(R, m) ∩ I0(R', m') = ∅` when one of `m_u ∪ {u}`, `m_v ∪ {v}`
avoids `R'` for any two points `u ≠ v` of `R`. -/
theorem disjoint_pureI0_pureI0 (R R' : Finset (Fin n)) (m m' : Fin n → Finset (Fin n))
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → Disjoint (insert u (m u)) R' ∨ Disjoint (insert v (m v)) R') :
    Disjoint (pureI0 gates p R m) (pureI0 gates p R' m') := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  rw [atom0_castSucc, atom0_castSucc]
  rcases h u hu v hv huv with h1 | h1
  · exact Or.inl (ext_le_of_le (canonPt_le_Zof h1) le_rfl)
  · exact Or.inr (ext_le_of_le (canonPt_le_Zof h1) le_rfl)

/-- With `|R ∩ R'| ≤ 1`, a point false only on `R'` is true at one of any two points of `R`. -/
theorem pair_true_of_inter (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1)
    (P : Fin n → Prop) (hP : ∀ u, u ∉ R' → P u) :
    ∀ u ∈ R, ∀ v ∈ R, u ≠ v → P u ∨ P v := by
  intro u hu v hv huv
  by_cases hu' : u ∈ R'
  · by_cases hv' : v ∈ R'
    · have hsub : ({u, v} : Finset (Fin n)) ⊆ R ∩ R' := by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact Finset.mem_inter.mpr ⟨hu, hu'⟩
        · rw [Finset.mem_singleton.mp hc]; exact Finset.mem_inter.mpr ⟨hv, hv'⟩
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_pair huv] at h2
      omega
    · exact Or.inr (hP v hv')
  · exact Or.inl (hP u hu')

include hg hU hN in
/-- **W1 at `top`-type zero points.** `|S_w ∩ S_w'| ≤ 1` and `Z'` false only on `R'` (e.g.
`Z' = top_w'`) ⇒ `I1(R, Z) ∩ I1(R', Z') = ∅`. -/
theorem disjoint_pureI1_top (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1) (Z Z' : Fin n → Bool)
    (hZ' : ∀ c, Z' c = false → c ∈ R') : Disjoint (pureI1 gates p R Z) (pureI1 gates p R' Z') :=
  disjoint_pureI1_pureI1 gates p hp hg hU hN R R' Z Z'
    (pair_true_of_inter R R' hRR _ fun u hu => by
      by_contra h
      exact hu (hZ' u (by simpa using h)))

include hg hU hN in
/-- **W0 with avoiding points.** `|S_w ∩ S_w'| ≤ 1` and every `m_u` (`u ∈ R`) avoiding `R'` ⇒
`I0(R, m) ∩ I0(R', m') = ∅`. -/
theorem disjoint_pureI0_avoid (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1)
    (m m' : Fin n → Finset (Fin n)) (hm : ∀ u ∈ R, Disjoint (m u) R') :
    Disjoint (pureI0 gates p R m) (pureI0 gates p R' m') := by
  refine disjoint_pureI0_pureI0 gates p hp hg hU hN R R' m m' fun u hu v hv huv => ?_
  rcases pair_true_of_inter R R' hRR (fun u => u ∈ R → Disjoint (insert u (m u)) R')
      (fun u hu' hu => Finset.disjoint_insert_left.mpr ⟨hu', hm u hu⟩) u hu v hv huv with h | h
  · exact Or.inl (h hu)
  · exact Or.inr (h hv)

include hg hU hN in
/-- **D across worlds at `top`-type zero points.** `|S_w ∩ S_w'| ≤ 1`, `Z'` false only on `R'`
and every `m_u` (`u ∈ R`) avoiding `R'` ⇒ `I0(R, m) ∩ I1(R', Z') = ∅`. -/
theorem disjoint_pureI0_top (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1)
    (m : Fin n → Finset (Fin n)) (hm : ∀ u ∈ R, Disjoint (m u) R') (Z' : Fin n → Bool)
    (hZ' : ∀ c, Z' c = false → c ∈ R') : Disjoint (pureI0 gates p R m) (pureI1 gates p R' Z') := by
  have hT : ∀ u ∈ R, u ∉ R' → ∀ c ∈ insert u (m u), Z' c = true := by
    intro u hu hu' c hc
    by_contra h
    have hcR' := hZ' c (by simpa using h)
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hu' hcR'
    · exact Finset.disjoint_left.mp (hm u hu) hc hcR'
  refine disjoint_pureI0_pureI1 gates p hp hg hU hN R R' m Z' fun u hu v hv huv => ?_
  rcases pair_true_of_inter R R' hRR (fun u => u ∈ R → ∀ c ∈ insert u (m u), Z' c = true)
      (fun u hu' hu => hT u hu hu') u hu v hv huv with h | h
  · exact Or.inl (h hu)
  · exact Or.inr (h hv)

/-! ## The bound and the reduction -/

include hg hU hN in
/-- **PureSDR ⇒ the bound with one gate to spare**: `∑ (|S_w| - 1) ≤ gates.length - 1`. -/
theorem bound_of_pureSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : PureSDR S gates p) : ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  classical
  obtain ⟨c, hc, hdis⟩ := H
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => pureCls gates p (S w) (c w) :=
    fun w _ w' _ hww => hdis w w' hww
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (pureCls gates p (S w) (c w)).card :=
        Finset.sum_le_sum fun w _ => card_pureCls gates p hp hg hU hN (S w) (c w) (hc w) (out w) (hev w)
    _ = (Finset.univ.biUnion fun w => pureCls gates p (S w) (c w)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ => pureCls_subset gates p (S w) (c w))
    _ = gates.length - 1 := by rw [Nat.card_Ico, length_lift n p gates hp]; omega

end PureSDR

/-- **951 from PureSDR**: if every minimal counterexample has a NOT gate with a PureSDR, there is
no minimal counterexample. -/
theorem no_minCE_of_pureSDR
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ PureSDR S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, hN, hP⟩ := H n m S gates out M
  have h1 := bound_of_pureSDR gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev hP
  have h2 := M.ce.hlt
  omega

/-- **951 from PureSDR for the NOT gate**: the same with PureSDR asked for every NOT gate (there is
exactly one: `MinCE.exists_not`, `AtMostOneNot`). -/
theorem no_minCE_of_pureSDR'
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
        PureSDR S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_pureSDR fun n m S gates out M => by
    obtain ⟨p, hp, hN⟩ := M.exists_not
    exact ⟨p, hp, hN, H n m S gates out M p hp hN⟩

end PEqualNP.Outside.L_meta_951_aux
