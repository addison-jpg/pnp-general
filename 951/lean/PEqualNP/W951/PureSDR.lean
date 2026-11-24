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
