import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.CanonClass
import PEqualNP.W951.CanonOneNot
import PEqualNP.W951.Lift
import PEqualNP.W951.LiftHelpers
import PEqualNP.W951.Cases

/-!
# CanonD1: lemma D at every I1 point (candidate "D1") — per-atom D proved, D1 REFUTED

Notation of `CanonOneNot.lean`. For a set `R = S_w` and a zero point `Z` of `w`, `K1Z gates p R Z`
is the world-1 class at `Z` (OR gates of the lift `0` at `(Z, 1)` and `1` at `(e_u, 1)` for two
`u ∈ R` or more); `K1Z gates p R (Zof R) = K1 gates p R`. For a set `R' = S_v` and an I0 choice
`m : Fin n → Finset (Fin n)` (`m u'` the minterm chosen for the atom `u' ∈ R'`), `K0of gates p R' m`
is the world-0 class with per-atom bases (OR gates `0` at `(top_v, 0)` and `1` at
`(m u' + e_u', 0)` for two `u' ∈ R'` or more); `K0of gates p R' (fun _ => m) = K0 gates p R' m`.

* `disjoint_K0of_K1` (**D at `top_w`, per-atom choices**): `K_0(v; (m_u')) ∩ K_1(w) = ∅` for
  `|S_v ∩ S_w| ≤ 1` once every `m_u' ∩ S_w = ∅`. (CanonOneNot's `disjoint_K0_K1` has one common `m`.)
* `disjoint_K0of_K1Z_of_le` (D's argument at an arbitrary `Z`): disjoint whenever of any two
  world-0 atoms of `v` one lies below `Z` (as a real point, `m u' ∪ {u'} ⊆ Z`).
* `atom0_not_le_Z`, `atom1_not_le_ext_false` (**where `Z ≠ top_w` breaks D**): if the NOT gate is
  `1` at `Z` (`h(Z) = 0`) and `0` at `m` (`h(m) = 1`), then NO world-0 atom `(m + e_u', 0)` lies
  below `(Z, 1)`; and no world-1 atom `(e_u, 1)` lies below any `(Z', 0)`. So neither orientation of
  `orClz_disjoint` applies to `K1Z(w; Z)` against `K0of(v; m)` once `|S_v| ≥ 2`
  (`D_hyp_fails`), for EVERY I1 point `Z`, including `Z = top_w` when `h(top_w) = 0`
  (there D is used against minterms avoiding `S_w`, which `top_w` contains: `h(top_w) = 1`).
* `D1Stmt` (the candidate as a `Prop`, over all correct one-NOT circuits) and `not_D1Stmt`:
  **D1 is false**. Counterexample on `n = 5`, `S_w = {0,1}`, `S_v = {2,3}`, `h = x_4`,
  `Z = top_w \ {4} = {2,3}`, `m_2 = m_3 = {4}`: the gate
  `g = (y ∧ x_0 ∨ x_4 ∧ x_2) ∨ (y ∧ x_1 ∨ x_4 ∧ x_3)` lies in both classes (also in both merge
  sets of `tools/kill_tests/canon.py`; `typeA.py` reports the collision).

Fully proved, no `sorry`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CanonD1

variable {n : ℕ}

/-! ## The classes at an arbitrary zero point / with per-atom bases -/

/-- **`K_1(w; Z)`** (world 1 at the zero point `Z`), as real wires. -/
noncomputable def K1Z (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (Z : Fin n → Bool) :
    Finset ℕ :=
  (orClz (lift n p gates) (ext Z true)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) {Fin.last n}))).image (realWire n p)

/-- **`K_0(v; (m_u'))`** (world 0, one base `m u'` per atom `u' ∈ R`), as real wires. -/
noncomputable def K0of (gates : List Gate) (p : ℕ) (R : Finset (Fin n))
    (m : Fin n → Finset (Fin n)) : Finset ℕ :=
  (orClz (lift n p gates) (ext (Zof R) false)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) (liftSet (m (enumF R t)))))).image
    (realWire n p)

theorem K1Z_top (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) :
    K1Z gates p R (Zof R) = K1 gates p R := rfl

theorem K0of_const (gates : List Gate) (p : ℕ) (R m : Finset (Fin n)) :
    K0of gates p R (fun _ => m) = K0 gates p R m := rfl

/-! ## Points -/

theorem d1_ext_le_ext {x z : Fin n → Bool} {b b' : Bool} (hxz : x ≤ z) (hb : b ≤ b') :
    ext x b ≤ ext z b' := by
  intro c
  induction c using Fin.lastCases with
  | last => rw [ext_last, ext_last]; exact hb
  | cast c => rw [ext_castSucc, ext_castSucc]; exact hxz c

theorem le_of_ext_le {x z : Fin n → Bool} {b b' : Bool} (h : ext x b ≤ ext z b') : x ≤ z := by
  intro c
  have := h (Fin.castSucc c)
  rwa [ext_castSucc, ext_castSucc] at this

theorem canonPt_mono {A B : Finset (Fin n)} (h : A ⊆ B) : canonPt A ≤ canonPt B := by
  intro c
  refine Bool.le_iff_imp.mpr fun hc => ?_
  exact canonPt_eq_true.mpr (h (canonPt_eq_true.mp hc))

/-- A world-0 atom `(M + e_u, 0)` lies below `(top_{R'}, 1)` if `u ∉ R'` and `M ∩ R' = ∅`. -/
theorem atom0_le_top (R' M : Finset (Fin n)) (u : Fin n) (hu : u ∉ R') (hM : Disjoint M R') :
    canonPt (insert (Fin.castSucc u) (liftSet M)) ≤ ext (Zof R') true := by
  rw [atom0_eq]
  refine d1_ext_le_ext (fun c => Bool.le_iff_imp.mpr fun hc => ?_) (by decide)
  have hc' := canonPt_eq_true.mp hc
  simp only [Zof, decide_eq_true_eq]
  rcases Finset.mem_insert.mp hc' with rfl | hc'
  · exact hu
  · exact Finset.disjoint_left.mp hM hc'

/-! ## D at `top_w` with per-atom choices -/

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **D, general zero point.** `K_0(v; (m_u')) ∩ K_1(w; Z) = ∅` whenever of any two distinct
`u, u' ∈ S_v` one has `m_u ∪ {u} ⊆ Z` (as points: `canonPt (insert u (m u)) ≤ Z`). -/
theorem disjoint_K0of_K1Z_of_le (R R' : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (Z : Fin n → Bool)
    (hle : ∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
      canonPt (insert u (m u)) ≤ Z ∨ canonPt (insert u' (m u')) ≤ Z) :
    Disjoint (K0of gates p R m) (K1Z gates p R' Z) := by
  classical
  rw [K0of, K1Z, Finset.disjoint_image (realWire_injective n p)]
  refine orClz_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _
    fun s t hst => ?_
  have hne : enumF R s ≠ enumF R t := fun h => hst (enumF_injective R h)
  rcases hle _ (enumF_mem R s) _ (enumF_mem R t) hne with h | h
  · left; rw [atom0_eq]; exact d1_ext_le_ext h (by decide)
  · right; rw [atom0_eq]; exact d1_ext_le_ext h (by decide)

include hg hU hN in
/-- **D at `top_w`, per-atom I0 choices.** `K_0(v; (m_u')) ∩ K_1(w) = ∅` for `|S_v ∩ S_w| ≤ 1`
once every `m_u'` (`u' ∈ S_v`) avoids `S_w`. -/
theorem disjoint_K0of_K1 (R R' : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (hRR : (R ∩ R').card ≤ 1) (hm : ∀ u ∈ R, Disjoint (m u) R') :
    Disjoint (K0of gates p R m) (K1 gates p R') := by
  classical
  rw [K0of, K1, Finset.disjoint_image (realWire_injective n p)]
  refine orClz_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _
    fun s t hst => ?_
  have hne : enumF R s ≠ enumF R t := fun h => hst (enumF_injective R h)
  by_cases hs : enumF R s ∈ R'
  · right
    refine atom0_le_top R' _ _ (fun ht => ?_) (hm _ (enumF_mem R t))
    have hsub : ({enumF R s, enumF R t} : Finset (Fin n)) ⊆ R ∩ R' := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact Finset.mem_inter.mpr ⟨enumF_mem R s, hs⟩
      · rw [Finset.mem_singleton.mp hc]
        exact Finset.mem_inter.mpr ⟨enumF_mem R t, ht⟩
    have h2 := Finset.card_pair hne
    have h3 := Finset.card_le_card hsub
    omega
  · exact Or.inl (atom0_le_top R' _ _ hs (hm _ (enumF_mem R s)))

/-! ## Where `Z ≠ top_w` breaks D -/

include hg hU hN in
/-- **The obstruction.** If the NOT gate is `1` at `Z` (`h(Z) = 0`) and `0` at `canonPt M`
(`h(M) = 1`), then no world-0 atom `(M + e_u, 0)` lies below `(Z, 1)`. -/
theorem atom0_not_le_Z (Z : Fin n → Bool) (M : Finset (Fin n)) (u : Fin n)
    (hZ : val gates Z (n + p) = true) (hM : val gates (canonPt M) (n + p) = false) :
    ¬ canonPt (insert (Fin.castSucc u) (liftSet M)) ≤ ext Z true := by
  intro hle
  rw [atom0_eq] at hle
  have h1 : canonPt M ≤ Z :=
    (canonPt_mono (Finset.subset_insert u M)).trans (le_of_ext_le hle)
  have := not_false_of_le gates p hp hg hU hN h1 hM
  rw [hZ] at this
  exact absurd this (by decide)

/-- No world-1 atom `(A, 1)` lies below a world-0 point `(Z', 0)`. -/
theorem atom1_not_le_ext_false (A : Finset (Fin (n + 1))) (Z' : Fin n → Bool) :
    ¬ canonPt (insert (Fin.last n) A) ≤ ext Z' false := by
  intro hle
  have := hle (Fin.last n)
  rw [ext_last, canonPt_eq_true.mpr (Finset.mem_insert_self _ _)] at this
  exact absurd this (show ¬ (true ≤ false) from fun h => Bool.noConfusion (h rfl))

include hg hU hN in
/-- **D's hypothesis fails at every I1 point.** If the NOT gate is `1` at `Z` and `0` at every
chosen `m u'`, and `S_v` has two distinct points, the hypothesis of `orClz_disjoint` (first system
`K_0(v; m)`, second zero point `(Z, 1)`) is false. -/
theorem D_hyp_fails (R : Finset (Fin n)) (m : Fin n → Finset (Fin n)) (Z : Fin n → Bool)
    (hZ : val gates Z (n + p) = true)
    (hm : ∀ u ∈ R, val gates (canonPt (m u)) (n + p) = false) (h2 : 1 < R.card) :
    ¬ ∀ s t : Fin R.card, s ≠ t →
      canonPt (insert (Fin.castSucc (enumF R s)) (liftSet (m (enumF R s)))) ≤ ext Z true ∨
      canonPt (insert (Fin.castSucc (enumF R t)) (liftSet (m (enumF R t)))) ≤ ext Z true := by
  intro h
  have hne : (⟨0, by omega⟩ : Fin R.card) ≠ ⟨1, h2⟩ := by simp [Fin.ext_iff]
  rcases h _ _ hne with h' | h'
  · exact atom0_not_le_Z gates p hp hg hU hN Z _ _ hZ (hm _ (enumF_mem R _)) h'
  · exact atom0_not_le_Z gates p hp hg hU hN Z _ _ hZ (hm _ (enumF_mem R _)) h'

end CanonD1

/-! ## D1 as stated is false -/

/-- **Candidate D1** over all correct one-NOT circuits: `w ≠ v` given by `R = S_w`, `R' = S_v`
(`|S_w ∩ S_v| ≤ 1`, outputs `o`, `o'` computing `OR_R`, `OR_R'`); `Z` an I1 point of `w` (false on
`R`, `h(Z) = 0`, maximal); `m` an I0 choice of `v` (each `m u'`, `u' ∈ R'`, a minterm of `h` with
`m u' ∩ R' ⊆ {u'}`) with every `m u' ∩ R = ∅`. Then `K_1(w; Z) ∩ K_0(v; m) = ∅`. -/
def D1Stmt : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (p : ℕ) (hp : p < gates.length),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    AtMostOneNot gates → (gates[p]'hp).op = GateOp.not →
    ∀ (R R' : Finset (Fin n)) (o o' : ℕ), (R ∩ R').card ≤ 1 →
    (∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) →
    (∀ x : Fin n → Bool, val gates x o' = decide (∃ v ∈ R', x v = true)) →
    ∀ (Z : Fin n → Bool), (∀ c ∈ R, Z c = false) → val gates Z (n + p) = true →
    (∀ c, c ∉ R → Z c = false → val gates (Function.update Z c true) (n + p) = false) →
    ∀ (m : Fin n → Finset (Fin n)),
    (∀ u ∈ R', val gates (canonPt (m u)) (n + p) = false ∧
      (∀ c ∈ m u, val gates (canonPt ((m u).erase c)) (n + p) = true) ∧
      m u ∩ R' ⊆ {u} ∧ Disjoint (m u) R) →
    Disjoint (K1Z gates p R Z) (K0of gates p R' m)

/-- The counterexample circuit on `n = 5` (wires `0..4` inputs, wire `5 + k` gate `k`):
`y = ¬x_4`; `P = (y ∧ x_0) ∨ (x_4 ∧ x_2)`; `Q = (y ∧ x_1) ∨ (x_4 ∧ x_3)`; `g = P ∨ Q` (wire 12);
outputs `x_0 ∨ x_1` (wire 13) and `x_2 ∨ x_3` (wire 14). -/
def ceGates : List Gate :=
  [⟨GateOp.not, [4]⟩, ⟨GateOp.and, [5, 0]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [6, 7]⟩,
   ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [8, 11]⟩,
   ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩]

def ceR : Finset (Fin 5) := {0, 1}
def ceR' : Finset (Fin 5) := {2, 3}
/-- `Z = top_w \ {4}`: true exactly on `{2, 3}`. -/
def ceZ : Fin 5 → Bool := canonPt {2, 3}
def ceM : Fin 5 → Finset (Fin 5) := fun _ => {4}

theorem ce_hg : ∀ g ∈ ceGates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [ceGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ce_hU : AtMostOneNot ceGates := by
  have key : ∀ i (h : i < ceGates.length), (ceGates[i]'h).op = GateOp.not → i = 0 := by
    intro i h
    have h' : i < 10 := h
    interval_cases i <;> simp [ceGates]
  intro i1 i2 h1 h2 e1 e2
  rw [key i1 h1 e1, key i2 h2 e2]

theorem ce_hp : 0 < ceGates.length := by simp [ceGates]

theorem ce_hN : (ceGates[0]'ce_hp).op = GateOp.not := rfl

/-- Both atoms of a two-element set, enumerated by `enumF`. -/
theorem enumF_cases (R : Finset (Fin 5)) (a b : Fin 5) (hR : R = {a, b}) (t : Fin R.card) :
    enumF R t = a ∨ enumF R t = b := by
  have key : ∀ c ∈ R, c = a ∨ c = b := by rw [hR]; simp
  exact key _ (enumF_mem R t)

theorem card_atomsAt_of_all {N k : ℕ} (gs : List Gate) (a : Fin k → Fin N → Bool) (i : ℕ)
    (h : ∀ t, val gs (a t) i = true) : (atomsAt gs a i).card = k := by
  have : atomsAt gs a i = Finset.univ := by
    ext t; simp [mem_atomsAt, h t]
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- The gate `g` (wire 12; gate 6 of the lift) lies in `K_1(w; Z) ∩ K_0(v; m)`. -/
theorem ce_mem : 12 ∈ K1Z ceGates 0 ceR ceZ ∩ K0of ceGates 0 ceR' ceM := by
  have hw : realWire 5 0 6 = 12 := rfl
  rw [Finset.mem_inter, K1Z, K0of]
  constructor
  · refine Finset.mem_image.mpr ⟨6, mem_orClz.mpr ⟨by decide, ⟨_, rfl, rfl⟩, by decide, ?_⟩, hw⟩
    rw [card_atomsAt_of_all]
    · decide
    · intro t
      rcases enumF_cases ceR 0 1 rfl t with h | h <;> rw [h] <;> decide
  · refine Finset.mem_image.mpr ⟨6, mem_orClz.mpr ⟨by decide, ⟨_, rfl, rfl⟩, by decide, ?_⟩, hw⟩
    rw [card_atomsAt_of_all]
    · decide
    · intro t
      rcases enumF_cases ceR' 2 3 rfl t with h | h <;> rw [h] <;> decide

/-- **D1 is false**: the circuit `ceGates` is a correct one-NOT circuit for the sets
`{0,1}`, `{2,3}`, `Z = {2,3}` is an I1 point of `{0,1}` (`h = x_4`), `m_2 = m_3 = {4}` is an I0
choice of `{2,3}` avoiding `{0,1}`, and wire 12 is in both classes. -/
theorem not_D1Stmt : ¬ D1Stmt := by
  intro H
  have hd := H 5 ceGates 0 ce_hp ce_hg ce_hU ce_hN ceR ceR' 13 14 (by decide)
    (by decide) (by decide) ceZ (by decide) (by decide) (by decide) ceM (by decide)
  exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp ce_mem).1 (Finset.mem_inter.mp ce_mem).2

end PEqualNP.Outside.L_meta_951_aux
