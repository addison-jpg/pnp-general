import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureStar

/-!
# MUInduct: the class UC and MU by induction on points

The board integrator's route (12:13; coord 12:06, owner: counting only). A one-NOT circuit `gates`
on `n` inputs, NOT gate at `p`, lifted to the monotone list `L = lift n p gates` (`C_b` is `L` at
`y = b`, `val_lift_wld`; wire numbers are LIFTED, as for `pureCls`). For a set `R`, deleted points
`D` (fixed to `0`) and points `Q` fixed to `1`:

* `UCWit gates p R D Q i` (the UC witness of the lifted wire `i`): a world `b`, a point `Z` and two
  points `u ≠ u'` of `R \ D` with `Z = 0` on `R` and on `D`, `Z = 1` on `Q`, wire `i` of `C_b` is `0`
  at `Z` and `1` at `Z + e_u` and at `Z + e_u'`, and the face condition `FaceOK`: world 1, the NOT
  gate is `1` at `Z` (`h(Z) = 0`); world 0, the NOT gate is `0` at `Z + e_u` and at `Z + e_u'`
  (`h = 1` there; TWO witnesses only, so the class is restriction-closed).
* `UC gates p S D Q`: the OR gates of `L` with a UC witness for a set alive at `Q` (`aliveSets`).

Results:

* `runMT_or`, `runMT_wit`: in a monotone list with the test-point condition `hT`, every merge of the
  union-find run (`runMT`) is an OR gate, `0` at the zero point `z` and `1` at `z + e_u`, `z + e_u'`
  for two points `u ≠ u'` of the set. No minimality.
* `pureCls_subset_UC`: every class of a valid pure option (all four kinds) lies in `UC S ∅ ∅`; so
  `muc_of_mu`: MU ⇒ `MUC` (MU for UC is weaker). `UQ_subset_UC`: `U(Q) ⊆ UC S ∅ Q` (PureStar).
* `bound_of_muc`, `no_minCE_of_MUC`: `MUC` closes 951 (UC lies in the `gates.length - 1` lifted gates).
* Heredity (restriction = evaluation on the subcube, no rebuilt circuit): `UC_mono`, so
  `UC S (insert v D) Q ⊆ UC S D Q` (`x_v := 0`) and `UC S D (insert v Q) ⊆ UC S D Q` (`x_v := 1`).
* Base: `baseDQ S D Q = ∑_{w alive at Q} (|S_w \ D| - 1)`. `baseDQ_insertQ`: `x_v := 1` removes the
  sets through `v` (`∑_{star} d_w`). `baseDQ_insertD`: `x_v := 0` (`v ∉ D`) lowers the base by
  `degDQ`, the alive sets through `v` with `|S_w \ D| ≥ 2`; `degDQ_eq_card`: exactly `deg(v)` when
  every alive set through `v` keeps two points.
* The induction, gain as a HYPOTHESIS (the pattern of `menuSDR_of_starSep`): `GainOne` (`x_v := 1`,
  `∑_{star} d_w ≤ |UC(D, Q) \ UC(D, Q ∪ {v})|`), `GainZero` (`x_v := 0`,
  `degDQ ≤ |UC(D, Q) \ UC(D ∪ {v}, Q)|`). `base_le_UC_one`: `GainOne` at some star point for every
  `Q` ⇒ `base ≤ |UC S ∅ ∅|`. `base_le_UC`: one of the two moves at every `(D, Q)` with positive base
  ⇒ the same. `no_minCE_of_gainOne`, `no_minCE_of_gain`.
* Induction on the unfixed points (a point in no alive set costs `0`, Fable N3): `base_le_UC_pts`
  (either move at some `v ∉ D ∪ Q`), `base_le_UC_one_pts` (`x_v := 1` at some `v ∉ Q`, no deleted
  points), `muc_of_gain_pts`, `muc_of_gainOne_pts`, `no_minCE_of_gainOne_pts`.
* Lemma C0 (Fable N2): `not_UCWit_of_C0` (`C_0(g)(Q) = 1` ⇒ no witness with `Q` fixed to `1`),
  `card_C0_le_gain` (the UC gates with `C_0 = 1` at `Q ∪ {v}` leave under `x_v := 1`).

The Fable's report (`one-not/board/agents/fable-mu-induction.md`, N1): on FANO-FORMULA no point has
`GainZero` for this UC (gain `deg(v) - 1` everywhere), so an induction by `x_v := 0` alone is dead;
`x_v := 1` is good at every point there. The mixed inductions stay usable.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Merges in a monotone list -/

section Merges

variable {N : ℕ} (z : Fin N → Bool) (q : Fin N → Fin N → Bool) (R : Finset (Fin N))
  (gs : List Gate)

/-- The test-point condition `hT` says `q u ≤ z + e_u`. -/
theorem le_update_of_hT {u : Fin N} (h : ∀ c : Fin N, q u c = true → z c = false → c = u) :
    q u ≤ Function.update z u true := by
  intro c
  refine Bool.le_iff_imp.mpr fun hc => ?_
  by_cases hcu : c = u
  · subst hcu
    simp
  · rw [Function.update_of_ne hcu]
    by_contra hz
    exact hcu (h c hc (by simpa using hz))

/-- **Merges are OR gates** (any monotone list, any test points with `hT`): an AND gate that is `0`
at `z` has an input that is `0` at `z` and `1` on the gate's whole trace, and the run invariant
(`runLT_inv`) puts that trace in one block. -/
theorem runMT_or (hm : MonoList gs)
    (hT : ∀ u ∈ R, ∀ c : Fin N, q u c = true → z c = false → c = u) {i : ℕ}
    (hi : i ∈ runMT z q R gs gs.length) : ∃ j, i = N + j ∧ IsOrAt gs j := by
  classical
  obtain ⟨j, hjl, rfl, hmg⟩ := (runMT_mem z q R gs gs.length i).mp hi
  obtain ⟨⟨u, hu, v, hv, hui, hvi, hne⟩, -⟩ := run_recordT z q R gs gs.length j hi
  refine ⟨j, rfl, gs[j], List.getElem?_eq_getElem hjl, ?_⟩
  have hz : val gs z (N + j) = false := hmg.1
  have hinv := runLT_inv z q R gs hT j
  rcases (hm _ (List.getElem_mem hjl)).1 with hop | hop
  · exfalso
    rw [mr_val_gate gs z j hjl, hop] at hz
    rw [mr_val_gate gs _ j hjl, hop] at hui hvi
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id] at hz hui hvi
    obtain ⟨a, ha, haz⟩ := hz
    have hua := hui a ha
    have hva := hvi a ha
    have ha' : a < N + j := by
      by_contra h
      rw [mr_val_ge (gs.take j) _ a (by simp; omega)] at hua
      exact absurd hua (by simp)
    rw [← mr_val_take gs _ j a ha'] at hua hva
    have haz' : val gs z a = false := by
      rw [mr_val_take gs _ j a ha']
      simpa using haz
    exact hne (hinv a ha' haz' u hu v hv hua hva)
  · exact hop

/-- **The UC witness of a merge**: an OR gate, `0` at `z`, `1` at `z + e_u` and `z + e_u'` for two
points `u ≠ u'` of `R` (monotone list, `hT`). -/
theorem runMT_wit (hm : MonoList gs)
    (hT : ∀ u ∈ R, ∀ c : Fin N, q u c = true → z c = false → c = u) {i : ℕ}
    (hi : i ∈ runMT z q R gs gs.length) :
    (∃ j, i = N + j ∧ IsOrAt gs j) ∧ val gs z i = false ∧
      ∃ u ∈ R, ∃ u' ∈ R, u ≠ u' ∧ val gs (Function.update z u true) i = true ∧
        val gs (Function.update z u' true) i = true := by
  classical
  refine ⟨runMT_or z q R gs hm hT hi, ?_⟩
  have h1 := run_sub_DT z q R gs _ hi
  rw [DT, Finset.mem_filter] at h1
  obtain ⟨-, hz, u, v, huv, hu, hv, hui, hvi⟩ := h1
  refine ⟨hz, u, hu, v, hv, huv, ?_, ?_⟩
  · have := val_le_of_le gs hm.andOr (le_update_of_hT z q (hT u hu)) i
    rw [hui] at this
    exact top_le_iff.mp this
  · have := val_le_of_le gs hm.andOr (le_update_of_hT z q (hT v hv)) i
    rw [hvi] at this
    exact top_le_iff.mp this

end Merges

section MUInduct

variable {n m : ℕ}

theorem ext_update (Z : Fin n → Bool) (u : Fin n) (b : Bool) :
    Function.update (ext Z b) (Fin.castSucc u) true = ext (Function.update Z u true) b := by
  funext c
  induction c using Fin.lastCases with
  | last =>
    rw [Function.update_of_ne (Fin.castSucc_ne_last u).symm, ext_last, ext_last]
  | cast c =>
    rw [ext_castSucc]
    by_cases hc : c = u
    · subst hc
      simp
    · rw [Function.update_of_ne (fun h => hc (Fin.castSucc_injective n h)), ext_castSucc,
        Function.update_of_ne hc]

/-- `hT` for lifted atoms `({u} ∪ B_u, b)` at the zero point `(Z, b)`, when `B_u ⊆ Z ∪ {u}`. -/
theorem hT_liftAtoms (R : Finset (Fin n)) (Z : Fin n → Bool) (b : Bool)
    (B : Fin n → Finset (Fin n)) (q : Fin (n + 1) → Fin (n + 1) → Bool)
    (hq : ∀ u ∈ R, q (Fin.castSucc u) = ext (canonPt (insert u (B u))) b)
    (hB : ∀ u ∈ R, ∀ v ∈ B u, v = u ∨ Z v = true) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), q c c' = true → ext Z b c' = false → c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [hq u hu] at h1
  induction c' using Fin.lastCases with
  | last =>
    rw [ext_last] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  | cast v =>
    rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
    rw [ext_castSucc] at h2
    rcases h1 with rfl | h1
    · rfl
    · rcases hB u hu v h1 with rfl | h3
      · rfl
      · rw [h3] at h2
        exact absurd h2 (by decide)

/-- **Lifted merges**: a merge of a lifted run with atoms `({u} ∪ B_u, b)` at zero point `(Z, b)`,
`B_u ⊆ Z ∪ {u}`, is a lifted OR gate, `0` at `(Z, b)` and `1` at `(Z + e_u, b)` and `(Z + e_u', b)`
for two points `u ≠ u'` of `R`. -/
theorem lift_runMT_wit (gates : List Gate) (p : ℕ) (hm : MonoList (lift n p gates))
    (R : Finset (Fin n)) (Z : Fin n → Bool) (b : Bool) (B : Fin n → Finset (Fin n))
    (q : Fin (n + 1) → Fin (n + 1) → Bool)
    (hq : ∀ u ∈ R, q (Fin.castSucc u) = ext (canonPt (insert u (B u))) b)
    (hB : ∀ u ∈ R, ∀ v ∈ B u, v = u ∨ Z v = true) {i : ℕ}
    (hi : i ∈ runMT (ext Z b) q (liftSet R) (lift n p gates) (lift n p gates).length) :
    (∃ j, i = n + 1 + j ∧ IsOrAt (lift n p gates) j) ∧ val (lift n p gates) (ext Z b) i = false ∧
      ∃ u ∈ R, ∃ u' ∈ R, u ≠ u' ∧
        val (lift n p gates) (ext (Function.update Z u true) b) i = true ∧
        val (lift n p gates) (ext (Function.update Z u' true) b) i = true := by
  obtain ⟨hor, hz, c, hc, c', hc', hcc, h1, h2⟩ :=
    runMT_wit (ext Z b) q (liftSet R) (lift n p gates) hm (hT_liftAtoms R Z b B q hq hB) hi
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨u', hu', rfl⟩ := mem_liftSet_iff.mp hc'
  rw [ext_update] at h1 h2
  exact ⟨hor, hz, u, hu, u', hu', fun h => hcc (h ▸ rfl), h1, h2⟩

/-! ## UC -/

/-- The face condition. World 1 (`b = true`): the NOT gate is `1` at `Z` (`h(Z) = 0`). World 0
(`b = false`): the NOT gate is `0` at `Z + e_u` and at `Z + e_u'` (`h = 1` there). -/
def FaceOK (gates : List Gate) (p : ℕ) (Z : Fin n → Bool) (u u' : Fin n) : Bool → Prop
  | true => val gates Z (n + p) = true
  | false => val gates (Function.update Z u true) (n + p) = false ∧
      val gates (Function.update Z u' true) (n + p) = false

/-- **The UC witness** of the lifted wire `i` for the set `R`, deleted points `D` and points `Q`
fixed to `1`. -/
def UCWit (gates : List Gate) (p : ℕ) (R D Q : Finset (Fin n)) (i : ℕ) : Prop :=
  ∃ (b : Bool) (Z : Fin n → Bool) (u u' : Fin n), u ∈ R ∧ u' ∈ R ∧ u ≠ u' ∧ u ∉ D ∧ u' ∉ D ∧
    (∀ v ∈ R, Z v = false) ∧ (∀ v ∈ D, Z v = false) ∧ (∀ v ∈ Q, Z v = true) ∧
    FaceOK gates p Z u u' b ∧ val (lift n p gates) (ext Z b) i = false ∧
    val (lift n p gates) (ext (Function.update Z u true) b) i = true ∧
    val (lift n p gates) (ext (Function.update Z u' true) b) i = true

theorem UCWit.mono {gates : List Gate} {p : ℕ} {R D D' Q Q' : Finset (Fin n)} {i : ℕ}
    (hD : D ⊆ D') (hQ : Q ⊆ Q') (h : UCWit gates p R D' Q' i) : UCWit gates p R D Q i := by
  obtain ⟨b, Z, u, u', hu, hu', huu, huD, hu'D, hZR, hZD, hZQ, rest⟩ := h
  exact ⟨b, Z, u, u', hu, hu', huu, fun h => huD (hD h), fun h => hu'D (hD h), hZR,
    fun v hv => hZD v (hD hv), fun v hv => hZQ v (hQ hv), rest⟩

open Classical in
/-- **UC**: the lifted OR gates with a UC witness for a set alive at `Q`. -/
noncomputable def UC (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) :
    Finset ℕ :=
  (Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)).filter fun i =>
    IsOrAt (lift n p gates) (i - (n + 1)) ∧ ∃ w ∈ aliveSets S Q, UCWit gates p (S w) D Q i

theorem mem_UC {gates : List Gate} {p : ℕ} {S : Fin m → Finset (Fin n)} {D Q : Finset (Fin n)}
    {i : ℕ} : i ∈ UC gates p S D Q ↔ (∃ j, i = n + 1 + j ∧ IsOrAt (lift n p gates) j) ∧
      ∃ w ∈ aliveSets S Q, UCWit gates p (S w) D Q i := by
  classical
  rw [UC, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, -⟩, hor, hw⟩
    exact ⟨⟨i - (n + 1), by omega, hor⟩, hw⟩
  · rintro ⟨⟨j, rfl, hor⟩, hw⟩
    obtain ⟨g, hg, hgo⟩ := hor
    have hj : j < (lift n p gates).length := (List.getElem?_eq_some_iff.mp hg).1
    refine ⟨⟨by omega, by omega⟩, ?_, hw⟩
    rw [Nat.add_sub_cancel_left]
    exact ⟨g, hg, hgo⟩

/-- **Heredity**: more deleted points or more points fixed to `1` give a smaller UC. -/
theorem UC_mono (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) {D D' Q Q' : Finset (Fin n)}
    (hD : D ⊆ D') (hQ : Q ⊆ Q') : UC gates p S D' Q' ⊆ UC gates p S D Q := by
  intro i hi
  obtain ⟨hor, w, hw, hwit⟩ := mem_UC.mp hi
  refine mem_UC.mpr ⟨hor, w, ?_, hwit.mono hD hQ⟩
  exact mem_aliveSets.mpr (Finset.disjoint_of_subset_right hQ (mem_aliveSets.mp hw))

/-- `x_v := 0`: `UC(D ∪ {v}, Q) ⊆ UC(D, Q)`. -/
theorem UC_insertD_subset (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (D Q : Finset (Fin n)) (v : Fin n) : UC gates p S (insert v D) Q ⊆ UC gates p S D Q :=
  UC_mono gates p S (Finset.subset_insert v D) le_rfl

/-- `x_v := 1`: `UC(D, Q ∪ {v}) ⊆ UC(D, Q)`. -/
theorem UC_insertQ_subset (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (D Q : Finset (Fin n)) (v : Fin n) : UC gates p S D (insert v Q) ⊆ UC gates p S D Q :=
  UC_mono gates p S le_rfl (Finset.subset_insert v Q)

/-- UC lies in the gate wires of the lift. -/
theorem UC_subset (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) :
    UC gates p S D Q ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
  classical
  exact Finset.filter_subset _ _

/-! ## Pure classes lie in UC -/

section Pure

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

/-- The zero point of a pure option (`top_w` for `zero m`). -/
def PureOpt.zeroPt (R : Finset (Fin n)) : PureOpt n → Fin n → Bool
  | .one Z => Z
  | .zero _ => Zof R
  | .zeroAt z _ => z
  | .oneAt Z _ => Z

include hg hU hN in
/-- **Pure classes are UC**: every gate of the class of a valid pure option (all four kinds) is a
lifted OR gate with a UC witness for `R`, no deleted points, and any `Q` on which the option's zero
point is `1`. Atoms lie below `Z + e_u` by validity, both faces are monotone. -/
theorem pureCls_UCWit (R Q : Finset (Fin n)) (c : PureOpt n) (hc : PureValid gates p R c)
    (hQ : ∀ v ∈ Q, c.zeroPt R v = true) {i : ℕ} (hi : i ∈ pureCls gates p R c) :
    (∃ j, i = n + 1 + j ∧ IsOrAt (lift n p gates) j) ∧ UCWit gates p R ∅ Q i := by
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  -- the world-0 face from `h(m_u) = 1` and `m_u ⊆ Z ∪ {u}`
  have face0 : ∀ (Z : Fin n → Bool) (M : Fin n → Finset (Fin n)),
      (∀ u ∈ R, ∀ v ∈ M u, v = u ∨ Z v = true) →
      (∀ u ∈ R, val gates (canonPt (M u)) (n + p) = false) →
      ∀ u ∈ R, val gates (Function.update Z u true) (n + p) = false := by
    intro Z M hM hh u hu
    refine not_false_of_le gates p hp hg hU hN (canonPt_le fun v hv => ?_) (hh u hu)
    rcases hM u hu v hv with rfl | h
    · simp
    · by_cases hvu : v = u
      · subst hvu
        simp
      · rw [Function.update_of_ne hvu]
        exact h
  cases c with
  | one Z =>
    obtain ⟨hZR, hZ⟩ := hc
    obtain ⟨hor, hz, u, hu, u', hu', huu, h1, h2⟩ := lift_runMT_wit gates p hm R Z true
      (fun _ => ∅) atom1 (fun u _ => by rw [atom1_castSucc]; rfl) (fun _ _ v hv => absurd hv (by simp)) hi
    exact ⟨hor, true, Z, u, u', hu, hu', huu, by simp, by simp, hZR, by simp, hQ, hZ, hz, h1, h2⟩
  | zero M =>
    obtain ⟨hMR, hh⟩ := hc
    have hB : ∀ u ∈ R, ∀ v ∈ M u, v = u ∨ Zof R v = true := by
      intro u hu v hv
      by_cases hvR : v ∈ R
      · exact Or.inl (hMR u hu v hv hvR)
      · right
        simp [Zof, hvR]
    obtain ⟨hor, hz, u, hu, u', hu', huu, h1, h2⟩ := lift_runMT_wit gates p hm R (Zof R) false
      M (atom0 M) (fun u _ => atom0_castSucc M u) hB hi
    exact ⟨hor, false, Zof R, u, u', hu, hu', huu, by simp, by simp, Zof_zero R, by simp, hQ,
      ⟨face0 _ M hB hh u hu, face0 _ M hB hh u' hu'⟩, hz, h1, h2⟩
  | zeroAt z M =>
    obtain ⟨hzR, hB, hh⟩ := hc
    obtain ⟨hor, hz, u, hu, u', hu', huu, h1, h2⟩ := lift_runMT_wit gates p hm R z false
      M (atom0 M) (fun u _ => atom0_castSucc M u) hB hi
    exact ⟨hor, false, z, u, u', hu, hu', huu, by simp, by simp, hzR, by simp, hQ,
      ⟨face0 _ M hB hh u hu, face0 _ M hB hh u' hu'⟩, hz, h1, h2⟩
  | oneAt Z A =>
    obtain ⟨hZR, hZ, hA⟩ := hc
    obtain ⟨hor, hz, u, hu, u', hu', huu, h1, h2⟩ := lift_runMT_wit gates p hm R Z true
      A (atom1W A) (fun u _ => atom1W_castSucc A u) hA hi
    exact ⟨hor, true, Z, u, u', hu, hu', huu, by simp, by simp, hZR, by simp, hQ, hZ, hz, h1, h2⟩

include hg hU hN in
/-- **pureMenu ⊆ UC**: every class of a valid pure option of any set lies in `UC S ∅ ∅`. -/
theorem pureMenu_subset_UC (S : Fin m → Finset (Fin n)) (w : Fin m) :
    pureMenu gates p (S w) ⊆ UC gates p S ∅ ∅ := by
  intro i hi
  obtain ⟨c, hc, hic⟩ := mem_pureMenu.mp hi
  obtain ⟨hor, hwit⟩ := pureCls_UCWit gates p hp hg hU hN (S w) ∅ c hc (by simp) hic
  exact mem_UC.mpr ⟨hor, w, mem_aliveSets.mpr (Finset.disjoint_empty_right _), hwit⟩

include hg hU hN in
/-- **U(Q) ⊆ UC(∅, Q)**: the `Menu1_Q` classes of PureStar (STAR-COUNT's `U(Q)`) are UC with `Q`
fixed to `1` (an `oneAt` zero point is `1` on `R' ⊇ Q`; `top_w` is `1` on `Q` for `w` alive). -/
theorem UQ_subset_UC (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    UQ gates p S Q ⊆ UC gates p S ∅ Q := by
  intro i hi
  obtain ⟨w, hw, c, hc, hic⟩ := mem_UQ.mp hi
  have hQ : ∀ v ∈ Q, c.zeroPt (S w) v = true := by
    cases c with
    | oneAt Z A =>
      obtain ⟨-, R', -, hQR, hRZ⟩ := hc
      exact fun v hv => hRZ v (hQR hv)
    | zero M =>
      intro v hv
      have : v ∉ S w := fun h => Finset.disjoint_left.mp (mem_aliveSets.mp hw) h hv
      simp [PureOpt.zeroPt, Zof, this]
    | one Z => exact hc.elim
    | zeroAt z M => exact hc.elim
  obtain ⟨hor, hwit⟩ := pureCls_UCWit gates p hp hg hU hN (S w) Q c hc.valid hQ hic
  exact mem_UC.mpr ⟨hor, w, hw, hwit⟩

include hg hU hN in
/-- **Lemma C0** (Fable N2): a lifted wire whose world-0 face `C_0` is `1` at `Q` has no UC witness
with `Q` fixed to `1` (both faces are monotone and `C_0 ≤ C_b`, so they are `1` at every `Z ⊇ Q`). -/
theorem not_UCWit_of_C0 (R D Q : Finset (Fin n)) {i : ℕ}
    (h0 : val (lift n p gates) (ext (canonPt Q) false) i = true) : ¬ UCWit gates p R D Q i := by
  rintro ⟨b, Z, -, -, -, -, -, -, -, -, -, hZQ, -, hz, -⟩
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hle := val_le_of_le (lift n p gates) hm.andOr
    (ext_le_of_le (canonPt_le fun c hc => hZQ c hc) (Bool.false_le b)) i
  rw [h0, hz] at hle
  exact absurd hle (by decide)

include hg hU hN in
/-- **The C0 count** (Fable N2): the UC gates whose `C_0` is `1` at `Q ∪ {v}` leave UC under
`x_v := 1`. -/
theorem card_C0_le_gain (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) (v : Fin n) :
    ((UC gates p S D Q).filter fun i =>
        val (lift n p gates) (ext (canonPt (insert v Q)) false) i = true).card ≤
      (UC gates p S D Q \ UC gates p S D (insert v Q)).card := by
  refine Finset.card_le_card fun i hi => ?_
  obtain ⟨hi, h0⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_sdiff.mpr ⟨hi, fun hi' => ?_⟩
  obtain ⟨-, w, -, hwit⟩ := mem_UC.mp hi'
  exact not_UCWit_of_C0 gates p hp hg hU hN (S w) D (insert v Q) h0 hwit

end Pure

/-! ## MU for UC -/

/-- **MUC**: `base = ∑_w (|S_w| - 1)` is at most `|UC S ∅ ∅|`. -/
def MUC (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) : Prop :=
  ∑ w, ((S w).card - 1) ≤ (UC gates p S ∅ ∅).card

/-- **MU ⇒ MUC** (MU for UC is weaker). -/
theorem muc_of_mu (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (H : MU S gates p) :
    MUC S gates p :=
  H.trans (Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ =>
    pureMenu_subset_UC gates p hp hg hU hN S w))

/-- **MUC ⇒ the bound with one gate to spare.** -/
theorem bound_of_muc (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (hp : p < gates.length) (H : MUC S gates p) : ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  have h := Finset.card_le_card (UC_subset gates p S ∅ ∅)
  rw [Nat.card_Ico, length_lift n p gates hp] at h
  unfold MUC at H
  omega

/-! ## Base and the deletion steps -/

/-- The base at `(D, Q)`: `∑_{w alive at Q} (|S_w \ D| - 1)`. -/
def baseDQ (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) : ℕ :=
  ∑ w ∈ aliveSets S Q, ((S w \ D).card - 1)

/-- The alive sets through `v` with at least two points off `D` (the drop of the base under
`x_v := 0`). -/
def degDQ (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) (v : Fin n) : ℕ :=
  ((aliveSets S Q).filter fun w => v ∈ S w ∧ 2 ≤ (S w \ D).card).card

theorem baseDQ_empty (S : Fin m → Finset (Fin n)) : baseDQ S ∅ ∅ = ∑ w, ((S w).card - 1) := by
  have hall : aliveSets S ∅ = Finset.univ := by
    ext w
    simp [mem_aliveSets]
  rw [baseDQ, hall]
  simp

theorem filter_aliveSets_not_mem (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    (aliveSets S Q).filter (fun w => v ∉ S w) = aliveSets S (insert v Q) := by
  ext w
  rw [Finset.mem_filter, aliveSets_insert]

/-- **`x_v := 1`**: the base drops by `∑_{alive w ∋ v} d_w` (relative to `D`). -/
theorem baseDQ_insertQ (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) (v : Fin n) :
    baseDQ S D (insert v Q) + ∑ w ∈ starSets S Q v, ((S w \ D).card - 1) = baseDQ S D Q := by
  rw [baseDQ, baseDQ, ← filter_aliveSets_not_mem, starSets, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- **`x_v := 0`** (`v ∉ D`): the base drops by `degDQ`. -/
theorem baseDQ_insertD (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) {v : Fin n}
    (hv : v ∉ D) : baseDQ S (insert v D) Q + degDQ S D Q v = baseDQ S D Q := by
  classical
  rw [baseDQ, baseDQ, degDQ, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sdiff_insert]
  by_cases hvw : v ∈ S w
  · have hmem : v ∈ S w \ D := Finset.mem_sdiff.mpr ⟨hvw, hv⟩
    rw [Finset.card_erase_of_mem hmem]
    by_cases h2 : 2 ≤ (S w \ D).card
    · rw [ite_eq_left ⟨hvw, h2⟩]
      omega
    · rw [ite_eq_right fun h => h2 h.2]
      omega
  · rw [Finset.erase_eq_of_notMem fun h => hvw (Finset.mem_sdiff.mp h).1,
      ite_eq_right fun h => hvw h.1]
    rfl

/-- **Exactly `deg(v)`** when every alive set through `v` keeps two points off `D`. -/
theorem degDQ_eq_card (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) (v : Fin n)
    (h : ∀ w ∈ starSets S Q v, 2 ≤ (S w \ D).card) : degDQ S D Q v = (starSets S Q v).card := by
  rw [degDQ, starSets]
  congr 1
  ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hw, hv, -⟩
    exact ⟨hw, hv⟩
  · rintro ⟨hw, hv⟩
    exact ⟨hw, hv, h w (Finset.mem_filter.mpr ⟨hw, hv⟩)⟩

/-! ## The induction (gain as a hypothesis) -/

/-- **GAIN for `x_v := 1`**: `∑_{alive w ∋ v} d_w ≤ |UC(D, Q) \ UC(D, Q ∪ {v})|`. -/
def GainOne (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n))
    (v : Fin n) : Prop :=
  ∑ w ∈ starSets S Q v, ((S w \ D).card - 1) ≤
    (UC gates p S D Q \ UC gates p S D (insert v Q)).card

/-- **GAIN for `x_v := 0`**: `degDQ ≤ |UC(D, Q) \ UC(D ∪ {v}, Q)|`. -/
def GainZero (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n))
    (v : Fin n) : Prop :=
  degDQ S D Q v ≤ (UC gates p S D Q \ UC gates p S (insert v D) Q).card

/-- **The `x_v := 1` induction** (no deleted points): `GainOne` at a point of an alive set for every
`Q` with an alive set ⇒ `base(Q) ≤ |UC(∅, Q)|` for every `Q`. -/
theorem base_le_UC_one (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ GainOne gates p S ∅ Q v) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k →
      baseDQ S ∅ Q ≤ (UC gates p S ∅ Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hQ
    rw [baseDQ, Finset.card_eq_zero.mp (Nat.le_zero.mp hQ), Finset.sum_empty]
    exact Nat.zero_le _
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · rw [baseDQ, h0, Finset.sum_empty]
      exact Nat.zero_le _
    obtain ⟨v, ⟨w0, hw0⟩, hgain⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    have hih := ih (insert v Q) (by omega)
    have hb := baseDQ_insertQ S ∅ Q v
    have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertQ_subset gates p S ∅ Q v)
    unfold GainOne at hgain
    omega

/-- The measure of the combined induction: `∑_{w alive at Q} (|S_w \ D| + 1)`. -/
def measDQ (S : Fin m → Finset (Fin n)) (D Q : Finset (Fin n)) : ℕ :=
  ∑ w ∈ aliveSets S Q, ((S w \ D).card + 1)

/-- **The combined induction**: at every `(D, Q)` with positive base, `GainOne` at a point `v` of an
alive set, or `GainZero` at a point `v ∉ D` of an alive set ⇒ `base(D, Q) ≤ |UC(D, Q)|`. -/
theorem base_le_UC (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ D Q, 0 < baseDQ S D Q → ∃ v, ((starSets S Q v).Nonempty ∧ GainOne gates p S D Q v) ∨
      (v ∉ D ∧ (starSets S Q v).Nonempty ∧ GainZero gates p S D Q v)) :
    ∀ k (D Q : Finset (Fin n)), measDQ S D Q ≤ k → baseDQ S D Q ≤ (UC gates p S D Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro D Q hk
    have h0 : aliveSets S Q = ∅ := by
      by_contra hne
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have := Finset.single_le_sum (f := fun w => (S w \ D).card + 1) (fun _ _ => Nat.zero_le _) hw
      unfold measDQ at hk
      omega
    rw [baseDQ, h0, Finset.sum_empty]
    exact Nat.zero_le _
  | succ k ih =>
    intro D Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S D Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hv⟩ := H D Q hpos
    rcases hv with ⟨⟨w0, hw0⟩, hgain⟩ | ⟨hvD, ⟨w0, hw0⟩, hgain⟩
    · -- `x_v := 1`
      have hmeas : measDQ S D (insert v Q) + ∑ w ∈ starSets S Q v, ((S w \ D).card + 1) =
          measDQ S D Q := by
        rw [measDQ, measDQ, ← filter_aliveSets_not_mem, starSets, add_comm]
        exact Finset.sum_filter_add_sum_filter_not _ _ _
      have hpos' := Finset.single_le_sum (f := fun w => (S w \ D).card + 1)
        (fun _ _ => Nat.zero_le _) hw0
      have hih := ih D (insert v Q) (by omega)
      have hb := baseDQ_insertQ S D Q v
      have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertQ_subset gates p S D Q v)
      unfold GainOne at hgain
      omega
    · -- `x_v := 0`
      have hw0' := Finset.mem_filter.mp hw0
      have hlt : measDQ S (insert v D) Q < measDQ S D Q := by
        refine Finset.sum_lt_sum (fun w _ => ?_) ⟨w0, hw0'.1, ?_⟩
        · exact Nat.add_le_add_right (Finset.card_le_card
            (Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert v D))) 1
        · refine Nat.add_lt_add_right (Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff le_rfl
            (Finset.subset_insert v D), fun hsub => ?_⟩) 1
          have := hsub (Finset.mem_sdiff.mpr ⟨hw0'.2, hvD⟩)
          exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self v D)
      have hih := ih (insert v D) Q (by omega)
      have hb := baseDQ_insertD S D Q hvD
      have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertD_subset gates p S D Q v)
      unfold GainZero at hgain
      omega

/-- **Induction on the unfixed points**: at every `(D, Q)` with positive base, some point `v ∉ D ∪ Q`
has `GainOne` or `GainZero`. A point in no alive set costs `0` for both moves (Fable N3), so it is
always allowed. ⇒ `base(D, Q) ≤ |UC(D, Q)|`. -/
theorem base_le_UC_pts (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ D Q, 0 < baseDQ S D Q → ∃ v, v ∉ D ∧ v ∉ Q ∧
      (GainOne gates p S D Q v ∨ GainZero gates p S D Q v)) :
    ∀ k (D Q : Finset (Fin n)), (Finset.univ \ (D ∪ Q)).card ≤ k →
      baseDQ S D Q ≤ (UC gates p S D Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro D Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S D Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvD, hvQ, -⟩ := H D Q hpos
    have : v ∈ Finset.univ \ (D ∪ Q) := by simp [hvD, hvQ]
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hk)] at this
    exact absurd this (Finset.notMem_empty v)
  | succ k ih =>
    intro D Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S D Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvD, hvQ, hgain⟩ := H D Q hpos
    have hv : v ∈ Finset.univ \ (D ∪ Q) := by simp [hvD, hvQ]
    have hdrop : ∀ D' Q' : Finset (Fin n), D' ∪ Q' = insert v (D ∪ Q) →
        (Finset.univ \ (D' ∪ Q')).card ≤ k := by
      intro D' Q' he
      rw [he, Finset.sdiff_insert, Finset.card_erase_of_mem hv]
      omega
    rcases hgain with hgain | hgain
    · have hih := ih D (insert v Q) (hdrop D (insert v Q) (by ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto))
      have hb := baseDQ_insertQ S D Q v
      have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertQ_subset gates p S D Q v)
      unfold GainOne at hgain
      omega
    · have hih := ih (insert v D) Q (hdrop (insert v D) Q (by ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto))
      have hb := baseDQ_insertD S D Q hvD
      have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertD_subset gates p S D Q v)
      unfold GainZero at hgain
      omega

/-- **The `x_v := 1` induction on the unfixed points** (no deleted points; free points allowed): at
every `Q` with positive base, some `v ∉ Q` has `GainOne` ⇒ `base(Q) ≤ |UC(∅, Q)|`. -/
theorem base_le_UC_one_pts (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainOne gates p S ∅ Q v) :
    ∀ k (Q : Finset (Fin n)), (Finset.univ \ Q).card ≤ k →
      baseDQ S ∅ Q ≤ (UC gates p S ∅ Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvQ, -⟩ := H Q hpos
    have : v ∈ Finset.univ \ Q := by simp [hvQ]
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hk)] at this
    exact absurd this (Finset.notMem_empty v)
  | succ k ih =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvQ, hgain⟩ := H Q hpos
    have hv : v ∈ Finset.univ \ Q := by simp [hvQ]
    have hih := ih (insert v Q) (by rw [Finset.sdiff_insert, Finset.card_erase_of_mem hv]; omega)
    have hb := baseDQ_insertQ S ∅ Q v
    have hcard := Finset.card_sdiff_add_card_eq_card (UC_insertQ_subset gates p S ∅ Q v)
    unfold GainOne at hgain
    omega

/-- **`x_v := 1` gains at unfixed points ⇒ MUC.** -/
theorem muc_of_gainOne_pts (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainOne gates p S ∅ Q v) : MUC S gates p := by
  have h := base_le_UC_one_pts gates p S H _ ∅ le_rfl
  rwa [baseDQ_empty] at h

/-- **Gains for either move at unfixed points ⇒ MUC.** -/
theorem muc_of_gain_pts (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ D Q, 0 < baseDQ S D Q → ∃ v, v ∉ D ∧ v ∉ Q ∧
      (GainOne gates p S D Q v ∨ GainZero gates p S D Q v)) : MUC S gates p := by
  have h := base_le_UC_pts gates p S H _ ∅ ∅ le_rfl
  rwa [baseDQ_empty] at h

/-- **`x_v := 1` gains ⇒ MUC.** -/
theorem muc_of_gainOne (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ GainOne gates p S ∅ Q v) :
    MUC S gates p := by
  have h := base_le_UC_one gates p S H _ ∅ le_rfl
  rwa [baseDQ_empty] at h

/-- **Gains for either move ⇒ MUC.** -/
theorem muc_of_gain (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ D Q, 0 < baseDQ S D Q → ∃ v, ((starSets S Q v).Nonempty ∧ GainOne gates p S D Q v) ∨
      (v ∉ D ∧ (starSets S Q v).Nonempty ∧ GainZero gates p S D Q v)) :
    MUC S gates p := by
  have h := base_le_UC gates p S H _ ∅ ∅ le_rfl
  rwa [baseDQ_empty] at h

end MUInduct

/-- **951 from MUC**: if every minimal counterexample has a NOT gate whose UC covers `base` gates,
there is no minimal counterexample. -/
theorem no_minCE_of_MUC
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        MUC S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, -, hP⟩ := H n m S gates out M
  have h1 := bound_of_muc S gates p hp hP
  have h2 := M.ce.hlt
  omega

/-- **951 from `x_v := 1` gains** (the integrator's primary move). -/
theorem no_minCE_of_gainOne
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ GainOne gates p S ∅ Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MUC fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, hN, muc_of_gainOne gates p S hS⟩

/-- **951 from gains for either move.** -/
theorem no_minCE_of_gain
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ D Q, 0 < baseDQ S D Q → ∃ v, ((starSets S Q v).Nonempty ∧ GainOne gates p S D Q v) ∨
          (v ∉ D ∧ (starSets S Q v).Nonempty ∧ GainZero gates p S D Q v)) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MUC fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, hN, muc_of_gain gates p S hS⟩

/-- **951 from `x_v := 1` gains at unfixed points** (free points allowed, Fable N3). -/
theorem no_minCE_of_gainOne_pts
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainOne gates p S ∅ Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MUC fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, hN, muc_of_gainOne_pts gates p S hS⟩

end PEqualNP.Outside.L_meta_951_aux
