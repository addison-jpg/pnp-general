import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureGP

/-!
# UGame: Theorem G of the global-price route (Fable, fable-global-price.md §3), refereed by cTAHG

The U-GAME on the lifted outputs: every set picks a valid lifted test system (`LTSValid`), and every
pair of sets is certified in one direction by Theorem U (`LTSCert`: of every two distinct atoms of `t`,
one lies below the zero point of `t'`). **Theorem G**: a won U-game gives LiftSDR, hence MUL and
`base ≤ #gates - 1`. No minimality, no hypothesis on Berge cycles or junk gates.

* `LTSCert`, `UGameWon`, **`liftSDR_of_ugame`** (Theorem G), **`no_minCE_of_ugame`**.
* The pure-world forms: **G1** (`ugame_of_G1`: zero points `(Z_w, 1)` with `h(Z_w) = 0`, atoms `(e_u, 1)`,
  certificate `|S_w \ Z_w'| ≤ 1`) and **G0** (`ugame_of_G0`: zero points `(top_w, 0)`, atoms
  `(A_u, 0)` with `h(A_u) = 1`, `A_u ∩ S_w ⊆ {u}`, certificate: of two points one atom misses `S_w'`).
* Corollaries: (a) `ugame_of_allHeavy` (every point of every set heavy); (c) `ugame_of_typeB` (every
  set type B, `h(top_w) = 0`).

Referee (cTAHG, board 951/board/agents/cTAHG-referee-thmG.md): Theorem G, Lemma N, Propositions 1, 2, S,
G0/G1 validity, corollaries (a)-(e), Theorem D and Lemma T checked line by line; the U-game is won and
independently verified on 19 of the 21 barrier witnesses (MATCH-C, MATCH-S, all twin trees, STAR4,
STAR4b, PAPPUS-JUNK, cxMU_clean2, ...) and lost exactly on cxMU_dd and cx44_1_junk (the DD core, the
open part (X) of the note).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section UGame

variable {n m : ℕ}

/-- **Theorem U's certificate** `t → t'` for the set `R`: of every two distinct atoms of `t`, one lies
below the zero point of `t'`. -/
def LTSCert (R : Finset (Fin n)) (t t' : LTS n) : Prop :=
  ∀ c ∈ liftSet R, ∀ c' ∈ liftSet R, c ≠ c' → t.atom c ≤ t'.zero ∨ t.atom c' ≤ t'.zero

/-- **The U-game is won**: valid lifted test systems, every pair certified in one direction. -/
def UGameWon (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) (p : ℕ) : Prop :=
  ∃ t : Fin m → LTS n, (∀ w, LTSValid gates p (S w) (out w) (t w)) ∧
    ∀ w w', w ≠ w' → LTSCert (S w) (t w) (t w') ∨ LTSCert (S w') (t w') (t w)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **Theorem U** for lifted test systems: a certificate `t → t'` makes the classes disjoint. -/
theorem ltsCls_disjoint_of_cert (R R' : Finset (Fin n)) (t t' : LTS n) (h : LTSCert R t t') :
    Disjoint (ltsCls gates p R t) (ltsCls gates p R' t') :=
  runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _ h

include hp hg hU hN in
/-- **Theorem G**: a won U-game gives LiftSDR. -/
theorem liftSDR_of_ugame (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (H : UGameWon S gates out p) : LiftSDR S gates out p := by
  obtain ⟨t, hv, hc⟩ := H
  refine ⟨t, hv, fun w w' hww => ?_⟩
  rcases hc w w' hww with h | h
  · exact ltsCls_disjoint_of_cert gates p hp hg hU hN _ _ _ _ h
  · exact (ltsCls_disjoint_of_cert gates p hp hg hU hN _ _ _ _ h).symm

/-! ## The pure-world forms -/

include hp hg hU hN in
/-- **G1** (world 1): zero points `(Z_w, 1)` with `Z_w ∩ S_w = ∅` and `h(Z_w) = 0` (the NOT gate `1`),
atoms `(e_u, 1)`; certificate `w → w'` when at most one point of `S_w` is outside `Z_w'`. -/
theorem ugame_of_G1 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (Z : Fin m → Fin n → Bool) (hZS : ∀ w, ∀ u ∈ S w, Z w u = false)
    (hZ : ∀ w, val gates (Z w) (n + p) = true)
    (hcert : ∀ w w', w ≠ w' →
      ((S w).filter fun u => Z w' u = false).card ≤ 1 ∨
        ((S w').filter fun u => Z w u = false).card ≤ 1) :
    UGameWon S gates out p := by
  have hone : ∀ (R R' : Finset (Fin n)) (Z' : Fin n → Bool),
      (R.filter fun u => Z' u = false).card ≤ 1 → ∀ Z0 : Fin n → Bool,
      LTSCert R ((PureOpt.one Z0).toLTS R) ((PureOpt.one Z').toLTS R') := by
    intro R R' Z' hR Z0
    refine liftSet_pairs fun u hu v hv huv => ?_
    simp only [PureOpt.toLTS]
    rw [atom1_castSucc, atom1_castSucc]
    have key : ∀ x : Fin n, Z' x = true → ext (canonPt {x}) true ≤ ext Z' true := fun x hx =>
      ext_le_of_le (canonPt_le fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hx) le_rfl
    by_cases hu' : Z' u = true
    · exact Or.inl (key u hu')
    · by_cases hv' : Z' v = true
      · exact Or.inr (key v hv')
      · have : 1 < (R.filter fun u => Z' u = false).card := Finset.one_lt_card.mpr
          ⟨u, Finset.mem_filter.mpr ⟨hu, by simpa using hu'⟩, v,
            Finset.mem_filter.mpr ⟨hv, by simpa using hv'⟩, huv⟩
        omega
  refine ⟨fun w => (PureOpt.one (Z w)).toLTS (S w), fun w => ?_, fun w w' hww => ?_⟩
  · exact pureValid_ltsValid gates p hp hg hU hN (S w) (out w) (hev w) _ ⟨hZS w, hZ w⟩
  · rcases hcert w w' hww with h | h
    · exact Or.inl (hone (S w) (S w') (Z w') h (Z w))
    · exact Or.inr (hone (S w') (S w) (Z w) h (Z w'))

include hp hg hU hN in
/-- **G0** (world 0): zero points `(top_w, 0)`, atoms `(A_u, 0)` with `h(A_u) = 1` (the NOT gate `0`)
and `A_u ∩ S_w ⊆ {u}`; certificate `w → w'` when of every two points of `S_w` one atom misses
`S_w'`. -/
theorem ugame_of_G0 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (A : Fin m → Fin n → Finset (Fin n)) (hAS : ∀ w, ∀ u ∈ S w, ∀ v ∈ A w u, v ∈ S w → v = u)
    (hA : ∀ w, ∀ u ∈ S w, val gates (canonPt (A w u)) (n + p) = false)
    (hcert : ∀ w w', w ≠ w' →
      (∀ u ∈ S w, ∀ u' ∈ S w, u ≠ u' →
        Disjoint (insert u (A w u)) (S w') ∨ Disjoint (insert u' (A w u')) (S w')) ∨
      (∀ u ∈ S w', ∀ u' ∈ S w', u ≠ u' →
        Disjoint (insert u (A w' u)) (S w) ∨ Disjoint (insert u' (A w' u')) (S w))) :
    UGameWon S gates out p := by
  have hzero : ∀ (R R' : Finset (Fin n)) (A' : Fin n → Finset (Fin n)),
      (∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
        Disjoint (insert u (A' u)) R' ∨ Disjoint (insert u' (A' u')) R') →
      LTSCert R ((PureOpt.zero A').toLTS R) ((PureOpt.zero A').toLTS R') := by
    intro R R' A' h
    refine liftSet_pairs fun u hu v hv huv => ?_
    simp only [PureOpt.toLTS]
    rw [atom0_castSucc, atom0_castSucc]
    have key : ∀ x : Fin n, Disjoint (insert x (A' x)) R' →
        ext (canonPt (insert x (A' x))) false ≤ ext (Zof R') false := fun x hx =>
      ext_le_of_le (canonPt_le fun y hy => by
        simp [Zof, Finset.disjoint_left.mp hx hy]) le_rfl
    rcases h u hu v hv huv with h1 | h1
    · exact Or.inl (key u h1)
    · exact Or.inr (key v h1)
  refine ⟨fun w => (PureOpt.zero (A w)).toLTS (S w), fun w => ?_, fun w w' hww => ?_⟩
  · exact pureValid_ltsValid gates p hp hg hU hN (S w) (out w) (hev w) _ ⟨hAS w, hA w⟩
  · rcases hcert w w' hww with h | h
    · left
      have := hzero (S w) (S w') (A w) h
      intro c hc c' hc' hcc
      rcases this c hc c' hc' hcc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · right
      have := hzero (S w') (S w) (A w') h
      intro c hc c' hc' hcc
      rcases this c hc c' hc' hcc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1

include hp hg hU hN in
/-- **Corollary (a)**: if every point of every set is heavy (`h(e_u) = 1`), the U-game is won (G0 with
`A_u = {u}`). -/
theorem ugame_of_allHeavy (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hheavy : ∀ w, ∀ u ∈ S w, val gates (canonPt {u}) (n + p) = false) :
    UGameWon S gates out p := by
  classical
  refine ugame_of_G0 gates p hp hg hU hN S out hev (fun _ u => {u})
    (fun w u _ v hv _ => Finset.mem_singleton.mp hv) hheavy fun w w' hww => Or.inl ?_
  intro u hu u' hu' huu
  simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.disjoint_singleton_left]
  by_contra hc
  push Not at hc
  have : 1 < (S w ∩ S w').card := Finset.one_lt_card.mpr
    ⟨u, Finset.mem_inter.mpr ⟨hu, hc.1⟩, u', Finset.mem_inter.mpr ⟨hu', hc.2⟩, huu⟩
  have := hS w w' hww
  omega

include hp hg hU hN in
/-- **Corollary (c)**: if every set is type B (`h(top_w) = 0`, the NOT gate `1` at `Zof S_w`), the
U-game is won (G1 with `Z_w = top_w`). -/
theorem ugame_of_typeB (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hB : ∀ w, val gates (Zof (S w)) (n + p) = true) : UGameWon S gates out p := by
  classical
  refine ugame_of_G1 gates p hp hg hU hN S out hev (fun w => Zof (S w)) (fun w u hu => by simp [Zof, hu]) hB
    fun w w' hww => Or.inl ?_
  have : ((S w).filter fun u => Zof (S w') u = false) = S w ∩ S w' := by
    ext u
    simp [Zof, Finset.mem_inter]
  rw [this]
  exact hS w w' hww

end UGame

/-- **951 from the U-game** (Theorem G): if every minimal counterexample has a NOT gate whose lifted
outputs win the U-game, there is no minimal counterexample. -/
theorem no_minCE_of_ugame
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ UGameWon S gates out p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_liftSDR fun n m S gates out M => by
    obtain ⟨p, hp, hN, hW⟩ := H n m S gates out M
    exact ⟨p, hp, hN, liftSDR_of_ugame gates p hp M.ce.hg M.ce.hU hN S out hW⟩

end PEqualNP.Outside.L_meta_951_aux
