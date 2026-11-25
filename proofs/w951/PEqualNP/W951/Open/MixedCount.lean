import PEqualNP.W951.Open.DDAbsorb
import PEqualNP.W951.Open.MixedStepNegIff

/-!
# MixedCount: the mixed count from DD absorption (seat A15)

Board `open-one-not`. Paper: `A7_dd_absorption.md`, `A4_f2_transfer.md`.

* `mixedCount_of_ddAbsorb`: for a one-NOT correct circuit with a NOT gate `p`, pairwise
  `|S a ∩ S b| ≤ 1`, `Disjoint Q D` and an `out` wire per set, `DDAbsorb` gives `0 ≤ mslack`.
* `mixedStepNeg_of_ddAbsorb`: `MinCE` supplies every hypothesis (`hS`, `hg`, `hU`, `hev`), so
  `DDAbsorb` at every state of every minimal counterexample (plus the monotone case, where no NOT
  gate `p` exists) gives `MixedStepNeg`, hence `no_minCE`.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **The mixed count from DD absorption.** -/
theorem mixedCount_of_ddAbsorb (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (hQD : Disjoint Q D) (hov : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hev : ∀ w, ∃ out : ℕ, ∀ x : Fin n → Bool,
      val gates x out = decide (∃ u ∈ S w, x u = true))
    (hD : DDAbsorb gates p S Q D) :
    0 ≤ MixedSlack.mslack gates S Q D := by
  classical
  have hdis : ∀ w ∈ aliveSets S Q, Disjoint Q (S w ∪ D) := fun w hw =>
    Finset.disjoint_union_right.mpr ⟨(mem_aliveSets.mp hw).symm, hQD⟩
  set Ns := (aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w) with hNs
  set DDs := (aliveSets S Q).filter (DDAt gates p S Q D) with hDDs
  set N := Ns.biUnion (unitMerge gates S Q D) with hNdef
  have hNa : ∀ w ∈ Ns, w ∈ aliveSets S Q := fun w hw => (Finset.mem_filter.mp hw).1
  have hpair : ∀ a ∈ Ns, ∀ b ∈ Ns, a ≠ b →
      Disjoint (unitMerge gates S Q D a) (unitMerge gates S Q D b) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨hza, u, hu, u', hu', huu, h1, h2⟩ := unitMerge_data gates S Q D a i hia
    obtain ⟨hzb, v, hv, v', hv', hvv, h3, h4⟩ := unitMerge_data gates S Q D b i hib
    exact (Finset.mem_filter.mp ha).2 (overlap_needs_DD gates p hp hg hU hN S a b (hov a b hab)
      Q D (hdis a (hNa a ha)) (hdis b (hNa b hb)) i hza hzb hu hu' huu h1 h2 hv hv' hvv h3 h4).1
  have hsub : N ⊆ MixedSlack.F2Mix gates S Q D := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨out, hout⟩ := hev w
    exact (unitMerge_card_ge_and_subset gates p hp hg hU hN S Q D w (hdis w (hNa w hw))
      (Finset.mem_filter.mp hw).2 out hout).2 hiw
  have hsum : ∑ w ∈ Ns, ((S w \ D).card - 1) ≤ N.card := by
    rw [hNdef, Finset.card_biUnion hpair]
    exact Finset.sum_le_sum fun w hw => by
      obtain ⟨out, hout⟩ := hev w
      exact (unitMerge_card_ge_and_subset gates p hp hg hU hN S Q D w (hdis w (hNa w hw))
        (Finset.mem_filter.mp hw).2 out hout).1
  have hbase : baseDQ S D Q = ∑ w ∈ DDs, ((S w \ D).card - 1) +
      ∑ w ∈ Ns, ((S w \ D).card - 1) := by
    unfold baseDQ
    rw [← Finset.sum_filter_add_sum_filter_not (aliveSets S Q) (DDAt gates p S Q D)]
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hD' : ∑ w ∈ DDs, ((S w \ D).card - 1) ≤ (MixedSlack.F2Mix gates S Q D \ N).card := hD
  unfold MixedSlack.mslack
  have : baseDQ S D Q ≤ (MixedSlack.F2Mix gates S Q D).card := by omega
  have := (Nat.cast_le (α := ℤ)).mpr this
  omega

end PEqualNP.Outside.L_meta_951_aux.F2Transfer

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

/-- **`MixedStepNeg` from DD absorption.** `hD`: at every state of every minimal counterexample and
every NOT gate `p`, `DDAbsorb`; `hmono`: the mixed count for a minimal counterexample with no NOT
gate (where `DDAt` has no index `p`). -/
theorem mixedStepNeg_of_ddAbsorb
    (hD : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
        ∀ Q D : Finset (Fin n), Disjoint Q D → DDAbsorb gates p S Q D)
    (hmono : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → (∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op ≠ GateOp.not) →
        MixedSlack.MixedCount gates S) :
    MixedSlack.MixedStepNeg := by
  rw [MixedSlack.mixedStepNeg_iff]
  intro n m S gates out M
  by_cases hex : ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not
  · obtain ⟨p, hp, hN⟩ := hex
    intro Q D hd
    exact mixedCount_of_ddAbsorb gates p hp M.ce.hg M.ce.hU hN S Q D hd M.ce.hS
      (fun w => ⟨out w, M.ce.hev w⟩) (hD n m S gates out M p hp hN Q D hd)
  · push Not at hex
    exact hmono n m S gates out M hex

/-- `no_minCE` from the two hypotheses of `mixedStepNeg_of_ddAbsorb`. -/
theorem no_minCE_of_ddAbsorb
    (hD : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
        ∀ Q D : Finset (Fin n), Disjoint Q D → DDAbsorb gates p S Q D)
    (hmono : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → (∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op ≠ GateOp.not) →
        MixedSlack.MixedCount gates S) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  MixedSlack.no_minCE_of_MixedStepNeg (mixedStepNeg_of_ddAbsorb hD hmono)

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
