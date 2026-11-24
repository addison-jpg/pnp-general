import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCEFacts

/-!
# Absorbing lemma

`rel_prop`: propagation of a reflexive relation `R` between the wire values at two inputs `x, y`
that differ only at `u`, through gates that either satisfy `R` directly or preserve `R` when they do
not look at wire `u` (`Kernel.listVal_rel_off`).
`absorb_rel` (absorbing lemma, relational core): if such an `R` with `¬ R false true` propagates
from `x` to `x[u := 1]`, then no set `S w ∋ u` vanishes at `x`.
`absorb_eq` (`R = Eq`, AND/OR/constant form): all gates except `r` are insensitive to wire `u` and
gate `r` takes the same value at `x` and `x[u := 1]`.
`absorb_anti` (`R a b := b → a`, NOT form): the only NOT gate `r` is the only gate reading wire `u`
and gate `r` does not go `0 → 1` from `x` to `x[u := 1]`.
`MinCE.dc1_facts`, `MinCE.absorbR`: a point with at most one dead gate (`MinCE.dc_facts`,
`MinCE.absorb0`: the instances for a point of degree `≤ 2`, by `MinCE.card_DC_le_one_of_deg2`).
G1.1 (`MinCE.no_minCE_deg2`) is a corollary of the bottom lemma and lives in `Bottom`.
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

theorem rel_prop {n : ℕ} (R : Bool → Bool → Prop) (hR : ∀ b, R b b) (u : Fin n)
    (gates : List Gate) (x y : Fin n → Bool) (hxy : ∀ v, v ≠ u → x v = y v)
    (h : ∀ (k : ℕ) (hk : k < gates.length),
      R (val gates x (n + k)) (val gates y (n + k)) ∨
      ∀ f f' : ℕ → Bool, (∀ i, i ≠ (u : ℕ) → R (f i) (f' i)) →
        R ((gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f))
          ((gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f'))) :
    ∀ i, i ≠ (u : ℕ) → R (val gates x i) (val gates y i) :=
  Kernel.listVal_rel_off R hR u gates x y
    (fun j hj => by rw [hxy j (Fin.ne_of_val_ne hj)]; exact hR _) h

theorem andor_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, f' i = true → f i = true) :
    g.op.eval (g.inputs.map f') = true → g.op.eval (g.inputs.map f) = true := by
  rcases hop with e | e <;> rw [e] <;> simp [GateOp.eval]
  · intro H a ha; exact h a ha (H a ha)
  · rintro a ha H; exact ⟨a, ha, h a ha H⟩

section
variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))

include h2 hev in
/-- No output is an input wire. -/
theorem out_ne_inp (w : Fin m) (u : Fin n) : out w ≠ (u : ℕ) :=
  ne_inp_of_orOn u gates (out w) (S w) (h2 w) fun x _ => hev w x
include h2 hev in
/-- Absorbing lemma, relational core: a reflexive relation `R` with `¬ R false true` cannot
propagate from `x` to `x[u := 1]` when some `S w ∋ u` vanishes at `x`. -/
theorem absorb_rel (R : Bool → Bool → Prop) (hR : ∀ b, R b b) (hft : ¬ R false true) (u : Fin n)
    (x : Fin n → Bool)
    (h : ∀ (k : ℕ) (hk : k < gates.length),
      R (val gates x (n + k)) (val gates (Function.update x u true) (n + k)) ∨
      ∀ f f' : ℕ → Bool, (∀ i, i ≠ (u : ℕ) → R (f i) (f' i)) →
        R ((gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f))
          ((gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f')))
    (w : Fin m) (hu : u ∈ S w) (hz : ∀ v ∈ S w, x v = false) : False := by
  have hy : ∀ v, v ≠ u → x v = Function.update x u true v := fun v hv => by
    rw [Function.update_of_ne hv]
  have key := rel_prop R hR u gates x _ hy h (out w) (out_ne_inp S gates out h2 hev w u)
  rw [hev, hev] at key
  have h1 : decide (∃ v ∈ S w, x v = true) = false := by
    simp only [decide_eq_false_iff_not]
    rintro ⟨v, hv, hxv⟩
    rw [hz v hv] at hxv; exact absurd hxv (by simp)
  have h2' : decide (∃ v ∈ S w, Function.update x u true v = true) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp⟩
  rw [h1, h2'] at key
  exact hft key

include h2 hev in
/-- Absorbing lemma (equality form). -/
theorem absorb_eq (u : Fin n) (r : ℕ)
    (hr : ∀ (k : ℕ) (hk : k < gates.length), k ≠ r → Insens u (gates[k]'hk))
    (x : Fin n → Bool)
    (hf : val gates x (n + r) = val gates (Function.update x u true) (n + r))
    (w : Fin m) (hu : u ∈ S w) (hz : ∀ v ∈ S w, x v = false) : False :=
  absorb_rel S gates out h2 hev Eq (fun _ => rfl) (by simp) u x (fun k hk => by
    by_cases hkr : k = r
    · subst hkr; exact Or.inl hf
    · exact Or.inr (hr k hk hkr)) w hu hz

include h2 hev in
/-- Absorbing lemma (NOT form): the unique NOT gate `r` is the only gate that reads wire `u`. -/
theorem absorb_anti
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (u : Fin n) (r : ℕ) (hrl : r < gates.length) (hop : (gates[r]'hrl).op = GateOp.not)
    (hr : ∀ (k : ℕ) (hk : k < gates.length), k ≠ r → (u : ℕ) ∉ (gates[k]'hk).inputs)
    (x : Fin n → Bool)
    (hf : val gates (Function.update x u true) (n + r) = true → val gates x (n + r) = true)
    (w : Fin m) (hu : u ∈ S w) (hz : ∀ v ∈ S w, x v = false) : False :=
  absorb_rel S gates out h2 hev (fun a b => b = true → a = true) (fun _ h => h) (by simp) u x
    (fun k hk => by
      by_cases hkr : k = r
      · subst hkr; exact Or.inl hf
      · right
        intro f f' hff
        have hao : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or := by
          rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (hU k r hk hrl h hop) hkr
        exact andor_mono _ hao f f' (fun i hi => hff i (fun e => hr k hk hkr (e ▸ hi))))
    w hu hz

end

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- A point with exactly one dead gate `k` has degree `≥ 2`, and no other dead gate. -/
theorem dc1_facts (M : MinCE S gates out) {v : Fin n} (hdv : (DC v gates).card ≤ 1) (k : ℕ)
    (hk : k < gates.length) (hd : DCp v gates k ∨ DTr v gates k) :
    2 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w).card ∧
      ∀ k', k' < gates.length → k' ≠ k → ¬ (DCp v gates k' ∨ DTr v gates k') := by
  classical
  have hmem : k ∈ DC v gates := by simp [DC, hk, hd]
  have hpos : 1 ≤ (DC v gates).card := Finset.card_pos.mpr ⟨k, hmem⟩
  have hb := M.deadBound v hpos
  have hlt := M.ce.hlt
  refine ⟨by omega, fun k' hk' hne hd' => hne ?_⟩
  have hmem' : k' ∈ DC v gates := by simp [DC, hk', hd']
  exact Finset.card_le_one.mp hdv k' hmem' k hmem

/-- A point of degree `≤ 2` has at most one dead gate. -/
theorem card_DC_le_one_of_deg2 (M : MinCE S gates out) {v : Fin n}
    (hdv : (Finset.univ.filter fun w : Fin m => v ∈ S w).card ≤ 2) : (DC v gates).card ≤ 1 := by
  by_contra h
  have hb := M.deadBound v (by omega)
  have hlt := M.ce.hlt
  omega

/-- A point of degree `≤ 2` with a dead gate `k` has degree exactly 2 and no other dead gate. -/
theorem dc_facts (M : MinCE S gates out) {v : Fin n}
    (hdv : (Finset.univ.filter fun w : Fin m => v ∈ S w).card ≤ 2) (k : ℕ)
    (hk : k < gates.length) (hd : DCp v gates k ∨ DTr v gates k) :
    (Finset.univ.filter fun w : Fin m => v ∈ S w).card = 2 ∧
      ∀ k', k' < gates.length → k' ≠ k → ¬ (DCp v gates k' ∨ DTr v gates k') :=
  have h := M.dc1_facts (M.card_DC_le_one_of_deg2 hdv) k hk hd
  ⟨le_antisymm hdv h.1, h.2⟩

/-- A point of degree `≥ 2` lies in a set avoiding any given other point. -/
theorem avoid (M : MinCE S gates out) {u : Fin n}
    (hdu : 2 ≤ (Finset.univ.filter fun w : Fin m => u ∈ S w).card) (b : Fin n) (hb : u ≠ b) :
    ∃ w, u ∈ S w ∧ b ∉ S w := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨w1, h1, w2, h2, hw12⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (Finset.univ.filter fun w : Fin m => u ∈ S w).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  have hsub : ({u, b} : Finset (Fin n)) ⊆ S w1 ∩ S w2 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨h1, h2⟩
    · exact Finset.mem_inter.mpr ⟨hall _ h1, hall _ h2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hb] at this
  have := M.ce.hS w1 w2 hw12
  omega

/-- Absorbing lemma for a point whose only dead gate is `r`. -/
theorem absorbR (M : MinCE S gates out) (r : ℕ) (hr : r < gates.length) (u : Fin n)
    (hdu : (DC u gates).card ≤ 1)
    (hd : DCp u gates r ∨ DTr u gates r) (x : Fin n → Bool)
    (hf : val gates x (n + r) = val gates (Function.update x u true) (n + r))
    (w : Fin m) (hu : u ∈ S w) (hz : ∀ v ∈ S w, x v = false) : False :=
  absorb_eq S gates out M.ce.h2 M.ce.hev u r
    (fun k hk hk0 => insens_of_notDead u gates k hk (M.ce.hg _ (List.getElem_mem hk))
      ((M.dc1_facts hdu r hr hd).2 k hk hk0)) x hf w hu hz

theorem absorb0 (M : MinCE S gates out) (hpos : 0 < gates.length) (u : Fin n)
    (hdu : (Finset.univ.filter fun w : Fin m => u ∈ S w).card ≤ 2)
    (hd : DCp u gates 0 ∨ DTr u gates 0) (x : Fin n → Bool)
    (hf : val gates x n = val gates (Function.update x u true) n)
    (w : Fin m) (hu : u ∈ S w) (hz : ∀ v ∈ S w, x v = false) : False :=
  M.absorbR 0 hpos u (M.card_DC_le_one_of_deg2 hdu) hd x hf w hu hz

end MinCE

end PEqualNP.Outside.L_meta_951_aux
