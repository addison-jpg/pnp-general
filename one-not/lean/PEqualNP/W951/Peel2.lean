import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Peel
import PEqualNP.Kernel.W951Minimal
import PEqualNP.Kernel.W951Cube

/-!
# Peel2: exact G1.9 for tight points, the G1.3 / G1.6 degree corollaries, and G1.3 (iii)

Source: front's `g1_fable.md` (G1.3, G1.6, G1.9).  Notation as in `PairLemma.lean` / `Peel.lean`:
`σ = base - s ≥ 1`, `V1` = points with exactly one reader, `B` = points with at least two.

* Level 1 (exact G1.9 equality case).  `MinCE.pairGate_unique` (cleanliness: at most one gate is
  `x_u ∨ x_w`), `IsPairGate.reader_left/right`, `MinCE.pairReaders_le` (the pair-gate readers of
  `x_u` are at most `p(u)`), and `MinCE.tight_exact`: for a tight `u` every pair partner `w` has
  exactly one pair gate `x_u ∨ x_w`, `#readers(u) = nonpair(u) + p(u)`, no single-reader point uses
  `u` as singleton (`Users = ∅`, in particular `kL(u) = 0`), and `nonpair(u) = l(u) - σ`
  (additively `base + nonpair(u) = s + l(u)`).
* Level 2 (G1.3 (ii) / G1.6 corollaries, from `MinCE.capacity`): `MinCE.peel_deg`,
  `MinCE.peel_deg_B` (`u ∈ B` used as singleton: `deg u ≥ 3 + σ`), `MinCE.peel_deg_V1`
  (`u ∈ V1`: `deg u ≥ 2 + σ`), `MinCE.capacity_B`, `MinCE.capacity_V1`.
* Level 3 (G1.3 (iii), two-point form).  Kernel part (restriction `x_Z := 0` for a point SET `Z`,
  the set version of `Kernel.list_restrictVar` / `restrictVar_bound`): `Kernel.zeroOn`,
  `Dag.val_restrictZero`, `deadZ`, `list_restrictZero`, `restrictZero_bound`.  W951 part: `DCZ Z`
  (gates dead under `x_Z := 0`), `MinCE.deadBoundSet` (N2 for point sets:
  `base + #DCZ(Z) ≤ s + ∑_{u ∈ Z} deg u`), `MinCE.peel_two` (G1.3 (iii), any `σ`, no tightness:
  `base + #(R_u1 ∪ R_u2) + 1 + [c ∉ R_u1 ∪ R_u2] ≤ s + deg u1 + deg u2`), `MinCE.peel_two_tight`
  (`u1, u2` tight and `σ = 1`: `c` reads `x_u1` or `x_u2`, or the gate `x_u1 ∨ x_u2` exists).
No sorry.
-/

-- The kernel part (`zeroOn`, `Dag.val_restrictZero`, `deadZ`, `list_restrictZero`,
-- `restrictZero_bound`, ...) now lives in `Kernel/W951Cube.lean`: it is the case `ρ = 0`
-- of the cube restriction.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Level 1: the exact G1.9 equality case -/

/-- A pair gate `x_u ∨ x_w` is a reader of `x_u`. -/
theorem IsPairGate.reader_left {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : k ∈ Readers u gates := by
  classical
  obtain ⟨hk, hop, hin⟩ := h
  simp only [Readers, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk, hk, Or.inl ⟨Or.inr hop, ?_⟩⟩
  rcases hin with hin | hin <;> rw [hin] <;> simp

/-- A pair gate `x_u ∨ x_w` is a reader of `x_w`. -/
theorem IsPairGate.reader_right {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : k ∈ Readers w gates := by
  classical
  obtain ⟨hk, hop, hin⟩ := h
  simp only [Readers, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk, hk, Or.inl ⟨Or.inr hop, ?_⟩⟩
  rcases hin with hin | hin <;> rw [hin] <;> simp

theorem IsPairGate.symm {n : ℕ} {gates : List Gate} {k : ℕ} {u w : Fin n}
    (h : IsPairGate gates k u w) : IsPairGate gates k w u := by
  obtain ⟨hk, hop, hin⟩ := h
  exact ⟨hk, hop, hin.symm⟩

theorem pair_right_inj {n : ℕ} {u w w' : Fin n} (huw : u ≠ w)
    (h : ({u, w} : Finset (Fin n)) = {u, w'}) : w = w' := by
  have : w ∈ ({u, w'} : Finset (Fin n)) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact absurd e.symm huw
  · exact e

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- No duplicate pair gates (cleanliness): at most one gate is `x_u ∨ x_w`. -/
theorem pairGate_unique (M : MinCE S gates out) (u w : Fin n) (k k' : ℕ)
    (h : IsPairGate gates k u w) (h' : IsPairGate gates k' u w) : k = k' := by
  have key : ∀ a b : ℕ, IsPairGate gates a u w → IsPairGate gates b u w → ¬ a < b := by
    intro a b ha hb hlt
    have hbl : b < gates.length := by obtain ⟨hbl, -⟩ := hb; exact hbl
    exact M.clean b (n + a) hbl (by omega) fun x => by
      rw [val_pairGate gates b u w hb, val_pairGate gates a u w ha]
  rcases lt_trichotomy k k' with hlt | he | hlt
  · exact absurd hlt (key k k' h h')
  · exact he
  · exact absurd hlt (key k' k h' h)

open Classical in
/-- The readers of `x_u` that are pair gates `x_u ∨ x_w` of pair-sets `{u, w}` are at most `p(u)`
(one per pair-set, by cleanliness). -/
theorem pairReaders_le (M : MinCE S gates out) (u : Fin n) :
    ((Readers u gates).filter
      fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card ≤ pairDeg S u := by
  have C := M.ce
  set PS := Finset.univ.filter fun i : Fin m => u ∈ S i ∧ (S i).card = 2 with hPS
  let g : Fin m → ℕ := fun i =>
    if h : ∃ k w, S i = {u, w} ∧ IsPairGate gates k u w then h.choose else 0
  have hsub : (Readers u gates).filter
      (fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) ⊆ PS.image g := by
    intro k hk
    obtain ⟨-, w, ⟨i, hi⟩, hpg⟩ := Finset.mem_filter.mp hk
    have huw : u ≠ w := by
      intro e; have := C.h2 i; rw [hi, e] at this; simp at this
    have hex : ∃ k w, S i = {u, w} ∧ IsPairGate gates k u w := ⟨k, w, hi, hpg⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · simp only [hPS, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
      exact ⟨by simp, Finset.card_pair huw⟩
    · have hg : g i = hex.choose := by simp only [g]; rw [dif_pos hex]
      obtain ⟨w', hi', hpg'⟩ := hex.choose_spec
      have hww : w = w' := pair_right_inj huw (hi.symm.trans hi')
      rw [hg]
      exact M.pairGate_unique u w _ _ (hww ▸ hpg') hpg
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A point of some set has a gate dead under `x_u := 0`. -/
theorem dc_pos (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i) :
    1 ≤ (DC u gates).card := by
  have C := M.ce
  have hc := pair_count S gates out C.h2 C.hS C.hev C.hg u
  have hd := deg_split S C.h2 u
  have hdeg : 1 ≤ degOf S u := by
    obtain ⟨i, hi⟩ := hu
    unfold degOf
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  by_cases hp : 1 ≤ pairDeg S u
  · omega
  · have := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u (by omega)
    omega

open Classical in
/-- **G1.9, exact equality case.**  Let `u` be tight (`#readers(u) = deg u - σ`).  Then
1. every pair partner `w` (`{u, w}` a set) has exactly one pair gate `x_u ∨ x_w` (existence by
   G1.9, uniqueness by cleanliness);
2. the pair-gate readers of `x_u` are exactly `p(u)` many, and `#readers(u) = nonpair(u) + p(u)`;
3. no single-reader point uses `u` as singleton: `Users = ∅`, in particular `kL(u) = 0`;
4. `nonpair(u) = l(u) - σ`, additively `base + nonpair(u) = s + l(u)`;
5. `#readers(u) = deg u - σ` exactly, additively `s + deg u = base + #readers(u)`. -/
theorem tight_exact (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (ht : Tight S gates u) :
    (∀ (w : Fin n) (i : Fin m), S i = {u, w} → ∃! k, IsPairGate gates k u w) ∧
    ((Readers u gates).filter
      fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card = pairDeg S u ∧
    (Readers u gates).card = nonpair S gates u + pairDeg S u ∧
    Users S gates u = ∅ ∧ LineUsers S gates u = ∅ ∧
    baseOf S + nonpair S gates u = gates.length + lineDeg S u ∧
    gates.length + degOf S u = baseOf S + (Readers u gates).card := by
  have C := M.ce
  obtain ⟨heq, hnp⟩ := M.tight_readers u hu ht
  obtain ⟨-, hdb, hrp⟩ := M.rule_p u hu
  have hle := M.pairReaders_le u
  have hsplit := Finset.card_filter_add_card_filter_not (s := Readers u gates)
    (fun k => ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w)
  have hnpdef : nonpair S gates u = ((Readers u gates).filter
      fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card := rfl
  have hd := deg_split S C.h2 u
  have hpos := M.dc_pos u hu
  rw [← heq] at hpos hdb
  have hcap := (M.capacity u hpos).2
  have hkL := (M.rule_p_kL u hu).2
  unfold Tight at ht
  refine ⟨fun w i hi => ?_, by omega, by omega, ?_, ?_, by omega, by omega⟩
  · obtain ⟨k, hk⟩ := M.pairGate_of_tight u w i hi ht
    exact ⟨k, hk, fun k' hk' => M.pairGate_unique u w k' k hk' hk⟩
  · exact Finset.card_eq_zero.mp (by omega)
  · exact Finset.card_eq_zero.mp (by omega)

/-! ## Level 2: the G1.3 (ii) / G1.6 corollary forms -/

/-- G1.3 (ii), general form: if a single-reader point `v` uses `u` as the only earlier point of
one of its sets and `x_u` has a reader, then `dead0(u) ≥ #readers(u) + 1` and
`deg u ≥ #readers(u) + 1 + σ`. -/
theorem peel_deg (M : MinCE S gates out) (u : Fin n) (hU : (Users S gates u).Nonempty)
    (hr : 1 ≤ (Readers u gates).card) :
    (Readers u gates).card + 1 ≤ (DC u gates).card ∧
    baseOf S + (Readers u gates).card + 1 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.capacity u hr
  have := Finset.card_pos.mpr hU
  exact ⟨by omega, by omega⟩

/-- G1.3 (ii) for `u ∈ B` (at least two readers): a point of `B` used as the only earlier point
by some single-reader point has `dead0(u) ≥ 3` and `deg u ≥ 3 + σ`. -/
theorem peel_deg_B (M : MinCE S gates out) (u : Fin n) (hB : 2 ≤ (Readers u gates).card)
    (hU : (Users S gates u).Nonempty) :
    3 ≤ (DC u gates).card ∧ baseOf S + 3 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.peel_deg u hU (by omega)
  exact ⟨by omega, by omega⟩

/-- G1.3 (ii) for `u ∈ V1` (exactly one reader): `dead0(u) ≥ 2` and `deg u ≥ 2 + σ`. -/
theorem peel_deg_V1 (M : MinCE S gates out) (u : Fin n) (hV : (Readers u gates).card = 1)
    (hU : (Users S gates u).Nonempty) :
    2 ≤ (DC u gates).card ∧ baseOf S + 2 ≤ gates.length + degOf S u := by
  obtain ⟨h1, h2⟩ := M.peel_deg u hU (by omega)
  exact ⟨by omega, by omega⟩

/-- The same two corollaries stated with one user: `v` single-reader, `u` the only point of
`S i` other than `v` with a reader below the reader of `v`. -/
theorem peel_deg_of_uses (M : MinCE S gates out) (u v : Fin n) (i : Fin m)
    (h : UsesVia S gates u v i) :
    (2 ≤ (Readers u gates).card → baseOf S + 3 ≤ gates.length + degOf S u) ∧
    ((Readers u gates).card = 1 → baseOf S + 2 ≤ gates.length + degOf S u) := by
  classical
  have hU : (Users S gates u).Nonempty :=
    ⟨v, by simp only [Users, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  exact ⟨fun hB => (M.peel_deg_B u hB hU).2, fun hV => (M.peel_deg_V1 u hV hU).2⟩

/-- G1.6 for `u ∈ B`: `#Users(u) ≤ deg u - σ - 2`. -/
theorem capacity_B (M : MinCE S gates out) (u : Fin n) (hB : 2 ≤ (Readers u gates).card) :
    baseOf S + 2 + (Users S gates u).card ≤ gates.length + degOf S u := by
  have := (M.capacity u (by omega)).2
  omega

/-- G1.6 for `u ∈ V1`: `#Users(u) ≤ deg u - σ - 1`. -/
theorem capacity_V1 (M : MinCE S gates out) (u : Fin n) (hV : (Readers u gates).card = 1) :
    baseOf S + 1 + (Users S gates u).card ≤ gates.length + degOf S u := by
  have := (M.capacity u (by omega)).2
  omega

end MinCE

/-! ## Level 3: G1.3 (iii), the two-point form -/

open Classical in
/-- The gates dead under the restriction `x_Z := 0` (`Z` a point set): on `{x | x = 0 on Z}` the
gate equals an earlier wire, or is constant. -/
noncomputable def DCZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k =>
    (∃ j, j < n + k ∧ ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) →
      val gates x (n + k) = val gates x j) ∨
    ∃ c : Bool, ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) → val gates x (n + k) = c

/-- Dead under `x_u := 0` implies dead under `x_Z := 0` for `u ∈ Z`. -/
theorem DC_sub_DCZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) (u : Fin n) (hu : u ∈ Z) :
    DC u gates ⊆ DCZ Z gates := by
  classical
  intro k hk
  simp only [DC, Finset.mem_filter, Finset.mem_range] at hk
  simp only [DCZ, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk.1, ?_⟩
  rcases hk.2 with ⟨j, hj, h⟩ | h
  · exact Or.inl ⟨j, hj, fun x hx => h x (hx u hu)⟩
  · exact Or.inr ⟨true, fun x hx => h x (hx u hu)⟩

theorem DCZ_sub_deadZ {n : ℕ} (Z : Finset (Fin n)) (gates : List Gate) (O : Finset ℕ) :
    DCZ Z gates ⊆ Kernel.deadZ gates Z O := by
  classical
  intro k hk
  simp only [DCZ, Finset.mem_filter, Finset.mem_range] at hk
  rcases hk.2 with ⟨j, hj, h⟩ | ⟨c, h⟩
  · exact Kernel.mem_deadZ_of_copy gates Z O k hk.1 j hj h
  · exact Kernel.mem_deadZ_of_const gates Z O k hk.1 c h

/-- An OR gate of fan-in `≤ 2` reading both `x_u1` and `x_u2` (`u1 ≠ u2`) is the pair gate. -/
theorem isPairGate_of_readers {n : ℕ} (gates : List Gate) (u1 u2 : Fin n) (h12 : u1 ≠ u2)
    (k : ℕ) (hk : k < gates.length) (hop : (gates[k]'hk).op = GateOp.or)
    (hlen : (gates[k]'hk).inputs.length ≤ 2)
    (h1 : k ∈ Readers u1 gates) (h2 : k ∈ Readers u2 gates) : IsPairGate gates k u1 u2 := by
  classical
  rw [readers_eq_wreaders] at h1 h2
  obtain ⟨_, h1⟩ := (mem_wreaders _ _ _).mp h1
  obtain ⟨_, h2⟩ := (mem_wreaders _ _ _).mp h2
  have hne : (u1 : ℕ) ≠ (u2 : ℕ) := Fin.val_ne_of_ne h12
  have m1 : (u1 : ℕ) ∈ (gates[k]'hk).inputs := by
    rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [hop] at h; cases h
  have m2 : (u2 : ℕ) ∈ (gates[k]'hk).inputs := by
    rcases h2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [hop] at h; cases h
  refine ⟨hk, hop, ?_⟩
  generalize (gates[k]'hk).inputs = l at hlen m1 m2
  match l, hlen with
  | [], _ => simp at m1
  | [a], _ =>
    simp only [List.mem_singleton] at m1 m2
    exact absurd (m1.trans m2.symm) hne
  | [a, b], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2
    rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left; rw [← e1, ← e2]
    · right; rw [← e1, ← e2]
    · exact absurd (e1.trans e2.symm) hne
  | _ :: _ :: _ :: _, h => simp at h

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- **N2 for point sets**: in a minimal counterexample, for every point set `Z` with at least one
gate dead under `x_Z := 0`, `base + #dead(Z := 0) ≤ s + ∑_{u ∈ Z} deg u`. -/
theorem deadBoundSet (M : MinCE S gates out) (Z : Finset (Fin n))
    (hd : 1 ≤ (DCZ Z gates).card) :
    baseOf S + (DCZ Z gates).card ≤ gates.length + ∑ u ∈ Z, degOf S u := by
  classical
  have C := M.ce
  have hsub := Finset.card_le_card (DCZ_sub_deadZ Z gates (Finset.univ.image out))
  have h := Kernel.restrictZero_bound S gates out C.hS C.hg C.hU C.hev
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) Z (by omega)
  set I := Finset.univ.filter (fun w : Fin m => 2 ≤ (S w \ Z).card)
  have key : ∀ w : Fin m, (S w).card - 1 ≤
      (if w ∈ I then (S w \ Z).card - 1 else 0) + (S w ∩ Z).card := by
    intro w
    have h1 := Finset.card_sdiff_add_card_inter (S w) Z
    by_cases hI : w ∈ I
    · rw [if_pos hI]; omega
    · rw [if_neg hI]
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hI
      omega
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => key w
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hsum
  have hdeg : ∑ w : Fin m, (S w ∩ Z).card = ∑ u ∈ Z, degOf S u := by
    have e1 : ∀ w : Fin m, (S w ∩ Z).card = ∑ u ∈ Z, (if u ∈ S w then 1 else 0) := by
      intro w
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    have e2 : ∀ u : Fin n, degOf S u = ∑ w : Fin m, (if u ∈ S w then 1 else 0) := by
      intro u
      unfold degOf
      rw [Finset.card_filter]
    rw [Finset.sum_congr rfl (fun w _ => e1 w), Finset.sum_comm,
      Finset.sum_congr rfl (fun u _ => e2 u)]
  unfold baseOf
  omega

open Classical in
/-- **G1.3 (iii), two-point form (general: any `σ`, no tightness).**  Let `v` be a single-reader
point with reader `r`, `S i ∋ v`, and let `u1 ≠ u2` (both `≠ v`) be such that no point of `S i`
other than `u1, u2` has a reader below `r` (`S i ∩ A_j ⊆ {u1, u2}`).  Then the other input of `r`
is a gate `c < r`, and under `x_u1 = x_u2 = 0` the readers of `x_u1`, of `x_u2`, the gate `r`
(which is no reader of either) and the gate `c` all die:
`base + #(R_u1 ∪ R_u2) + 1 + [c ∉ R_u1 ∪ R_u2] ≤ s + deg u1 + deg u2`. -/
theorem peel_two (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r})
    (i : Fin m) (hvi : v ∈ S i) (u1 u2 : Fin n) (h12 : u1 ≠ u2) (hv1 : u1 ≠ v) (hv2 : u2 ≠ v)
    (hA : ∀ t ∈ S i, t ≠ u1 → t ≠ u2 → ∀ k ∈ Readers t gates, r ≤ k) :
    ∃ c, c < r ∧ (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = n + c) ∧
      r ∉ Readers u1 gates ∪ Readers u2 gates ∧
      baseOf S + (Readers u1 gates ∪ Readers u2 gates).card + 1 +
        (if c ∈ Readers u1 gates ∪ Readers u2 gates then 0 else 1) ≤
          gates.length + degOf S u1 + degOf S u2 := by
  have C := M.ce
  obtain ⟨c, b, hc1, hc2, hr, hnu, hW, -, hcore⟩ := M.single_core2 v r hR
  set Z : Finset (Fin n) := {u1, u2} with hZ
  set R := Readers u1 gates ∪ Readers u2 gates with hRdef
  have hx : ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) →
      val gates x c = b ∧ val gates x (n + r) = x v := by
    intro x hxZ
    refine hcore i hvi x fun t ht hex => ?_
    by_cases ht1 : t = u1
    · rw [ht1]; exact hxZ u1 (by simp [hZ])
    · by_cases ht2 : t = u2
      · rw [ht2]; exact hxZ u2 (by simp [hZ])
      · obtain ⟨k, hk, hlt⟩ := hex
        exact absurd hlt (by have := hA t ht ht1 ht2 k hk; omega)
  have hrR : r ∉ R := by
    simp only [hRdef, Finset.mem_union, not_or]
    exact ⟨hnu u1 hv1, hnu u2 hv2⟩
  have hRsub : R ⊆ DCZ Z gates := by
    refine Finset.union_subset ?_ ?_
    · exact (readers_sub_DC u1 gates C.hg).trans (DC_sub_DCZ Z gates u1 (by simp [hZ]))
    · exact (readers_sub_DC u2 gates C.hg).trans (DC_sub_DCZ Z gates u2 (by simp [hZ]))
  have hrD : r ∈ DCZ Z gates := by
    simp only [DCZ, Finset.mem_filter, Finset.mem_range]
    exact ⟨hr, Or.inl ⟨v, by have := v.2; omega, fun x hxZ => by
      rw [(hx x hxZ).2, val_inp _ _ _ v.2]⟩⟩
  have hcD : c - n ∈ DCZ Z gates := by
    simp only [DCZ, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inr ⟨b, fun x hxZ => by
      rw [show n + (c - n) = c by omega]; exact (hx x hxZ).1⟩⟩
  refine ⟨c - n, by omega, fun p hp => ?_, hrR, ?_⟩
  · rw [show n + (c - n) = c by omega]; exact hW p hp
  have hins : insert (c - n) (insert r R) ⊆ DCZ Z gates :=
    Finset.insert_subset hcD (Finset.insert_subset hrD hRsub)
  have hcard := Finset.card_le_card hins
  have hcr : c - n ∉ insert r R ↔ c - n ∉ R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hb := M.deadBoundSet Z (by have := Finset.card_pos.mpr ⟨r, hrD⟩; omega)
  have hsumZ : ∑ u ∈ Z, degOf S u = degOf S u1 + degOf S u2 := Finset.sum_pair h12
  have h1 : (insert r R).card = R.card + 1 := Finset.card_insert_of_notMem hrR
  by_cases hcR : c - n ∈ R
  · rw [if_pos hcR]
    have := Finset.card_le_card (Finset.insert_subset hrD hRsub)
    omega
  · rw [if_neg hcR]
    rw [Finset.card_insert_of_notMem (hcr.mpr hcR), h1] at hcard
    omega

/-- **G1.3 (iii) as stated in the notes** (`u1, u2` tight, `σ = 1`): the other input `c` of the
reader `r` of `v` is a direct reader of `x_u1` or of `x_u2`, or the gate `x_u1 ∨ x_u2` exists. -/
theorem peel_two_tight (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r})
    (i : Fin m) (hvi : v ∈ S i) (u1 u2 : Fin n) (h12 : u1 ≠ u2) (hv1 : u1 ≠ v) (hv2 : u2 ≠ v)
    (hA : ∀ t ∈ S i, t ≠ u1 → t ≠ u2 → ∀ k ∈ Readers t gates, r ≤ k)
    (ht1 : Tight S gates u1) (ht2 : Tight S gates u2) (hσ : baseOf S = gates.length + 1) :
    ∃ c, c < r ∧ (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = n + c) ∧
      (c ∈ Readers u1 gates ∨ c ∈ Readers u2 gates ∨ ∃ k, IsPairGate gates k u1 u2) := by
  classical
  have C := M.ce
  obtain ⟨c, hcr, hW, -, hb⟩ := M.peel_two v r hR i hvi u1 u2 h12 hv1 hv2 hA
  refine ⟨c, hcr, hW, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hc2, hnp⟩ := hne
  have hcR : c ∉ Readers u1 gates ∪ Readers u2 gates := by
    simp only [Finset.mem_union, not_or]; exact ⟨hc1, hc2⟩
  rw [if_neg hcR] at hb
  have hint : Readers u1 gates ∩ Readers u2 gates = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_inter.mp hk
    have hkl : k < gates.length := by
      have := Finset.mem_filter.mp hk1
      exact Finset.mem_range.mp this.1
    exact hnp k (isPairGate_of_readers gates u1 u2 h12 k hkl (M.tight_or u1 ht1 k hkl hk1)
      (C.hg _ (List.getElem_mem hkl)).2 hk1 hk2)
  have hu := Finset.card_union_add_card_inter (Readers u1 gates) (Readers u2 gates)
  rw [hint, Finset.card_empty] at hu
  unfold Tight at ht1 ht2
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux
