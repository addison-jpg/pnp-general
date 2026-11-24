import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Bottom

/-!
# G1.9 (pair lemma) and rule 'p' (PAIR-N2) for a minimal counterexample

Notation (g1_fable.md / pairrule_log.md): `deg u = #{w | u ∈ S w}`, `l(u) = #{w | u ∈ S w, |S w| ≥ 3}`
(`lineDeg`), `p(u) = #{w | u ∈ S w, |S w| = 2}` (`pairDeg`), `base = ∑ (|S w| - 1)`, `s = #gates`,
`σ = base - s`.  `Readers u gates` (MinCEFacts) = the gates reading `x_u`; `DC u gates` (Dead) = the
gates dead under `x_u := 0`.

* `lowest_pair_gate` (the mechanism of G1.9): if gate `k` is the LOWEST gate that equals `x_w` on
  `{x_u = 0}` and `k` reads `x_u`, then gate `k` is the pair gate `x_u ∨ x_w`.
* `MinCE.pairGate_of_tight` (level 1, G1.9): if `u` is tight (`#readers(u) = deg u - σ`, stated as
  `s + deg u ≤ base + #readers(u)`) and `{u, w}` is one of the sets, some gate is `x_u ∨ x_w`.
* Rule 'p' (counting form, `kL(u)` term dropped): `pair_count` (`nonpair(u) + p(u) ≤ #DC(u)`, any
  correct circuit), `nonpair_pos` (`l(u) ≥ 1 → nonpair(u) ≥ 1`), `MinCE.rule_p`
  (`nonpair(u) + p(u) ≤ #DC(u) ≤ deg u - σ`, `nonpair(u) ≤ l(u) - σ`), `MinCE.line_bound`
  (`l(u) ≥ 1 + σ`), `MinCE.tight_readers`.
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section defs
variable {n m : ℕ}

/-- `base = ∑ (|S w| - 1)`. -/
def baseOf (S : Fin m → Finset (Fin n)) : ℕ := ∑ i : Fin m, ((S i).card - 1)

/-- `deg u = #{w | u ∈ S w}`. -/
def degOf (S : Fin m → Finset (Fin n)) (u : Fin n) : ℕ :=
  (Finset.univ.filter fun w : Fin m => u ∈ S w).card

/-- `l(u) = #{w | u ∈ S w, |S w| ≥ 3}` (lines through `u`). -/
def lineDeg (S : Fin m → Finset (Fin n)) (u : Fin n) : ℕ :=
  (Finset.univ.filter fun w : Fin m => u ∈ S w ∧ 3 ≤ (S w).card).card

/-- `p(u) = #{w | u ∈ S w, |S w| = 2}` (pair-sets through `u`). -/
def pairDeg (S : Fin m → Finset (Fin n)) (u : Fin n) : ℕ :=
  (Finset.univ.filter fun w : Fin m => u ∈ S w ∧ (S w).card = 2).card

/-- `u` is tight: `#readers(u) = deg u - σ` (with `σ = base - s`); stated as the nontrivial
inequality `s + deg u ≤ base + #readers(u)` (the reverse holds by N2 whenever `u` has a reader). -/
def Tight (S : Fin m → Finset (Fin n)) (gates : List Gate) (u : Fin n) : Prop :=
  gates.length + degOf S u ≤ baseOf S + (Readers u gates).card

/-- Gate `k` is the pair gate `x_u ∨ x_w` (op OR, inputs the two input wires `u, w` in some
order). -/
def IsPairGate (gates : List Gate) (k : ℕ) (u w : Fin n) : Prop :=
  ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.or ∧
    ((gates[k]'hk).inputs = [(u : ℕ), (w : ℕ)] ∨ (gates[k]'hk).inputs = [(w : ℕ), (u : ℕ)])

open Classical in
/-- `nonpair(u)`: the readers of `x_u` that are not a pair gate `x_u ∨ x_w` with `{u, w}` a set. -/
noncomputable def nonpair (S : Fin m → Finset (Fin n)) (gates : List Gate) (u : Fin n) : ℕ :=
  ((Readers u gates).filter fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w).card

end defs

/-! ## The lowest gate restricting to `x_w` -/

/-- The mechanism of G1.9: the LOWEST gate `k` that equals `x_w` on `{x_u = 0}`, if it reads `x_u`,
is the pair gate `x_u ∨ x_w`. -/
theorem lowest_pair_gate {n : ℕ} (gates : List Gate) (u w : Fin n) (huw : u ≠ w)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gates.length)
    (hres : ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w)
    (hlow : ∀ k', k' < k → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w)
    (hR : k ∈ Readers u gates) : IsPairGate gates k u w := by
  classical
  set ew : Fin n → Bool := fun t => decide (t = w) with hewdef
  have hewu : ew u = false := by simp [hewdef, huw]
  have hew : ew w = true := by simp [hewdef]
  set z0 : Fin n → Bool := fun _ => false with hz0
  -- an input of gate `k` that restricts to `x_w` is the input wire `w`
  have hc : ∀ c : ℕ, (∀ x : Fin n → Bool, x u = false → val (gates.take k) x c = x w) →
      c = w := by
    intro c hcx
    by_cases hcn : c < n
    · by_contra hne
      have h1 := hcx ew hewu
      rw [val_inp _ _ _ hcn, hew] at h1
      have h2 : ew ⟨c, hcn⟩ = false := by
        simp only [hewdef, decide_eq_false_iff_not]
        intro e; exact hne (by rw [← e])
      rw [h2] at h1; exact absurd h1 (by simp)
    · by_cases hck : c < n + k
      · exfalso
        apply hlow (c - n) (by omega)
        intro x hx
        rw [show n + (c - n) = c by omega, ← val_take gates x k c (by omega) hck]
        exact hcx x hx
      · exfalso
        have h1 := hcx ew hewu
        rw [val_take_ge _ _ _ _ (by omega), hew] at h1
        exact absurd h1 (by simp)
  have hux : ∀ x : Fin n → Bool, x u = false → val (gates.take k) x u = false := by
    intro x hx; rw [val_inp _ _ _ u.2]; exact hx
  have hv := fun x : Fin n → Bool => val_gate gates x k hk
  simp only [Readers, Finset.mem_filter, Finset.mem_range] at hR
  obtain ⟨-, hk2, hR⟩ := hR
  replace hR : (((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧
      (u : ℕ) ∈ (gates[k]'hk).inputs) ∨
      ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = (u : ℕ) :: rest) := hR
  clear hk2
  have hlen := (hg _ (List.getElem_mem hk)).2
  unfold IsPairGate
  refine ⟨hk, ?_⟩
  generalize gates[k]'hk = g at hR hlen hv
  obtain ⟨op, ins⟩ := g
  simp only at hR hlen hv ⊢
  -- the gate value at `e_w` must be `true`, at `0` must be `false`
  have hA := hres ew hewu
  have hB := hres z0 rfl
  rw [hv, hew] at hA
  rw [hv] at hB
  simp only [hz0] at hB
  match ins, hlen with
  | [], _ => simp at hR
  | [a], _ =>
    rcases hR with ⟨hop, ha⟩ | ⟨hop, rest, ha⟩
    · simp only [List.mem_singleton] at ha
      subst ha
      rcases hop with rfl | rfl <;> simp [GateOp.eval, hux ew hewu] at hA
    · simp only [List.cons.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      subst hop
      simp [GateOp.eval] at hB
      exact absurd (hB.symm.trans (hux _ rfl)) (by simp)
  | [a, b], _ =>
    rcases hR with ⟨hop, ha⟩ | ⟨hop, rest, ha⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases hop with rfl | rfl
      · rcases ha with rfl | rfl <;> simp [GateOp.eval, hux ew hewu] at hA
      · refine ⟨rfl, ?_⟩
        rcases ha with rfl | rfl
        · left
          have : b = w := hc b fun x hx => by
            have h := hres x hx
            rw [hv] at h
            simpa [GateOp.eval, hux x hx] using h
          rw [this]
        · right
          have : a = w := hc a fun x hx => by
            have h := hres x hx
            rw [hv] at h
            simpa [GateOp.eval, hux x hx] using h
          rw [this]
    · simp only [List.cons.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      subst hop
      simp [GateOp.eval] at hB
      exact absurd (hB.symm.trans (hux _ rfl)) (by simp)
  | _ :: _ :: _ :: _, h => simp at h

/-- A gate restricting to `x_w` on `{x_u = 0}` is dead there (a copy of the input wire `w`). -/
theorem dc_of_restrict {n : ℕ} (gates : List Gate) (u w : Fin n) (k : ℕ) (hk : k < gates.length)
    (hres : ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w) : k ∈ DC u gates := by
  classical
  simp only [DC, Finset.mem_filter, Finset.mem_range]
  refine ⟨hk, Or.inl ⟨w, by have := w.2; omega, fun x hx => ?_⟩⟩
  rw [hres x hx, val_inp _ _ _ w.2]

section pairset
variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))

include h2 hev in
/-- The output of a pair-set `{u, w}` is a gate that restricts to `x_w` on `{x_u = 0}`. -/
theorem pair_out_gate (u w : Fin n) (i : Fin m) (hi : S i = {u, w}) :
    ∃ k, k < gates.length ∧ out i = n + k ∧
      ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w := by
  classical
  have huw : u ≠ w := by
    intro e; have := h2 i; rw [hi, e] at this; simp at this
  have hres : ∀ x : Fin n → Bool, x u = false → val gates x (out i) = x w := by
    intro x hx
    rw [hev, hi]
    cases hxw : x w <;> simp [hx, hxw]
  have hn : n ≤ out i := by
    by_contra h
    exact out_ne_inp S gates out h2 hev i ⟨out i, by omega⟩ rfl
  have hlt : out i < n + gates.length := by
    by_contra h
    have := hres (fun t => decide (t = w)) (by simp [huw])
    rw [val_ge _ _ _ (by omega)] at this
    simp at this
  exact ⟨out i - n, by omega, by omega, fun x hx => by
    rw [show n + (out i - n) = out i by omega]; exact hres x hx⟩

include h2 hev in
/-- For a pair-set `{u, w}`: the lowest gate restricting to `x_w` on `{x_u = 0}` exists, is dead
under `x_u := 0`, and if it reads `x_u` it is the pair gate `x_u ∨ x_w`. -/
theorem pair_lowest
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (u w : Fin n) (i : Fin m) (hi : S i = {u, w}) :
    ∃ k, k < gates.length ∧ (∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w) ∧
      k ∈ DC u gates ∧ (k ∈ Readers u gates → IsPairGate gates k u w) := by
  classical
  have huw : u ≠ w := by
    intro e; have := h2 i; rw [hi, e] at this; simp at this
  have hex : ∃ k, k < gates.length ∧
      ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w := by
    obtain ⟨k, hk, -, hres⟩ := pair_out_gate S gates out h2 hev u w i hi
    exact ⟨k, hk, hres⟩
  set k := Nat.find hex with hkdef
  obtain ⟨hk, hres⟩ := Nat.find_spec hex
  refine ⟨k, hk, hres, dc_of_restrict gates u w k hk hres, fun hR => ?_⟩
  refine lowest_pair_gate gates u w huw hg k hk hres (fun k' hk' hall => ?_) hR
  exact Nat.find_min hex hk' ⟨by omega, hall⟩

end pairset

/-! ## Rule 'p' (PAIR-N2), counting form -/

section rulep
variable {n m : ℕ}

theorem deg_split (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (u : Fin n) :
    degOf S u = lineDeg S u + pairDeg S u := by
  classical
  unfold degOf lineDeg pairDeg
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    have := h2 i
    constructor
    · intro h
      by_cases h3 : 3 ≤ (S i).card
      · exact Or.inl ⟨h, h3⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · rw [Finset.disjoint_filter]
    intro i _ h h'
    omega

/-- A pair-set through `u` is `{u, w}` for some `w`. -/
theorem pair_other (S : Fin m → Finset (Fin n)) (u : Fin n) (i : Fin m) (hu : u ∈ S i)
    (hc : (S i).card = 2) : ∃ w, S i = {u, w} := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hc
  rw [he] at hu ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact ⟨b, rfl⟩
  · exact ⟨a, Finset.pair_comm _ _⟩

/-- The pair gate `x_u ∨ x_w` computes `x_u ∨ x_w`. -/
theorem val_pairGate {n : ℕ} (gates : List Gate) (k : ℕ) (u w : Fin n)
    (h : IsPairGate gates k u w) (x : Fin n → Bool) :
    val gates x (n + k) = (x u || x w) := by
  obtain ⟨hk, hop, hin⟩ := h
  rw [val_gate gates x k hk, hop]
  rcases hin with hin | hin <;> rw [hin] <;>
    simp [GateOp.eval, val_inp _ _ _ u.2, val_inp _ _ _ w.2, Bool.or_comm]

open Classical in
/-- The lowest gate that equals the output of set `i` on `{x_u = 0}` (`0` if there is none). -/
noncomputable def lowR (gates : List Gate) (out : Fin m → ℕ) (u : Fin n) (i : Fin m) : ℕ :=
  if h : ∃ k, k < gates.length ∧
      ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = val gates x (out i)
  then Nat.find h else 0

variable (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)

include h2 hev in
/-- For a pair-set `S i = {u, w}`, `lowR u i` is the lowest gate equal to `x_w` on `{x_u = 0}`. -/
theorem lowR_spec (u w : Fin n) (i : Fin m) (hi : S i = {u, w}) :
    lowR gates out u i < gates.length ∧
      (∀ x : Fin n → Bool, x u = false → val gates x (n + lowR gates out u i) = x w) ∧
      ∀ k', k' < lowR gates out u i →
        ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w := by
  classical
  have hres : ∀ x : Fin n → Bool, x u = false → val gates x (out i) = x w := by
    intro x hx
    rw [hev, hi]
    cases hxw : x w <;> simp [hx, hxw]
  obtain ⟨k0, hk0, ho, -⟩ := pair_out_gate S gates out h2 hev u w i hi
  have hex : ∃ k, k < gates.length ∧
      ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = val gates x (out i) :=
    ⟨k0, hk0, fun x _ => by rw [ho]⟩
  have hdef : lowR gates out u i = Nat.find hex := by
    unfold lowR; exact dif_pos hex
  obtain ⟨hk, hk'⟩ := Nat.find_spec hex
  rw [hdef]
  refine ⟨hk, fun x hx => (hk' x hx).trans (hres x hx), fun k' hlt hall => ?_⟩
  exact Nat.find_min hex hlt ⟨by omega, fun x hx => (hall x hx).trans (hres x hx).symm⟩

include h2 hS hev hg in
/-- Rule 'p', counting half (any correct circuit): `nonpair(u) + p(u) ≤ #DC(u)`.  The readers of
`x_u` that are not pair gates, and the lowest gates `g_w` restricting to `x_w` (one per pair-set
`{u, w}`), are distinct gates dead under `x_u := 0`. -/
theorem pair_count (u : Fin n) : nonpair S gates u + pairDeg S u ≤ (DC u gates).card := by
  classical
  set PS := Finset.univ.filter fun i : Fin m => u ∈ S i ∧ (S i).card = 2 with hPS
  set N := (Readers u gates).filter
    (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) with hN
  set G := PS.image (lowR gates out u) with hG
  have hw : ∀ i ∈ PS, ∃ w, S i = {u, w} := by
    intro i hi
    simp only [hPS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact pair_other S u i hi.1 hi.2
  have huw : ∀ (w : Fin n) (i : Fin m), S i = {u, w} → u ≠ w := by
    intro w i hi e; have := h2 i; rw [hi, e] at this; simp at this
  have hGsub : G ⊆ DC u gates := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨hlt, hres, -⟩ := lowR_spec S gates out h2 hev u w i hiw
    exact dc_of_restrict gates u w _ hlt hres
  have hNsub : N ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (readers_sub_DC u gates hg)
  have hdisj : Disjoint N G := by
    rw [Finset.disjoint_left]
    intro k hkN hkG
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkG
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨hlt, hres, hlow⟩ := lowR_spec S gates out h2 hev u w i hiw
    simp only [hN, Finset.mem_filter] at hkN
    exact hkN.2 ⟨w, ⟨i, hiw⟩,
      lowest_pair_gate gates u w (huw w i hiw) hg _ hlt hres hlow hkN.1⟩
  have hinj : Set.InjOn (lowR gates out u) PS := by
    intro i hi j hj hij
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨w', hjw⟩ := hw j hj
    obtain ⟨-, hres, -⟩ := lowR_spec S gates out h2 hev u w i hiw
    obtain ⟨-, hres', -⟩ := lowR_spec S gates out h2 hev u w' j hjw
    have hww : w = w' := by
      have h1 := hres (fun t => decide (t = w)) (by simp [huw w i hiw])
      have h2' := hres' (fun t => decide (t = w)) (by simp [huw w i hiw])
      rw [hij] at h1
      rw [h1] at h2'
      have h3 : w' = w := by simpa using h2'
      exact h3.symm
    by_contra hne
    have := hS i j hne
    rw [hiw, hjw, hww, Finset.inter_self, Finset.card_pair (huw w' j hjw)] at this
    omega
  have hGc : G.card = PS.card := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card (Finset.union_subset hNsub hGsub)
  rw [Finset.card_union_of_disjoint hdisj] at hle
  unfold nonpair pairDeg
  rw [← hPS, ← hN]
  omega

include h2 hS hev hg in
/-- Rule 'p', `nonpair(u) ≥ 1` (any correct circuit): a point on a line (`|S| ≥ 3`) has a reader
that is not a pair gate.  If every reader of `x_u` were a pair gate `x_u ∨ x_w`, then at
`z = 1_{P(u)}` toggling `x_u` changes no wire except `x_u`, but it changes `OR(L)` for a line
`L ∋ u` (which avoids every pair partner of `u`). -/
theorem nonpair_pos (u : Fin n) (hl : 1 ≤ lineDeg S u) : 1 ≤ nonpair S gates u := by
  classical
  by_contra h0
  have hN : ∀ k ∈ Readers u gates, ∃ w, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w := by
    intro k hk
    by_contra hne
    have hmem : k ∈ (Readers u gates).filter
        (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) :=
      Finset.mem_filter.mpr ⟨hk, hne⟩
    have := Finset.card_pos.mpr ⟨k, hmem⟩
    unfold nonpair at h0
    omega
  have huw : ∀ (w : Fin n) (i : Fin m), S i = {u, w} → u ≠ w := by
    intro w i hi e; have := h2 i; rw [hi, e] at this; simp at this
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by unfold lineDeg at hl; omega :
    0 < (Finset.univ.filter fun w : Fin m => u ∈ S w ∧ 3 ≤ (S w).card).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0
  set z : Fin n → Bool := fun t => decide (∃ i, S i = {u, t}) with hzdef
  have hzu : z u = false := by
    simp only [hzdef, decide_eq_false_iff_not, not_exists]
    intro i hi; have := h2 i; rw [hi] at this; simp at this
  have hzL : ∀ t ∈ S i0, z t = false := by
    intro t ht
    simp only [hzdef, decide_eq_false_iff_not, not_exists]
    intro i hi
    have hut := huw t i hi
    have hne : i ≠ i0 := by
      intro e; subst e
      have := hi0.2; rw [hi, Finset.card_pair hut] at this; omega
    have hsub : ({u, t} : Finset (Fin n)) ⊆ S i ∩ S i0 := by
      intro a ha
      rw [Finset.mem_inter]
      refine ⟨by rw [hi]; exact ha, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hi0.1
      · exact ht
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hut] at this
    have := hS i i0 hne
    omega
  set y := Function.update z u true with hydef
  have hzy : ∀ v, v ≠ u → z v = y v := fun v hv => by rw [hydef, Function.update_of_ne hv]
  have key := rel_prop Eq (fun _ => rfl) u gates z y hzy (fun k hk => by
    by_cases hR : k ∈ Readers u gates
    · left
      obtain ⟨w, ⟨i, hi⟩, hpg⟩ := hN k hR
      have hzw : z w = true := by simp only [hzdef, decide_eq_true_eq]; exact ⟨i, hi⟩
      rw [val_pairGate gates k u w hpg, val_pairGate gates k u w hpg, ← hzy w (huw w i hi).symm,
        hzw]
      simp
    · right
      exact insens_of_not_reader u gates k hk hR (hg _ (List.getElem_mem hk)).1)
    (out i0) (out_ne_inp S gates out h2 hev i0 u)
  rw [hev, hev] at key
  have hl : decide (∃ v ∈ S i0, z v = true) = false := by
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv; rw [hzL v hv]; simp
  have hr : decide (∃ v ∈ S i0, y v = true) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨u, hi0.1, by simp [hydef]⟩
  rw [hl, hr] at key
  exact absurd key (by simp)

end rulep

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- G1.9, level 1: in a minimal counterexample, if `u` is tight and `{u, w}` is one of the sets,
then some gate is exactly `x_u ∨ x_w`. -/
theorem pairGate_of_tight (M : MinCE S gates out) (u w : Fin n) (i : Fin m)
    (hi : S i = {u, w}) (ht : Tight S gates u) : ∃ k, IsPairGate gates k u w := by
  classical
  have C := M.ce
  obtain ⟨k, hk, -, hDC, hpair⟩ := pair_lowest S gates out C.h2 C.hev C.hg u w i hi
  refine ⟨k, hpair ?_⟩
  have hpos : 1 ≤ (DC u gates).card := Finset.card_pos.mpr ⟨k, hDC⟩
  have hb := M.deadBound u hpos
  have hsub := readers_sub_DC u gates C.hg
  have heq : Readers u gates = DC u gates := by
    apply Finset.eq_of_subset_of_card_le hsub
    unfold Tight baseOf degOf at ht
    omega
  rw [heq]; exact hDC

/-- Rule 'p' (PAIR-N2, G1.9 in counting form, without the `kL(u)` term): for every point `u` of
some set,  `nonpair(u) + p(u) ≤ #dead(x_u := 0) ≤ deg u - σ`, hence `nonpair(u) ≤ l(u) - σ`
(stated additively: `base + nonpair(u) ≤ s + l(u)`). -/
theorem rule_p (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i) :
    nonpair S gates u + pairDeg S u ≤ (DC u gates).card ∧
      baseOf S + (DC u gates).card ≤ gates.length + degOf S u ∧
      baseOf S + nonpair S gates u ≤ gates.length + lineDeg S u := by
  classical
  have C := M.ce
  have hc := pair_count S gates out C.h2 C.hS C.hev C.hg u
  have hd := deg_split S C.h2 u
  have hdeg : 1 ≤ degOf S u := by
    obtain ⟨i, hi⟩ := hu
    unfold degOf
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hpos : 1 ≤ (DC u gates).card := by
    by_cases hp : 1 ≤ pairDeg S u
    · omega
    · have := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u (by omega)
      omega
  have hb := M.deadBound u hpos
  unfold baseOf degOf
  unfold degOf at hd
  omega

/-- Every point of some set lies on at least `1 + σ` lines (sets of size `≥ 3`):
`base + 1 ≤ s + l(u)` ("count lines, not sets"). -/
theorem line_bound (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i) :
    baseOf S + 1 ≤ gates.length + lineDeg S u := by
  have C := M.ce
  have h := (M.rule_p u hu).2.2
  have hlt := C.hlt
  by_cases hl : 1 ≤ lineDeg S u
  · have := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u hl
    omega
  · unfold baseOf at h ⊢
    omega

/-- G1.9, tight case: if `u` is tight then the gates dead under `x_u := 0` are exactly the readers
of `x_u`, so every lowest gate `g_w` is a reader (a pair gate) and
`nonpair(u) + p(u) ≤ #readers(u)`. -/
theorem tight_readers (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (ht : Tight S gates u) :
    Readers u gates = DC u gates ∧
      nonpair S gates u + pairDeg S u ≤ (Readers u gates).card := by
  classical
  have C := M.ce
  obtain ⟨hc, hb, -⟩ := M.rule_p u hu
  have hsub := readers_sub_DC u gates C.hg
  have heq : Readers u gates = DC u gates := by
    apply Finset.eq_of_subset_of_card_le hsub
    unfold Tight at ht
    omega
  exact ⟨heq, by rw [heq]; exact hc⟩

end MinCE

end PEqualNP.Outside.L_meta_951_aux
