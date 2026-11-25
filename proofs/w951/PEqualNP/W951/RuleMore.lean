import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.RuleS
import PEqualNP.Kernel.W951Cube
import PEqualNP.W951.MinCEN3

section RuleAB

/-!
# Rule 'a' (p-tight pair lemma), frontier15_log.md §1 — and the multi-point restriction bound

* `MinCE.cubeBound` : for a partial assignment `(Z, ρ)` with at least one dead gate,
  `∑_{w ∈ I} (|S w \ Z| - 1) + #dead ≤ s` (`I` = sets with `|S w \ Z| ≥ 2` not set to `1`).
  `MinCE.zeroCubeBound` : for `x_Z := 0`, `base + #dead ≤ s + ∑_{t ∈ Z} deg t`
  ("dead(ρ) ≤ loss(ρ) - σ").  `DC_sub_cube` : gates dead under `x_a := 0` are dead on the cube.
* `PTight u` : `nonpair(u) = l(u) - σ`.  `MinCE.ptight_dc` : then every gate dead under `x_u := 0`
  that is not a reader of `x_u` is a lowest gate `g_w`, `w ∈ P(u)`; `MinCE.ptight_card`.
* (T1) `MinCE.ptight_fanout` : every later reader of a non-OR reader of a p-tight `u` is a `g_w`.
* (T2) `MinCE.ptight_single_or` : the reader of a p-tight single-reader point is an OR gate.
* `PTPair S gates v a b i r` : the hypotheses of Lemma A (`σ = 1`).  `MinCE.lemmaA` : (A0) and
  (A1): `g1 = x_a ∨ x_b` exists, is the only gate reading both `x_a` and `x_b`, its only later
  reader is `c = c_v`, `c` is an AND gate and no reader of `x_a`, `x_b`; `a`, `b` are not
  single-reader points.  Helpers `wreader_cases`, `two_reads`, `const_readerOn`.
NOT formalized here: (A2), (A3') of Lemma A, and rule 'b'.
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.Kernel (Cube proj deadLC)

/-- Gates dead under `x_a := 0` are dead under `x_Z := 0` for every `Z ∋ a`. -/
theorem DC_sub_cube {n : ℕ} (gates : List Gate) (Z : Finset (Fin n)) (O : Finset ℕ) (a : Fin n)
    (ha : a ∈ Z) : DC a gates ⊆ deadLC gates Z (fun _ => false) O := by
  classical
  intro k hk
  simp only [DC, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkl, hd⟩ := hk
  rcases hd with ⟨j, hj, h⟩ | h
  · exact Kernel.mem_deadLC_of_copy gates Z _ O k hkl j hj (fun x hx => h x (hx a ha))
  · exact Kernel.mem_deadLC_of_const gates Z _ O k hkl true (fun x hx => h x (hx a ha))

/-- `u` is p-tight: `nonpair(u) = l(u) - σ`, stated as `s + l(u) ≤ base + nonpair(u)` (the reverse
is rule 'p'). -/
def PTight {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (u : Fin n) : Prop :=
  gates.length + lineDeg S u ≤ baseOf S + nonpair S gates u

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- Multi-point N2/N3: restriction to the subcube `x = ρ on Z`. -/
theorem cubeBound (M : MinCE S gates out) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (hd : 1 ≤ (deadLC gates Z ρ (Finset.univ.image out)).card) :
    ∑ w ∈ Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card ∧ ∀ t ∈ S w, t ∈ Z → ρ t = false),
        ((S w \ Z).card - 1) + (deadLC gates Z ρ (Finset.univ.image out)).card ≤
      gates.length :=
  Kernel.restrictCube_bound S gates out M.ce.hS M.ce.hg M.ce.hU M.ce.hev
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) Z ρ hd

/-- Multi-point N2: `x_Z := 0` kills at most `∑_{t ∈ Z} deg t - σ` gates. -/
theorem zeroCubeBound (M : MinCE S gates out) (Z : Finset (Fin n))
    (hd : 1 ≤ (deadLC gates Z (fun _ => false) (Finset.univ.image out)).card) :
    baseOf S + (deadLC gates Z (fun _ => false) (Finset.univ.image out)).card ≤
      gates.length + ∑ t ∈ Z, degOf S t := by
  classical
  have h := M.cubeBound Z (fun _ => false) hd
  simp only [implies_true, and_true] at h
  set I := Finset.univ.filter (fun w : Fin m => 2 ≤ (S w \ Z).card) with hI
  have key : ∀ w, (S w).card - 1 ≤
      (if w ∈ I then (S w \ Z).card - 1 else 0) + (S w ∩ Z).card := by
    intro w
    have hc := Finset.card_sdiff_add_card_inter (S w) Z
    by_cases hw : w ∈ I
    · rw [if_pos hw]; omega
    · rw [if_neg hw]
      have : ¬ 2 ≤ (S w \ Z).card := fun h2 => hw (by simp [hI, h2])
      omega
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ (Finset.univ : Finset (Fin m))) => key w
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hsum
  have e3 : ∑ w : Fin m, (S w ∩ Z).card = ∑ t ∈ Z, degOf S t := by
    have e1 : ∀ w, (S w ∩ Z).card = ∑ t ∈ Z, if t ∈ S w then 1 else 0 := by
      intro w
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    have e2 : ∀ t, degOf S t = ∑ w : Fin m, if t ∈ S w then 1 else 0 := by
      intro t; unfold degOf; rw [Finset.card_filter]
    simp only [e1, e2]
    exact Finset.sum_comm
  unfold baseOf
  omega

open Classical in
/-- For a p-tight `u`: every gate dead under `x_u := 0` that is not a reader of `x_u` is a lowest
gate `g_w` restricting to `x_w`, `{u, w}` a pair-set. -/
theorem ptight_dc (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (ht : PTight S gates u) :
    baseOf S + (DC u gates).card = gates.length + degOf S u ∧
    ∀ k ∈ DC u gates, k ∉ Readers u gates →
      ∃ (w : Fin n) (i : Fin m), S i = {u, w} ∧ k < gates.length ∧
        (∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w) ∧
        ∀ k', k' < k → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w := by
  have C := M.ce
  obtain ⟨G, hGsub, hGc, -, -, hNG, -, -, hGspec⟩ := M.pkL_sets u
  set N := (Readers u gates).filter
    (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) with hN
  have hNc : N.card = nonpair S gates u := by unfold nonpair; rfl
  have hNsub : N ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (readers_sub_DC u gates C.hg)
  have hb := (M.rule_p u hu).2.1
  have hd := deg_split S C.h2 u
  have hle := Finset.card_le_card (Finset.union_subset hNsub hGsub)
  rw [Finset.card_union_of_disjoint hNG, hGc, hNc] at hle
  unfold PTight at ht
  have hEq : N ∪ G = DC u gates := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hNsub hGsub)
    rw [Finset.card_union_of_disjoint hNG, hGc, hNc]
    omega
  refine ⟨by omega, fun k hk hkR => ?_⟩
  rw [← hEq] at hk
  rcases Finset.mem_union.mp hk with h | h
  · exact absurd (Finset.mem_filter.mp h).1 hkR
  · exact hGspec k h

/-- (T1): every later reader of a non-OR reader `g` of a p-tight `u` is a lowest gate `g_w`,
`w ∈ P(u)` (and no reader of `x_u`). -/
theorem ptight_fanout (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (ht : PTight S gates u) (k : ℕ) (hk : k < gates.length) (hR : k ∈ Readers u gates)
    (hop : (gates[k]'hk).op ≠ GateOp.or) (k' : ℕ) (hkk : k < k')
    (hW : k' ∈ WReaders (n + k) gates) :
    ∃ (w : Fin n) (i : Fin m), S i = {u, w} ∧ k' < gates.length ∧
      (∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w) ∧
      ∀ k'', k'' < k' → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k'') = x w := by
  obtain ⟨b, hb⟩ := reader_const0 u gates M.ce.hg k hk hR hop
  exact (M.ptight_dc u hu ht).2 k' (wreaders_sub_DC u gates M.ce.hg k b hb hW)
    (M.fanout_not_reader u k hk hR hop k' hkk hW)

/-- (T2): the reader of a p-tight single-reader point is an OR gate. -/
theorem ptight_single_or (M : MinCE S gates out) (v : Fin n) (r : ℕ)
    (hR : Readers v gates = {r}) (ht : PTight S gates v) (hr : r < gates.length) :
    (gates[r]'hr).op = GateOp.or := by
  classical
  by_contra hop
  have C := M.ce
  have hrR : r ∈ Readers v gates := by rw [hR]; simp
  have hdeg := M.deg_two_of_reader v r hrR
  obtain ⟨w0, hw0⟩ : ∃ w, v ∈ S w := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega :
      0 < (Finset.univ.filter fun w : Fin m => v ∈ S w).card)
    exact ⟨w, by simpa using hw⟩
  have hnp1 : nonpair S gates v ≤ 1 := by
    unfold nonpair
    refine (Finset.card_filter_le _ _).trans ?_
    rw [hR]; simp
  obtain ⟨c, b, -, -, -, hnu, -⟩ := M.single_core3 v r hR
  unfold PTight at ht
  refine M.tight_nonOr_false v ⟨w0, hw0⟩ (by omega) r hr hrR ?_ hop
  rintro ⟨w, ⟨i, hi⟩, hk, hor, hin⟩
  have hvw : w ≠ v := by
    rintro rfl; have := C.h2 i; rw [hi] at this; simp at this
  refine hnu w hvw ?_
  rw [readers_eq_wreaders]
  refine (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inr hor, ?_⟩⟩
  rcases hin with h | h <;> rw [h] <;> simp

end MinCE

/-! ## Lemma A (p-tight pair lemma, `σ = 1`) -/

/-- The three shapes of an effective reader `k` of an earlier wire `p`. -/
theorem wreader_cases {n : ℕ} (gates : List Gate) (k : ℕ) (hk : k < gates.length) (p : ℕ)
    (hp : p < n + k) (hW : k ∈ WReaders p gates) :
    ((gates[k]'hk).op = GateOp.and ∧
      ∀ x : Fin n → Bool, val gates x (n + k) = true → val gates x p = true) ∨
    ((gates[k]'hk).op = GateOp.or ∧
      ∀ x : Fin n → Bool, val gates x p = true → val gates x (n + k) = true) ∨
    ((gates[k]'hk).op = GateOp.not ∧ ∀ x : Fin n → Bool, val gates x (n + k) = !val gates x p) := by
  obtain ⟨_, h⟩ := (mem_wreaders _ _ _).mp hW
  have hP : ∀ x : Fin n → Bool, val (gates.take k) x p = val gates x p := fun x =>
    val_take gates x k p (by omega) hp
  rcases h with ⟨hao | hao, hin⟩ | ⟨hn, rest, hin⟩
  · refine Or.inl ⟨hao, fun x hx => ?_⟩
    rw [val_gate gates x k hk, hao] at hx
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hx
    have := hx _ ⟨p, hin, rfl⟩
    rwa [hP] at this
  · refine Or.inr (Or.inl ⟨hao, fun x hx => ?_⟩)
    rw [val_gate gates x k hk, hao]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨_, ⟨p, hin, rfl⟩, by rw [hP]; exact hx⟩
  · refine Or.inr (Or.inr ⟨hn, fun x => ?_⟩)
    rw [val_gate gates x k hk, hn, hin]
    simp [GateOp.eval, hP]

/-- A gate reading two distinct earlier wires `p, q` effectively is `p ∧ q` or `p ∨ q`. -/
theorem two_reads {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (k : ℕ) (hk : k < gates.length) (p q : ℕ) (hpq : p ≠ q)
    (hp : p < n + k) (hq : q < n + k) (hWp : k ∈ WReaders p gates) (hWq : k ∈ WReaders q gates) :
    ((gates[k]'hk).inputs = [p, q] ∨ (gates[k]'hk).inputs = [q, p]) ∧
    (((gates[k]'hk).op = GateOp.and ∧
        ∀ x : Fin n → Bool, val gates x (n + k) = (val gates x p && val gates x q)) ∨
     ((gates[k]'hk).op = GateOp.or ∧
        ∀ x : Fin n → Bool, val gates x (n + k) = (val gates x p || val gates x q))) := by
  obtain ⟨_, h1⟩ := (mem_wreaders _ _ _).mp hWp
  obtain ⟨_, h2⟩ := (mem_wreaders _ _ _).mp hWq
  have hlen := (hg _ (List.getElem_mem hk)).2
  have hv := fun x : Fin n → Bool => val_gate gates x k hk
  have hP : ∀ (x : Fin n → Bool) (c : ℕ), c < n + k → val (gates.take k) x c = val gates x c :=
    fun x c hc => val_take gates x k c (by omega) hc
  generalize gates[k]'hk = g at h1 h2 hlen hv
  obtain ⟨op, ins⟩ := g
  simp only at h1 h2 hlen hv ⊢
  rcases h1 with ⟨hao, hin1⟩ | ⟨hn, rest, hin1⟩
  · rcases h2 with ⟨-, hin2⟩ | ⟨hn2, -⟩
    · match ins, hlen with
      | [], _ => simp at hin1
      | [a], _ =>
        simp only [List.mem_singleton] at hin1 hin2
        exact absurd (hin1.trans hin2.symm) hpq
      | [a, c], _ =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1 hin2
        have hcase : (a = p ∧ c = q) ∨ (a = q ∧ c = p) := by
          rcases hin1 with h | h <;> rcases hin2 with h' | h'
          · exact absurd (h.trans h'.symm) hpq
          · exact Or.inl ⟨h.symm, h'.symm⟩
          · exact Or.inr ⟨h'.symm, h.symm⟩
          · exact absurd (h.trans h'.symm) hpq
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hao with rfl | rfl
        · exact ⟨Or.inl rfl, Or.inl ⟨rfl, fun x => by
            simp [hv, GateOp.eval, hP x _ hp, hP x _ hq]⟩⟩
        · exact ⟨Or.inl rfl, Or.inr ⟨rfl, fun x => by
            simp [hv, GateOp.eval, hP x _ hp, hP x _ hq]⟩⟩
        · exact ⟨Or.inr rfl, Or.inl ⟨rfl, fun x => by
            simp [hv, GateOp.eval, hP x _ hp, hP x _ hq, Bool.and_comm]⟩⟩
        · exact ⟨Or.inr rfl, Or.inr ⟨rfl, fun x => by
            simp [hv, GateOp.eval, hP x _ hp, hP x _ hq, Bool.or_comm]⟩⟩
      | _ :: _ :: _ :: _, h => simp at h
    · rcases hao with h | h <;> rw [h] at hn2 <;> exact absurd hn2 (by simp)
  · rcases h2 with ⟨hao, -⟩ | ⟨-, rest2, hin2⟩
    · rcases hao with h | h <;> rw [h] at hn <;> exact absurd hn (by simp)
    · rw [hin1] at hin2
      simp only [List.cons.injEq] at hin2
      exact absurd hin2.1 hpq

/-- `const_reader` relative to a set `P` of inputs: an AND/OR gate reading a wire that is constant
on `P` is, on `P`, constant or a copy of an earlier wire. -/
theorem const_readerOn {n : ℕ} (P : (Fin n → Bool) → Prop) (gates : List Gate) (r : ℕ)
    (hr : r < gates.length)
    (hop : (gates[r]'hr).op = GateOp.and ∨ (gates[r]'hr).op = GateOp.or)
    (hlen : (gates[r]'hr).inputs.length ≤ 2) (p : ℕ) (hp : p ∈ (gates[r]'hr).inputs)
    (b : Bool) (hb : ∀ x : Fin n → Bool, P x → val (gates.take r) x p = b) :
    (∃ b' : Bool, ∀ x : Fin n → Bool, P x → val gates x (n + r) = b') ∨
    (∃ j, j < n + r ∧ ∀ x : Fin n → Bool, P x → val gates x (n + r) = val gates x j) := by
  have hC : ∀ c : ℕ, (∀ x : Fin n → Bool, P x → val gates x (n + r) = val (gates.take r) x c) →
      (∃ b' : Bool, ∀ x : Fin n → Bool, P x → val gates x (n + r) = b') ∨
      (∃ j, j < n + r ∧ ∀ x : Fin n → Bool, P x → val gates x (n + r) = val gates x j) := by
    intro c h
    by_cases hc : c < n + r
    · exact Or.inr ⟨c, hc, fun x hx => (h x hx).trans (val_take gates x r c (by omega) hc)⟩
    · exact Or.inl ⟨false, fun x hx => (h x hx).trans (val_take_ge _ _ _ _ (by omega))⟩
  have hv := fun x : Fin n → Bool => val_gate gates x r hr
  generalize gates[r]'hr = g at hop hlen hp hv
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hp hv
  match ins, hlen with
  | [], _ => simp at hp
  | [c], _ =>
    simp only [List.mem_singleton] at hp
    subst hp
    left
    refine ⟨b, fun x hx => ?_⟩
    rcases hop with rfl | rfl <;> simp [hv, GateOp.eval, hb x hx]
  | [c, d], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rcases hop with rfl | rfl <;> cases b
    · exact Or.inl ⟨false, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
    · exact hC d fun x hx => by simp [hv, GateOp.eval, hb x hx]
    · exact hC d fun x hx => by simp [hv, GateOp.eval, hb x hx]
    · exact Or.inl ⟨true, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
    · exact Or.inl ⟨false, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
    · exact hC c fun x hx => by simp [hv, GateOp.eval, hb x hx]
    · exact hC c fun x hx => by simp [hv, GateOp.eval, hb x hx]
    · exact Or.inl ⟨true, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
  | _ :: _ :: _ :: _, h => simp at h

/-- The hypotheses of Lemma A: `σ = 1`; `v` a p-tight single-reader point with reader `r`; `S i` a
set through `v` whose only points with a reader below `r` are `a` and `b`
(`T_S(v) = {a, b}`); `a`, `b` p-tight; `P(a) ∩ P(b) = ∅`. -/
structure PTPair {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (v a b : Fin n)
    (i : Fin m) (r : ℕ) : Prop where
  hσ : gates.length + 1 = baseOf S
  hR : Readers v gates = {r}
  hv : PTight S gates v
  hvi : v ∈ S i
  hai : a ∈ S i
  hbi : b ∈ S i
  hav : a ≠ v
  hbv : b ≠ v
  hab : a ≠ b
  hT : ∀ t ∈ S i, t ≠ a → t ≠ b → ∀ k ∈ Readers t gates, r ≤ k
  ha : PTight S gates a
  hb : PTight S gates b
  hP : ∀ w : Fin n, (∃ j, S j = {a, w}) → (∃ j, S j = {b, w}) → False

theorem PTPair.symm {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {v a b : Fin n}
    {i : Fin m} {r : ℕ} (H : PTPair S gates v a b i r) : PTPair S gates v b a i r :=
  ⟨H.hσ, H.hR, H.hv, H.hvi, H.hbi, H.hai, H.hbv, H.hav, H.hab.symm,
    fun t ht h1 h2 => H.hT t ht h2 h1, H.hb, H.ha, fun w h1 h2 => H.hP w h2 h1⟩

theorem pg_readers {n : ℕ} (gates : List Gate) (k : ℕ) (a b : Fin n)
    (h : IsPairGate gates k a b) : k ∈ Readers a gates ∧ k ∈ Readers b gates := by
  obtain ⟨hk, hor, hin⟩ := h
  constructor
  · rw [readers_eq_wreaders]
    refine (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inr hor, ?_⟩⟩
    rcases hin with h | h <;> rw [h] <;> simp
  · rw [readers_eq_wreaders]
    refine (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inr hor, ?_⟩⟩
    rcases hin with h | h <;> rw [h] <;> simp

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- **Lemma A, (A0) and (A1)** (`σ = 1`).  In the situation `PTPair`: a gate `g1 = x_a ∨ x_b`
exists; it is the only gate reading both `x_a` and `x_b` (so `x_a ∧ x_b` does not exist); its
ONLY later reader is the other input `c` of the reader `r = x_v ∨ c` of `v`; `c` is an AND gate
(`c = g1 ∧ y`) and no reader of `x_a` or `x_b`; and `a`, `b` are not single-reader points. -/
theorem lemmaA {v a b : Fin n} {i : Fin m} {r : ℕ} (M : MinCE S gates out)
    (H : PTPair S gates v a b i r) :
    ∃ (g1 c : ℕ), IsPairGate gates g1 a b ∧ n ≤ c ∧ c < n + r ∧ r ∈ WReaders c gates ∧
      (∀ x : Fin n → Bool, val gates x (n + r) = (x v || val gates x c)) ∧
      (∀ k', g1 < k' → k' ∈ WReaders (n + g1) gates → n + k' = c) ∧
      c - n ∈ WReaders (n + g1) gates ∧ g1 < c - n ∧
      (∀ hc : c - n < gates.length, (gates[c - n]'hc).op = GateOp.and) ∧
      c - n ∉ Readers a gates ∧ c - n ∉ Readers b gates ∧
      (∀ k ∈ Readers a gates, k ∈ Readers b gates → k = g1) ∧
      (¬ ∃ r', Readers a gates = {r'}) ∧ (¬ ∃ r', Readers b gates = {r'}) := by
  classical
  have C := M.ce
  have hE : ∀ (w t : Fin n), t ≠ w → (fun s : Fin n => decide (s = w)) t = false :=
    fun w t h => by simp [h]
  -- `S i` is a line, and two of its points are not pair-partners
  have h3 : 3 ≤ (S i).card := by
    have hsub : ({v, a, b} : Finset (Fin n)) ⊆ S i := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact H.hvi
      · exact H.hai
      · exact H.hbi
    have hc : ({v, a, b} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [H.hav.symm, H.hbv.symm]),
        Finset.card_pair H.hab]
    have := Finset.card_le_card hsub
    omega
  have noPair : ∀ x y : Fin n, x ∈ S i → y ∈ S i → x ≠ y → ¬ ∃ j, S j = {x, y} := by
    rintro x y hx hy hxy ⟨j, hj⟩
    have hne : j ≠ i := by
      rintro rfl
      rw [hj, Finset.card_pair hxy] at h3; omega
    have hsub : ({x, y} : Finset (Fin n)) ⊆ S j ∩ S i := by
      intro t ht
      rw [Finset.mem_inter]
      refine ⟨by rw [hj]; exact ht, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hx
      · exact hy
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hxy] at this
    have := C.hS j i hne
    omega
  have pairNe : ∀ (x w : Fin n) (j : Fin m), S j = {x, w} → w ≠ x := by
    intro x w j hj e; have := C.h2 j; rw [hj, e] at this; simp at this
  -- the reader of `v`
  obtain ⟨c, b0, hc1, hc2, hr, hnu, hWonly, hWc, hform0, hopb, hcore⟩ := M.single_core3 v r H.hR
  have hb0 : b0 = false := by
    have h1 := hopb hr
    rw [M.ptight_single_or v r H.hR H.hv hr] at h1
    cases b0
    · rfl
    · simp at h1
  subst hb0
  have hform : ∀ x : Fin n → Bool, val gates x (n + r) = (x v || val gates x c) := fun x => by
    simpa using hform0 x
  have hvA : ¬ ∃ k ∈ Readers v gates, k < r := by
    rintro ⟨k, hk, hlt⟩
    rw [H.hR] at hk
    have := Finset.mem_singleton.mp hk
    omega
  have hF1 : ∀ x : Fin n → Bool, x a = false → x b = false →
      val gates x c = false ∧ val gates x (n + r) = x v := by
    intro x hxa hxb
    refine hcore i H.hvi x fun t ht hex => ?_
    by_cases hta : t = a
    · rw [hta]; exact hxa
    · by_cases htb : t = b
      · rw [htb]; exact hxb
      · obtain ⟨k, hk, hlt⟩ := hex
        exact absurd hlt (by have := H.hT t ht hta htb k hk; omega)
  -- a second set through `v`
  have hrR : r ∈ Readers v gates := by rw [H.hR]; simp
  have hdeg := M.deg_two_of_reader v r hrR
  obtain ⟨i', hvi', hii'⟩ : ∃ i', v ∈ S i' ∧ i' ≠ i := by
    obtain ⟨w1, h1, w2, h2, hw12⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (Finset.univ.filter fun w : Fin m => v ∈ S w).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    by_cases hw1 : w1 = i
    · exact ⟨w2, h2, fun e => hw12 (hw1.trans e.symm)⟩
    · exact ⟨w1, h1, hw1⟩
  -- `c` vanishes on inputs supported on `S i \ v`
  have hF2 : ∀ x : Fin n → Bool, (∀ t, x t = true → t ∈ S i ∧ t ≠ v) → val gates x c = false := by
    intro x hx
    refine (hcore i' hvi' x fun t ht hex => ?_).1
    by_contra hxt
    have hxt' : x t = true := by cases h : x t <;> simp_all
    obtain ⟨hti, htv⟩ := hx t hxt'
    have hsub : ({t, v} : Finset (Fin n)) ⊆ S i' ∩ S i := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨ht, hti⟩
      · exact Finset.mem_inter.mpr ⟨hvi', H.hvi⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair htv] at this
    have := C.hS i' i hii'
    omega
  have hcl : c - n < gates.length := by omega
  have hcc : n + (c - n) = c := by omega
  -- facts generic in the order of `a, b`
  have gen : ∀ a' b' : Fin n, PTPair S gates v a' b' i r →
      r ∉ DC a' gates ∧ c - n ∉ DC a' gates ∧
      (∀ k, k ∈ Readers a' gates → k ∈ DC b' gates → k ∈ Readers b' gates) := by
    intro a' b' H'
    have hF1' : ∀ x : Fin n → Bool, x a' = false → x b' = false → val gates x c = false := by
      intro x h1 h2
      refine (hcore i H'.hvi x fun t ht hex => ?_).1
      by_cases hta : t = a'
      · rw [hta]; exact h1
      · by_cases htb : t = b'
        · rw [htb]; exact h2
        · obtain ⟨k, hk, hlt⟩ := hex
          exact absurd hlt (by have := H'.hT t ht hta htb k hk; omega)
    have dcA := (M.ptight_dc a' ⟨i, H'.hai⟩ H'.ha).2
    have notG : ∀ (w : Fin n) (j : Fin m), S j = {a', w} →
        (∀ x : Fin n → Bool, x a' = false → val gates x (n + r) = x w) → False := by
      intro w j hj hres
      have h1 := hres (fun t => decide (t = v)) (hE v a' H'.hav)
      rw [hform] at h1
      have hwv : w = v := by simpa using h1
      rw [hwv] at hj
      exact noPair a' v H'.hai H'.hvi H'.hav ⟨j, hj⟩
    refine ⟨fun hr' => ?_, fun hc' => ?_, fun k hkA hkB => ?_⟩
    · by_cases hRd : r ∈ Readers a' gates
      · exact hnu a' H'.hav hRd
      · obtain ⟨w, j, hj, -, hres, -⟩ := dcA r hr' hRd
        exact notG w j hj hres
    · by_cases hRd : c - n ∈ Readers a' gates
      · by_cases hor : (gates[c - n]'hcl).op = GateOp.or
        · rcases wreader_cases (n := n) gates (c - n) hcl (a' : ℕ) (by have := a'.2; omega)
            (by rw [← readers_eq_wreaders]; exact hRd) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
          · rw [hor] at h; exact absurd h (by simp)
          · have := h (fun t => decide (t = a')) (by rw [val_inp _ _ _ a'.2]; simp)
            rw [hcc, hF2 _ (fun t ht => by
              have : t = a' := by simpa using ht
              rw [this]; exact ⟨H'.hai, H'.hav⟩)] at this
            exact absurd this (by simp)
          · rw [hor] at h; exact absurd h (by simp)
        · obtain ⟨w, j, hj, -, hres, -⟩ := M.ptight_fanout a' ⟨i, H'.hai⟩ H'.ha (c - n) hcl hRd
            hor r (by omega) (by rw [hcc]; exact hWc)
          exact notG w j hj hres
      · obtain ⟨w, j, hj, -, hres, -⟩ := dcA _ hc' hRd
        have hwa : w ≠ a' := pairNe a' w j hj
        have hwb : w ≠ b' := by
          rintro rfl
          exact noPair a' w H'.hai H'.hbi H'.hab ⟨j, hj⟩
        have h1 := hres (fun t => decide (t = w)) (hE w a' hwa.symm)
        rw [hcc, hF1' _ (hE w a' hwa.symm) (hE w b' hwb.symm)] at h1
        simp at h1
    · by_contra hkRb
      obtain ⟨w, j, hj, hkl, hres, -⟩ := (M.ptight_dc b' ⟨i, H'.hbi⟩ H'.hb).2 k hkB hkRb
      have hwb : w ≠ b' := pairNe b' w j hj
      have hwa : w ≠ a' := by
        rintro rfl
        exact noPair b' w H'.hbi H'.hai H'.hab.symm ⟨j, hj⟩
      rcases wreader_cases (n := n) gates k hkl (a' : ℕ) (by have := a'.2; omega)
          (by rw [← readers_eq_wreaders]; exact hkA) with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · have := h (fun t => decide (t = w)) (by rw [hres _ (hE w b' hwb.symm)]; simp)
        rw [val_inp _ _ _ a'.2] at this
        exact hwa (by simpa using this : a' = w).symm
      · have := h (fun t => decide (t = a')) (by rw [val_inp _ _ _ a'.2]; simp)
        rw [hres (fun t => decide (t = a')) (hE a' b' H'.hab.symm)] at this
        exact hwa (by simpa using this)
      · have := h (fun _ => false)
        rw [hres _ rfl, val_inp _ _ _ a'.2] at this
        simp at this
  obtain ⟨hrA, hcA, crossA⟩ := gen a b H
  obtain ⟨hrB, hcB, crossB⟩ := gen b a H.symm
  have dcA := (M.ptight_dc a ⟨i, H.hai⟩ H.ha)
  have dcB := (M.ptight_dc b ⟨i, H.hbi⟩ H.hb)
  -- two lowest gates `g_w^a`, `g_w'^b` cannot coincide
  have twoG : ∀ (k : ℕ) (w w' : Fin n) (j j' : Fin m), S j = {a, w} → S j' = {b, w'} →
      (∀ x : Fin n → Bool, x a = false → val gates x (n + k) = x w) →
      (∀ x : Fin n → Bool, x b = false → val gates x (n + k) = x w') → False := by
    intro k w w' j j' hj hj' hresA hresB
    have hwa : w ≠ a := pairNe a w j hj
    have hwb : w ≠ b := by
      rintro rfl
      exact noPair a w H.hai H.hbi H.hab ⟨j, hj⟩
    have h1 := hresA (fun t => decide (t = w)) (hE w a hwa.symm)
    have h2 := hresB (fun t => decide (t = w)) (hE w b hwb.symm)
    rw [h1] at h2
    have hww : w' = w := by simpa using h2
    rw [hww] at hj'
    exact H.hP w ⟨j, hj⟩ ⟨j', hj'⟩
  have pg_of_both : ∀ k, k ∈ Readers a gates → k ∈ Readers b gates → IsPairGate gates k a b := by
    intro k hRa hRb
    obtain ⟨hkl, -⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hRa)
    obtain ⟨hins, hval⟩ := two_reads (n := n) gates C.hg k hkl (a : ℕ) (b : ℕ)
      (fun e => H.hab (Fin.ext e)) (by have := a.2; omega) (by have := b.2; omega)
      (by rw [← readers_eq_wreaders]; exact hRa) (by rw [← readers_eq_wreaders]; exact hRb)
    rcases hval with ⟨hand, -⟩ | ⟨hor, -⟩
    · exfalso
      have hop : (gates[k]'hkl).op ≠ GateOp.or := by rw [hand]; simp
      obtain ⟨k', hkk, hW⟩ := M.has_later_reader k hkl (M.reader_not_out a k hkl hRa hop)
      obtain ⟨w, j, hj, -, hresA, -⟩ :=
        M.ptight_fanout a ⟨i, H.hai⟩ H.ha k hkl hRa hop k' hkk hW
      obtain ⟨w', j', hj', -, hresB, -⟩ :=
        M.ptight_fanout b ⟨i, H.hbi⟩ H.hb k hkl hRb hop k' hkk hW
      exact twoG k' w w' j j' hj hj' hresA hresB
    · exact ⟨hkl, hor, hins⟩
  have hpg : ∀ k ∈ DC a gates ∩ DC b gates, IsPairGate gates k a b := by
    intro k hk
    obtain ⟨hkA, hkB⟩ := Finset.mem_inter.mp hk
    have hRa : k ∈ Readers a gates := by
      by_contra hna
      by_cases hRb : k ∈ Readers b gates
      · exact hna (crossB k hRb hkA)
      · obtain ⟨w, j, hj, -, hresA, -⟩ := dcA.2 k hkA hna
        obtain ⟨w', j', hj', -, hresB, -⟩ := dcB.2 k hkB hRb
        exact twoG k w w' j j' hj hj' hresA hresB
    exact pg_of_both k hRa (crossA k hRa hkB)
  -- the count under `x_a = x_b = 0`
  set D := deadLC gates ({a, b} : Finset (Fin n)) (fun _ => false) (Finset.univ.image out) with hD
  have hrD : r ∈ D :=
    Kernel.mem_deadLC_of_copy gates _ _ _ r hr (v : ℕ) (by have := v.2; omega) fun x hx => by
      rw [(hF1 x (hx a (by simp)) (hx b (by simp))).2, val_inp _ _ _ v.2]
  have hcD : c - n ∈ D :=
    Kernel.mem_deadLC_of_const gates _ _ _ (c - n) hcl false fun x hx => by
      rw [hcc]; exact (hF1 x (hx a (by simp)) (hx b (by simp))).1
  have hAD : DC a gates ⊆ D := DC_sub_cube gates _ _ a (by simp)
  have hBD : DC b gates ⊆ D := DC_sub_cube gates _ _ b (by simp)
  have hbound : baseOf S + D.card ≤ gates.length + (degOf S a + degOf S b) := by
    have h := M.zeroCubeBound ({a, b} : Finset (Fin n)) (Finset.card_pos.mpr ⟨r, hrD⟩)
    rw [Finset.sum_pair H.hab] at h
    exact h
  set X := DC a gates ∪ DC b gates with hX
  set Y := insert (c - n) (insert r X) with hY
  have hrX : r ∉ X := fun h => by
    rcases Finset.mem_union.mp h with h | h
    · exact hrA h
    · exact hrB h
  have hcX : c - n ∉ insert r X := fun h => by
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · rcases Finset.mem_union.mp h with h | h
      · exact hcA h
      · exact hcB h
  have hYsub : Y ⊆ D := by
    intro k hk
    rcases Finset.mem_insert.mp hk with h | h
    · rw [h]; exact hcD
    · rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hrD
      · rcases Finset.mem_union.mp h with h | h
        · exact hAD h
        · exact hBD h
  have hYc : Y.card = X.card + 2 := by
    rw [hY, Finset.card_insert_of_notMem hcX, Finset.card_insert_of_notMem hrX]
  have hui : X.card + (DC a gates ∩ DC b gates).card = (DC a gates).card + (DC b gates).card :=
    Finset.card_union_add_card_inter (DC a gates) (DC b gates)
  have hYD := Finset.card_le_card hYsub
  have hσ := H.hσ
  have hint1 : 1 ≤ (DC a gates ∩ DC b gates).card := by
    have := dcA.1; have := dcB.1
    omega
  obtain ⟨g1, hg1⟩ := Finset.card_pos.mp hint1
  have hg1p := hpg g1 hg1
  have uniq : ∀ k, IsPairGate gates k a b → k = g1 := by
    intro k hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hgl : g1 < gates.length := let ⟨h, _⟩ := hg1p; h
      exact M.clean g1 (n + k) hgl (by omega) fun x => by
        rw [val_pairGate gates g1 a b hg1p, val_pairGate gates k a b hk]
    · have hkl : k < gates.length := let ⟨h, _⟩ := hk; h
      exact M.clean k (n + g1) hkl (by omega) fun x => by
        rw [val_pairGate gates g1 a b hg1p, val_pairGate gates k a b hk]
  have hint_le : (DC a gates ∩ DC b gates).card ≤ 1 :=
    Finset.card_le_one.mpr fun k hk k' hk' => (uniq k (hpg k hk)).trans (uniq k' (hpg k' hk')).symm
  have hYeq : Y = D := by
    apply Finset.eq_of_subset_of_card_le hYsub
    have := dcA.1; have := dcB.1
    omega
  have hg1l : g1 < gates.length := let ⟨h, _⟩ := hg1p; h
  have hg1val : ∀ x : Fin n → Bool, val gates x (n + g1) = (x a || x b) :=
    val_pairGate gates g1 a b hg1p
  have hea : val gates (fun t => decide (t = a)) c = false :=
    hF2 _ fun t ht => by
      have : t = a := by simpa using ht
      rw [this]; exact ⟨H.hai, H.hav⟩
  -- a later reader of `g1` lying in `DC a'` is impossible
  have gen2 : ∀ a' b' : Fin n, PTPair S gates v a' b' i r →
      (∀ x : Fin n → Bool, val gates x (n + g1) = (x a' || x b')) →
      ∀ k', g1 < k' → k' ∈ WReaders (n + g1) gates → k' ∈ DC a' gates → False := by
    intro a' b' H' hval' k' hlt hW hk'
    obtain ⟨hk'l, -⟩ := (mem_wreaders _ _ _).mp hW
    by_cases hRd : k' ∈ Readers a' gates
    · obtain ⟨-, hv2⟩ := two_reads (n := n) gates C.hg k' hk'l (a' : ℕ) (n + g1)
        (by have := a'.2; omega) (by have := a'.2; omega) (by omega)
        (by rw [← readers_eq_wreaders]; exact hRd) hW
      rcases hv2 with ⟨-, h⟩ | ⟨-, h⟩
      · exact M.clean k' (a' : ℕ) hk'l (by have := a'.2; omega) fun x => by
          have hxa : val gates x (a' : ℕ) = x a' := val_inp _ _ _ a'.2
          rw [h x, hval', hxa]; cases x a' <;> cases x b' <;> rfl
      · exact M.clean k' (n + g1) hk'l (by omega) fun x => by
          have hxa : val gates x (a' : ℕ) = x a' := val_inp _ _ _ a'.2
          rw [h x, hval', hxa]; cases x a' <;> cases x b' <;> rfl
    · obtain ⟨w, j, hj, -, hres, -⟩ := (M.ptight_dc a' ⟨i, H'.hai⟩ H'.ha).2 k' hk' hRd
      have hwa : w ≠ a' := pairNe a' w j hj
      have hwb : w ≠ b' := by
        rintro rfl
        exact noPair a' w H'.hai H'.hbi H'.hab ⟨j, hj⟩
      rcases wreader_cases (n := n) gates k' hk'l (n + g1) (by omega) hW with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · have := h (fun t => decide (t = w)) (by rw [hres _ (hE w a' hwa.symm)]; simp)
        rw [hval'] at this
        simp [hwa.symm, hwb.symm] at this
      · have := h (fun t => decide (t = b')) (by rw [hval']; simp)
        rw [hres (fun t => decide (t = b')) (hE b' a' H'.hab)] at this
        exact hwb (by simpa using this)
      · have := h (fun _ => false)
        rw [hres _ rfl, hval'] at this
        simp at this
  have only : ∀ k', g1 < k' → k' ∈ WReaders (n + g1) gates → k' = c - n := by
    intro k' hlt hW
    obtain ⟨hk'l, hd⟩ := (mem_wreaders _ _ _).mp hW
    have hk'D : k' ∈ D := by
      rcases wreader_cases (n := n) gates k' hk'l (n + g1) (by omega) hW with ⟨-, h⟩ | ⟨hor, -⟩ | ⟨-, h⟩
      · refine Kernel.mem_deadLC_of_const gates _ _ _ k' hk'l false fun x hx => ?_
        cases hv : val gates x (n + k')
        · rfl
        · have := h x hv
          rw [hg1val, hx a (by simp), hx b (by simp)] at this
          exact absurd this (by simp)
      · have hin : n + g1 ∈ (gates[k']'hk'l).inputs := by
          rcases hd with ⟨-, h'⟩ | ⟨hn, -⟩
          · exact h'
          · rw [hor] at hn; exact absurd hn (by simp)
        rcases const_readerOn (Cube ({a, b} : Finset (Fin n)) (fun _ => false)) gates k' hk'l
            (Or.inr hor) (C.hg _ (List.getElem_mem hk'l)).2 (n + g1) hin false (fun x hx => by
              rw [val_take gates x k' (n + g1) (by omega) (by omega), hg1val, hx a (by simp),
                hx b (by simp)]; rfl) with ⟨b', hb'⟩ | ⟨j, hj, hcopy⟩
        · exact Kernel.mem_deadLC_of_const gates _ _ _ k' hk'l b' hb'
        · exact Kernel.mem_deadLC_of_copy gates _ _ _ k' hk'l j hj hcopy
      · refine Kernel.mem_deadLC_of_const gates _ _ _ k' hk'l true fun x hx => ?_
        rw [h x, hg1val, hx a (by simp), hx b (by simp)]; rfl
    rw [← hYeq] at hk'D
    rcases Finset.mem_insert.mp hk'D with h | h
    · exact h
    · exfalso
      rcases Finset.mem_insert.mp h with h | h
      · rw [h] at hW
        rcases hWonly _ hW with e | e
        · have := v.2; omega
        · have h1 := hg1val (fun t => decide (t = a))
          rw [e, hea] at h1
          simp at h1
      · rcases Finset.mem_union.mp h with h | h
        · exact gen2 a b H hg1val k' hlt hW h
        · exact gen2 b a H.symm (fun x => by rw [hg1val, Bool.or_comm]) k' hlt hW h
  -- `g1` is not an output, so it has a later reader, which is `c`
  have hout : ∀ w, out w ≠ n + g1 := by
    intro w e
    have hv := fun x => C.hev w x
    simp only [e, hg1val] at hv
    have hmem : ∀ t : Fin n, (t = a ∨ t = b) → t ∈ S w := by
      intro t ht
      have h1 := hv (fun s => decide (s = t))
      have : ((fun s : Fin n => decide (s = t)) a || (fun s : Fin n => decide (s = t)) b) = true := by
        rcases ht with rfl | rfl <;> simp
      rw [this] at h1
      have h2 : ∃ u ∈ S w, (fun s : Fin n => decide (s = t)) u = true := by simpa using h1.symm
      obtain ⟨u, hu, hut⟩ := h2
      have : u = t := by simpa using hut
      rw [← this]; exact hu
    have hwi : w = i := by
      by_contra hne
      have hsub : ({a, b} : Finset (Fin n)) ⊆ S w ∩ S i := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hmem _ (Or.inl rfl), H.hai⟩
        · exact Finset.mem_inter.mpr ⟨hmem _ (Or.inr rfl), H.hbi⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair H.hab] at this
      have := C.hS w i hne
      omega
    have h1 := hv (fun s => decide (s = v))
    have ha' : decide (a = v) = false := by simp [H.hav]
    have hb' : decide (b = v) = false := by simp [H.hbv]
    rw [ha', hb', hwi] at h1
    have h2 : decide (∃ u ∈ S i, (fun s : Fin n => decide (s = v)) u = true) = true := by
      simp only [decide_eq_true_eq]; exact ⟨v, H.hvi, by simp⟩
    rw [h2] at h1
    simp at h1
  obtain ⟨k', hkk, hW⟩ := M.has_later_reader g1 hg1l hout
  have hk'c := only k' hkk hW
  rw [hk'c] at hkk hW
  have hopc : (gates[c - n]'hcl).op = GateOp.and := by
    rcases wreader_cases (n := n) gates (c - n) hcl (n + g1) (by omega) hW with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      have := h (fun t => decide (t = a)) (by rw [hg1val]; simp)
      rw [hcc, hea] at this
      exact absurd this (by simp)
    · exfalso
      have := h (fun _ => false)
      rw [hcc, (hF1 _ rfl rfl).1, hg1val] at this
      simp at this
  obtain ⟨hg1a, hg1b⟩ := pg_readers gates g1 a b hg1p
  refine ⟨g1, c, hg1p, hc1, hc2, hWc, hform, fun k' hlt hW' => ?_, hW, hkk, fun _ => hopc,
    fun h => hcA (readers_sub_DC a gates C.hg h), fun h => hcB (readers_sub_DC b gates C.hg h),
    fun k hka hkb => uniq k (pg_of_both k hka hkb), ?_, ?_⟩
  · rw [only k' hlt hW', hcc]
  · rintro ⟨r', hr'⟩
    have hr1 : g1 = r' := by
      have := hg1a; rw [hr'] at this; exact Finset.mem_singleton.mp this
    obtain ⟨-, -, -, -, -, hnu', -⟩ := M.single_core a r' hr'
    exact hnu' b H.hab.symm (hr1 ▸ hg1b)
  · rintro ⟨r', hr'⟩
    have hr1 : g1 = r' := by
      have := hg1b; rw [hr'] at this; exact Finset.mem_singleton.mp this
    obtain ⟨-, -, -, -, -, hnu', -⟩ := M.single_core b r' hr'
    exact hnu' a H.hab (hr1 ▸ hg1a)

end MinCE

end PEqualNP.Outside.L_meta_951_aux

end RuleAB

section RuleN

/-!
# Rule 'n' (frontier15_log.md §§6, 7, 9): Lemma N-O and the equality-case surcharge (E)

* `MinCE.lemma_NO` (LEMMA N-O): every point `w` of some set has a direct reader that is neither a
  pair gate `x_w ∨ x_w'` (`{w, w'}` a set) nor an output gate.
* `MinCE.surcharge_E` ((E), set form): the two-sided restriction `x_w := 1` / `x_w := 0`.
  Setting: `{t, w}` a pair-set with pair gate `p`, a gate `h = x_t ∨ c` or `h = x_t ∧ c` whose other
  input `c` is a gate that is constant on `Q = {x_w = 1}` (`0` for OR, `1` for AND) and below which
  `x_w` is read only by `p`.  If the gates dead under `x_w := 1` are only `c`, `h`, readers of `x_w`
  and outputs of sets through `w`, and (OR-type only) `w` is p-tight, there is a contradiction.
* `MinCE.surcharge_E_count` ((E), counting form): the same with the death count
  `2 + deg w + #R = loss(w) - σ` in place of the exact description of the dead gates (`R` = reader
  deaths, `R = {h_w}` on paper).
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- A gate's value depends only on the wires it reads effectively. -/
theorem eval_congr_wreaders (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (k : ℕ) (hk : k < gates.length) (f f' : ℕ → Bool)
    (hkey : ∀ a, k ∈ WReaders a gates → f a = f' a) :
    (gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f) =
      (gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f') := by
  rcases (hg _ (List.getElem_mem hk)).1 with hop' | hop' | hop'
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact hkey a ((mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inl hop', ha⟩⟩)
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact hkey a ((mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inr hop', ha⟩⟩)
  · rw [hop']
    rcases hin' : (gates[k]'hk).inputs with _ | ⟨a, rest⟩
    · rfl
    · have := hkey a ((mem_wreaders _ _ _).mpr ⟨hk, Or.inr ⟨hop', rest, hin'⟩⟩)
      simp [GateOp.eval, this]

/-- Prefix form of `val_congr_off2`: inputs that agree off `x_u` agree at every gate `k ≤ K`,
`k ≠ h`, if every such gate agrees outright or reads neither `x_u` nor (when above `h`) gate `h`. -/
theorem val_congr_prefix2 {n : ℕ} (u : Fin n) (h K : ℕ) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (x y : Fin n → Bool)
    (hxy : ∀ v, v ≠ u → x v = y v) (hK : K < gates.length)
    (H : ∀ k, k ≤ K → k ≠ h → val gates x (n + k) = val gates y (n + k) ∨
      (k ∉ Readers u gates ∧ (h < k → k ∉ WReaders (n + h) gates))) :
    ∀ k, k ≤ K → k ≠ h → val gates x (n + k) = val gates y (n + k) := by
  intro k hk hkh
  have hT : (gates.take (K + 1)).length = K + 1 := by simp; omega
  have key := val_congr_off2 u h (gates.take (K + 1)) x y hxy (fun k' hk' hk'h => by
    have hk'K : k' ≤ K := by rw [hT] at hk'; omega
    have hk'l : k' < gates.length := by omega
    rcases H k' hk'K hk'h with e | ⟨h1, h2⟩
    · left
      rw [val_take gates x (K + 1) (n + k') (by omega) (by omega),
        val_take gates y (K + 1) (n + k') (by omega) (by omega)]
      exact e
    · right
      intro f f' hff
      simp only [List.getElem_take]
      apply eval_congr_wreaders gates hg k' hk'l
      intro a ha
      apply hff a
      · rintro rfl; exact h1 (by rw [readers_eq_wreaders]; exact ha)
      · intro hlt e; subst e; exact h2 hlt ha) (n + k) (by have := u.2; omega) (by omega)
  rwa [val_take gates x (K + 1) (n + k) (by omega) (by omega),
    val_take gates y (K + 1) (n + k) (by omega) (by omega)] at key

/-- A gate with at most two inputs, one of them `q`: its AND / OR value is `F q ∘ F a` for another
input `a` (`a = q` for a single input). -/
theorem two_input_form (ins : List ℕ) (hlen : ins.length ≤ 2) (q : ℕ) (hq : q ∈ ins) :
    ∃ a, a ∈ ins ∧ (∀ F : ℕ → Bool, GateOp.and.eval (ins.map F) = (F q && F a)) ∧
      (∀ F : ℕ → Bool, GateOp.or.eval (ins.map F) = (F q || F a)) := by
  match ins, hlen, hq with
  | [], _, hq => simp at hq
  | [a], _, hq =>
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨q, by simp, by simp [GateOp.eval], by simp [GateOp.eval]⟩
  | [a, c], _, hq =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨c, by simp, by simp [GateOp.eval], by simp [GateOp.eval]⟩
    · exact ⟨a, by simp, by simp [GateOp.eval, Bool.and_comm], by simp [GateOp.eval, Bool.or_comm]⟩
  | _ :: _ :: _ :: _, h, _ => simp at h

/-- A gate with at most two inputs, among them `q₁ ≠ q₂`: its AND / OR value. -/
theorem two_mem_form (ins : List ℕ) (hlen : ins.length ≤ 2) (q₁ q₂ : ℕ) (hne : q₁ ≠ q₂)
    (h₁ : q₁ ∈ ins) (h₂ : q₂ ∈ ins) :
    (∀ F : ℕ → Bool, GateOp.and.eval (ins.map F) = (F q₁ && F q₂)) ∧
      (∀ F : ℕ → Bool, GateOp.or.eval (ins.map F) = (F q₁ || F q₂)) := by
  match ins, hlen, h₁, h₂ with
  | [], _, h₁, _ => simp at h₁
  | [a], _, h₁, h₂ =>
    simp only [List.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  | [a, c], _, h₁, h₂ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨by simp [GateOp.eval], by simp [GateOp.eval]⟩
    · exact ⟨by simp [GateOp.eval, Bool.and_comm], by simp [GateOp.eval, Bool.or_comm]⟩
    · exact absurd rfl hne
  | _ :: _ :: _ :: _, h, _, _ => simp at h

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- In a minimal counterexample every effective reader of a gate is a later gate. -/
theorem wreader_gt (M : MinCE S gates out) (k k' : ℕ) (hW : k' ∈ WReaders (n + k) gates) :
    k < k' := by
  by_contra hle
  push Not at hle
  have C := M.ce
  obtain ⟨hk', h⟩ := (mem_wreaders _ _ _).mp hW
  have hbt : ∀ x : Fin n → Bool, val (gates.take k') x (n + k) = false := fun x =>
    val_take_ge gates x k' (n + k) (by omega)
  rcases h with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
  · rcases const_reader gates k' hk' hop (C.hg _ (List.getElem_mem hk')).2 _ hin false hbt with
      ⟨b', hc⟩ | ⟨j, hj, hcopy⟩
    · exact M.no_const k' hk' b' hc
    · exact M.clean k' j hk' hj hcopy
  · exact M.no_const k' hk' true fun x => by
      rw [val_gate gates x k' hk', hop, hin]
      simp [GateOp.eval, hbt x]

/-- LEMMA N-O (frontier15_log §6): in a minimal counterexample every point `w` lying in some set
has a direct reader that is neither a pair gate `x_w ∨ x_w'` of a pair-set `{w, w'}` nor an
output gate. -/
theorem lemma_NO (M : MinCE S gates out) (w : Fin n) (hw : ∃ i, w ∈ S i) :
    ∃ k ∈ Readers w gates,
      (¬ ∃ w' : Fin n, (∃ i, S i = {w, w'}) ∧ IsPairGate gates k w w') ∧
      ∀ i, out i ≠ n + k := by
  classical
  by_contra hcon
  push Not at hcon
  have C := M.ce
  set N := (Readers w gates).filter
    (fun k => ¬ ∃ w' : Fin n, (∃ i, S i = {w, w'}) ∧ IsPairGate gates k w w') with hN
  have hNc : N.card = nonpair S gates w := by unfold nonpair; rfl
  have hrp := (M.rule_p w hw).2.2
  have hlt : gates.length < baseOf S := C.hlt
  set Lines := Finset.univ.filter fun i : Fin m => w ∈ S i ∧ 3 ≤ (S i).card with hLines
  have hLc : Lines.card = lineDeg S w := rfl
  set O := Lines.filter fun i => ∃ k ∈ N, out i = n + k with hO
  have hOc : O.card ≤ N.card := by
    apply Finset.card_le_card_of_injOn (fun i => out i - n)
    · intro i hi
      obtain ⟨k, hk, hik⟩ := (Finset.mem_filter.mp hi).2
      simp only [hik, Nat.add_sub_cancel_left]; exact hk
    · intro i hi i' hi' hii
      obtain ⟨k, hk, hik⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨k', hk', hik'⟩ := (Finset.mem_filter.mp hi').2
      simp only [hik, hik', Nat.add_sub_cancel_left] at hii
      exact out_inj3 S C.h2 C.hS gates out C.hev i i' (by rw [hik, hik', hii])
  obtain ⟨iL, hiLn, hiO⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (by omega : O.card < Lines.card)
  obtain ⟨hiL1, hiL3⟩ := (Finset.mem_filter.mp hiLn).2
  have two : ∀ (t : Fin n) (i i' : Fin m), t ≠ w → w ∈ S i → t ∈ S i → w ∈ S i' → t ∈ S i' →
      i = i' := by
    intro t i i' htw h1 h2 h3 h4
    by_contra hne
    have hsub : ({w, t} : Finset (Fin n)) ⊆ S i ∩ S i' := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨h1, h3⟩
      · exact Finset.mem_inter.mpr ⟨h2, h4⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm htw)] at this
    have := C.hS i i' hne
    omega
  set z : Fin n → Bool := fun t => decide (t ≠ w ∧ ((∃ i, S i = {w, t}) ∨
    ∃ i, w ∈ S i ∧ t ∈ S i ∧ ∃ k ∈ N, out i = n + k)) with hzdef
  have hzL : ∀ t ∈ S iL, z t = false := by
    intro t ht
    simp only [hzdef, decide_eq_false_iff_not]
    rintro ⟨htw, ⟨i, hi⟩ | ⟨i, hwi, hti, hk⟩⟩
    · have e := two t i iL htw (by rw [hi]; simp) (by rw [hi]; simp) hiL1 ht
      subst e
      rw [hi, Finset.card_pair (Ne.symm htw)] at hiL3; omega
    · have e := two t i iL htw hwi hti hiL1 ht
      subst e
      exact hiO (Finset.mem_filter.mpr ⟨hiLn, hk⟩)
  set y := Function.update z w true with hydef
  have hzy : ∀ v, v ≠ w → z v = y v := fun v hv => by rw [hydef, Function.update_of_ne hv]
  have hR : ∀ k ∈ Readers w gates,
      val gates z (n + k) = true ∧ val gates y (n + k) = true := by
    intro k hk
    by_cases hp : ∃ w' : Fin n, (∃ i, S i = {w, w'}) ∧ IsPairGate gates k w w'
    · obtain ⟨w', ⟨i, hi⟩, hpg⟩ := hp
      have hww : w' ≠ w := by
        intro e; have := C.h2 i; rw [hi, e] at this; simp at this
      have hz : z w' = true := by
        simp only [hzdef, decide_eq_true_eq]; exact ⟨hww, Or.inl ⟨i, hi⟩⟩
      rw [val_pairGate gates k w w' hpg, val_pairGate gates k w w' hpg, ← hzy w' hww, hz]
      simp
    · obtain ⟨i, hi⟩ := hcon k hk (fun w' hi hpg => hp ⟨w', hi, hpg⟩)
      have hkN : k ∈ N := Finset.mem_filter.mpr ⟨hk, hp⟩
      obtain ⟨hkl, hkd⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hk)
      have hor : (gates[k]'hkl).op = GateOp.or := by
        by_contra hop
        exact M.reader_not_out w k hkl hk hop i hi
      have hin : (w : ℕ) ∈ (gates[k]'hkl).inputs := by
        rcases hkd with ⟨-, h'⟩ | ⟨hn, -⟩
        · exact h'
        · rw [hor] at hn; exact absurd hn (by simp)
      have h1 : ∀ x : Fin n → Bool, x w = true → val gates x (n + k) = true := by
        intro x hx
        rw [val_gate gates x k hkl, hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
        exact ⟨_, ⟨w, hin, rfl⟩, by rw [val_inp _ _ _ w.2]; exact hx⟩
      have hwi : w ∈ S i := by
        have := h1 (fun v => decide (v = w)) (by simp)
        rw [← hi, C.hev] at this
        simp only [decide_eq_true_eq] at this
        obtain ⟨v, hv, hvw⟩ := this
        rwa [hvw] at hv
      obtain ⟨t, ht, htw⟩ := Finset.exists_mem_ne (C.h2 i) w
      have hz : z t = true := by
        simp only [hzdef, decide_eq_true_eq]
        exact ⟨htw, Or.inr ⟨i, hwi, ht, k, hkN, hi⟩⟩
      rw [← hi, C.hev, C.hev]
      simp only [decide_eq_true_eq]
      exact ⟨⟨t, ht, hz⟩, ⟨t, ht, by rw [← hzy t htw]; exact hz⟩⟩
  have key := val_congr_of_insens (w : ℕ) gates z y
    (fun j hj => hzy j (fun e => hj (by rw [e])))
    (fun k hk => by
      by_cases hkR : k ∈ Readers w gates
      · left; rw [(hR k hkR).1, (hR k hkR).2]
      · exact Or.inr (insens_of_not_reader w gates k hk hkR (C.hg _ (List.getElem_mem hk)).1))
    (out iL) (out_ne_inp S gates out C.h2 C.hev iL w)
  have e1 : decide (∃ v ∈ S iL, z v = true) = false := by
    simp only [decide_eq_false_iff_not]
    rintro ⟨v, hv, hx⟩
    rw [hzL v hv] at hx; exact absurd hx (by simp)
  have e2 : decide (∃ v ∈ S iL, y v = true) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨w, hiL1, by rw [hydef, Function.update_self]⟩
  rw [C.hev, C.hev, e1, e2] at key
  exact absurd key (by simp)

/-! ## The equality case (E) -/

section E

variable (M : MinCE S gates out) (t w : Fin n) (j : Fin m) (hj : S j = {t, w}) (p kc h : ℕ)
  (hp : IsPairGate gates p t w) (hkc : kc < h) (hh : h < gates.length)
  (hhin : (gates[h]'hh).inputs = [(t : ℕ), n + kc] ∨ (gates[h]'hh).inputs = [n + kc, (t : ℕ)])
  (hhop : ((gates[h]'hh).op = GateOp.or ∧
        ∀ x : Fin n → Bool, x w = true → val gates x (n + kc) = false) ∨
      ((gates[h]'hh).op = GateOp.and ∧
        ∀ x : Fin n → Bool, x w = true → val gates x (n + kc) = true))
  (hcone : ∀ k, k ≤ kc → k ∈ Readers w gates → k = p)

include M hj hp hkc hhin hhop hcone in
/-- Basic facts of the (E) setting: `h = x_t ∘ c`, `c ≠ p`, `h` does not read `x_w`, an output of
a set through `t, w` is `p`, and no gate `≤ c` other than `p` is an output of a set through `w`. -/
theorem E_facts :
    t ≠ w ∧
    ((gates[h]'hh).op = GateOp.or →
      ∀ x : Fin n → Bool, val gates x (n + h) = (x t || val gates x (n + kc))) ∧
    ((gates[h]'hh).op = GateOp.and →
      ∀ x : Fin n → Bool, val gates x (n + h) = (x t && val gates x (n + kc))) ∧
    kc ≠ p ∧ h ∉ Readers w gates ∧
    (∀ (r : ℕ) (i : Fin m), w ∈ S i → t ∈ S i → out i = n + r → r = p) ∧
    (∀ ka, ka ≤ kc → ∀ i : Fin m, w ∈ S i → out i = n + ka → ka = p) := by
  classical
  have C := M.ce
  have htw : t ≠ w := by
    intro e; have := C.h2 j; rw [hj, e] at this; simp at this
  have hpv := val_pairGate gates p t w hp
  have hpl : p < gates.length := by obtain ⟨hpl, -⟩ := hp; exact hpl
  have hcv : ∀ x : Fin n → Bool, val (gates.take h) x (n + kc) = val gates x (n + kc) :=
    fun x => val_take gates x h (n + kc) (by omega) (by omega)
  have htv : ∀ x : Fin n → Bool, val (gates.take h) x (t : ℕ) = x t :=
    fun x => val_inp _ _ _ t.2
  have hhor : (gates[h]'hh).op = GateOp.or →
      ∀ x : Fin n → Bool, val gates x (n + h) = (x t || val gates x (n + kc)) := by
    intro hop x
    rw [val_gate gates x h hh, hop]
    rcases hhin with e | e <;> rw [e] <;> simp [GateOp.eval, hcv, htv, Bool.or_comm]
  have hhand : (gates[h]'hh).op = GateOp.and →
      ∀ x : Fin n → Bool, val gates x (n + h) = (x t && val gates x (n + kc)) := by
    intro hop x
    rw [val_gate gates x h hh, hop]
    rcases hhin with e | e <;> rw [e] <;> simp [GateOp.eval, hcv, htv, Bool.and_comm]
  have hkcp : kc ≠ p := by
    rintro rfl
    rcases hhop with ⟨hop, -⟩ | ⟨hop, -⟩
    · exact M.clean h (n + kc) hh (by omega) fun x => by
        rw [hhor hop x, hpv x]; cases x t <;> cases x w <;> rfl
    · exact M.clean h t hh (by have := t.2; omega) fun x => by
        rw [hhand hop x, hpv x, val_inp _ _ _ t.2]; cases x t <;> cases x w <;> rfl
  have hhnr : h ∉ Readers w gates := by
    intro hR
    obtain ⟨_, hd'⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hR)
    have hwt : (w : ℕ) ≠ t := fun e => htw (Fin.ext e).symm
    have := w.2
    rcases hd' with ⟨-, hin⟩ | ⟨-, rest, hin⟩
    · rcases hhin with e | e <;> rw [e] at hin <;> simp at hin <;> omega
    · rcases hhin with e | e <;> rw [e] at hin <;> simp at hin <;> omega
  have hfin : ∀ (r : ℕ) (i : Fin m), w ∈ S i → t ∈ S i → out i = n + r → r = p := by
    intro r i hwi hti ho
    have hij : i = j := by
      by_contra hne
      have hsub : ({t, w} : Finset (Fin n)) ⊆ S i ∩ S j := by
        intro a ha
        rw [Finset.mem_inter, hj]
        refine ⟨?_, ha⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hti
        · exact hwi
      have := Finset.card_le_card hsub
      rw [Finset.card_pair htw] at this
      have := C.hS i j hne
      omega
    have hr : ∀ x : Fin n → Bool, val gates x (n + r) = val gates x (n + p) := fun x => by
      rw [← ho, C.hev, hij, hj, hpv]
      cases hxt : x t <;> cases hxw : x w <;> simp [hxt, hxw]
    have hrl : r < gates.length := by
      by_contra hge
      have := hr (fun _ => true)
      rw [val_ge _ _ _ (by omega), hpv] at this
      simp at this
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact M.clean p (n + r) hpl (by omega) fun x => (hr x).symm
    · exact M.clean r (n + p) hrl (by omega) hr
  refine ⟨htw, hhor, hhand, hkcp, hhnr, hfin, ?_⟩
  intro ka hka i hwi ho
  apply hfin ka i hwi _ ho
  set x : Fin n → Bool := fun v => decide (v = t) with hx
  set y := Function.update x w true with hy
  have hxy : ∀ v, v ≠ w → x v = y v := fun v hv => by rw [hy, Function.update_of_ne hv]
  have hxt : x t = true := by simp [hx]
  have key := val_congr_prefix2 w (ka + 1) ka gates C.hg x y hxy (by omega) (fun k hk _ => by
    by_cases hkp : k = p
    · left
      rw [hkp, hpv, hpv, ← hxy t htw, hxt]; simp
    · exact Or.inr ⟨fun hR => hkp (hcone k (by omega) hR), fun hlt => by omega⟩)
    ka le_rfl (by omega)
  rw [← ho, C.hev, C.hev] at key
  have e2 : decide (∃ v ∈ S i, y v = true) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨w, hwi, by rw [hy, Function.update_self]⟩
  rw [e2] at key
  simp only [decide_eq_true_eq] at key
  obtain ⟨v, hv, hvt⟩ := key
  simp only [hx, decide_eq_true_eq] at hvt
  rwa [hvt] at hv

include M hj hp hkc hhin hhop hcone in
/-- (E), EQUALITY CASE of the refined bottom lemma (frontier15_log §6, holds verbatim with the
pseudo pair-gates of §7), set form.  `{t, w}` is a pair-set with pair gate `p = x_t ∨ x_w`;
`h = x_t ∨ c` or `h = x_t ∧ c` where `c` is a gate, constant on `Q = {x_w = 1}` (`0` for OR, `1`
for AND), and no gate `≤ c` other than `p` reads `x_w`.  `htight`: `w` is p-tight
(`nonpair(w) = l(w) - σ`; used only for `h = x_t ∨ c`).  `heq` (the equality `dead = loss - σ`):
the gates dead under `x_w := 1` are only `c`, `h`, readers of `x_w` and outputs of sets through
`w`.  Contradiction, by the two-sided restriction `x_w := 1` / `x_w := 0`. -/
theorem surcharge_E
    (htight : (gates[h]'hh).op = GateOp.or →
      gates.length + lineDeg S w ≤ baseOf S + nonpair S gates w)
    (heq : ∀ k ∈ DC1 w gates, k = kc ∨ k = h ∨ k ∈ Readers w gates ∨
      ∃ i, w ∈ S i ∧ out i = n + k) : False := by
  classical
  have C := M.ce
  obtain ⟨htw, hhor, hhand, hkcp, hhnr, hfin, hF2⟩ :=
    E_facts M t w j hj p kc h hp hkc hh hhin hhop hcone
  have hpv := val_pairGate gates p t w hp
  have hkcl : kc < gates.length := by omega
  have hcQ : ∃ b : Bool, ∀ x : Fin n → Bool, x w = true → val gates x (n + kc) = b := by
    rcases hhop with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact ⟨false, hc⟩
    · exact ⟨true, hc⟩
  -- every reader of `p` is `c`
  have hRp : ∀ r ∈ WReaders (n + p) gates, r = kc := by
    intro r hr
    have hpr := M.wreader_gt p r hr
    obtain ⟨hrl, hrd⟩ := (mem_wreaders _ _ _).mp hr
    have hpx : ∀ x : Fin n → Bool, val (gates.take r) x (n + p) = (x t || x w) := fun x => by
      rw [val_take gates x r (n + p) (by omega) (by omega), hpv]
    have hpt : ∀ x : Fin n → Bool, x w = true → val (gates.take r) x (n + p) = true :=
      fun x hx => by rw [hpx, hx]; simp
    have hlen := (C.hg _ (List.getElem_mem hrl)).2
    have hdead : r ∈ DC1 w gates := by
      simp only [DC1, DCq, Finset.mem_filter, Finset.mem_range]
      refine ⟨hrl, ?_⟩
      rcases hrd with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
      · exact deadQ_of_andor w true gates r hrl hop hlen _ hin true hpt
      · exact deadQ_of_not w true gates r hrl hop _ rest hin true hpt
    rcases heq r hdead with e | e | e | ⟨i, hwi, ho⟩
    · exact e
    · exfalso
      subst e
      have := t.2
      rcases hrd with ⟨-, hin⟩ | ⟨-, rest, hin⟩
      · rcases hhin with e | e <;> rw [e] at hin <;> simp at hin <;> omega
      · rcases hhin with e | e <;> rw [e] at hin <;> simp at hin <;> omega
    · exfalso
      obtain ⟨_, hwd⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact e)
      have hwp : (w : ℕ) ≠ n + p := by have := w.2; omega
      have hwx : ∀ x : Fin n → Bool, val (gates.take r) x (w : ℕ) = x w :=
        fun x => val_inp _ _ _ w.2
      rcases hrd with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
      · have hinw : (w : ℕ) ∈ (gates[r]'hrl).inputs := by
          rcases hwd with ⟨-, h'⟩ | ⟨hn, -⟩
          · exact h'
          · rcases hop with hop | hop <;> rw [hop] at hn <;> exact absurd hn (by simp)
        obtain ⟨hA, hO⟩ := two_mem_form _ hlen _ _ hwp hinw hin
        rcases hop with hop | hop
        · exact M.clean r w hrl (by have := w.2; omega) fun x => by
            rw [val_gate gates x r hrl, hop, hA, hwx, hpx, val_inp _ _ _ w.2]
            cases x t <;> cases x w <;> rfl
        · exact M.clean r (n + p) hrl (by omega) fun x => by
            rw [val_gate gates x r hrl, hop, hO, hwx, hpx, hpv]
            cases x t <;> cases x w <;> rfl
      · rcases hwd with ⟨hao, -⟩ | ⟨-, rest', hin'⟩
        · rcases hao with hao | hao <;> rw [hao] at hop <;> exact absurd hop (by simp)
        · rw [hin] at hin'; simp at hin'; omega
    · exfalso
      have hrp : r ≠ p := by omega
      apply hrp
      apply hfin r i hwi _ ho
      rcases hrd with ⟨hop | hop, hin⟩ | ⟨hop, rest, hin⟩
      · obtain ⟨v, hv, hvw⟩ := Finset.exists_mem_ne (C.h2 i) w
        have h1 := C.hev i (fun u => decide (u = v))
        have e1 : decide (∃ u ∈ S i, (fun u : Fin n => decide (u = v)) u = true) = true := by
          simp only [decide_eq_true_eq]; exact ⟨v, hv, rfl⟩
        rw [e1, ho, val_gate gates _ r hrl, hop] at h1
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h1
        have h2 := h1 _ ⟨n + p, hin, rfl⟩
        rw [hpx] at h2
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
        rcases h2 with h2 | h2
        · rw [h2]; exact hv
        · exact absurd h2.symm hvw
      · have h1 := C.hev i (fun u => decide (u = t))
        have e1 : val gates (fun u => decide (u = t)) (n + r) = true := by
          rw [val_gate gates _ r hrl, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          exact ⟨_, ⟨n + p, hin, rfl⟩, by rw [hpx]; simp⟩
        rw [ho, e1] at h1
        have h2 := h1.symm
        simp only [decide_eq_true_eq] at h2
        obtain ⟨v, hv, hvt⟩ := h2
        rwa [hvt] at hv
      · have h1 := C.hev i (fun _ => false)
        rw [ho, val_gate gates _ r hrl, hop, hin] at h1
        simp [GateOp.eval, hpx] at h1
  -- `c` reads `p`
  have hkcR : kc ∈ WReaders (n + p) gates := by
    by_contra hnot
    obtain ⟨b, hb⟩ := hcQ
    apply M.no_const kc hkcl b
    intro x
    cases hx : x w
    · have key := val_congr_prefix2 w p kc gates C.hg x (Function.update x w true)
        (fun v hv => by rw [Function.update_of_ne hv]) hkcl
        (fun k hk hkp => Or.inr ⟨fun hR => hkp (hcone k hk hR),
          fun _ hW => hnot (hRp k hW ▸ hW)⟩) kc le_rfl hkcp
      rw [key]
      exact hb _ (Function.update_self _ _ _)
    · exact hb x hx
  have hpkc := M.wreader_gt p kc hkcR
  have hpx : ∀ x : Fin n → Bool, val (gates.take kc) x (n + p) = (x t || x w) := fun x => by
    rw [val_take gates x kc (n + p) (by omega) (by omega), hpv]
  obtain ⟨_, hkd⟩ := (mem_wreaders _ _ _).mp hkcR
  rcases hkd with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
  · obtain ⟨a, hamem, hA, hO⟩ :=
      two_input_form _ (C.hg _ (List.getElem_mem hkcl)).2 (n + p) hin
    rcases hop with hop | hop
    · -- `c = p ∧ y`
      have hkv : ∀ x : Fin n → Bool,
          val gates x (n + kc) = ((x t || x w) && val (gates.take kc) x a) := fun x => by
        rw [val_gate gates x kc hkcl, hop, hA, hpx]
      obtain ⟨b, hb⟩ := hcQ
      have haQ : ∀ x : Fin n → Bool, x w = true → val (gates.take kc) x a = b := fun x hx => by
        have := hb x hx
        rw [hkv, hx] at this
        simpa using this
      by_cases han : a < n
      · by_cases haw : a = w
        · apply hkcp
          apply hcone kc le_rfl
          rw [readers_eq_wreaders]
          exact (mem_wreaders _ _ _).mpr ⟨hkcl, Or.inl ⟨Or.inl hop, haw ▸ hamem⟩⟩
        · have h1 := haQ (fun _ => true) rfl
          have h2 := haQ (fun v => decide (v = w)) (by simp)
          rw [val_inp _ _ _ han] at h1 h2
          have h3 : decide ((⟨a, han⟩ : Fin n) = w) = false := by
            simp only [decide_eq_false_iff_not]
            intro e; exact haw (by rw [← e])
          rw [h3] at h2
          rw [← h2] at h1
          exact absurd h1 (by simp)
      · by_cases hak : a < n + kc
        · have hka : ∀ x : Fin n → Bool, val gates x (n + (a - n)) = val (gates.take kc) x a :=
            fun x => by
              rw [show n + (a - n) = a by omega]
              exact (val_take gates x kc a (by omega) hak).symm
          have hdead : a - n ∈ DC1 w gates := by
            simp only [DC1, DCq, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, deadQ_of_const w true gates (a - n) b fun x hx => by
              rw [hka]; exact haQ x hx⟩
          have hkap : a - n = p := by
            rcases heq _ hdead with e | e | e | ⟨i, hwi, ho⟩
            · omega
            · omega
            · exact hcone _ (by omega) e
            · exact hF2 _ (by omega) i hwi ho
          exact M.clean kc (n + p) hkcl (by omega) fun x => by
            rw [hkv, ← hka, hkap, hpv]; simp
        · exact M.no_const kc hkcl false fun x => by
            rw [hkv, val_take_ge _ _ _ _ (by omega)]; simp
    · -- `c = p ∨ y`
      have hkv : ∀ x : Fin n → Bool,
          val gates x (n + kc) = ((x t || x w) || val (gates.take kc) x a) := fun x => by
        rw [val_gate gates x kc hkcl, hop, hO, hpx]
      rcases hhop with ⟨ho, hc⟩ | ⟨ho, hc⟩
      · have := hc (fun _ => true) rfl
        rw [hkv] at this
        simp at this
      · exact M.clean h t hh (by have := t.2; omega) fun x => by
          rw [hhand ho x, hkv, val_inp _ _ _ t.2]; cases x t <;> simp
  · -- `c = ¬p`
    have hkv : ∀ x : Fin n → Bool, val gates x (n + kc) = !(x t || x w) := fun x => by
      rw [val_gate gates x kc hkcl, hop, hin]
      simp [GateOp.eval, hpx]
    rcases hhop with ⟨ho, hc⟩ | ⟨ho, hc⟩
    · -- `h = x_t ∨ ¬x_w` is constant `1` on `{x_w = 0}`: one death too many for the p-tight `w`
      have hDT : h ∈ DC w gates := by
        simp only [DC, Finset.mem_filter, Finset.mem_range]
        exact ⟨hh, Or.inr fun x hx => by rw [hhor ho x, hkv, hx]; cases x t <;> rfl⟩
      have hu : ∃ i, w ∈ S i := ⟨j, by rw [hj]; simp⟩
      obtain ⟨G, hGsub, hGc, -, -, hNG, -, -, hGspec⟩ := M.pkL_sets w
      set N := (Readers w gates).filter
        (fun k => ¬ ∃ w' : Fin n, (∃ i, S i = {w, w'}) ∧ IsPairGate gates k w w') with hN
      have hNc : N.card = nonpair S gates w := by unfold nonpair; rfl
      have hNsub : N ⊆ DC w gates :=
        (Finset.filter_subset _ _).trans (readers_sub_DC w gates C.hg)
      have hdb := (M.rule_p w hu).2.1
      have hd := deg_split S C.h2 w
      have ht := htight ho
      have hDCeq : N ∪ G = DC w gates := by
        apply Finset.eq_of_subset_of_card_le (Finset.union_subset hNsub hGsub)
        rw [Finset.card_union_of_disjoint hNG, hGc, hNc]
        omega
      rw [← hDCeq] at hDT
      rcases Finset.mem_union.mp hDT with hN' | hG'
      · exact hhnr (Finset.mem_filter.mp hN').1
      · obtain ⟨w', i, -, -, hres, -⟩ := hGspec h hG'
        have h0 := hres (fun _ => false) rfl
        rw [hhor ho, hkv] at h0
        simp at h0
    · have := hc (fun _ => true) rfl
      rw [hkv] at this
      simp at this

include M hj hp hkc hhin hhop hcone in
/-- (E), counting form: the equality `dead = loss(w) - σ` as a number.  `R` is a set of readers
of `x_w` that die under `x_w := 1` and are not outputs of sets through `w` (on paper `R = {h_w}`);
the counted deaths are `c`, `h`, the `deg w` outputs through `w` and `R`.  If
`2 + deg w + #R ≥ loss(w) - σ`, i.e. `s ≤ ∑_{S ∌ w} (|S| - 1) + deg w + 2 + #R`, contradiction. -/
theorem surcharge_E_count
    (htight : (gates[h]'hh).op = GateOp.or →
      gates.length + lineDeg S w ≤ baseOf S + nonpair S gates w)
    (R : Finset ℕ) (hRr : R ⊆ Readers w gates) (hRd : R ⊆ DC1 w gates)
    (hRo : ∀ r ∈ R, ∀ i, w ∈ S i → out i ≠ n + r)
    (hcount : gates.length ≤
      ∑ i ∈ Finset.univ.filter (fun i => w ∉ S i), ((S i).card - 1) + degOf S w + 2 + R.card) :
    False := by
  classical
  have C := M.ce
  obtain ⟨htw, hhor, hhand, hkcp, hhnr, hfin, hF2⟩ :=
    E_facts M t w j hj p kc h hp hkc hh hhin hhop hcone
  have hkcl : kc < gates.length := by omega
  have hOn : ∀ i, n ≤ out i := by
    intro i
    by_contra hlt
    exact out_ne_inp S gates out C.h2 C.hev i ⟨out i, by omega⟩ rfl
  have hOl : ∀ i, out i < n + gates.length := by
    intro i
    by_contra hge
    exact M.out_not_const i false fun x => val_ge _ _ _ (by omega)
  set Outs := (Finset.univ.filter fun i : Fin m => w ∈ S i).image (fun i => out i - n) with hOuts
  have hOmem : ∀ k, k ∈ Outs ↔ ∃ i, w ∈ S i ∧ out i = n + k := by
    intro k
    simp only [hOuts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by have := hOn i; omega⟩
    · rintro ⟨i, hi, ho⟩; exact ⟨i, hi, by omega⟩
  have hOc : Outs.card = degOf S w := by
    unfold degOf
    apply Finset.card_image_of_injOn
    intro i _ i' _ hii
    exact out_inj3 S C.h2 C.hS gates out C.hev i i'
      (by have := hOn i; have := hOn i'; simp only at hii; omega)
  have hOd : Outs ⊆ DC1 w gates := by
    intro k hk
    obtain ⟨i, hwi, ho⟩ := (hOmem k).mp hk
    simp only [DC1, DCq, Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := hOl i; omega, deadQ_of_const w true gates k true fun x hx => ?_⟩
    rw [← ho, C.hev]
    simp only [decide_eq_true_eq]
    exact ⟨w, hwi, hx⟩
  have hkcD : kc ∈ DC1 w gates := by
    simp only [DC1, DCq, Finset.mem_filter, Finset.mem_range]
    refine ⟨hkcl, ?_⟩
    rcases hhop with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact deadQ_of_const w true gates kc false hc
    · exact deadQ_of_const w true gates kc true hc
  have hhQ : ∀ x : Fin n → Bool, x w = true → val gates x (n + h) = x t := by
    intro x hx
    rcases hhop with ⟨ho, hc⟩ | ⟨ho, hc⟩
    · rw [hhor ho, hc x hx]; simp
    · rw [hhand ho, hc x hx]; simp
  have hhD : h ∈ DC1 w gates := by
    simp only [DC1, DCq, Finset.mem_filter, Finset.mem_range]
    exact ⟨hh, Or.inl ⟨t, by have := t.2; omega, fun x hx => by
      rw [hhQ x hx, val_inp _ _ _ t.2]⟩⟩
  have hkcO : kc ∉ Outs := fun hk => by
    obtain ⟨i, hwi, ho⟩ := (hOmem kc).mp hk
    exact hkcp (hF2 kc le_rfl i hwi ho)
  have hhO : h ∉ Outs := fun hk => by
    obtain ⟨i, hwi, ho⟩ := (hOmem h).mp hk
    have h1 := hhQ (fun v => decide (v = w)) (by simp)
    rw [← ho, C.hev] at h1
    have e1 : decide (∃ v ∈ S i, (fun v : Fin n => decide (v = w)) v = true) = true := by
      simp only [decide_eq_true_eq]; exact ⟨w, hwi, rfl⟩
    rw [e1] at h1
    have := h1.symm
    simp only [decide_eq_true_eq] at this
    exact htw this
  have hkcR : kc ∉ R := fun hk => hkcp (hcone kc le_rfl (hRr hk))
  have hhR : h ∉ R := fun hk => hhnr (hRr hk)
  have hOR : Disjoint Outs R := by
    rw [Finset.disjoint_left]
    intro k hk hkR
    obtain ⟨i, hwi, ho⟩ := (hOmem k).mp hk
    exact hRo k hkR i hwi ho
  set D := insert kc (insert h (Outs ∪ R)) with hD
  have hDc : D.card = degOf S w + 2 + R.card := by
    rw [hD, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_union_of_disjoint hOR, hOc]
    · omega
    · simp [hhO, hhR]
    · simp only [Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨by omega, hkcO, hkcR⟩
  have hDsub : D ⊆ DC1 w gates := by
    intro k hk
    simp only [hD, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | rfl | hk | hk
    · exact hkcD
    · exact hhD
    · exact hOd hk
    · exact hRd hk
  have hlb := M.liveBound1 w (Finset.card_pos.mpr ⟨kc, hkcD⟩)
  have hDeq : D = DC1 w gates := Finset.eq_of_subset_of_card_le hDsub (by omega)
  refine surcharge_E M t w j hj p kc h hp hkc hh hhin hhop hcone htight fun k hk => ?_
  rw [← hDeq] at hk
  simp only [hD, Finset.mem_insert, Finset.mem_union] at hk
  rcases hk with rfl | rfl | hk | hk
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr ((hOmem k).mp hk)))
  · exact Or.inr (Or.inr (Or.inl (hRr hk)))

end E

end MinCE

end PEqualNP.Outside.L_meta_951_aux

end RuleN
