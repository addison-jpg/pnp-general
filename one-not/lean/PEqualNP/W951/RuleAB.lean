import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.RuleS
import PEqualNP.Kernel.W951Cube

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
