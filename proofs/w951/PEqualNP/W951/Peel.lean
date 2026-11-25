import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PairLemma

/-!
# G1.5 (AND/NOT-reader lemma), G1.3 (peeling cascade), G1.6 (capacity) for a minimal counterexample

`WReaders p gates` = the gates reading wire `p` effectively (`Readers v = WReaders v`).

* `wreaders_sub_DC` : if gate `k` is constant on `{x_u = 0}`, every reader of gate `k` is dead there.
* `MinCE.no_const` : no gate of a minimal counterexample is constant.
* `MinCE.has_later_reader` : every gate that is not an output has a later effective reader.
* `MinCE.and_reader_dead` (G1.5) : if a reader `g` (gate `k`) of `x_u` is not an OR gate (so it is
  `x_u ∧ c`, or the NOT gate reading `x_u`), then the later readers `F` of `g` are nonempty, dead
  under `x_u := 0`, and none of them reads `x_u`; so `#readers(u) + #F ≤ #DC(u) ≤ deg u - σ`.
* `MinCE.tight_or` : a tight point has only OR readers (in particular it is not read by the NOT).
* G1.3: `val_congr_below` (gates below position `ρ` depend only on variables with a reader below
  `ρ`), `MinCE.single_core` (AL: the reader `r` of a single-reader point `v` is `x_v ∘ c`, `c` an
  earlier gate), `MinCE.peel_meets` ((i): every set through `v` has a point with a reader below
  `r`), `MinCE.peel_dead` ((ii): if `u` is the only such point of `S i`, then `x_u := 0` kills `r`
  and `c`, and `r` is not a reader of `x_u`).  The order `v_1, v_2, …` is not formalized: "`t` has
  a reader below `r`" replaces "`t ∈ A_j`" (it implies `t ∈ A_j`, so the hypotheses here are
  weaker and the conclusion (i) stronger).
* G1.6: `MinCE.capacity` (`#readers(u) + #Users(u) ≤ #DC(u) ≤ deg u - σ`), and
  `MinCE.rule_p_kL` (rule 'p' with the `kL` term: `nonpair(u) + kL(u) ≤ l(u) - σ`).
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

open Classical in
/-- Gates that read wire `p` effectively: AND/OR with `p` among the inputs, or NOT with first
input `p`. -/
noncomputable def WReaders (p : ℕ) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k => ∃ hk : k < gates.length,
    (((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧ p ∈ (gates[k]'hk).inputs) ∨
    ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = p :: rest)

theorem readers_eq_wreaders {n : ℕ} (v : Fin n) (gates : List Gate) :
    Readers v gates = WReaders (v : ℕ) gates := rfl

theorem mem_wreaders (p : ℕ) (gates : List Gate) (k : ℕ) :
    k ∈ WReaders p gates ↔ ∃ hk : k < gates.length,
      (((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧
        p ∈ (gates[k]'hk).inputs) ∨
      ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = p :: rest) := by
  classical
  simp only [WReaders, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun ⟨hk, h⟩ => ⟨hk, hk, h⟩⟩

/-- A gate that does not read wire `p` effectively is insensitive to it. -/
theorem insens_of_not_wreader (p : ℕ) (gates : List Gate) (k : ℕ)
    (hk : k < gates.length) (h : k ∉ WReaders p gates)
    (hgk : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or ∨
      (gates[k]'hk).op = GateOp.not) : Insens p (gates[k]'hk) := by
  classical
  have h' : ¬ ((((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧
      p ∈ (gates[k]'hk).inputs) ∨
      ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = p :: rest)) := by
    intro hh
    exact h ((mem_wreaders p gates k).mpr ⟨hk, hh⟩)
  push Not at h'
  intro f f' hff
  rcases hgk with hop | hop | hop
  · have hvn : p ∉ (gates[k]'hk).inputs := fun hm => h'.1 (Or.inl hop) hm
    congr 1
    exact List.map_congr_left fun a ha => hff a (fun e => hvn (e ▸ ha))
  · have hvn : p ∉ (gates[k]'hk).inputs := fun hm => h'.1 (Or.inr hop) hm
    congr 1
    exact List.map_congr_left fun a ha => hff a (fun e => hvn (e ▸ ha))
  · rw [hop]
    rcases hin : (gates[k]'hk).inputs with _ | ⟨a, rest⟩
    · rfl
    · have hav : a ≠ p := by
        rintro rfl
        exact h'.2 hop rest hin
      simp [GateOp.eval, hff a hav]

/-- If gate `k` is constant on `{x_u = 0}`, every effective reader of gate `k` is dead there. -/
theorem wreaders_sub_DC {n : ℕ} (u : Fin n) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (k : ℕ) (b : Bool)
    (hc : ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = b) :
    WReaders (n + k) gates ⊆ DC u gates := by
  classical
  intro k' hk'
  obtain ⟨hk1, h⟩ := (mem_wreaders _ _ _).mp hk'
  have hb : ∀ x : Fin n → Bool, x u = false →
      val (gates.take k') x (n + k) = (if k < k' then b else false) := by
    intro x hx
    by_cases hlt : k < k'
    · rw [if_pos hlt, val_take gates x k' (n + k) (by omega) (by omega)]; exact hc x hx
    · rw [if_neg hlt]; exact val_take_ge _ _ _ _ (by omega)
  have hd : DCp u gates k' ∨ DTr u gates k' := by
    rcases h with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
    · exact dead_of_andor u gates k' hk1 hop (hg _ (List.getElem_mem hk1)).2 _ hin _ hb
    · exact dead_of_not u gates k' hk1 hop _ rest hin _ hb
  simp only [DC, Finset.mem_filter, Finset.mem_range]
  exact ⟨hk1, hd⟩

/-- A reader of `x_u` that is not an OR gate is `≤ x_u` (AND) or `= ¬x_u` (NOT). -/
theorem reader_const {n : ℕ} (u : Fin n) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (k : ℕ) (hk : k < gates.length) (hR : k ∈ Readers u gates)
    (hop : (gates[k]'hk).op ≠ GateOp.or) :
    ((gates[k]'hk).op = GateOp.and ∧
      ∀ x : Fin n → Bool, val gates x (n + k) = true → x u = true) ∨
    ((gates[k]'hk).op = GateOp.not ∧ ∀ x : Fin n → Bool, val gates x (n + k) = !x u) := by
  classical
  rw [readers_eq_wreaders] at hR
  obtain ⟨_, h⟩ := (mem_wreaders _ _ _).mp hR
  rcases h with ⟨hao, hin⟩ | ⟨hn, rest, hin⟩
  · have ha : (gates[k]'hk).op = GateOp.and := hao.resolve_right hop
    refine Or.inl ⟨ha, fun x hx => ?_⟩
    rw [val_gate gates x k hk, ha] at hx
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hx
    have := hx _ ⟨u, hin, rfl⟩
    rwa [val_inp _ _ _ u.2] at this
  · refine Or.inr ⟨hn, fun x => ?_⟩
    rw [val_gate gates x k hk, hn, hin]
    simp [GateOp.eval, val_inp _ _ _ u.2]

/-- A reader of `x_u` that is not an OR gate is constant on `{x_u = 0}`. -/
theorem reader_const0 {n : ℕ} (u : Fin n) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (k : ℕ) (hk : k < gates.length) (hR : k ∈ Readers u gates)
    (hop : (gates[k]'hk).op ≠ GateOp.or) :
    ∃ b : Bool, ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = b := by
  rcases reader_const u gates hg k hk hR hop with ⟨-, h⟩ | ⟨-, h⟩
  · refine ⟨false, fun x hx => ?_⟩
    cases hv : val gates x (n + k)
    · rfl
    · rw [h x hv] at hx; exact absurd hx (by simp)
  · exact ⟨true, fun x hx => by rw [h x, hx]; rfl⟩

/-- An AND/OR gate `r` reading a constant earlier wire `p` is constant or a copy of an earlier
wire. -/
theorem const_reader {n : ℕ} (gates : List Gate) (r : ℕ) (hr : r < gates.length)
    (hop : (gates[r]'hr).op = GateOp.and ∨ (gates[r]'hr).op = GateOp.or)
    (hlen : (gates[r]'hr).inputs.length ≤ 2) (p : ℕ) (hp : p ∈ (gates[r]'hr).inputs)
    (b : Bool) (hb : ∀ x : Fin n → Bool, val (gates.take r) x p = b) :
    (∃ b' : Bool, ∀ x : Fin n → Bool, val gates x (n + r) = b') ∨
    (∃ j, j < n + r ∧ ∀ x : Fin n → Bool, val gates x (n + r) = val gates x j) := by
  have hC : ∀ c : ℕ, (∀ x : Fin n → Bool, val gates x (n + r) = val (gates.take r) x c) →
      (∃ b' : Bool, ∀ x : Fin n → Bool, val gates x (n + r) = b') ∨
      (∃ j, j < n + r ∧ ∀ x : Fin n → Bool, val gates x (n + r) = val gates x j) := by
    intro c h
    by_cases hc : c < n + r
    · exact Or.inr ⟨c, hc, fun x => (h x).trans (val_take gates x r c (by omega) hc)⟩
    · exact Or.inl ⟨false, fun x => (h x).trans (val_take_ge _ _ _ _ (by omega))⟩
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
    refine ⟨b, fun x => ?_⟩
    rcases hop with rfl | rfl <;> simp [hv, GateOp.eval, hb x]
  | [c, d], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rcases hop with rfl | rfl <;> cases b
    · exact Or.inl ⟨false, fun x => by simp [hv, GateOp.eval, hb x]⟩
    · exact hC d fun x => by simp [hv, GateOp.eval, hb x]
    · exact hC d fun x => by simp [hv, GateOp.eval, hb x]
    · exact Or.inl ⟨true, fun x => by simp [hv, GateOp.eval, hb x]⟩
    · exact Or.inl ⟨false, fun x => by simp [hv, GateOp.eval, hb x]⟩
    · exact hC c fun x => by simp [hv, GateOp.eval, hb x]
    · exact hC c fun x => by simp [hv, GateOp.eval, hb x]
    · exact Or.inl ⟨true, fun x => by simp [hv, GateOp.eval, hb x]⟩
  | _ :: _ :: _ :: _, h => simp at h

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- A gate that is not an output and to which every later gate is insensitive cannot exist
(it could be deleted). -/
theorem not_droppable (M : MinCE S gates out) (k : ℕ) (hk : k < gates.length)
    (hno : ∀ g ∈ gates.drop (k + 1), Insens (n + k) g) (hout : ∀ w, out w ≠ n + k) : False := by
  have C := M.ce
  have hlen := dropGate_length gates k 0 n hk
  have hg' := dropGate_hg gates k 0 n C.hg
  have hU' := dropGate_hU gates k 0 n hk C.hU
  have hev' : ∀ (w : Fin m) (x : Fin n → Bool),
      val (dropGate gates k 0 n) x (redir (n + k) 0 (out w)) =
        decide (∃ v ∈ S w, x v = true) := by
    intro w x
    rw [val_dropIns gates k 0 hk hno x (out w) (hout w)]
    exact C.hev w x
  have := M.bound_lt n m S (dropGate gates k 0 n) (fun w => redir (n + k) 0 (out w)) (by omega)
    C.h2 C.hS hg' hU' hev'
  have := C.hlt
  omega

/-- Every gate that is not an output has a later effective reader. -/
theorem has_later_reader (M : MinCE S gates out) (k : ℕ) (hk : k < gates.length)
    (hout : ∀ w, out w ≠ n + k) : ∃ k', k < k' ∧ k' ∈ WReaders (n + k) gates := by
  by_contra hne
  push Not at hne
  refine M.not_droppable k hk (fun g hg => ?_) hout
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [List.getElem_drop]
  have hi' : k + 1 + i < gates.length := by simp at hi; omega
  exact insens_of_not_wreader (n + k) gates (k + 1 + i) hi' (hne _ (by omega))
    (M.ce.hg _ (List.getElem_mem hi')).1

/-- No output is constant. -/
theorem out_not_const (M : MinCE S gates out) (w : Fin m) (b : Bool) :
    ¬ ∀ x : Fin n → Bool, val gates x (out w) = b := by
  intro h
  have C := M.ce
  have h0 := h (fun _ => false)
  have h1 := h (fun _ => true)
  rw [C.hev] at h0 h1
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by have := C.h2 w; omega : 0 < (S w).card)
  have e1 : decide (∃ v ∈ S w, (fun _ : Fin n => true) v = true) = true := by
    simp only [decide_eq_true_eq]; exact ⟨v, hv, by simp⟩
  have e0 : decide (∃ v ∈ S w, (fun _ : Fin n => false) v = true) = false := by simp
  rw [e1] at h1; rw [e0] at h0
  rw [← h0] at h1; exact absurd h1 (by simp)

/-- No gate of a minimal counterexample is constant. -/
theorem no_const (M : MinCE S gates out) (k : ℕ) (hk : k < gates.length) (b : Bool) :
    ¬ ∀ x : Fin n → Bool, val gates x (n + k) = b := by
  classical
  intro hkb
  have C := M.ce
  set K := (Finset.range gates.length).filter fun k =>
    ∃ b : Bool, ∀ x : Fin n → Bool, val gates x (n + k) = b with hK
  have hKne : K.Nonempty := ⟨k, by simp only [hK, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, b, hkb⟩⟩
  set k0 := K.max' hKne with hk0
  have hk0K : k0 ∈ K := Finset.max'_mem K hKne
  have hmax : ∀ k', k0 < k' → k' < gates.length →
      ¬ ∃ b : Bool, ∀ x : Fin n → Bool, val gates x (n + k') = b := by
    intro k' hlt hk' hex
    have : k' ∈ K := by simp only [hK, Finset.mem_filter, Finset.mem_range]; exact ⟨hk', hex⟩
    have := Finset.le_max' K k' this
    omega
  simp only [hK, Finset.mem_filter, Finset.mem_range] at hk0K
  obtain ⟨hk0l, b0, hb0⟩ := hk0K
  refine M.not_droppable k0 hk0l (fun g hg => ?_) (fun w e => M.out_not_const w b0 (by rw [e]; exact hb0))
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [List.getElem_drop]
  have hi' : k0 + 1 + i < gates.length := by simp at hi; omega
  by_contra hins
  have hW : k0 + 1 + i ∈ WReaders (n + k0) gates := by
    by_contra hnw
    exact hins (insens_of_not_wreader (n + k0) gates _ hi' hnw (C.hg _ (List.getElem_mem hi')).1)
  obtain ⟨_, h⟩ := (mem_wreaders _ _ _).mp hW
  have hbt : ∀ x : Fin n → Bool, val (gates.take (k0 + 1 + i)) x (n + k0) = b0 := fun x => by
    rw [val_take gates x _ (n + k0) (by omega) (by omega)]; exact hb0 x
  rcases h with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
  · rcases const_reader gates _ hi' hop (C.hg _ (List.getElem_mem hi')).2 _ hin b0 hbt with
      hc | ⟨j, hj, hcopy⟩
    · exact hmax _ (by omega) hi' hc
    · exact M.clean _ j hi' hj hcopy
  · refine hmax _ (by omega) hi' ⟨!b0, fun x => ?_⟩
    rw [val_gate gates x _ hi', hop, hin]
    simp [GateOp.eval, hbt x]

/-- A reader of `x_u` that is not an OR gate is not an output. -/
theorem reader_not_out (M : MinCE S gates out) (u : Fin n) (k : ℕ) (hk : k < gates.length)
    (hR : k ∈ Readers u gates) (hop : (gates[k]'hk).op ≠ GateOp.or) (w : Fin m) :
    out w ≠ n + k := by
  classical
  intro e
  have C := M.ce
  rcases reader_const u gates C.hg k hk hR hop with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨t, ht, htu⟩ := Finset.exists_mem_ne (C.h2 w) u
    have h1 := C.hev w (fun v => decide (v = t))
    rw [e] at h1
    have e1 : decide (∃ v ∈ S w, (fun v : Fin n => decide (v = t)) v = true) = true := by
      simp only [decide_eq_true_eq]; exact ⟨t, ht, rfl⟩
    rw [e1] at h1
    have := h _ h1
    simp only [decide_eq_true_eq] at this
    exact htu this.symm
  · have h1 := C.hev w (fun _ => false)
    rw [e, h] at h1
    simp at h1

/-- A later reader of a non-OR reader `g` of `x_u` does not read `x_u`. -/
theorem fanout_not_reader (M : MinCE S gates out) (u : Fin n) (k : ℕ) (hk : k < gates.length)
    (hR : k ∈ Readers u gates) (hop : (gates[k]'hk).op ≠ GateOp.or) (k' : ℕ) (hkk : k < k')
    (hW : k' ∈ WReaders (n + k) gates) : k' ∉ Readers u gates := by
  classical
  intro hR'
  have C := M.ce
  rw [readers_eq_wreaders] at hR'
  obtain ⟨hk', h1⟩ := (mem_wreaders _ _ _).mp hW
  obtain ⟨_, h2⟩ := (mem_wreaders _ _ _).mp hR'
  have hun : (u : ℕ) ≠ n + k := by have := u.2; omega
  have hlen := (C.hg _ (List.getElem_mem hk')).2
  have hv := fun x : Fin n → Bool => val_gate gates x k' hk'
  have hG : ∀ x : Fin n → Bool, val (gates.take k') x (n + k) = val gates x (n + k) := fun x =>
    val_take gates x k' (n + k) (by omega) (by omega)
  have hX : ∀ x : Fin n → Bool, val (gates.take k') x (u : ℕ) = x u := fun x =>
    val_inp _ _ _ u.2
  -- the value of gate `k'` is `x_u ∘ g`
  have key : ((gates[k']'hk').op = GateOp.and ∧
        ∀ x : Fin n → Bool, val gates x (n + k') = (x u && val gates x (n + k))) ∨
      ((gates[k']'hk').op = GateOp.or ∧
        ∀ x : Fin n → Bool, val gates x (n + k') = (x u || val gates x (n + k))) := by
    generalize gates[k']'hk' = g at h1 h2 hlen hv
    obtain ⟨op, ins⟩ := g
    simp only at h1 h2 hlen hv ⊢
    rcases h1 with ⟨hao, hin1⟩ | ⟨hn, rest, hin1⟩
    · rcases h2 with ⟨-, hin2⟩ | ⟨hn2, -⟩
      · match ins, hlen with
        | [], _ => simp at hin1
        | [a], _ =>
          simp only [List.mem_singleton] at hin1 hin2
          exact absurd (hin2.trans hin1.symm) hun
        | [a, c], _ =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1 hin2
          have hcase : (a = (u : ℕ) ∧ c = n + k) ∨ (a = n + k ∧ c = (u : ℕ)) := by
            rcases hin1 with h | h <;> rcases hin2 with h' | h'
            · exact absurd (h'.trans h.symm) hun
            · exact Or.inr ⟨h.symm, h'.symm⟩
            · exact Or.inl ⟨h'.symm, h.symm⟩
            · exact absurd (h'.trans h.symm) hun
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hao with rfl | rfl
          · exact Or.inl ⟨rfl, fun x => by simp [hv, GateOp.eval, hG x, hX x]⟩
          · exact Or.inr ⟨rfl, fun x => by simp [hv, GateOp.eval, hG x, hX x]⟩
          · exact Or.inl ⟨rfl, fun x => by simp [hv, GateOp.eval, hG x, hX x, Bool.and_comm]⟩
          · exact Or.inr ⟨rfl, fun x => by simp [hv, GateOp.eval, hG x, hX x, Bool.or_comm]⟩
        | _ :: _ :: _ :: _, h => simp at h
      · rcases hao with h | h <;> rw [h] at hn2 <;> exact absurd hn2 (by simp)
    · rcases h2 with ⟨hao, -⟩ | ⟨-, rest2, hin2⟩
      · rcases hao with h | h <;> rw [h] at hn <;> exact absurd hn (by simp)
      · rw [hin1] at hin2
        simp only [List.cons.injEq] at hin2
        exact absurd hin2.1.symm hun
  rcases reader_const u gates C.hg k hk hR hop with ⟨-, hle⟩ | ⟨-, hnot⟩
  · rcases key with ⟨-, hval⟩ | ⟨-, hval⟩
    · refine M.clean k' (n + k) hk' (by omega) fun x => ?_
      rw [hval x]
      cases hx : x u
      · cases hv' : val gates x (n + k)
        · rfl
        · rw [hle x hv'] at hx; exact absurd hx (by simp)
      · simp
    · refine M.clean k' (u : ℕ) hk' (by have := u.2; omega) fun x => ?_
      rw [hval x, val_inp _ _ _ u.2]
      cases hx : x u
      · cases hv' : val gates x (n + k)
        · rfl
        · rw [hle x hv'] at hx; exact absurd hx (by simp)
      · simp
  · rcases key with ⟨-, hval⟩ | ⟨-, hval⟩
    · exact M.no_const k' hk' false fun x => by rw [hval x, hnot x]; cases x u <;> rfl
    · exact M.no_const k' hk' true fun x => by rw [hval x, hnot x]; cases x u <;> rfl

open Classical in
/-- G1.5 (AND-reader / NOT-reader lemma): if gate `k` reads `x_u` and is not an OR gate, then its
later readers `F` are nonempty, dead under `x_u := 0` and disjoint from the readers of `x_u`:
`#readers(u) + #F ≤ #DC(u)` and `base + #readers(u) + #F ≤ s + deg u`. -/
theorem and_reader_dead (M : MinCE S gates out) (u : Fin n) (k : ℕ) (hk : k < gates.length)
    (hR : k ∈ Readers u gates) (hop : (gates[k]'hk).op ≠ GateOp.or) :
    1 ≤ ((WReaders (n + k) gates).filter fun k' => k < k').card ∧
    Disjoint (Readers u gates) ((WReaders (n + k) gates).filter fun k' => k < k') ∧
    (Readers u gates).card + ((WReaders (n + k) gates).filter fun k' => k < k').card
      ≤ (DC u gates).card ∧
    baseOf S + (Readers u gates).card + ((WReaders (n + k) gates).filter fun k' => k < k').card
      ≤ gates.length + degOf S u := by
  have C := M.ce
  set F := (WReaders (n + k) gates).filter fun k' => k < k' with hF
  obtain ⟨k', hkk, hW⟩ := M.has_later_reader k hk (M.reader_not_out u k hk hR hop)
  have hpos : 1 ≤ F.card :=
    Finset.card_pos.mpr ⟨k', Finset.mem_filter.mpr ⟨hW, hkk⟩⟩
  have hdisj : Disjoint (Readers u gates) F := by
    rw [Finset.disjoint_right]
    intro a ha
    obtain ⟨haW, hka⟩ := Finset.mem_filter.mp ha
    exact M.fanout_not_reader u k hk hR hop a hka haW
  obtain ⟨b, hb⟩ := reader_const0 u gates C.hg k hk hR hop
  have hFsub : F ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (wreaders_sub_DC u gates C.hg k b hb)
  have hle := Finset.card_le_card (Finset.union_subset (readers_sub_DC u gates C.hg) hFsub)
  rw [Finset.card_union_of_disjoint hdisj] at hle
  have hd := M.deadBound u (by omega)
  refine ⟨hpos, hdisj, hle, ?_⟩
  unfold baseOf degOf
  omega

/-- A tight point has only OR readers; in particular it is not read by the NOT gate. -/
theorem tight_or (M : MinCE S gates out) (u : Fin n) (ht : Tight S gates u) (k : ℕ)
    (hk : k < gates.length) (hR : k ∈ Readers u gates) : (gates[k]'hk).op = GateOp.or := by
  by_contra hop
  obtain ⟨h1, -, -, h4⟩ := M.and_reader_dead u k hk hR hop
  unfold Tight at ht
  omega

end MinCE

/-! ## G1.3 (peeling / cascade) and G1.6 (capacity) -/

/-- The gates below position `ρ` depend only on the variables that have a reader below `ρ`. -/
theorem val_congr_below {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (ρ : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ t : Fin n, (∃ k ∈ Readers t gates, k < ρ) → x t = y t) :
    ∀ k, k < ρ → ∀ hk : k < gates.length, val gates x (n + k) = val gates y (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hkρ hk
  rw [val_gate gates x k hk, val_gate gates y k hk]
  have hin : ∀ a, (∀ ha : a < n, k ∈ Readers (⟨a, ha⟩ : Fin n) gates) →
      val (gates.take k) x a = val (gates.take k) y a := by
    intro a hR
    by_cases ha : a < n
    · rw [val_inp _ _ _ ha, val_inp _ _ _ ha]; exact hxy _ ⟨k, hR ha, hkρ⟩
    · by_cases hak : a < n + k
      · rw [val_take gates x k a (by omega) hak, val_take gates y k a (by omega) hak]
        have := ih (a - n) (by omega) (by omega) (by omega)
        rwa [show n + (a - n) = a by omega] at this
      · rw [val_take_ge _ _ _ _ (by omega), val_take_ge _ _ _ _ (by omega)]
  rcases (hg _ (List.getElem_mem hk)).1 with hop | hop | hop
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact hin a fun han => by
      rw [readers_eq_wreaders]; exact (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inl hop, ha⟩⟩
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact hin a fun han => by
      rw [readers_eq_wreaders]; exact (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨Or.inr hop, ha⟩⟩
  · rw [hop]
    rcases hin' : (gates[k]'hk).inputs with _ | ⟨a, rest⟩
    · rfl
    · have := hin a fun han => by
        rw [readers_eq_wreaders]; exact (mem_wreaders _ _ _).mpr ⟨hk, Or.inr ⟨hop, rest, hin'⟩⟩
      simp [GateOp.eval, this]

open Classical in
/-- The reader of a single-reader point (the least reader in general, `0` if there is none). -/
noncomputable def rdr {n : ℕ} (gates : List Gate) (v : Fin n) : ℕ :=
  if h : (Readers v gates).Nonempty then (Readers v gates).min' h else 0

theorem rdr_eq {n : ℕ} (gates : List Gate) (v : Fin n) (r : ℕ) (h : Readers v gates = {r}) :
    rdr gates v = r := by
  have hne : (Readers v gates).Nonempty := ⟨r, by rw [h]; simp⟩
  unfold rdr
  rw [dif_pos hne]
  exact Finset.mem_singleton.mp ((Finset.ext_iff.mp h _).mp (Finset.min'_mem _ hne))

/-- `v` is a single-reader point (reader `r`) that uses `u` as the only earlier point of its set
`S i`: `u, v ∈ S i`, and no point of `S i` other than `u` has a reader below `r`.
(With `A_j = B ∪ {v_1..v_{j-1}}` as in G1.3 this is implied by `S i ∩ A_j = {u}`.) -/
def UsesVia {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (u v : Fin n)
    (i : Fin m) : Prop :=
  v ≠ u ∧ u ∈ S i ∧ v ∈ S i ∧ ∃ r, Readers v gates = {r} ∧
    ∀ t ∈ S i, t ≠ u → ∀ k ∈ Readers t gates, r ≤ k

open Classical in
/-- The single-reader points using `u` as singleton (through any set). -/
noncomputable def Users {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ i, UsesVia S gates u v i

open Classical in
/-- `kL(u)`: the single-reader points using `u` as singleton through a line (`|S i| ≥ 3`). -/
noncomputable def LineUsers {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ i, 3 ≤ (S i).card ∧ UsesVia S gates u v i

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- A point with a reader has degree `≥ 2`. -/
theorem deg_two_of_reader (M : MinCE S gates out) (v : Fin n) (k : ℕ)
    (hk : k ∈ Readers v gates) : 2 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  have C := M.ce
  have hpos : 1 ≤ (DC v gates).card :=
    Finset.card_pos.mpr ⟨k, readers_sub_DC v gates C.hg hk⟩
  have := M.deadBound v hpos
  have := C.hlt
  omega

/-- `single_core` with the shape of `r` exposed: the wires read by `r` are `v` and `c`, and
`r = x_v ∧ c` (`b = true`) or `r = x_v ∨ c` (`b = false`). -/
theorem single_core3 (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r}) :
    ∃ (c : ℕ) (b : Bool), n ≤ c ∧ c < n + r ∧ r < gates.length ∧
      (∀ u : Fin n, u ≠ v → r ∉ Readers u gates) ∧
      (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = c) ∧ r ∈ WReaders c gates ∧
      (∀ x : Fin n → Bool, val gates x (n + r) =
        if b then (x v && val gates x c) else (x v || val gates x c)) ∧
      (∀ hr : r < gates.length, (gates[r]'hr).op = if b then GateOp.and else GateOp.or) ∧
      ∀ i, v ∈ S i → ∀ x : Fin n → Bool,
        (∀ t ∈ S i, (∃ k ∈ Readers t gates, k < r) → x t = false) →
        val gates x c = b ∧ val gates x (n + r) = x v := by
  classical
  have C := M.ce
  have hrR : r ∈ Readers v gates := by rw [hR]; simp
  obtain ⟨hr, hrd⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hrR)
  have hnotR : ∀ k, k ≠ r → k ∉ Readers v gates := fun k hkr hk => by
    rw [hR] at hk; exact hkr (Finset.mem_singleton.mp hk)
  have hins : ∀ (k : ℕ) (hk : k < gates.length), k ≠ r → Insens v (gates[k]'hk) :=
    fun k hk hkr => insens_of_not_reader v gates k hk (hnotR k hkr)
      (C.hg _ (List.getElem_mem hk)).1
  have hdeg := M.deg_two_of_reader v r hrR
  obtain ⟨w0, hw0⟩ : ∃ w, v ∈ S w := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega :
      0 < (Finset.univ.filter fun w : Fin m => v ∈ S w).card)
    exact ⟨w, by simpa using hw⟩
  have AL : ∀ (x : Fin n → Bool) (w : Fin m), v ∈ S w → (∀ t ∈ S w, x t = false) →
      val gates x (n + r) ≠ val gates (Function.update x v true) (n + r) :=
    fun x w hv hz hf => absorb_eq S gates out C.h2 C.hev v r hins x hf w hv hz
  have hao : (gates[r]'hr).op = GateOp.and ∨ (gates[r]'hr).op = GateOp.or := by
    rcases hrd with ⟨hao, -⟩ | ⟨hn, rest, hin⟩
    · exact hao
    · exfalso
      refine absorb_anti S gates out C.h2 C.hev C.hg C.hU v r hr hn (fun k hk hkr hmem => ?_)
        (fun _ => false) (fun h => ?_) w0 hw0 (fun _ _ => rfl)
      · apply hnotR k hkr
        rw [readers_eq_wreaders]
        refine (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨?_, hmem⟩⟩
        rcases (C.hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (C.hU k r hk hr h hn) hkr
      · rw [val_gate gates _ r hr, hn, hin] at h
        simp [GateOp.eval, val_inp _ _ _ v.2] at h
  have hvin : (v : ℕ) ∈ (gates[r]'hr).inputs := by
    rcases hrd with ⟨-, h⟩ | ⟨hn, -⟩
    · exact h
    · rcases hao with h | h <;> rw [h] at hn <;> exact absurd hn (by simp)
  have hX : ∀ x : Fin n → Bool, val (gates.take r) x (v : ℕ) = x v := fun x => val_inp _ _ _ v.2
  have pre : ∃ c, (∀ a ∈ (gates[r]'hr).inputs, a = (v : ℕ) ∨ a = c) ∧
      c ∈ (gates[r]'hr).inputs ∧
      (((gates[r]'hr).op = GateOp.and ∧
          ∀ x : Fin n → Bool, val gates x (n + r) = (x v && val (gates.take r) x c)) ∨
       ((gates[r]'hr).op = GateOp.or ∧
          ∀ x : Fin n → Bool, val gates x (n + r) = (x v || val (gates.take r) x c))) := by
    have hv := fun x : Fin n → Bool => val_gate gates x r hr
    have hlen := (C.hg _ (List.getElem_mem hr)).2
    generalize gates[r]'hr = g at hao hvin hv hlen
    obtain ⟨op, ins⟩ := g
    simp only at hao hvin hv hlen ⊢
    match ins, hlen with
    | [], _ => simp at hvin
    | [a], _ =>
      simp only [List.mem_singleton] at hvin
      subst hvin
      refine ⟨(v : ℕ), by simp, by simp, ?_⟩
      rcases hao with rfl | rfl
      · exact Or.inl ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x]⟩
      · exact Or.inr ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x]⟩
    | [a, c], _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
      rcases hvin with rfl | rfl
      · refine ⟨c, by simp, by simp, ?_⟩
        rcases hao with rfl | rfl
        · exact Or.inl ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x]⟩
        · exact Or.inr ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x]⟩
      · refine ⟨a, by simp [or_comm], by simp, ?_⟩
        rcases hao with rfl | rfl
        · exact Or.inl ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x, Bool.and_comm]⟩
        · exact Or.inr ⟨rfl, fun x => by simp [hv, GateOp.eval, hX x, Bool.or_comm]⟩
    | _ :: _ :: _ :: _, h => simp at h
  obtain ⟨c, hcin, hcmem, hval⟩ := pre
  have hWc : r ∈ WReaders c gates := (mem_wreaders _ _ _).mpr ⟨hr, Or.inl ⟨hao, hcmem⟩⟩
  by_cases hcn : c < n
  · exfalso
    have hC : ∀ x : Fin n → Bool, val (gates.take r) x c = x ⟨c, hcn⟩ := fun x =>
      val_inp _ _ _ hcn
    by_cases htv : (⟨c, hcn⟩ : Fin n) = v
    · refine M.clean r (v : ℕ) hr (by have := v.2; omega) fun x => ?_
      rcases hval with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h x, hC, htv, val_inp _ _ _ v.2] <;> simp
    · obtain ⟨w, hvw, htw⟩ := M.avoid hdeg ⟨c, hcn⟩ (Ne.symm htv)
      rcases hval with ⟨ho, h⟩ | ⟨ho, h⟩
      · refine AL (fun _ => false) w hvw (fun _ _ => rfl) ?_
        rw [h, h, hC, hC, Function.update_of_ne htv]; simp
      · refine AL (fun t => decide (t = ⟨c, hcn⟩)) w hvw (fun t ht => ?_) ?_
        · simp only [decide_eq_false_iff_not]; rintro rfl; exact htw ht
        · rw [h, h, hC, hC, Function.update_of_ne htv]; simp
  · by_cases hcr : c < n + r
    · have hCt : ∀ x : Fin n → Bool, val (gates.take r) x c = val gates x c := fun x =>
        val_take gates x r c (by omega) hcr
      have hnu : ∀ u : Fin n, u ≠ v → r ∉ Readers u gates := by
        intro u huv hu
        rw [readers_eq_wreaders] at hu
        obtain ⟨_, h⟩ := (mem_wreaders _ _ _).mp hu
        have hmem : (u : ℕ) ∈ (gates[r]'hr).inputs := by
          rcases h with ⟨-, h⟩ | ⟨-, rest, h⟩
          · exact h
          · rw [h]; simp
        rcases hcin _ hmem with e | e
        · exact huv (Fin.ext e)
        · have := u.2; omega
      have hW : ∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = c := by
        intro p hp
        obtain ⟨_, h⟩ := (mem_wreaders _ _ _).mp hp
        have hmem : p ∈ (gates[r]'hr).inputs := by
          rcases h with ⟨-, h⟩ | ⟨-, rest, h⟩
          · exact h
          · rw [h]; simp
        exact hcin _ hmem
      have hCc : ∀ x y : Fin n → Bool,
          (∀ t : Fin n, (∃ k ∈ Readers t gates, k < r) → x t = y t) →
          val gates x c = val gates y c := by
        intro x y h
        have := val_congr_below gates C.hg r x y h (c - n) (by omega) (by omega)
        rwa [show n + (c - n) = c by omega] at this
      have hvA : ¬ ∃ k ∈ Readers v gates, k < r := by
        rintro ⟨k, hk, hlt⟩
        rw [hR] at hk
        have := Finset.mem_singleton.mp hk
        omega
      -- the constant: `true` for an AND reader, `false` for an OR reader
      have main : ∀ b : Bool,
          ((∀ x : Fin n → Bool, val gates x (n + r) = (x v && val gates x c)) ∧ b = true ∨
           (∀ x : Fin n → Bool, val gates x (n + r) = (x v || val gates x c)) ∧ b = false) →
          ∀ i, v ∈ S i → ∀ x : Fin n → Bool,
          (∀ t ∈ S i, (∃ k ∈ Readers t gates, k < r) → x t = false) →
          val gates x c = b ∧ val gates x (n + r) = x v := by
        intro b hb i hvi x hx
        set y : Fin n → Bool := fun t => if (∃ k ∈ Readers t gates, k < r) then x t else false
          with hy
        have hy0 : ∀ t ∈ S i, y t = false := by
          intro t ht
          by_cases hA : ∃ k ∈ Readers t gates, k < r
          · simp only [hy, if_pos hA]; exact hx t ht hA
          · simp only [hy, if_neg hA]
        have hxy : val gates x c = val gates y c :=
          hCc x y fun t ht => by simp only [hy, if_pos ht]
        have hyy : val gates (Function.update y v true) c = val gates y c :=
          hCc _ _ fun t ht => by
            rw [Function.update_of_ne]; rintro rfl; exact hvA ht
        have hne := AL y i hvi hy0
        have hyv := hy0 v hvi
        rcases hb with ⟨h, rfl⟩ | ⟨h, rfl⟩
        · rw [h y, h (Function.update y v true), hyy, hyv, Function.update_self] at hne
          cases hC : val gates y c
          · rw [hC] at hne; exact absurd rfl hne
          · exact ⟨hxy.trans hC, by rw [h x, hxy, hC]; simp⟩
        · rw [h y, h (Function.update y v true), hyy, hyv, Function.update_self] at hne
          cases hC : val gates y c
          · exact ⟨hxy.trans hC, by rw [h x, hxy, hC]; simp⟩
          · rw [hC] at hne; exact absurd rfl hne
      rcases hval with ⟨ho, h⟩ | ⟨ho, h⟩
      · exact ⟨c, true, by omega, hcr, hr, hnu, hW, hWc, fun x => by simp [h x, hCt x],
          fun _ => by simpa using ho,
          main true (Or.inl ⟨fun x => by rw [h x, hCt], rfl⟩)⟩
      · exact ⟨c, false, by omega, hcr, hr, hnu, hW, hWc, fun x => by simp [h x, hCt x],
          fun _ => by simpa using ho,
          main false (Or.inr ⟨fun x => by rw [h x, hCt], rfl⟩)⟩
    · exfalso
      have hC : ∀ x : Fin n → Bool, val (gates.take r) x c = false := fun x =>
        val_take_ge _ _ _ _ (by omega)
      rcases hval with ⟨ho, h⟩ | ⟨ho, h⟩
      · exact M.no_const r hr false fun x => by rw [h x, hC]; simp
      · exact M.clean r (v : ℕ) hr (by have := v.2; omega) fun x => by
          rw [h x, hC, val_inp _ _ _ v.2]; simp

/-- `single_core3` without the operation of `r`. -/
theorem single_core2 (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r}) :
    ∃ (c : ℕ) (b : Bool), n ≤ c ∧ c < n + r ∧ r < gates.length ∧
      (∀ u : Fin n, u ≠ v → r ∉ Readers u gates) ∧
      (∀ p, r ∈ WReaders p gates → p = (v : ℕ) ∨ p = c) ∧
      (∀ x : Fin n → Bool, val gates x (n + r) =
        if b then (x v && val gates x c) else (x v || val gates x c)) ∧
      ∀ i, v ∈ S i → ∀ x : Fin n → Bool,
        (∀ t ∈ S i, (∃ k ∈ Readers t gates, k < r) → x t = false) →
        val gates x c = b ∧ val gates x (n + r) = x v := by
  obtain ⟨c, b, h1, h2, h3, h4, h5, -, h6, -, h7⟩ := M.single_core3 v r hR
  exact ⟨c, b, h1, h2, h3, h4, h5, h6, h7⟩

/-- G1.2 (AL) for a single-reader point `v` with reader `r`: `r = x_v ∘ c` with `c` an earlier
GATE; `r` reads no other variable; and for every set `S i ∋ v` and every `x` vanishing on the
points of `S i` that have a reader below `r`, `c(x) = b` (a fixed constant) and `r(x) = x_v`. -/
theorem single_core (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r}) :
    ∃ (c : ℕ) (b : Bool), n ≤ c ∧ c < n + r ∧ r < gates.length ∧
      (∀ u : Fin n, u ≠ v → r ∉ Readers u gates) ∧
      ∀ i, v ∈ S i → ∀ x : Fin n → Bool,
        (∀ t ∈ S i, (∃ k ∈ Readers t gates, k < r) → x t = false) →
        val gates x c = b ∧ val gates x (n + r) = x v := by
  obtain ⟨c, b, h1, h2, h3, h4, -, -, h5⟩ := M.single_core2 v r hR
  exact ⟨c, b, h1, h2, h3, h4, h5⟩

/-- The reader `r_v = x_v ∘ c` of a user `v` of `u`: `c` is constant (`b`) on `{x_u = 0}`, with
`b = true` for an AND reader and `b = false` for an OR reader. -/
theorem uses_core (M : MinCE S gates out) (u v : Fin n) (i : Fin m)
    (h : UsesVia S gates u v i) :
    ∃ (c : ℕ) (b : Bool), n ≤ c ∧ c < n + rdr gates v ∧
      (∀ p, rdr gates v ∈ WReaders p gates → p = (v : ℕ) ∨ p = c) ∧
      (∀ x : Fin n → Bool, val gates x (n + rdr gates v) =
        if b then (x v && val gates x c) else (x v || val gates x c)) ∧
      ∀ x : Fin n → Bool, x u = false → val gates x c = b := by
  obtain ⟨hvu, hui, hvi, r, hR, hA⟩ := h
  rw [rdr_eq gates v r hR]
  obtain ⟨c, b, hc1, hc2, hr, -, hW, hform, hcore⟩ := M.single_core2 v r hR
  refine ⟨c, b, hc1, hc2, hW, hform, fun x hxu => (hcore i hvi x fun t ht hex => ?_).1⟩
  by_cases htu : t = u
  · rw [htu]; exact hxu
  · obtain ⟨k, hk, hlt⟩ := hex
    exact absurd hlt (by have := hA t ht htu k hk; omega)

/-- G1.3 (i): every set through a single-reader point `v` (reader `r`) contains a point with a
reader below `r`. -/
theorem peel_meets (M : MinCE S gates out) (v : Fin n) (r : ℕ) (hR : Readers v gates = {r})
    (i : Fin m) (hvi : v ∈ S i) : ∃ t ∈ S i, ∃ k ∈ Readers t gates, k < r := by
  by_contra hne
  push Not at hne
  obtain ⟨c, b, hc1, hc2, hr, -, hcore⟩ := M.single_core v r hR
  refine M.no_const (c - n) (by omega) b fun x => ?_
  rw [show n + (c - n) = c by omega]
  refine (hcore i hvi x fun t ht hex => ?_).1
  obtain ⟨k, hk, hlt⟩ := hex
  exact absurd hlt (by have := hne t ht k hk; omega)

/-- G1.3 (ii): if the single-reader point `v` uses `u` as singleton through `S i`, then under
`x_u := 0` the reader `r` of `v` becomes `x_v` and its other input `c` (a gate below `r`) becomes
constant: both die, and `r` is not a reader of `x_u`. -/
theorem peel_dead (M : MinCE S gates out) (u v : Fin n) (i : Fin m)
    (h : UsesVia S gates u v i) :
    rdr gates v ∈ DC u gates ∧ rdr gates v ∉ Readers u gates ∧
      (∀ x : Fin n → Bool, x u = false → val gates x (n + rdr gates v) = x v) ∧
      ∃ c, c < rdr gates v ∧ c ∈ DC u gates := by
  classical
  obtain ⟨hvu, hui, hvi, r, hR, hA⟩ := h
  rw [rdr_eq gates v r hR]
  obtain ⟨c, b, hc1, hc2, hr, hnu, hcore⟩ := M.single_core v r hR
  have hx : ∀ x : Fin n → Bool, x u = false →
      val gates x c = b ∧ val gates x (n + r) = x v := by
    intro x hxu
    refine hcore i hvi x fun t ht hex => ?_
    by_cases htu : t = u
    · rw [htu]; exact hxu
    · obtain ⟨k, hk, hlt⟩ := hex
      exact absurd hlt (by have := hA t ht htu k hk; omega)
  refine ⟨dc_of_restrict gates u v r hr fun x hxu => (hx x hxu).2, hnu u (Ne.symm hvu),
    fun x hxu => (hx x hxu).2, c - n, by omega, ?_⟩
  simp only [DC, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ?_⟩
  have hcc : ∀ x : Fin n → Bool, x u = false → val gates x (n + (c - n)) = b := fun x hxu => by
    rw [show n + (c - n) = c by omega]; exact (hx x hxu).1
  cases b
  · exact Or.inl (dcp_of_false u gates _ hcc)
  · exact Or.inr hcc

/-- The readers `r_v` of the users of `u` are distinct gates, dead under `x_u := 0`, none of them
a reader of `x_u`. -/
theorem users_image (M : MinCE S gates out) (u : Fin n) :
    (Users S gates u).image (rdr gates) ⊆ DC u gates ∧
    Disjoint (Readers u gates) ((Users S gates u).image (rdr gates)) ∧
    Set.InjOn (rdr gates) (Users S gates u : Set (Fin n)) := by
  classical
  have hU : ∀ v ∈ Users S gates u, ∃ i, UsesVia S gates u v i := fun v hv => by
    simpa [Users] using hv
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨i, hi⟩ := hU v hv
    exact (M.peel_dead u v i hi).1
  · rw [Finset.disjoint_right]
    intro k hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨i, hi⟩ := hU v hv
    exact (M.peel_dead u v i hi).2.1
  · intro v hv v' hv' hvv
    obtain ⟨i, hi⟩ := hU v hv
    obtain ⟨i', hi'⟩ := hU v' hv'
    have h1 := (M.peel_dead u v i hi).2.2.1 (fun t => decide (t = v))
      (by simp only [decide_eq_false_iff_not]; exact fun e => hi.1 e.symm)
    have h2 := (M.peel_dead u v' i' hi').2.2.1 (fun t => decide (t = v))
      (by simp only [decide_eq_false_iff_not]; exact fun e => hi.1 e.symm)
    rw [hvv] at h1
    rw [h1] at h2
    have h3 : v' = v := by simpa using h2.symm
    exact h3.symm

/-- G1.6 (capacity form of the cascade): the `k` single-reader points using `u` as singleton give
`k` distinct non-readers of `x_u` that die under `x_u := 0`:
`#readers(u) + k ≤ #DC(u)` and `k ≤ deg u - σ - #readers(u)`
(additively `base + #readers(u) + k ≤ s + deg u`). -/
theorem capacity (M : MinCE S gates out) (u : Fin n) (hu : 1 ≤ (Readers u gates).card) :
    (Readers u gates).card + (Users S gates u).card ≤ (DC u gates).card ∧
    baseOf S + (Readers u gates).card + (Users S gates u).card ≤ gates.length + degOf S u := by
  classical
  have C := M.ce
  obtain ⟨hsub, hdisj, hinj⟩ := M.users_image u
  have hcard : ((Users S gates u).image (rdr gates)).card = (Users S gates u).card :=
    Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card (Finset.union_subset (readers_sub_DC u gates C.hg) hsub)
  rw [Finset.card_union_of_disjoint hdisj, hcard] at hle
  have hd := M.deadBound u (by omega)
  refine ⟨hle, ?_⟩
  unfold baseOf degOf
  omega

open Classical in
/-- The three disjoint families of gates dead under `x_u := 0` behind rule 'p': the non-pair
readers `N`, the lowest gates `G` restricting to `x_w` (one per pair-set `{u, w}`), and the
readers `L` of the line-singleton users. -/
theorem pkL_sets (M : MinCE S gates out) (u : Fin n) : ∃ G : Finset ℕ,
    G ⊆ DC u gates ∧ G.card = pairDeg S u ∧
    (LineUsers S gates u).image (rdr gates) ⊆ DC u gates ∧
    ((LineUsers S gates u).image (rdr gates)).card = (LineUsers S gates u).card ∧
    Disjoint ((Readers u gates).filter
      (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w)) G ∧
    Disjoint ((Readers u gates).filter
      (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w))
      ((LineUsers S gates u).image (rdr gates)) ∧
    Disjoint G ((LineUsers S gates u).image (rdr gates)) ∧
    ∀ k ∈ G, ∃ (w : Fin n) (i : Fin m), S i = {u, w} ∧ k < gates.length ∧
      (∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w) ∧
      ∀ k', k' < k → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w := by
  have C := M.ce
  have C := M.ce
  have h2 := C.h2
  set PS := Finset.univ.filter fun i : Fin m => u ∈ S i ∧ (S i).card = 2 with hPS
  set N := (Readers u gates).filter
    (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) with hN
  set G := PS.image (lowR gates out u) with hG
  set L := (LineUsers S gates u).image (rdr gates) with hL
  have hLU : ∀ v ∈ LineUsers S gates u, ∃ i, 3 ≤ (S i).card ∧ UsesVia S gates u v i :=
    fun v hv => by simpa [LineUsers] using hv
  have hLsubU : LineUsers S gates u ⊆ Users S gates u := by
    intro v hv
    obtain ⟨i, -, hi⟩ := hLU v hv
    simp only [Users, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi⟩
  obtain ⟨hUsub, hUdisj, hUinj⟩ := M.users_image u
  have hLsub : L ⊆ DC u gates := (Finset.image_subset_image hLsubU).trans hUsub
  have hLcard : L.card = (LineUsers S gates u).card :=
    Finset.card_image_of_injOn (hUinj.mono (by exact_mod_cast hLsubU))
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
    obtain ⟨hlt, hres, -⟩ := lowR_spec S gates out h2 C.hev u w i hiw
    exact dc_of_restrict gates u w _ hlt hres
  have hNsub : N ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (readers_sub_DC u gates C.hg)
  have hNG : Disjoint N G := by
    rw [Finset.disjoint_left]
    intro k hkN hkG
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkG
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨hlt, hres, hlow⟩ := lowR_spec S gates out h2 C.hev u w i hiw
    simp only [hN, Finset.mem_filter] at hkN
    exact hkN.2 ⟨w, ⟨i, hiw⟩,
      lowest_pair_gate gates u w (huw w i hiw) C.hg _ hlt hres hlow hkN.1⟩
  have hNL : Disjoint N L := by
    rw [Finset.disjoint_left]
    intro k hkN hkL
    exact Finset.disjoint_left.mp hUdisj (Finset.mem_filter.mp hkN).1
      (Finset.image_subset_image hLsubU hkL)
  have hGL : Disjoint G L := by
    rw [Finset.disjoint_left]
    intro k hkG hkL
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkG
    obtain ⟨v, hv, hvk⟩ := Finset.mem_image.mp hkL
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨-, hres, -⟩ := lowR_spec S gates out h2 C.hev u w i hiw
    obtain ⟨j, hj3, hj⟩ := hLU v hv
    have hvu : v ≠ u := hj.1
    have h1 := (M.peel_dead u v j hj).2.2.1 (fun t => decide (t = v))
      (by simp only [decide_eq_false_iff_not]; exact fun e => hvu e.symm)
    rw [hvk, hres _ (by simp only [decide_eq_false_iff_not]; exact fun e => hvu e.symm)] at h1
    have hwv : w = v := by simpa using h1
    have hne : i ≠ j := by
      intro e
      rw [← e, hiw, Finset.card_pair (huw w i hiw)] at hj3
      omega
    have hsub : ({u, w} : Finset (Fin n)) ⊆ S i ∩ S j := by
      intro a ha
      rw [Finset.mem_inter]
      refine ⟨by rw [hiw]; exact ha, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hj.2.1
      · rw [hwv]; exact hj.2.2.1
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (huw w i hiw)] at this
    have := C.hS i j hne
    omega
  have hinj : Set.InjOn (lowR gates out u) PS := by
    intro i hi j hj hij
    obtain ⟨w, hiw⟩ := hw i hi
    obtain ⟨w', hjw⟩ := hw j hj
    obtain ⟨-, hres, -⟩ := lowR_spec S gates out h2 C.hev u w i hiw
    obtain ⟨-, hres', -⟩ := lowR_spec S gates out h2 C.hev u w' j hjw
    have hww : w = w' := by
      have h1 := hres (fun t => decide (t = w)) (by simp [huw w i hiw])
      have h2' := hres' (fun t => decide (t = w)) (by simp [huw w i hiw])
      rw [hij] at h1
      rw [h1] at h2'
      have h3 : w' = w := by simpa using h2'
      exact h3.symm
    by_contra hne
    have := C.hS i j hne
    rw [hiw, hjw, hww, Finset.inter_self, Finset.card_pair (huw w' j hjw)] at this
    omega
  have hGc : G.card = PS.card := Finset.card_image_of_injOn hinj
  refine ⟨G, hGsub, hGc, hLsub, hLcard, hNG, hNL, hGL, fun k hk => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨w, hiw⟩ := hw i hi
  obtain ⟨hlt, hres, hlow⟩ := lowR_spec S gates out h2 C.hev u w i hiw
  exact ⟨w, i, hiw, hlt, hres, hlow⟩

/-- Rule 'p' with the `kL(u)` term: `nonpair(u) + p(u) + kL(u) ≤ #DC(u)`, hence
`nonpair(u) + kL(u) ≤ l(u) - σ` (additively `base + nonpair(u) + kL(u) ≤ s + l(u)`). -/
theorem rule_p_kL (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i) :
    nonpair S gates u + pairDeg S u + (LineUsers S gates u).card ≤ (DC u gates).card ∧
    baseOf S + nonpair S gates u + (LineUsers S gates u).card ≤ gates.length + lineDeg S u := by
  classical
  have C := M.ce
  obtain ⟨G, hGsub, hGc, hLsub, hLcard, hNG, hNL, hGL, -⟩ := M.pkL_sets u
  have hNsub : (Readers u gates).filter
      (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (readers_sub_DC u gates C.hg)
  have hle := Finset.card_le_card
    (Finset.union_subset (Finset.union_subset hNsub hGsub) hLsub)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hNL, hGL⟩),
    Finset.card_union_of_disjoint hNG, hGc, hLcard] at hle
  have hcount : nonpair S gates u + pairDeg S u + (LineUsers S gates u).card
      ≤ (DC u gates).card := by
    unfold nonpair
    exact hle
  refine ⟨hcount, ?_⟩
  have hb := (M.rule_p u hu).2.1
  have hd := deg_split S C.h2 u
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux
