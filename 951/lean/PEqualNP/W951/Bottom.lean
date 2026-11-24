import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Absorb

/-!
# G1.2 (bottom lemma): two heavy points in a minimal counterexample

"Heavy" is measured by dead gates: `2 ≤ #DC(v)` (`DC v gates` = gates dead on `x_v := 0`; it contains
every direct reader of `x_v` by `readers_sub_DC`).  `MinCE.two_heavy`: a minimal counterexample has
two distinct points with at least two dead gates each; `MinCE.two_deg3`: hence two distinct points
of degree `≥ 3` (in fact `base + 2 ≤ s + deg`).  `MinCE.bottom_core`: no minimal counterexample in
which all points but one have at most one dead gate.  `MinCE.no_minCE_deg2` (G1.1): hence a point of
degree `≥ 3`.  The helpers `dc1_facts`, `avoid`, `absorbR` are in `Absorb`.  No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- A gate that does not read wire `u` (syntactically) is insensitive to it. -/
theorem insens_of_not_reader {n : ℕ} (u : Fin n) (gates : List Gate) (k : ℕ)
    (hk : k < gates.length) (h : k ∉ Readers u gates)
    (hgk : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or ∨
      (gates[k]'hk).op = GateOp.not) : Insens u (gates[k]'hk) :=
  insens_of_unread u _ hgk fun hh =>
    h (by simp only [Readers, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hk, hh⟩)

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- G1.2, core: no minimal counterexample in which every point except possibly `p` has at most one
dead gate. -/
theorem bottom_core (M : MinCE S gates out) (p : Fin n)
    (hp : ∀ v : Fin n, v ≠ p → (DC v gates).card ≤ 1) : False := by
  classical
  have C := M.ce
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; have := C.hlt; simp at this
    · exact h
  obtain ⟨v0, hv0, hv0p⟩ := Finset.exists_mem_ne (C.h2 ⟨0, hm⟩) p
  set z : Fin n → Bool := fun _ => false with hzdef
  have hpos : 0 < gates.length := by
    by_contra h0
    refine absorb_eq S gates out C.h2 C.hev v0 0 (fun k hk _ => absurd hk (by omega)) z ?_
      ⟨0, hm⟩ hv0 (fun _ _ => rfl)
    rw [val_ge _ _ _ (by omega), val_ge _ _ _ (by omega)]
  have hset : ∀ (r : ℕ) (_ : r < gates.length) (a : Fin n), a ≠ p →
      (DCp a gates r ∨ DTr a gates r) → ∃ w, a ∈ S w := by
    intro r hr a hap hd
    obtain ⟨hda, -⟩ := M.dc1_facts (hp a hap) r hr hd
    obtain ⟨w, hw⟩ : (Finset.univ.filter fun w : Fin m => a ∈ S w).Nonempty :=
      Finset.card_pos.mp (by omega)
    exact ⟨w, by simpa using hw⟩
  have hconst : ∀ (r : ℕ) (_ : r < gates.length) (c : Bool),
      (∀ x : Fin n → Bool, val gates x (n + r) = c) → False := by
    intro r hr c hc
    have hd : DCp v0 gates r ∨ DTr v0 gates r := by
      cases c
      · exact Or.inl (dcp_of_false v0 gates r fun x _ => hc x)
      · exact Or.inr fun x _ => hc x
    exact M.absorbR r hr v0 (hp v0 hv0p) hd z (by rw [hc, hc]) ⟨0, hm⟩ hv0 (fun _ _ => rfl)
  have hand' : ∀ (r : ℕ) (_ : r < gates.length) (a b : Fin n), a ≠ p → a ≠ b →
      (∀ x : Fin n → Bool, val gates x (n + r) = (x a && x b)) → False := by
    intro r hr a b hap hne hab
    have hd : DCp a gates r ∨ DTr a gates r :=
      Or.inl (dcp_of_false a gates r fun x hx => by rw [hab, hx]; rfl)
    obtain ⟨w, hw⟩ := hset r hr a hap hd
    exact M.absorbR r hr a (hp a hap) hd z
      (by rw [hab, hab]; simp [hzdef, Function.update_of_ne hne.symm]) w hw (fun _ _ => rfl)
  have hand : ∀ (r : ℕ) (_ : r < gates.length) (a b : Fin n), a ≠ b →
      (∀ x : Fin n → Bool, val gates x (n + r) = (x a && x b)) → False := by
    intro r hr a b hne hab
    by_cases hap : a = p
    · exact hand' r hr b a (fun e => hne (hap.trans e.symm)) hne.symm
        (fun x => by rw [hab, Bool.and_comm])
    · exact hand' r hr a b hap hne hab
  have hor' : ∀ (r : ℕ) (_ : r < gates.length) (a b : Fin n), a ≠ p → a ≠ b →
      (∀ x : Fin n → Bool, val gates x (n + r) = (x a || x b)) → False := by
    intro r hr a b hap hne hab
    have hd : DCp a gates r ∨ DTr a gates r :=
      Or.inl ⟨b, by have := b.2; omega, fun x hx => by
        rw [hab, hx, val_inp _ _ _ b.2]; simp⟩
    obtain ⟨hda, -⟩ := M.dc1_facts (hp a hap) r hr hd
    obtain ⟨w, hw, hbw⟩ := M.avoid hda b hne
    refine M.absorbR r hr a (hp a hap) hd (Function.update z b true) ?_ w hw ?_
    · rw [hab, hab]; simp [Function.update_of_ne hne]
    · intro v hv
      rw [Function.update_of_ne (fun e : v = b => hbw (e ▸ hv))]
  have hor : ∀ (r : ℕ) (_ : r < gates.length) (a b : Fin n), a ≠ b →
      (∀ x : Fin n → Bool, val gates x (n + r) = (x a || x b)) → False := by
    intro r hr a b hne hab
    by_cases hap : a = p
    · exact hor' r hr b a (fun e => hne (hap.trans e.symm)) hne.symm
        (fun x => by rw [hab, Bool.or_comm])
    · exact hor' r hr a b hap hne hab
  have hcopy : ∀ a : Fin n, (∀ x : Fin n → Bool, val gates x n = x a) → False :=
    fun a ha => M.clean 0 a hpos (by have := a.2; omega)
      (fun x => by rw [val_inp _ _ _ a.2]; exact ha x)
  have hnot' : (gates[0]'hpos).op = GateOp.not → ∀ a : Fin n, a ≠ p →
      (∀ x : Fin n → Bool, val gates x n = !x a) → False := by
    intro hop a hap hna
    have hd : DCp a gates 0 ∨ DTr a gates 0 :=
      Or.inr fun x hx => by
        show val gates x n = true
        rw [hna, hx]; rfl
    obtain ⟨w, hw⟩ := hset 0 hpos a hap hd
    have huniq := (M.dc1_facts (hp a hap) 0 hpos hd).2
    have hseen : ∀ y : Fin n → Bool, y a = false → ∀ k, val (gates.take k) y a = false := by
      intro y hy k
      rw [val_inp _ _ _ a.2]; exact hy
    refine absorb_anti S gates out C.h2 C.hev C.hg C.hU a 0 hpos hop
      (fun k hk hk0 hmem => huniq k hk hk0 ?_) z (fun _ => ?_) w hw (fun _ _ => rfl)
    · have hgk := C.hg _ (List.getElem_mem hk)
      have hao : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or := by
        rcases hgk.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (C.hU k 0 hk hpos h hop) hk0
      exact dead_of_andor a gates k hk hao hgk.2 a hmem false (fun y hy => hseen y hy k)
    · show val gates z n = true
      rw [hna]; rfl
  -- second stage: the first gate is `N = ¬ x_p`
  have stage2 : (gates[0]'hpos).op = GateOp.not →
      (∀ x : Fin n → Bool, val gates x n = !x p) → False := by
    intro hop0 hN
    have h2len : 1 < gates.length := by
      by_contra hle
      refine absorb_eq S gates out C.h2 C.hev v0 0 (fun k hk hk0 => absurd hk (by omega)) z ?_
        ⟨0, hm⟩ hv0 (fun _ _ => rfl)
      show val gates z n = val gates (Function.update z v0 true) n
      rw [hN, hN]; simp [hzdef, Function.update_of_ne hv0p.symm]
    have hv1 : ∀ x : Fin n → Bool, val gates x (n + 1) = (gates[1]'h2len).op.eval
        ((gates[1]'h2len).inputs.map fun i =>
          if h : i < n then x ⟨i, h⟩ else if i = n then !x p else false) := by
      intro x
      rw [val_gate gates x 1 h2len]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h h'
      · rw [val_take gates x 1 i (by omega) (by omega), val_inp _ _ _ h]
      · rw [h', val_take gates x 1 n (by omega) (by omega), hN]
      · exact val_take_ge _ _ _ _ (by omega)
    have hgk := C.hg _ (List.getElem_mem h2len)
    have hao : (gates[1]'h2len).op = GateOp.and ∨ (gates[1]'h2len).op = GateOp.or := by
      rcases hgk.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (C.hU 1 0 h2len hpos h hop0) (by omega)
    have hlen := hgk.2
    have hcopyN : (∀ x : Fin n → Bool, val gates x (n + 1) = !x p) → False :=
      fun h => M.clean 1 n h2len (by omega) (fun x => by rw [h, hN])
    have hcopy1 : ∀ a : Fin n, (∀ x : Fin n → Bool, val gates x (n + 1) = x a) → False :=
      fun a ha => M.clean 1 a h2len (by have := a.2; omega)
        (fun x => by rw [val_inp _ _ _ a.2]; exact ha x)
    have hNor : ∀ v : Fin n, v ≠ p →
        (∀ x : Fin n → Bool, val gates x (n + 1) = (!x p || x v)) → False := by
      intro v hvp hf
      have hd : DCp v gates 1 ∨ DTr v gates 1 :=
        Or.inl ⟨n, by omega, fun x hx => by rw [hf, hx, hN]; simp⟩
      obtain ⟨w, hw⟩ := hset 1 h2len v hvp hd
      exact M.absorbR 1 h2len v (hp v hvp) hd z
        (by rw [hf, hf]; simp [hzdef, Function.update_of_ne hvp.symm]) w hw (fun _ _ => rfl)
    have hNand : ∀ v : Fin n, v ≠ p →
        (∀ x : Fin n → Bool, val gates x (n + 1) = (!x p && x v)) → False := by
      intro v hvp hf
      have hd : DCp v gates 1 ∨ DTr v gates 1 :=
        Or.inl (dcp_of_false v gates 1 fun x hx => by rw [hf, hx]; simp)
      obtain ⟨hdv, -⟩ := M.dc1_facts (hp v hvp) 1 h2len hd
      obtain ⟨w, hw, hpw⟩ := M.avoid hdv p hvp
      refine M.absorbR 1 h2len v (hp v hvp) hd (Function.update z p true) ?_ w hw ?_
      · rw [hf, hf]; simp [Function.update_of_ne hvp.symm]
      · intro t ht
        rw [Function.update_of_ne (fun e : t = p => hpw (e ▸ ht))]
    generalize gates[1]'h2len = g at hv1 hao hlen
    obtain ⟨op, ins⟩ := g
    simp only at hv1 hao hlen
    match ins, hlen with
    | [], _ =>
      rcases hao with rfl | rfl
      · exact hconst 1 h2len true (fun x => by simp [hv1, GateOp.eval])
      · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval])
    | [c], _ =>
      by_cases hc : c < n
      · rcases hao with rfl | rfl <;>
          exact hcopy1 ⟨c, hc⟩ (fun x => by simp [hv1, GateOp.eval, hc])
      · by_cases hcn : c = n
        · rcases hao with rfl | rfl <;>
            exact hcopyN (fun x => by simp [hv1, GateOp.eval, hcn])
        · rcases hao with rfl | rfl <;>
            exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hcn])
    | [c, d], _ =>
      by_cases hc : c < n
      · by_cases hd : d < n
        · by_cases hcd : c = d
          · subst hcd
            rcases hao with rfl | rfl <;>
              exact hcopy1 ⟨c, hc⟩ (fun x => by simp [hv1, GateOp.eval, hc])
          · have hne : (⟨c, hc⟩ : Fin n) ≠ ⟨d, hd⟩ := fun e => hcd (by simpa using e)
            rcases hao with rfl | rfl
            · exact hand 1 h2len _ _ hne (fun x => by simp [hv1, GateOp.eval, hc, hd])
            · exact hor 1 h2len _ _ hne (fun x => by simp [hv1, GateOp.eval, hc, hd])
        · by_cases hdn : d = n
          · by_cases hcp : (⟨c, hc⟩ : Fin n) = p
            · rcases hao with rfl | rfl
              · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hdn, hcp])
              · exact hconst 1 h2len true (fun x => by simp [hv1, GateOp.eval, hc, hdn, hcp])
            · rcases hao with rfl | rfl
              · exact hNand _ hcp (fun x => by simp [hv1, GateOp.eval, hc, hdn, Bool.and_comm])
              · exact hNor _ hcp (fun x => by simp [hv1, GateOp.eval, hc, hdn, Bool.or_comm])
          · rcases hao with rfl | rfl
            · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hd, hdn])
            · exact hcopy1 ⟨c, hc⟩ (fun x => by simp [hv1, GateOp.eval, hc, hd, hdn])
      · by_cases hcn : c = n
        · by_cases hd : d < n
          · by_cases hdp : (⟨d, hd⟩ : Fin n) = p
            · rcases hao with rfl | rfl
              · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hd, hcn, hdp])
              · exact hconst 1 h2len true (fun x => by simp [hv1, GateOp.eval, hd, hcn, hdp])
            · rcases hao with rfl | rfl
              · exact hNand _ hdp (fun x => by simp [hv1, GateOp.eval, hd, hcn])
              · exact hNor _ hdp (fun x => by simp [hv1, GateOp.eval, hd, hcn])
          · by_cases hdn : d = n
            · rcases hao with rfl | rfl <;>
                exact hcopyN (fun x => by simp [hv1, GateOp.eval, hcn, hdn])
            · rcases hao with rfl | rfl
              · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hcn, hd, hdn])
              · exact hcopyN (fun x => by simp [hv1, GateOp.eval, hcn, hd, hdn])
        · by_cases hd : d < n
          · rcases hao with rfl | rfl
            · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hcn, hd])
            · exact hcopy1 ⟨d, hd⟩ (fun x => by simp [hv1, GateOp.eval, hc, hcn, hd])
          · by_cases hdn : d = n
            · rcases hao with rfl | rfl
              · exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hcn, hdn])
              · exact hcopyN (fun x => by simp [hv1, GateOp.eval, hc, hcn, hdn])
            · rcases hao with rfl | rfl <;>
                exact hconst 1 h2len false (fun x => by simp [hv1, GateOp.eval, hc, hcn, hd, hdn])
    | _ :: _ :: _ :: _, h => simp at h
  have hnot : (gates[0]'hpos).op = GateOp.not → ∀ a : Fin n,
      (∀ x : Fin n → Bool, val gates x n = !x a) → False := by
    intro hop a hna
    by_cases hap : a = p
    · subst hap; exact stage2 hop hna
    · exact hnot' hop a hap hna
  have hconst0 : ∀ c : Bool, (∀ x : Fin n → Bool, val gates x n = c) → False :=
    fun c hc => hconst 0 hpos c hc
  have hv : ∀ x : Fin n → Bool, val gates x n = (gates[0]'hpos).op.eval
      ((gates[0]'hpos).inputs.map fun i => if h : i < n then x ⟨i, h⟩ else false) := by
    intro x
    have := val_gate gates x 0 hpos
    simp only [List.take_zero, val_nil, Nat.add_zero] at this
    exact this
  obtain ⟨hop, hlen⟩ := C.hg _ (List.getElem_mem hpos)
  clear hnot' stage2
  generalize gates[0]'hpos = g at hv hop hlen hnot
  obtain ⟨op, ins⟩ := g
  simp only at hv hop hlen hnot
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact hconst0 true (fun x => by simp [hv, GateOp.eval])
    · exact hconst0 false (fun x => by simp [hv, GateOp.eval])
    · exact hconst0 true (fun x => by simp [hv, GateOp.eval])
  | [a], _ =>
    by_cases ha : a < n
    · rcases hop with rfl | rfl | rfl
      · exact hcopy ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
      · exact hcopy ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
      · exact hnot rfl ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
    · rcases hop with rfl | rfl | rfl
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha])
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha])
      · exact hconst0 true (fun x => by simp [hv, GateOp.eval, ha])
  | [a, b], _ =>
    by_cases ha : a < n <;> by_cases hb : b < n
    · by_cases hab : a = b
      · subst hab
        rcases hop with rfl | rfl | rfl
        · exact hcopy ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
        · exact hcopy ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
        · exact hnot rfl ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
      · have hne : (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := fun e => hab (by simpa using e)
        rcases hop with rfl | rfl | rfl
        · exact hand 0 hpos ⟨a, ha⟩ ⟨b, hb⟩ hne (fun x => by simp [hv, GateOp.eval, ha, hb])
        · exact hor 0 hpos ⟨a, ha⟩ ⟨b, hb⟩ hne (fun x => by simp [hv, GateOp.eval, ha, hb])
        · exact hnot rfl ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
    · rcases hop with rfl | rfl | rfl
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hcopy ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hnot rfl ⟨a, ha⟩ (fun x => by simp [hv, GateOp.eval, ha])
    · rcases hop with rfl | rfl | rfl
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hcopy ⟨b, hb⟩ (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hconst0 true (fun x => by simp [hv, GateOp.eval, ha])
    · rcases hop with rfl | rfl | rfl
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hconst0 false (fun x => by simp [hv, GateOp.eval, ha, hb])
      · exact hconst0 true (fun x => by simp [hv, GateOp.eval, ha])
  | _ :: _ :: _ :: _, h => simp at h

/-- G1.2 (bottom lemma): a minimal counterexample has two distinct points with at least two gates
dead on `x_v := 0` each. -/
theorem two_heavy (M : MinCE S gates out) :
    ∃ u v : Fin n, u ≠ v ∧ 2 ≤ (DC u gates).card ∧ 2 ≤ (DC v gates).card := by
  classical
  by_contra H
  push Not at H
  have C := M.ce
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; have := C.hlt; simp at this
    · exact h
  obtain ⟨v0, -⟩ : (S ⟨0, hm⟩).Nonempty :=
    Finset.card_pos.mp (by have := C.h2 ⟨0, hm⟩; omega)
  by_cases hex : ∃ p : Fin n, 2 ≤ (DC p gates).card
  · obtain ⟨p, hpc⟩ := hex
    exact M.bottom_core p (fun v hvp => by have := H p v (Ne.symm hvp) hpc; omega)
  · push Not at hex
    exact M.bottom_core v0 (fun v _ => by have := hex v; omega)

/-- G1.2, degree form: two distinct points `u, v` with `base + 2 ≤ s + deg` (so `deg ≥ 2 + σ ≥ 3`). -/
theorem two_deg (M : MinCE S gates out) :
    ∃ u v : Fin n, u ≠ v ∧
      ∑ i : Fin m, ((S i).card - 1) + 2 ≤
        gates.length + (Finset.univ.filter fun w : Fin m => u ∈ S w).card ∧
      ∑ i : Fin m, ((S i).card - 1) + 2 ≤
        gates.length + (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  obtain ⟨u, v, huv, hu, hv⟩ := M.two_heavy
  have h1 := M.deadBound u (by omega)
  have h2 := M.deadBound v (by omega)
  exact ⟨u, v, huv, by omega, by omega⟩

/-- G1.2, corollary: two distinct points of degree `≥ 3`. -/
theorem two_deg3 (M : MinCE S gates out) :
    ∃ u v : Fin n, u ≠ v ∧ 3 ≤ (Finset.univ.filter fun w : Fin m => u ∈ S w).card ∧
      3 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  obtain ⟨u, v, huv, hu, hv⟩ := M.two_deg
  have := M.ce.hlt
  exact ⟨u, v, huv, by omega, by omega⟩

/-- G1.1: a minimal counterexample has a point of degree `≥ 3`. -/
theorem no_minCE_deg2 (M : MinCE S gates out) :
    ∃ v : Fin n, 3 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  obtain ⟨u, -, -, hu, -⟩ := M.two_deg3
  exact ⟨u, hu⟩

end MinCE

end PEqualNP.Outside.L_meta_951_aux
