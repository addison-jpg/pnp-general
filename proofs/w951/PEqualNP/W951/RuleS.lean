import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Peel

/-!
# Rule 's' (absorption at the singleton user), frontier15_log.md §2

`MinCE.rule_s`: if a point `u` is used as singleton by at least one single-reader point (through a
line or a pair-set, `Users S gates u ≠ ∅`), then `kL(u) ≤ l(u) - σ - 2`
(additively `base + kL(u) + 2 ≤ s + l(u)`).

Proof (as on paper; no case split `u ∈ B` / `u ∈ V1` is needed).  Otherwise rule 'p' is tight:
`nonpair(u) = 1` (unique non-pair reader `h`) and `DC(u) = N ∪ G ∪ L` exactly.  The other input
`c_v` of a user's reader is constant on `{x_u = 0}`, hence dead, hence `= h`; so `h` is not an OR
gate.  With `z = 1` on `P(u) ∪ UL(u)` and a line `L₀ ∋ u` avoiding `UL(u)`:
* `h = ¬x_u`: every wire is antitone in `x_u` at `z` (the pair gates are `1`), but `OR(L₀)` rises;
* `h = x_u ∧ y`: every later reader of `h` dies and is no reader of `x_u`, so it is a `g_w`
  (then it is `h ∨ x_w`) or an `r_v` (then it is `x_v ∨ h`): all are `1` at `z` whatever `x_u`
  is, so no wire except `x_u`, `h` moves, but `OR(L₀)` does.
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- Inputs that agree off `x_u` agree at every wire except `u` and gate `h`, if every other gate
agrees outright or does not depend on what it reads at `u` and (when it is above `h`) at `h`. -/
theorem val_congr_off2 {n : ℕ} (u : Fin n) (h : ℕ) (gates : List Gate) (x y : Fin n → Bool)
    (hxy : ∀ v, v ≠ u → x v = y v)
    (H : ∀ (k : ℕ) (hk : k < gates.length), k ≠ h →
      val gates x (n + k) = val gates y (n + k) ∨
      ∀ f f' : ℕ → Bool, (∀ i, i ≠ (u : ℕ) → (h < k → i ≠ n + h) → f i = f' i) →
        (gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f) =
          (gates[k]'hk).op.eval ((gates[k]'hk).inputs.map f')) :
    ∀ i, i ≠ (u : ℕ) → i ≠ n + h → val gates x i = val gates y i := by
  have key : ∀ k, k ≤ gates.length → ∀ i, i ≠ (u : ℕ) → (h < k → i ≠ n + h) →
      val (gates.take k) x i = val (gates.take k) y i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi _
      simp only [List.take_zero, val_nil]
      by_cases hin : i < n
      · rw [dif_pos hin, dif_pos hin]; exact hxy _ (fun e => hi (by rw [← e]))
      · rw [dif_neg hin, dif_neg hin]
    | succ k ih =>
      intro hk i hi hih
      have hk' : k < gates.length := by omega
      have htk : gates.take (k + 1) = gates.take k ++ [gates[k]'hk'] :=
        List.take_succ_eq_append_getElem hk'
      have hl : (gates.take k).length = k := by simp; omega
      rw [htk, val_snoc, val_snoc, hl]
      by_cases hik : i = n + k
      · rw [if_pos hik, if_pos hik]
        have hkh : k ≠ h := by rintro rfl; exact hih (by omega) hik
        rcases H k hk' hkh with hl' | hr
        · rw [val_gate gates x k hk', val_gate gates y k hk'] at hl'; exact hl'
        · exact hr _ _ (fun j hj hjh => ih (by omega) j hj hjh)
      · rw [if_neg hik, if_neg hik]
        exact ih (by omega) i hi (fun hlt => hih (by omega))
  intro i hi hih
  have := key gates.length le_rfl i hi (fun _ => hih)
  rwa [List.take_length] at this

/-- The lowest gate `k` restricting to `x_w` on `{x_u = 0}`, if it reads a lower gate `h` that
vanishes on `{x_u = 0}`, is `h ∨ x_w`; in particular it is `1` wherever `x_w = 1`. -/
theorem lowest_reads_zero {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (u w : Fin n) (huw : u ≠ w) (h k : ℕ) (hk : k < gates.length)
    (hhk : h < k)
    (hz : ∀ x : Fin n → Bool, x u = false → val gates x (n + h) = false)
    (hres : ∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w)
    (hlow : ∀ k', k' < k → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w)
    (hW : k ∈ WReaders (n + h) gates) :
    ∀ x : Fin n → Bool, x w = true → val gates x (n + k) = true := by
  classical
  set ew : Fin n → Bool := fun t => decide (t = w) with hewdef
  have hewu : ew u = false := by simp [hewdef, huw]
  have hew : ew w = true := by simp [hewdef]
  have hG : ∀ x : Fin n → Bool, val (gates.take k) x (n + h) = val gates x (n + h) := fun x =>
    val_take gates x k (n + h) (by omega) (by omega)
  have hcw : ∀ c : ℕ, (∀ x : Fin n → Bool, x u = false → val (gates.take k) x c = x w) →
      ∀ x : Fin n → Bool, x w = true → val (gates.take k) x c = true := by
    intro c hC x hxw
    by_cases hcn : c < n
    · have h1 := hC ew hewu
      rw [val_inp _ _ _ hcn, hew] at h1
      have h2 : (⟨c, hcn⟩ : Fin n) = w := by simpa [hewdef] using h1
      rw [val_inp _ _ _ hcn, h2]; exact hxw
    · by_cases hck : c < n + k
      · exfalso
        apply hlow (c - n) (by omega)
        intro x hx
        rw [show n + (c - n) = c by omega, ← val_take gates x k c (by omega) hck]
        exact hC x hx
      · exfalso
        have h1 := hC ew hewu
        rw [val_take_ge _ _ _ _ (by omega), hew] at h1
        exact absurd h1 (by simp)
  have hv := fun x : Fin n → Bool => val_gate gates x k hk
  obtain ⟨_, hd⟩ := (mem_wreaders _ _ _).mp hW
  have hlen := (hg _ (List.getElem_mem hk)).2
  have hA := hres ew hewu
  have hB := hres (fun _ => false) rfl
  rw [hv, hew] at hA
  rw [hv] at hB
  generalize gates[k]'hk = g at hd hlen hv hA hB
  obtain ⟨op, ins⟩ := g
  simp only at hd hlen hv hA hB
  rcases hd with ⟨hao, hin⟩ | ⟨hn, rest, hin⟩
  · match ins, hlen with
    | [], _ => simp at hin
    | [a], _ =>
      simp only [List.mem_singleton] at hin
      subst hin
      exfalso
      rcases hao with rfl | rfl <;> simp [GateOp.eval, hG, hz ew hewu] at hA
    | [a, c], _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl <;> rcases hao with rfl | rfl
      · exfalso; simp [GateOp.eval, hG, hz ew hewu] at hA
      · have hC : ∀ x : Fin n → Bool, x u = false → val (gates.take k) x c = x w := by
          intro x hx
          have := hres x hx
          rw [hv] at this
          simpa [GateOp.eval, hG, hz x hx] using this
        intro x hxw
        rw [hv]
        simp [GateOp.eval, hcw c hC x hxw]
      · exfalso; simp [GateOp.eval, hG, hz ew hewu] at hA
      · have hC : ∀ x : Fin n → Bool, x u = false → val (gates.take k) x a = x w := by
          intro x hx
          have := hres x hx
          rw [hv] at this
          simpa [GateOp.eval, hG, hz x hx] using this
        intro x hxw
        rw [hv]
        simp [GateOp.eval, hcw a hC x hxw]
    | _ :: _ :: _ :: _, h => simp at h
  · exfalso
    subst hn
    rw [hin] at hB
    simp [GateOp.eval, hG, hz (fun _ => false) rfl] at hB

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

open Classical in
/-- Tight rule 'p' with one non-pair reader: if `kL(u) ≥ l(u) - σ - 1`
(`s + l(u) < base + kL(u) + 2`), then `x_u` has exactly one non-pair reader `h`, and every gate
dead under `x_u := 0` that is not a reader of `x_u` is a lowest gate `g_w` (`{u, w}` a pair-set)
or the reader `r_v` of a line user `v`. -/
theorem tight_decomp (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (hcon : gates.length + lineDeg S u < baseOf S + (LineUsers S gates u).card + 2) :
    ∃ h, h < gates.length ∧ h ∈ Readers u gates ∧
      (∀ k ∈ Readers u gates, k ≠ h →
        ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) ∧
      (¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates h u w) ∧
      ∀ k ∈ DC u gates, k ∉ Readers u gates →
        (∃ (w : Fin n) (i : Fin m), S i = {u, w} ∧ k < gates.length ∧
          (∀ x : Fin n → Bool, x u = false → val gates x (n + k) = x w) ∧
          ∀ k', k' < k → ¬ ∀ x : Fin n → Bool, x u = false → val gates x (n + k') = x w) ∨
        (∃ v ∈ LineUsers S gates u, k = rdr gates v) := by
  have C := M.ce
  obtain ⟨hcnt, hpk⟩ := M.rule_p_kL u hu
  have hlb := M.line_bound u hu
  have hslt : gates.length < baseOf S := C.hlt
  have hl2 : 1 ≤ lineDeg S u := by omega
  have hnp := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u hl2
  have hd := deg_split S C.h2 u
  obtain ⟨G, hGsub, hGc, hLsub, hLcard, hNG, hNL, hGL, hGspec⟩ := M.pkL_sets u
  set N := (Readers u gates).filter
    (fun k => ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w) with hN
  set L := (LineUsers S gates u).image (rdr gates) with hL
  have hNc : N.card = nonpair S gates u := by unfold nonpair; rfl
  have hNsub : N ⊆ DC u gates :=
    (Finset.filter_subset _ _).trans (readers_sub_DC u gates C.hg)
  have hdb : baseOf S + (DC u gates).card ≤ gates.length + degOf S u :=
    M.deadBound u (by omega)
  have hN1 : N.card = 1 := by omega
  have hDCeq : N ∪ G ∪ L = DC u gates := by
    apply Finset.eq_of_subset_of_card_le
      (Finset.union_subset (Finset.union_subset hNsub hGsub) hLsub)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hNL, hGL⟩),
      Finset.card_union_of_disjoint hNG, hGc, hLcard, hNc]
    omega
  obtain ⟨h, hNh⟩ := Finset.card_eq_one.mp hN1
  have hhN : h ∈ N := by rw [hNh]; simp
  have hhR : h ∈ Readers u gates := (Finset.mem_filter.mp hhN).1
  obtain ⟨hhl, -⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hhR)
  refine ⟨h, hhl, hhR, fun k hk hkh => ?_, (Finset.mem_filter.mp hhN).2, fun k hk hkR => ?_⟩
  · by_contra hp
    have : k ∈ N := Finset.mem_filter.mpr ⟨hk, hp⟩
    rw [hNh] at this
    exact hkh (Finset.mem_singleton.mp this)
  · rw [← hDCeq] at hk
    simp only [Finset.mem_union] at hk
    rcases hk with (hk | hk) | hk
    · exact absurd (Finset.mem_filter.mp hk).1 hkR
    · exact Or.inl (hGspec k hk)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
      exact Or.inr ⟨v, hv, rfl⟩

/-- In the tight situation of `tight_decomp`, the unique non-pair reader `h` of `x_u` is an OR
gate.  (`h = ¬x_u`: every wire is antitone in `x_u` at `z = 1` on `P(u) ∪ UL(u)`; `h = x_u ∧ y`:
every later reader of `h` is `1` at `z` whatever `x_u` is; but a line through `u` avoiding the
line users moves.) -/
theorem tight_nonOr_false (M : MinCE S gates out) (u : Fin n) (hu : ∃ i, u ∈ S i)
    (hcon : gates.length + lineDeg S u < baseOf S + (LineUsers S gates u).card + 2)
    (h : ℕ) (hhl : h < gates.length) (hhR : h ∈ Readers u gates)
    (hnp' : ¬ ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates h u w)
    (hop : (gates[h]'hhl).op ≠ GateOp.or) : False := by
  classical
  have C := M.ce
  obtain ⟨h', -, -, hpairs, -, hdec⟩ := M.tight_decomp u hu hcon
  have hh' : h = h' := by
    by_contra hne
    exact hnp' (hpairs h hhR hne)
  subst hh'
  obtain ⟨hcnt, hpk⟩ := M.rule_p_kL u hu
  have hlb := M.line_bound u hu
  have hslt : gates.length < baseOf S := C.hlt
  have hl2 : 1 ≤ lineDeg S u := by omega
  have hnp := nonpair_pos S gates out C.h2 C.hS C.hev C.hg u hl2
  have hLU : ∀ v ∈ LineUsers S gates u, ∃ i, 3 ≤ (S i).card ∧ UsesVia S gates u v i :=
    fun v hv => by simpa [LineUsers] using hv
  have huw : ∀ (w : Fin n) (i : Fin m), S i = {u, w} → u ≠ w := by
    intro w i hi e; have := C.h2 i; rw [hi, e] at this; simp at this
  -- a line through `u` avoiding the line users
  have hkLlt : (LineUsers S gates u).card < lineDeg S u := by omega
  obtain ⟨iL, hiL1, hiL3, hiLU⟩ : ∃ i, u ∈ S i ∧ 3 ≤ (S i).card ∧
      ∀ v ∈ LineUsers S gates u, v ∉ S i := by
    set Lines := Finset.univ.filter fun i : Fin m => u ∈ S i ∧ 3 ≤ (S i).card with hLines
    set T := Lines.filter fun i => ∃ v ∈ LineUsers S gates u, v ∈ S i with hT
    have hTc : T.card ≤ (LineUsers S gates u).card := by
      let f : Fin m → Fin n := fun i =>
        if hh : ∃ v ∈ LineUsers S gates u, v ∈ S i then Classical.choose hh else u
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        have hh := (Finset.mem_filter.mp hi).2
        simp only [f, dif_pos hh]
        exact (Classical.choose_spec hh).1
      · intro i hi j hj hij
        have hhi := (Finset.mem_filter.mp hi).2
        have hhj := (Finset.mem_filter.mp hj).2
        have hui := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.1
        have huj := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2.1
        simp only [f, dif_pos hhi, dif_pos hhj] at hij
        obtain ⟨hv1, hv2⟩ := Classical.choose_spec hhi
        have hv2' := (Classical.choose_spec hhj).2
        rw [← hij] at hv2'
        obtain ⟨i', -, hi'⟩ := hLU _ hv1
        have hvu := hi'.1
        by_contra hne
        have hsub : ({u, Classical.choose hhi} : Finset (Fin n)) ⊆ S i ∩ S j := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hui, huj⟩
          · exact Finset.mem_inter.mpr ⟨hv2, hv2'⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_pair (Ne.symm hvu)] at this
        have := C.hS i j hne
        omega
    have hLc : Lines.card = lineDeg S u := rfl
    obtain ⟨i, hiLn, hiT⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (by omega : T.card < Lines.card)
    have hi2 := (Finset.mem_filter.mp hiLn).2
    exact ⟨i, hi2.1, hi2.2, fun v hv hvi => hiT (Finset.mem_filter.mpr ⟨hiLn, v, hv, hvi⟩)⟩
  -- the input `z = 1` on `P(u) ∪ UL(u)`
  set z : Fin n → Bool := fun t => decide ((∃ i, S i = {u, t}) ∨ t ∈ LineUsers S gates u)
    with hzdef
  have hzL : ∀ t ∈ S iL, z t = false := by
    intro t ht
    simp only [hzdef, decide_eq_false_iff_not]
    rintro (⟨i, hi⟩ | hLu)
    · have hut := huw t i hi
      have hne : i ≠ iL := by
        intro e; subst e
        rw [hi, Finset.card_pair hut] at hiL3; omega
      have hsub : ({u, t} : Finset (Fin n)) ⊆ S i ∩ S iL := by
        intro a ha
        rw [Finset.mem_inter]
        refine ⟨by rw [hi]; exact ha, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hiL1
        · exact ht
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hut] at this
      have := C.hS i iL hne
      omega
    · exact hiLU t hLu ht
  have hzu : z u = false := hzL u hiL1
  have hzP : ∀ w : Fin n, (∃ i, S i = {u, w}) → z w = true := fun w hw => by
    simp only [hzdef, decide_eq_true_eq]; exact Or.inl hw
  have hzU : ∀ v ∈ LineUsers S gates u, z v = true := fun v hv => by
    simp only [hzdef, decide_eq_true_eq]; exact Or.inr hv
  set y := Function.update z u true with hydef
  have hzy : ∀ v, v ≠ u → z v = y v := fun v hv => by rw [hydef, Function.update_of_ne hv]
  have hout : val gates z (out iL) ≠ val gates y (out iL) := by
    have e1 : decide (∃ v ∈ S iL, z v = true) = false := by
      simp only [decide_eq_false_iff_not]
      rintro ⟨v, hv, hx⟩
      rw [hzL v hv] at hx; exact absurd hx (by simp)
    have e2 : decide (∃ v ∈ S iL, y v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨u, hiL1, by rw [hydef, Function.update_self]⟩
    rw [C.hev, C.hev, e1, e2]; simp
  have hpairR : ∀ k ∈ Readers u gates, k ≠ h →
      val gates z (n + k) = true ∧ val gates y (n + k) = true := by
    intro k hk hkh
    by_cases hp : ∃ w : Fin n, (∃ i, S i = {u, w}) ∧ IsPairGate gates k u w
    · obtain ⟨w, ⟨i, hi⟩, hpg⟩ := hp
      have hw := hzP w ⟨i, hi⟩
      rw [val_pairGate gates k u w hpg, val_pairGate gates k u w hpg,
        ← hzy w (huw w i hi).symm, hw]
      simp
    · exact absurd (hpairs k hk hkh) hp
  rcases reader_const u gates C.hg h hhl hhR hop with ⟨-, hle⟩ | ⟨hnot, hneg⟩
  · -- `h = x_u ∧ y`
    have hh0 : ∀ x : Fin n → Bool, x u = false → val gates x (n + h) = false := by
      intro x hx
      cases hv : val gates x (n + h)
      · rfl
      · rw [hle x hv] at hx; exact absurd hx (by simp)
    apply hout
    refine val_congr_off2 u h gates z y hzy (fun k hk hkh => ?_) (out iL)
      (out_ne_inp S gates out C.h2 C.hev iL u) (M.reader_not_out u h hhl hhR hop iL)
    by_cases hkR : k ∈ Readers u gates
    · left
      obtain ⟨a, b⟩ := hpairR k hkR hkh
      rw [a, b]
    by_cases hkW : h < k ∧ k ∈ WReaders (n + h) gates
    · left
      have hkDC : k ∈ DC u gates := wreaders_sub_DC u gates C.hg h false hh0 hkW.2
      rcases hdec k hkDC hkR with ⟨w, i, hi, hkl, hres, hlow⟩ | ⟨v, hv, rfl⟩
      · have key := lowest_reads_zero gates C.hg u w (huw w i hi) h k hkl hkW.1 hh0 hres hlow
          hkW.2
        rw [key z (hzP w ⟨i, hi⟩),
          key y (by rw [← hzy w (huw w i hi).symm]; exact hzP w ⟨i, hi⟩)]
      · obtain ⟨i, -, hi⟩ := hLU v hv
        have hvu : v ≠ u := hi.1
        obtain ⟨c, b, -, -, hW, hform, hcc⟩ := M.uses_core u v i hi
        have hcn : c = n + h := by
          rcases hW _ hkW.2 with e | e
          · have := v.2; omega
          · exact e.symm
        have hb : b = false := by
          have := hcc z hzu
          rw [hcn, hh0 z hzu] at this
          exact this.symm
        rw [hform z, hform y, hb, ← hzy v hvu, hzU v hv]
        simp
    · right
      intro f f' hff
      have hkey : ∀ a, k ∈ WReaders a gates → f a = f' a := by
        intro a ha
        apply hff a
        · rintro rfl; exact hkR (by rw [readers_eq_wreaders]; exact ha)
        · intro hlt e; subst e; exact hkW ⟨hlt, ha⟩
      rcases (C.hg _ (List.getElem_mem hk)).1 with hop' | hop' | hop'
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
  · -- `h = ¬x_u`
    have key := rel_prop (fun a b => b = true → a = true) (fun _ h => h) u gates z y hzy
      (fun k hk => by
        by_cases hkh : k = h
        · left
          subst hkh
          intro hy
          rw [hneg y, hydef, Function.update_self] at hy
          exact absurd hy (by simp)
        · by_cases hkR : k ∈ Readers u gates
          · exact Or.inl fun _ => (hpairR k hkR hkh).1
          · right
            intro f f' hff
            have hao : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or := by
              rcases (C.hg _ (List.getElem_mem hk)).1 with h' | h' | h'
              · exact Or.inl h'
              · exact Or.inr h'
              · exact absurd (C.hU k h hk hhl h' hnot) hkh
            exact andor_mono _ hao f f' (fun i hi => hff i (fun e => hkR (by
              rw [readers_eq_wreaders]
              exact (mem_wreaders _ _ _).mpr ⟨hk, Or.inl ⟨hao, e ▸ hi⟩⟩))))
      (out iL) (out_ne_inp S gates out C.h2 C.hev iL u)
    have e1 : decide (∃ v ∈ S iL, z v = true) = false := by
      simp only [decide_eq_false_iff_not]
      rintro ⟨v, hv, hx⟩
      rw [hzL v hv] at hx; exact absurd hx (by simp)
    have e2 : decide (∃ v ∈ S iL, y v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨u, hiL1, by rw [hydef, Function.update_self]⟩
    rw [C.hev, C.hev, e1, e2] at key
    exact absurd (key rfl) (by simp)


/-- Rule 's' (absorption at the singleton user, any `σ`): a point `u` used as singleton by at
least one single-reader point has `kL(u) ≤ l(u) - σ - 2`, i.e. `base + kL(u) + 2 ≤ s + l(u)`. -/
theorem rule_s (M : MinCE S gates out) (u : Fin n) (hU : (Users S gates u).Nonempty) :
    baseOf S + (LineUsers S gates u).card + 2 ≤ gates.length + lineDeg S u := by
  classical
  by_contra hcon
  push Not at hcon
  have C := M.ce
  obtain ⟨v0, hv0⟩ := hU
  obtain ⟨i0, hi0⟩ : ∃ i, UsesVia S gates u v0 i := by simpa [Users] using hv0
  have hu : ∃ i, u ∈ S i := ⟨i0, hi0.2.1⟩
  obtain ⟨h, hhl, hhR, hpairs, hnp', hdec⟩ := M.tight_decomp u hu hcon
  obtain ⟨_, hhd⟩ := (mem_wreaders _ _ _).mp (by rw [← readers_eq_wreaders]; exact hhR)
  have hLU : ∀ v ∈ LineUsers S gates u, ∃ i, 3 ≤ (S i).card ∧ UsesVia S gates u v i :=
    fun v hv => by simpa [LineUsers] using hv
  have huw : ∀ (w : Fin n) (i : Fin m), S i = {u, w} → u ≠ w := by
    intro w i hi e; have := C.h2 i; rw [hi, e] at this; simp at this
  have hnc : ∀ (j : ℕ) (b : Bool) (w : Fin n), w ≠ u →
      (∀ x : Fin n → Bool, x u = false → val gates x j = b) →
      (∀ x : Fin n → Bool, x u = false → val gates x j = x w) → False := by
    intro j b w hwu hc hvr
    have hu0 : (fun t : Fin n => decide (t = w)) u = false := by
      simp only [decide_eq_false_iff_not]; exact fun e => hwu e.symm
    have h1 := hc (fun t => decide (t = w)) hu0
    have h0 := hc (fun _ => false) rfl
    rw [hvr _ hu0] at h1
    rw [hvr _ rfl] at h0
    have h1' : b = true := by simpa using h1.symm
    have h0' : b = false := by simpa using h0.symm
    rw [h1'] at h0'; exact absurd h0' (by simp)
  -- the other input of the reader of the user `v0` is the unique non-pair reader `h`
  obtain ⟨c0, b0, hc1, hc2, -, -, hc0⟩ := M.uses_core u v0 i0 hi0
  have hrl : rdr gates v0 < gates.length := by
    have := (M.peel_dead u v0 i0 hi0).1
    simp only [DC, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have hc0' : ∀ x : Fin n → Bool, x u = false → val gates x (n + (c0 - n)) = b0 := fun x hx => by
    rw [show n + (c0 - n) = c0 by omega]; exact hc0 x hx
  have hc0DC : c0 - n ∈ DC u gates := by
    simp only [DC, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    cases b0
    · exact Or.inl (dcp_of_false u gates _ hc0')
    · exact Or.inr hc0'
  have hc0eq : c0 - n = h := by
    by_contra hne
    by_cases hR : c0 - n ∈ Readers u gates
    · obtain ⟨w, ⟨i, hi⟩, hpg⟩ := hpairs _ hR hne
      exact hnc _ b0 w (huw w i hi).symm hc0' fun x hx => by
        rw [val_pairGate gates (c0 - n) u w hpg x, hx]; simp
    · rcases hdec _ hc0DC hR with ⟨w, i, hi, -, hres, -⟩ | ⟨v, hv, hk⟩
      · exact hnc _ b0 w (huw w i hi).symm hc0' hres
      · obtain ⟨i, -, hi⟩ := hLU v hv
        exact hnc _ b0 v hi.1 hc0' (by rw [hk]; exact (M.peel_dead u v i hi).2.2.1)
  have hhc : ∀ x : Fin n → Bool, x u = false → val gates x (n + h) = b0 := fun x hx => by
    rw [← hc0eq]; exact hc0' x hx
  -- `h` is not an OR gate
  refine M.tight_nonOr_false u hu hcon h hhl hhR hnp' fun hor => ?_
  have hin : (u : ℕ) ∈ (gates[h]'hhl).inputs := by
    rcases hhd with ⟨-, h'⟩ | ⟨hn, -⟩
    · exact h'
    · rw [hor] at hn; exact absurd hn (by simp)
  have h1 : ∀ x : Fin n → Bool, x u = true → val gates x (n + h) = true := by
    intro x hx
    rw [val_gate gates x h hhl, hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨_, ⟨u, hin, rfl⟩, by rw [val_inp _ _ _ u.2]; exact hx⟩
  cases b0
  · refine M.clean h (u : ℕ) hhl (by have := u.2; omega) fun x => ?_
    rw [val_inp _ _ _ u.2]
    cases hx : x u
    · exact hhc x hx
    · exact h1 x hx
  · refine M.no_const h hhl true fun x => ?_
    cases hx : x u
    · exact hhc x hx
    · exact h1 x hx

end MinCE

end PEqualNP.Outside.L_meta_951_aux
