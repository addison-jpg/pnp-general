import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCE

/-!
# Minimality facts of SORRY_DISSECTION §2: output deletion (B8(3)) and R0 quantitative (N2)

`prune`: gates outside a set `K` of gate indices that is closed under past reads can be deleted
(one at a time, the largest first, by `val_dropIns`) without changing the wires of `K`, inputs
and out-of-range wires.  `MinCE.outDel`: in a minimal counterexample, for every nonempty family `F`
of outputs, `#gates outside every cone of F^c < ∑_{w ∈ F} (|S w| - 1)`.
`readers_sub_DC`: gates reading `x_v` are dead on `x_v := 0`.  `MinCE.deadBound` (N2, quantitative R0):
`base + #DC(v) ≤ s + deg v` (i.e. `#dead(x_v:=0) ≤ deg v - σ`) whenever `#DC(v) ≥ 1`.  No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- `K` (gate indices) is closed under past reads of its own gates. -/
def PastClosed (n : ℕ) (K : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ (i : ℕ) (hi : i < gs.length), i ∈ K → ∀ j ∈ (gs[i]'hi).inputs, n ≤ j → j < n + i → j - n ∈ K

theorem dropGate_getElem_lt (gates : List Gate) (k j n i : ℕ) (hk : k < gates.length)
    (hi : i < (dropGate gates k j n).length) (hik : i < k) :
    (dropGate gates k j n)[i]'hi = gates[i]'(by have := dropGate_length gates k j n hk; omega) := by
  simp [dropGate, List.getElem_append_left (show i < (gates.take k).length by simp; omega)]

theorem dropGate_getElem_ge (gates : List Gate) (k j n i : ℕ) (hk : k < gates.length)
    (hi : i < (dropGate gates k j n).length) (hik : k ≤ i) :
    (dropGate gates k j n)[i]'hi =
      redirG (n + k) j (gates[i + 1]'(by have := dropGate_length gates k j n hk; omega)) := by
  have hl : (gates.take k).length = k := by simp; omega
  have hge : ¬ i < (gates.take k).length := by rw [hl]; omega
  simp only [dropGate, List.getElem_append, hge, dite_false, List.getElem_map, List.getElem_drop]
  congr 2
  rw [hl]; omega

/-- Pruning: all gates outside `K` can be deleted. -/
theorem prune (n : ℕ) : ∀ (d : ℕ) (gates : List Gate) (K : Finset ℕ),
    K ⊆ Finset.range gates.length → gates.length = K.card + d →
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) → AtMostOneNot gates → PastClosed n K gates →
    ∀ {m' : ℕ} (out : Fin m' → ℕ),
      (∀ w, out w < n ∨ (n ≤ out w ∧ out w - n ∈ K) ∨ n + gates.length ≤ out w) →
    ∃ (gates' : List Gate) (out' : Fin m' → ℕ), gates'.length = K.card ∧
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧ AtMostOneNot gates' ∧
      ∀ (w : Fin m') (x : Fin n → Bool), val gates' x (out' w) = val gates x (out w) := by
  intro d
  induction d with
  | zero =>
    intro gates K _ hlen hg hU _ m' out _
    exact ⟨gates, out, by omega, hg, hU, fun _ _ => rfl⟩
  | succ d ih =>
    intro gates K hK hlen hg hU hP m' out hout
    classical
    have hne : ((Finset.range gates.length) \ K).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      have := Finset.card_le_card hsub
      simp at this
      omega
    set k := ((Finset.range gates.length) \ K).max' hne with hkdef
    have hkmem : k ∈ (Finset.range gates.length) \ K := Finset.max'_mem _ _
    have hk : k < gates.length := by simp at hkmem; exact hkmem.1
    have hkK : k ∉ K := (Finset.mem_sdiff.mp hkmem).2
    have hmax : ∀ t, t < gates.length → k < t → t ∈ K := by
      intro t ht hkt
      by_contra htK
      have hmem : t ∈ (Finset.range gates.length) \ K := by simp [ht, htK]
      have := Finset.le_max' _ t hmem
      have e : ((Finset.range gates.length) \ K).max' ⟨t, hmem⟩ = k := rfl
      omega
    have hlen' := dropGate_length gates k 0 n hk
    set sh : ℕ → ℕ := fun t => if t < k then t else t - 1 with hsh
    set K' := K.image sh with hK'
    have hinj : Set.InjOn sh K := by
      intro a ha b hb hab
      have ha' : a ≠ k := fun e => hkK (e ▸ ha)
      have hb' : b ≠ k := fun e => hkK (e ▸ hb)
      simp only [hsh] at hab
      split_ifs at hab <;> omega
    have hcard : K'.card = K.card := Finset.card_image_of_injOn hinj
    have hmemK' : ∀ t ∈ K, sh t ∈ K' := fun t ht => Finset.mem_image_of_mem _ ht
    have hK'mem : ∀ i ∈ K', (i < k ∧ i ∈ K) ∨ (k ≤ i ∧ i + 1 ∈ K) := by
      intro i hi
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
      have ht' : t ≠ k := fun e => hkK (e ▸ ht)
      simp only [hsh]
      split_ifs with h
      · exact Or.inl ⟨h, ht⟩
      · right; refine ⟨by omega, ?_⟩
        have : t - 1 + 1 = t := by omega
        rw [this]; exact ht
    have hK'sub : K' ⊆ Finset.range (dropGate gates k 0 n).length := by
      intro i hi
      have := hK'mem i hi
      simp only [Finset.mem_range]
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · omega
      · have := hK h2; simp at this; omega
    have hnoread : ∀ g ∈ gates.drop (k + 1), Insens (n + k) g := by
      intro g hg0
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hg0
      simp only [List.length_drop] at ht
      rw [List.getElem_drop]
      apply insens_of_not_mem
      intro hr
      exact hkK (by
        have := hP (k + 1 + t) (by omega) (hmax _ (by omega) (by omega)) (n + k) hr (by omega)
          (by omega)
        simpa using this)
    have hP' : PastClosed n K' (dropGate gates k 0 n) := by
      intro i hi hiK j hj hnj hji
      rcases hK'mem i hiK with ⟨hik, hiK0⟩ | ⟨hik, hiK0⟩
      · rw [dropGate_getElem_lt gates k 0 n i hk hi hik] at hj
        have := hP i (by omega) hiK0 j hj hnj hji
        have e : sh (j - n) = j - n := by simp only [hsh]; split_ifs <;> omega
        rw [← e]; exact hmemK' _ this
      · rw [dropGate_getElem_ge gates k 0 n i hk hi hik] at hj
        simp only [redirG, List.mem_map] at hj
        obtain ⟨j0, hj0, rfl⟩ := hj
        unfold redir at hnj hji ⊢
        by_cases h1 : j0 < n + k
        · simp only [h1, ite_true] at hnj hji ⊢
          have := hP (i + 1) (by omega) hiK0 j0 hj0 hnj (by omega)
          have e : sh (j0 - n) = j0 - n := by simp only [hsh]; split_ifs <;> omega
          rw [← e]; exact hmemK' _ this
        · by_cases h2 : j0 = n + k
          · exfalso
            subst h2
            have := hP (i + 1) (by omega) hiK0 (n + k) hj0 (by omega) (by omega)
            exact hkK (by simpa using this)
          · simp only [h1, h2, ite_false] at hnj hji ⊢
            have := hP (i + 1) (by omega) hiK0 j0 hj0 (by omega) (by omega)
            have e : sh (j0 - n) = j0 - 1 - n := by
              simp only [hsh]; split_ifs <;> omega
            rw [← e]; exact hmemK' _ this
    have hout' : ∀ w, redir (n + k) 0 (out w) < n ∨
        (n ≤ redir (n + k) 0 (out w) ∧ redir (n + k) 0 (out w) - n ∈ K') ∨
        n + (dropGate gates k 0 n).length ≤ redir (n + k) 0 (out w) := by
      intro w
      unfold redir
      rcases hout w with h | ⟨h1, h2⟩ | h
      · left; simp only [show out w < n + k by omega, ite_true]; exact h
      · right; left
        have hne' : out w ≠ n + k := fun e => hkK (by rw [e] at h2; simpa using h2)
        by_cases h3 : out w < n + k
        · simp only [h3, ite_true]
          refine ⟨h1, ?_⟩
          have e : sh (out w - n) = out w - n := by simp only [hsh]; split_ifs <;> omega
          rw [← e]; exact hmemK' _ h2
        · simp only [h3, hne', ite_false]
          refine ⟨by omega, ?_⟩
          have e : sh (out w - n) = out w - 1 - n := by simp only [hsh]; split_ifs <;> omega
          rw [← e]; exact hmemK' _ h2
      · right; right
        simp only [show ¬ out w < n + k by omega, show out w ≠ n + k by omega, ite_false]
        omega
    obtain ⟨gates', out', hl', hg', hU', hv'⟩ := ih (dropGate gates k 0 n) K' hK'sub
      (by omega) (dropGate_hg gates k 0 n hg) (dropGate_hU gates k 0 n hk hU) hP'
      (fun w => redir (n + k) 0 (out w)) hout'
    refine ⟨gates', out', by omega, hg', hU', fun w x => ?_⟩
    rw [hv' w x]
    apply val_dropIns gates k 0 hk hnoread x (out w)
    intro e
    rcases hout w with h | ⟨_, h2⟩ | h
    · omega
    · exact hkK (by rw [e] at h2; simpa using h2)
    · omega

theorem coneOf_sub (n : ℕ) (gates : List Gate) (o : ℕ) :
    coneOf n gates o ⊆ Finset.range gates.length := by
  classical
  intro k hk
  simp only [coneOf, Finset.mem_filter] at hk
  exact hk.1

/-- B8(3), output deletion: in a minimal counterexample, for every nonempty family `F` of outputs,
the number of gates outside every cone of the complementary outputs is `< ∑_{w ∈ F} (|S w| - 1)`. -/
theorem MinCE.outDel {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) (F : Finset (Fin m)) (hF : F.Nonempty) :
    gates.length - ((Finset.univ.filter fun w => w ∉ F).biUnion
      fun w => coneOf n gates (out w)).card < ∑ w ∈ F, ((S w).card - 1) := by
  classical
  have C := M.ce
  set K := (Finset.univ.filter fun w => w ∉ F).biUnion fun w => coneOf n gates (out w) with hKdef
  have hK : K ⊆ Finset.range gates.length := by
    intro k hk
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hk
    exact coneOf_sub n gates (out w) hw
  have hKc : K.card ≤ gates.length := by
    have := Finset.card_le_card hK; simpa using this
  have hP : PastClosed n K gates := by
    intro i hi hiK j hj hnj hji
    obtain ⟨w, hwF, hw⟩ := Finset.mem_biUnion.mp hiK
    exact Finset.mem_biUnion.mpr ⟨w, hwF,
      coneOf_closed n gates (out w) i hi hw j hj hnj (by omega)⟩
  let A := {w : Fin m // w ∉ F}
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hout : ∀ i : Fin (Fintype.card A), out (e i).1 < n ∨
      (n ≤ out (e i).1 ∧ out (e i).1 - n ∈ K) ∨ n + gates.length ≤ out (e i).1 := by
    intro i
    rcases coneOf_out n gates (out (e i).1) with h | h | h
    · exact Or.inl h
    · by_cases h' : out (e i).1 < n
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨by omega, Finset.mem_biUnion.mpr ⟨(e i).1, by simp [(e i).2], h⟩⟩)
    · exact Or.inr (Or.inr h)
  obtain ⟨gates', out', hl', hg', hU', hv'⟩ := prune n (gates.length - K.card) gates K hK
    (by omega) C.hg C.hU hP (fun i => out (e i).1) hout
  have hsubsum : ∀ f : Fin m → ℕ, ∑ i : Fin (Fintype.card A), f (e i).1 =
      ∑ w ∈ Finset.univ.filter (fun w => w ∉ F), f w := by
    intro f
    exact PEqualNP.Base.Matching.sum_equivFin_subtype (fun w => w ∉ F) f
  have hsplit : ∀ f : Fin m → ℕ, ∑ w, f w =
      ∑ w ∈ F, f w + ∑ w ∈ Finset.univ.filter (fun w => w ∉ F), f w := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ F) f]
    congr 1
    congr 1
    ext w; simp
  have hbound : ∑ i : Fin (Fintype.card A), ((S (e i).1).card - 1) ≤ gates'.length := by
    by_contra hlt'
    push Not at hlt'
    refine M.min n _ (fun i => S (e i).1) gates' out'
      ⟨fun i => C.h2 _, fun i j hij => C.hS _ _ (fun h => hij (e.injective (Subtype.ext h))),
        hg', hU', fun w x => by rw [hv' w x]; exact C.hev _ x, hlt'⟩ ?_
    by_cases hlt : K.card < gates.length
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      unfold ceSize
      rw [hsubsum (fun w => (S w).card), hsplit (fun w => (S w).card)]
      obtain ⟨w0, hw0⟩ := hF
      have : 0 < ∑ w ∈ F, (S w).card :=
        Finset.sum_pos (fun w _ => by have := C.h2 w; omega) ⟨w0, hw0⟩
      omega
  rw [hsubsum (fun w => (S w).card - 1)] at hbound
  have := C.hlt
  rw [hsplit (fun w => (S w).card - 1)] at this
  omega

open Classical in
/-- Gates that read the input `x_v` effectively: AND/OR with `v` among the inputs, or NOT with
first input `v`. -/
noncomputable def Readers {n : ℕ} (v : Fin n) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k => ∃ hk : k < gates.length,
    (((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧ (v : ℕ) ∈ (gates[k]'hk).inputs) ∨
    ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = (v : ℕ) :: rest)

/-- N2, first half: every reader of `x_v` is dead on `x_v := 0`. -/
theorem readers_sub_DC {n : ℕ} (v : Fin n) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) : Readers v gates ⊆ DC v gates := by
  classical
  intro k hk
  simp only [Readers, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hk0, hk1, h⟩ := hk
  have hb : ∀ x : Fin n → Bool, x v = false → val (gates.take k) x (v : ℕ) = false := by
    intro x hx; rw [val_inp _ _ _ v.2]; exact hx
  have hd : DCp v gates k ∨ DTr v gates k := by
    rcases h with ⟨hop, hin⟩ | ⟨hop, rest, hin⟩
    · exact dead_of_andor v gates k hk1 hop (hg _ (List.getElem_mem hk1)).2 _ hin false hb
    · exact dead_of_not v gates k hk1 hop _ rest hin false hb
  simp only [DC, Finset.mem_filter, Finset.mem_range]
  exact ⟨hk0, hd⟩

/-- N2 (R0 quantitative): in a minimal counterexample, for every point `v` with
at least one gate dead on `x_v := 0`, `∑ (|S w| - 1) + #DC(v) ≤ #gates + deg v`.
(Extracted from `r0_step`, with `DC_lower` replaced by the hypothesis `1 ≤ #DC(v)`.) -/
theorem MinCE.deadBound {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) (v : Fin n)
    (hDC : 1 ≤ (DC v gates).card) :
    ∑ i : Fin m, ((S i).card - 1) + (DC v gates).card ≤
      gates.length + (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  classical
  have C := M.ce
  have h2 := C.h2
  have hS := C.hS
  have hev := C.hev
  set T : Fin m → Finset (Fin n) := fun w => (S w).erase v with hT
  let A := {w : Fin m // 2 ≤ (T w).card}
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hpb := promise_bound v gates.length
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) gates.length
    (Fintype.card A) (fun i => T (e i).1) gates (fun i => out (e i).1) rfl
    (fun i => by simp [hT]) (fun i => (e i).2)
    (fun i j hij => by
      have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
      refine le_trans (Finset.card_le_card ?_) (hS _ _ hne)
      intro t ht
      simp only [hT, Finset.mem_inter, Finset.mem_erase] at ht
      exact Finset.mem_inter.mpr ⟨ht.1.2, ht.2.2⟩)
    C.hg C.hU
    (fun i x hx => by
      rw [hev]
      congr 1
      apply propext
      constructor
      · rintro ⟨u, hu, hxu⟩
        refine ⟨u, ?_, hxu⟩
        simp only [hT, Finset.mem_erase]
        exact ⟨fun e' => by rw [e', hx] at hxu; exact absurd hxu (by simp), hu⟩
      · rintro ⟨u, hu, hxu⟩
        exact ⟨u, Finset.mem_of_mem_erase hu, hxu⟩)
    (by omega)
  have h1 : ∀ w, (S w).card - 1 = ((T w).card - 1) + (if v ∈ S w then 1 else 0) := by
    intro w
    by_cases h : v ∈ S w
    · have := h2 w
      simp only [hT, Finset.card_erase_of_mem h, h, ite_true]
      omega
    · simp [hT, h]
  have h3 : ∑ w : Fin m, ((T w).card - 1) = ∑ i : Fin (Fintype.card A), ((T (e i).1).card - 1) := by
    rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun w : Fin m => 2 ≤ (T w).card)
      (f := fun w => (T w).card - 1) fun w _ hw => by omega]
    exact (PEqualNP.Base.Matching.sum_equivFin_subtype (fun w : Fin m => 2 ≤ (T w).card)
      (fun w => (T w).card - 1)).symm
  have hsum : ∑ w : Fin m, ((S w).card - 1) =
      ∑ i : Fin (Fintype.card A), ((T (e i).1).card - 1) +
        (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_add_distrib, h3, Finset.card_filter]
  omega

end PEqualNP.Outside.L_meta_951_aux
