import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.RuleS
import PEqualNP.W951.MinCEN3

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
