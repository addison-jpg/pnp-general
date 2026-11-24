import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Restrict

/-!
# Dead gates under a restriction `x_v := c`

A gate `k` is *dead on* `D = {x | x v = c}` if on `D` its wire equals an earlier wire (`DCpQ`) or
is constantly `!c` (`DTQ`); a gate constantly `c` on `D` is a copy of the input wire `v`.
`promise_boundQ`: a circuit correct only on `D` for a family avoiding `v` has
`base + #dead ≤ #gates`, given the ordinary bound for shorter circuits.

The restriction `x_v := 0` keeps its own names: `DCp`, `DTr`, `DC` are definitionally
`DCpQ v false`, `DTQ v false`, `DCq v false`, and `dcp_of_false`, `dead_of_andor`, `dead_of_not`,
`insens_of_notDead_at`, `DC_drop`, `indep_of_noDead`, `promise_bound` are the `c = false` instances
of the general lemmas (`MinCEN3` uses `c = true`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

/-- On `{x v = c}` gate `k` equals an earlier wire. -/
def DCpQ (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) : Prop :=
  ∃ j, j < n + k ∧ ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = val gates x j

/-- On `{x v = c}` gate `k` is constantly `!c`. -/
def DTQ (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = !c

open Classical in
/-- The gates dead under the restriction `x_v := c`. -/
noncomputable def DCq (v : Fin n) (c : Bool) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k => DCpQ v c gates k ∨ DTQ v c gates k

/-- On `D = {x | x v = false}` gate `k` equals an earlier wire (definitionally `DCpQ v false`). -/
def DCp (v : Fin n) (gates : List Gate) (k : ℕ) : Prop :=
  ∃ j, j < n + k ∧ ∀ x : Fin n → Bool, x v = false → val gates x (n + k) = val gates x j

/-- On `D = {x | x v = false}` gate `k` is constantly true (definitionally `DTQ v false`). -/
def DTr (v : Fin n) (gates : List Gate) (k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, x v = false → val gates x (n + k) = true

open Classical in
/-- The gates that are dead under the restriction `x_v := 0` (definitionally `DCq v false`). -/
noncomputable def DC (v : Fin n) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k => DCp v gates k ∨ DTr v gates k

/-- A gate equal to `c` on `{x v = c}` is a copy of the input wire `v`. -/
theorem dcpQ_of_eq (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ)
    (h : ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = c) : DCpQ v c gates k :=
  ⟨v, by have := v.2; omega, fun x hx => by rw [h x hx, val_inp _ _ _ v.2]; exact hx.symm⟩

theorem dcp_of_false (v : Fin n) (gates : List Gate) (k : ℕ)
    (h : ∀ x : Fin n → Bool, x v = false → val gates x (n + k) = false) : DCp v gates k :=
  dcpQ_of_eq v false gates k h

theorem deadQ_of_const (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) (b : Bool)
    (h : ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = b) :
    DCpQ v c gates k ∨ DTQ v c gates k := by
  by_cases hb : b = c
  · exact Or.inl (dcpQ_of_eq v c gates k fun x hx => (h x hx).trans hb)
  · right
    intro x hx
    rw [h x hx]
    cases b <;> cases c <;> simp_all

theorem dcp_of_seen (v : Fin n) (gates : List Gate) (k : ℕ) (hk : k < gates.length) (c : ℕ)
    (h : ∀ x : Fin n → Bool, x v = false → val gates x (n + k) = val (gates.take k) x c) :
    DCp v gates k := by
  by_cases hc : c < n + k
  · exact ⟨c, hc, fun x hx => (h x hx).trans (val_take gates x k c (by omega) hc)⟩
  · exact dcp_of_false v gates k fun x hx => by rw [h x hx, val_take_ge _ _ _ _ (by omega)]

theorem deadQ_of_seen (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (cc : ℕ) (h : ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = val (gates.take k) x cc) :
    DCpQ v c gates k ∨ DTQ v c gates k := by
  by_cases hc : cc < n + k
  · exact Or.inl ⟨cc, hc, fun x hx => (h x hx).trans (val_take gates x k cc (by omega) hc)⟩
  · exact deadQ_of_const v c gates k false fun x hx => by
      rw [h x hx, val_take_ge _ _ _ _ (by omega)]

theorem deadQ_of_andor (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or)
    (hlen : (gates[k]'hk).inputs.length ≤ 2) (a : ℕ) (ha : a ∈ (gates[k]'hk).inputs) (b : Bool)
    (hb : ∀ x : Fin n → Bool, x v = c → val (gates.take k) x a = b) :
    DCpQ v c gates k ∨ DTQ v c gates k := by
  have hv := fun x : Fin n → Bool => val_gate gates x k hk
  have key : (∃ b', ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = b') ∨
      ∃ cc, ∀ x : Fin n → Bool, x v = c → val gates x (n + k) = val (gates.take k) x cc := by
    generalize gates[k]'hk = g at hop hlen ha hv
    obtain ⟨op, ins⟩ := g
    simp only at hop hlen ha hv
    match ins, hlen with
    | [], _ => simp at ha
    | [d], _ =>
      simp only [List.mem_singleton] at ha
      subst ha
      left
      refine ⟨b, fun x hx => ?_⟩
      rcases hop with rfl | rfl <;> simp [hv, GateOp.eval, hb x hx]
    | [d, e], _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rcases hop with rfl | rfl <;> cases b
      · exact Or.inl ⟨false, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inr ⟨e, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inr ⟨e, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inl ⟨true, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inl ⟨false, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inr ⟨d, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inr ⟨d, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
      · exact Or.inl ⟨true, fun x hx => by simp [hv, GateOp.eval, hb x hx]⟩
    | _ :: _ :: _ :: _, h => simp at h
  rcases key with ⟨b', h⟩ | ⟨cc, h⟩
  · exact deadQ_of_const v c gates k b' h
  · exact deadQ_of_seen v c gates k hk cc h

theorem dead_of_andor (v : Fin n) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or)
    (hlen : (gates[k]'hk).inputs.length ≤ 2) (a : ℕ) (ha : a ∈ (gates[k]'hk).inputs) (b : Bool)
    (hb : ∀ x : Fin n → Bool, x v = false → val (gates.take k) x a = b) :
    DCp v gates k ∨ DTr v gates k :=
  deadQ_of_andor v false gates k hk hop hlen a ha b hb

theorem deadQ_of_not (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]'hk).op = GateOp.not) (a : ℕ) (rest : List ℕ)
    (ha : (gates[k]'hk).inputs = a :: rest) (b : Bool)
    (hb : ∀ x : Fin n → Bool, x v = c → val (gates.take k) x a = b) :
    DCpQ v c gates k ∨ DTQ v c gates k := by
  refine deadQ_of_const v c gates k (!b) fun x hx => ?_
  rw [val_gate gates x k hk, hop, ha]
  simp [GateOp.eval, hb x hx]

theorem dead_of_not (v : Fin n) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]'hk).op = GateOp.not) (a : ℕ) (rest : List ℕ)
    (ha : (gates[k]'hk).inputs = a :: rest) (b : Bool)
    (hb : ∀ x : Fin n → Bool, x v = false → val (gates.take k) x a = b) :
    DCp v gates k ∨ DTr v gates k :=
  deadQ_of_not v false gates k hk hop a rest ha b hb

/-- A gate that is not dead on `{x v = c}` ignores a wire `p` that is constant (`b`) there. -/
theorem insensQ_of_notDead_at (v : Fin n) (c : Bool) (gates : List Gate) (k : ℕ)
    (hk : k < gates.length)
    (hgk : ((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or ∨
      (gates[k]'hk).op = GateOp.not) ∧ (gates[k]'hk).inputs.length ≤ 2)
    (hno : ¬ (DCpQ v c gates k ∨ DTQ v c gates k)) (p : ℕ) (b : Bool)
    (hseen : ∀ y : Fin n → Bool, y v = c → val (gates.take k) y p = b) :
    Insens p (gates[k]'hk) :=
  insens_of_unread p _ hgk.1 fun h => hno <| by
    rcases h with ⟨hop, hm⟩ | ⟨hop, rest, hin⟩
    · exact deadQ_of_andor v c gates k hk hop hgk.2 p hm b hseen
    · exact deadQ_of_not v c gates k hk hop p rest hin b hseen

/-- A gate that is not dead on `{x v = false}` ignores a wire `p` that is constant (`b`) there. -/
theorem insens_of_notDead_at (v : Fin n) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hgk : ((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or ∨
      (gates[k]'hk).op = GateOp.not) ∧ (gates[k]'hk).inputs.length ≤ 2)
    (hno : ¬ (DCp v gates k ∨ DTr v gates k)) (p : ℕ) (b : Bool)
    (hseen : ∀ y : Fin n → Bool, y v = false → val (gates.take k) y p = b) :
    Insens p (gates[k]'hk) :=
  insensQ_of_notDead_at v false gates k hk hgk hno p b hseen

/-- A gate that is not dead on `{x v = false}` does not depend on wire `v`. -/
theorem insens_of_notDead (v : Fin n) (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hgk : ((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or ∨
      (gates[k]'hk).op = GateOp.not) ∧ (gates[k]'hk).inputs.length ≤ 2)
    (hno : ¬ (DCp v gates k ∨ DTr v gates k)) : Insens v (gates[k]'hk) :=
  insens_of_notDead_at v gates k hk hgk hno v false fun y hy => by rw [val_inp _ _ _ v.2]; exact hy

/-- A wire that computes `OR T` with `2 ≤ |T|` on `{x v = false}` is not the input wire `v`. -/
theorem ne_inp_of_orOn (v : Fin n) (gates : List Gate) (o : ℕ) (T : Finset (Fin n))
    (hT : 2 ≤ T.card)
    (hev : ∀ x : Fin n → Bool, x v = false → val gates x o = decide (∃ u ∈ T, x u = true)) :
    o ≠ v := by
  intro e
  obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_ne hT v
  have h := hev (eof b) (by simp [eof, hbv.symm])
  rw [e, val_inp _ _ _ v.2] at h
  simp [eof, hbv.symm, hb] at h

/-- For nonempty `T ∌ v`, `OR T` is `c'` at the point that is `c` at `v` and `c'` elsewhere. -/
theorem orOn_update_const (v : Fin n) (T : Finset (Fin n)) (hT : T.Nonempty) (hvT : v ∉ T)
    (c c' : Bool) : decide (∃ u ∈ T, Function.update (fun _ => c') v c u = true) = c' := by
  obtain ⟨u, hu⟩ := hT
  have hupd : ∀ u' ∈ T, Function.update (fun _ => c') v c u' = c' := fun u' hu' =>
    Function.update_of_ne (fun e : u' = v => hvT (e ▸ hu')) _ _
  cases c'
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro u' hu'; rw [hupd u' hu']; simp
  · simp only [decide_eq_true_eq]
    exact ⟨u, hu, hupd u hu⟩

theorem DCq_drop (v : Fin n) (c : Bool) (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hj : j < n + k)
    (Hval : ∀ x : Fin n → Bool, x v = c → ∀ i, i ≠ n + k →
      val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i)
    (HK : (∀ x : Fin n → Bool, x v = c → val gates x (n + k) = val gates x j) ∨
      DTQ v c gates k) :
    (DCq v c gates).card ≤ (DCq v c (dropGate gates k j n)).card + 1 := by
  classical
  have hlen := dropGate_length gates k j n hk
  set φ : ℕ → ℕ := fun k' => if k' < k then k' else k' - 1 with hφd
  have hφ : ∀ k', k' ≠ k → redir (n + k) j (n + k') = n + φ k' := by
    intro k' h
    simp only [redir, hφd]
    split_ifs <;> omega
  have hjj : redir (n + k) j j = j := by simp [redir, hj]
  have hmap : ∀ k' ∈ (DCq v c gates).erase k, φ k' ∈ DCq v c (dropGate gates k j n) := by
    intro k' hk'
    rw [Finset.mem_erase] at hk'
    obtain ⟨hne, hmem⟩ := hk'
    simp only [DCq, Finset.mem_filter, Finset.mem_range] at hmem ⊢
    obtain ⟨hlt, hd⟩ := hmem
    have hnew : ∀ x : Fin n → Bool, x v = c →
        val (dropGate gates k j n) x (n + φ k') = val gates x (n + k') := by
      intro x hx
      rw [← hφ k' hne]
      exact Hval x hx _ (by omega)
    refine ⟨by simp only [hφd]; split_ifs <;> omega, ?_⟩
    rcases hd with ⟨j', hj', hc⟩ | ht
    · by_cases hjk : j' = n + k
      · subst hjk
        rcases HK with hK | hK
        · left
          refine ⟨j, by simp only [hφd]; split_ifs <;> omega, fun x hx => ?_⟩
          rw [hnew x hx, hc x hx, hK x hx]
          have := Hval x hx j (by omega)
          rw [hjj] at this
          exact this.symm
        · right
          intro x hx
          rw [hnew x hx, hc x hx, hK x hx]
      · left
        refine ⟨redir (n + k) j j', ?_, fun x hx => ?_⟩
        · simp only [redir, hφd]; split_ifs <;> omega
        · rw [hnew x hx, hc x hx, Hval x hx j' hjk]
    · right
      intro x hx
      rw [hnew x hx]
      exact ht x hx
  have hinj : Set.InjOn φ ((DCq v c gates).erase k : Finset ℕ) := by
    intro a ha b hb hab
    have ha' : a ≠ k := (Finset.mem_erase.mp ha).1
    have hb' : b ≠ k := (Finset.mem_erase.mp hb).1
    simp only [hφd] at hab
    split_ifs at hab <;> omega
  have h1 := Finset.card_le_card_of_injOn φ hmap hinj
  have h2 := Finset.pred_card_le_card_erase (s := DCq v c gates) (a := k)
  omega

theorem DC_drop (v : Fin n) (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hj : j < n + k)
    (Hval : ∀ x : Fin n → Bool, x v = false → ∀ i, i ≠ n + k →
      val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i)
    (HK : (∀ x : Fin n → Bool, x v = false → val gates x (n + k) = val gates x j) ∨
      DTr v gates k) :
    (DC v gates).card ≤ (DC v (dropGate gates k j n)).card + 1 :=
  DCq_drop v false gates k j hk hj Hval HK

/-- Without dead gates the circuit does not depend on `x v` (any `c`). -/
theorem indepQ_of_noDead (v : Fin n) (c : Bool) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hno : ∀ k, k < gates.length → ¬ (DCpQ v c gates k ∨ DTQ v c gates k))
    (x : Fin n → Bool) (i : ℕ) (hi : i ≠ v) :
    val gates x i = val gates (Function.update x v c) i :=
  val_congr_of_insens v gates x _
    (fun _ hj => (Function.update_of_ne (Fin.ne_of_val_ne hj) _ _).symm)
    (fun k hk => Or.inr (insensQ_of_notDead_at v c gates k hk (hg _ (List.getElem_mem hk))
      (hno k hk) v c fun y hy => by rw [val_inp _ _ _ v.2]; exact hy))
    i hi

/-- Without dead gates the circuit does not depend on `x v`. -/
theorem indep_of_noDead (v : Fin n) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hno : ∀ k, k < gates.length → ¬ (DCp v gates k ∨ DTr v gates k))
    (x : Fin n → Bool) (i : ℕ) (hi : i ≠ v) :
    val gates x i = val gates (Function.update x v false) i :=
  indepQ_of_noDead v false gates hg hno x i hi

/-- The promise bound for the restriction `x_v := c` (`promise_bound` is `c = false`). -/
theorem promise_boundQ (v : Fin n) (c : Bool) (L0 : ℕ)
    (B : ∀ (m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      gates.length < L0 →
      (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true)) →
      ∑ i : Fin m, ((S i).card - 1) ≤ gates.length) :
    ∀ (L m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      gates.length = L → (∀ w, v ∉ S w) →
      (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ (w : Fin m) (x : Fin n → Bool), x v = c →
        val gates x (out w) = decide (∃ u ∈ S w, x u = true)) →
      L < L0 + (DCq v c gates).card →
      ∑ i : Fin m, ((S i).card - 1) + (DCq v c gates).card ≤ L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro m S gates out hL hvS h2 hS hg hU hev hlt
  -- on the promise, `OR (S w)` is `c'` at the point that is `c'` off `v`
  have hconst : ∀ (w : Fin m) (c' : Bool),
      decide (∃ u ∈ S w, (Function.update (fun _ => c') v c) u = true) = c' := fun w =>
    orOn_update_const v (S w) (Finset.card_pos.mp (by have := h2 w; omega)) (hvS w) c
  have hstep : ∀ k j : ℕ, k < gates.length → j < n + k →
      (∀ x : Fin n → Bool, x v = c → ∀ i, i ≠ n + k →
        val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i) →
      ((∀ x : Fin n → Bool, x v = c → val gates x (n + k) = val gates x j) ∨
        DTQ v c gates k) →
      (∀ w, out w = n + k → ∀ x : Fin n → Bool, x v = c →
        val (dropGate gates k j n) x (redir (n + k) j (out w)) = val gates x (out w)) →
      ∑ i : Fin m, ((S i).card - 1) + (DCq v c gates).card ≤ L := by
    intro k j hk hj Hval HK Hout
    have hlen := dropGate_length gates k j n hk
    have hcard := DCq_drop v c gates k j hk hj Hval HK
    have hev' : ∀ (w : Fin m) (x : Fin n → Bool), x v = c →
        val (dropGate gates k j n) x (redir (n + k) j (out w)) =
          decide (∃ u ∈ S w, x u = true) := by
      intro w x hx
      rw [← hev w x hx]
      by_cases ho : out w = n + k
      · exact Hout w ho x hx
      · exact Hval x hx _ ho
    have := ih (dropGate gates k j n).length (by omega) m S (dropGate gates k j n)
      (fun w => redir (n + k) j (out w)) rfl hvS h2 hS (dropGate_hg gates k j n hg)
      (dropGate_hU gates k j n hk hU) hev' (by omega)
    omega
  by_cases hc : ∃ k, k < gates.length ∧ DCpQ v c gates k
  · obtain ⟨k, hk, j, hj, hcp⟩ := hc
    exact hstep k j hk hj
      (fun x hx i _ => val_dropGate_pt gates k j hk hj x (hcp x hx) i) (Or.inl hcp)
      (fun w _ x hx => val_dropGate_pt gates k j hk hj x (hcp x hx) _)
  by_cases ht : ∃ k, k < gates.length ∧ DTQ v c gates k
  · obtain ⟨k, hk, hT⟩ := ht
    have hnoc : ∀ k', k' < gates.length → ¬ DCpQ v c gates k' :=
      fun k' h1 h2 => hc ⟨k', h1, h2⟩
    have hdead : ∀ k', (hk' : k' < gates.length) → k < k' →
        ¬ (DCpQ v c gates k' ∨ DTQ v c gates k') := by
      intro k' hk' hkk hd
      rcases hd with hd | hd
      · exact hnoc k' hk' hd
      · exact hnoc k' hk' ⟨n + k, by omega, fun x hx => by rw [hd x hx, hT x hx]⟩
    have hins : ∀ g ∈ gates.drop (k + 1), Insens (n + k) g := by
      intro g hgm
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hgm
      rw [List.getElem_drop]
      have hi' : k + 1 + i < gates.length := by simp at hi; omega
      exact insensQ_of_notDead_at v c gates _ hi' (hg _ (List.getElem_mem hi'))
        (hdead _ hi' (by omega)) (n + k) (!c) fun y hy => by
          rw [val_take _ _ _ _ (by omega) (by omega)]; exact hT y hy
    refine hstep k v hk (by have := v.2; omega)
      (fun x hx i hi => val_dropIns gates k v hk hins x i hi) (Or.inr hT) ?_
    intro w ho
    exfalso
    have h1 := hev w (Function.update (fun _ => c) v c) (by simp)
    rw [ho, hT _ (by simp), hconst w c] at h1
    cases c <;> simp at h1
  · have hno : ∀ k, k < gates.length → ¬ (DCpQ v c gates k ∨ DTQ v c gates k) := by
      intro k hk hd
      rcases hd with hd | hd
      · exact hc ⟨k, hk, hd⟩
      · exact ht ⟨k, hk, hd⟩
    have hDC : DCq v c gates = ∅ := by
      classical
      ext k
      simp only [DCq, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        not_and]
      exact fun hk => hno k hk
    rw [hDC] at hlt ⊢
    simp only [Finset.card_empty, add_zero] at hlt ⊢
    rw [← hL]
    refine B m S gates out (by omega) h2 hS hg hU fun w x => ?_
    have hov : out w ≠ (v : ℕ) := by
      intro ho
      have h1 := hev w (Function.update (fun _ => !c) v c) (by simp)
      rw [ho, val_inp _ _ _ v.2, hconst w (!c)] at h1
      simp at h1
    rw [indepQ_of_noDead v c gates hg hno x _ hov, hev w _ (by simp)]
    congr 1
    exact propext (exists_congr fun u => and_congr_right fun hu => by
      rw [Function.update_of_ne (fun e : u = v => hvS w (e ▸ hu))])

theorem promise_bound (v : Fin n) (L0 : ℕ)
    (B : ∀ (m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      gates.length < L0 →
      (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true)) →
      ∑ i : Fin m, ((S i).card - 1) ≤ gates.length) :
    ∀ (L m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      gates.length = L → (∀ w, v ∉ S w) →
      (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ (w : Fin m) (x : Fin n → Bool), x v = false →
        val gates x (out w) = decide (∃ u ∈ S w, x u = true)) →
      L < L0 + (DC v gates).card →
      ∑ i : Fin m, ((S i).card - 1) + (DC v gates).card ≤ L :=
  promise_boundQ v false L0 B

end PEqualNP.Outside.L_meta_951_aux
