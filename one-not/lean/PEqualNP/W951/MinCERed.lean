import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCE
import PEqualNP.W951.Lift
import PEqualNP.W951.MergeRunT
import PEqualNP.W951.LiftFrac

/-!
# MinCERed: the refereed reduction lemmas of a minimal counterexample (desktop Coord, 12:52)

All via M0 (`MinCE.bound_lt`): a correct circuit for the same sets with at most one NOT gate and fewer
gates satisfies the bound, against `s < base`.

* **Substitution of a constant on out-edges** (`subRd`, `subGates`): a reader `g` of wire `u` with the
  constant `c` on `u` is rewritten without reading `u` (`AND(1, y) = y`, `AND(0, y) = 0`, `OR(0, y) = y`,
  `OR(1, y) = 1`, `NOT(c) = ¬c`); `eval_subRd`, `val_subGates` (if every rewritten reader sees `c`
  on `u`, nothing changes), `subGates_hg`, `subGates_hU` (no new NOT gate).
* `shrink_of_const`: a correct circuit with a constant non-output gate has a correct circuit with one
  gate fewer (rewrite all readers, then delete the gate as dead).
* MinCE facts: R1 is `MinCE.no_const` (`Peel.lean`), `no_dup` (R2), `no_var` (R3), `live` (R4, in
  `MinCE.lean`),
  `not_used` (R5'), `observable` (R+: substituting a constant on a nonempty set of out-edges of any
  wire — readers that are AND/OR gates or NOT gates reading the wire first — gives an incorrect
  circuit).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Rewriting a reader for a constant -/

/-- A reader of `u`, rewritten for the constant `c` on `u` (it no longer reads `u`). -/
def subRd (u : ℕ) (c : Bool) : Gate → Gate
  | ⟨.and, l⟩ => if c then ⟨.and, l.filter (· ≠ u)⟩ else ⟨.or, []⟩
  | ⟨.or, l⟩ => if c then ⟨.and, []⟩ else ⟨.or, l.filter (· ≠ u)⟩
  | ⟨.not, []⟩ => ⟨.not, []⟩
  | ⟨.not, w :: l⟩ => if w = u then (if c then ⟨.or, []⟩ else ⟨.and, []⟩)
      else ⟨.not, w :: l.filter (· ≠ u)⟩
  | g => g

theorem all_filter_ne (l : List ℕ) (u : ℕ) (f : ℕ → Bool) (hf : f u = true) :
    ((l.filter (· ≠ u)).map f).all id = (l.map f).all id := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    by_cases hxu : x = u
    · subst hxu; exact hf
    · exact h _ (List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hxu⟩, rfl⟩)
  · intro h b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact h _ (List.mem_map.mpr ⟨x, (List.mem_filter.mp hx).1, rfl⟩)

theorem any_filter_ne (l : List ℕ) (u : ℕ) (f : ℕ → Bool) (hf : f u = false) :
    ((l.filter (· ≠ u)).map f).any id = (l.map f).any id := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hb1⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact ⟨f x, List.mem_map.mpr ⟨x, (List.mem_filter.mp hx).1, rfl⟩, hb1⟩
  · rintro ⟨b, hb, hb1⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    by_cases hxu : x = u
    · subst hxu; rw [hf] at hb1; exact absurd hb1 (by decide)
    · exact ⟨f x, List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hxu⟩, rfl⟩, hb1⟩

/-- **The rewritten reader computes the same value** when `u` carries `c`. -/
theorem eval_subRd (u : ℕ) (c : Bool) (g : Gate) (f : ℕ → Bool) (hf : f u = c)
    (hmem : g.op = .and ∨ g.op = .or → u ∈ g.inputs) :
    (subRd u c g).op.eval ((subRd u c g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    have hu : u ∈ l := hmem (Or.inl rfl)
    cases c
    · simp only [subRd, Bool.false_eq_true, ite_false, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨f u, List.mem_map_of_mem hu, by simp [hf]⟩
    · simp only [subRd, ite_true, GateOp.eval]
      exact all_filter_ne l u f hf
  | or =>
    have hu : u ∈ l := hmem (Or.inr rfl)
    cases c
    · simp only [subRd, Bool.false_eq_true, ite_false, GateOp.eval]
      exact any_filter_ne l u f hf
    · simp only [subRd, ite_true, GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨f u, List.mem_map_of_mem hu, by simp [hf]⟩
  | not =>
    cases l with
    | nil => rfl
    | cons w l =>
      by_cases hw : w = u
      · subst hw
        cases c <;> simp [subRd, GateOp.eval, hf]
      · simp [subRd, hw, GateOp.eval]
  | mod k => rfl
  | maj => rfl

theorem not_mem_subRd (u : ℕ) (c : Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) : u ∉ (subRd u c g).inputs := by
  obtain ⟨op, l⟩ := g
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · cases c <;> simp [subRd]
  · cases c <;> simp [subRd]
  · cases l with
    | nil => simp [subRd]
    | cons w l =>
      by_cases hw : w = u
      · cases c <;> simp [subRd, hw]
      · simp [subRd, hw, Ne.symm hw]

theorem subRd_ops (u : ℕ) (c : Bool) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ((subRd u c g).op = .and ∨ (subRd u c g).op = .or ∨ (subRd u c g).op = .not) ∧
      (subRd u c g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := hg
  have hl' : l.length ≤ 2 := hl
  have hf : (l.filter (· ≠ u)).length ≤ 2 := (List.length_filter_le _ _).trans hl'
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · cases c
    · simp only [subRd, Bool.false_eq_true, ite_false]
      exact ⟨by simp, by simp⟩
    · simp only [subRd, ite_true]
      exact ⟨by simp, hf⟩
  · cases c
    · simp only [subRd, Bool.false_eq_true, ite_false]
      exact ⟨by simp, hf⟩
    · simp only [subRd, ite_true]
      exact ⟨by simp, by simp⟩
  · cases l with
    | nil => exact ⟨by simp [subRd], by simp [subRd]⟩
    | cons w l =>
      have hll : l.length ≤ 1 := by simp at hl'; omega
      have hfl : (l.filter (· ≠ u)).length ≤ 1 := (List.length_filter_le _ _).trans hll
      by_cases hw : w = u
      · cases c
        · simp only [subRd, hw, ite_true, Bool.false_eq_true, ite_false]
          exact ⟨by simp, by simp⟩
        · simp only [subRd, hw, ite_true]
          exact ⟨by simp, by simp⟩
      · simp only [subRd, hw, ite_false]
        exact ⟨by simp, by simp only [List.length_cons]; omega⟩

/-- A rewritten gate is a NOT gate only if the original one was. -/
theorem subRd_not (u : ℕ) (c : Bool) (g : Gate) (h : (subRd u c g).op = .not) : g.op = .not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and => cases c <;> simp [subRd] at h
  | or => cases c <;> simp [subRd] at h
  | not => rfl
  | mod k => simp [subRd] at h
  | maj => simp [subRd] at h

/-! ## Rewriting a set of readers -/

/-- Rewrite the readers `k ∈ E` of `u`, reader `k` for the constant `cst k`. -/
def subGates (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate) : List Gate :=
  gs.mapIdx fun k g => if k ∈ E then subRd u (cst k) g else g

theorem subGates_length (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate) :
    (subGates u cst E gs).length = gs.length := List.length_mapIdx

theorem subGates_getElem (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate) (k : ℕ)
    (hk : k < (subGates u cst E gs).length) :
    (subGates u cst E gs)[k] =
      if k ∈ E then subRd u (cst k) (gs[k]'(by rw [subGates_length] at hk; exact hk))
      else gs[k]'(by rw [subGates_length] at hk; exact hk) := by
  simp [subGates, List.getElem_mapIdx]

theorem subGates_hg (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ subGates u cst E gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
  intro g hgm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hgm
  have hk' : k < gs.length := by rw [subGates_length] at hk; exact hk
  rw [subGates_getElem]
  split_ifs
  · exact subRd_ops u _ _ (hg _ (List.getElem_mem hk'))
  · exact hg _ (List.getElem_mem hk')

theorem subGates_hU (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate)
    (hU : AtMostOneNot gs) : AtMostOneNot (subGates u cst E gs) := by
  intro i1 i2 h1 h2 e1 e2
  have h1' : i1 < gs.length := by rw [subGates_length] at h1; exact h1
  have h2' : i2 < gs.length := by rw [subGates_length] at h2; exact h2
  have key : ∀ i (hi : i < (subGates u cst E gs).length) (hi' : i < gs.length),
      ((subGates u cst E gs)[i]'hi).op = .not → (gs[i]'hi').op = .not := by
    intro i hi hi' e
    rw [subGates_getElem] at e
    split_ifs at e
    · exact subRd_not u _ _ e
    · exact e
  exact hU i1 i2 h1' h2' (key i1 h1 h1' e1) (key i2 h2 h2' e2)

/-- **Value congruence**: two gate lists of the same length whose gates evaluate alike on the
first list's prefix values have the same values. -/
theorem val_congr_gates {n : ℕ} (gs gs' : List Gate) (hlen : gs'.length = gs.length) (x : Fin n → Bool)
    (hgate : ∀ k (hk : k < gs.length) (hk' : k < gs'.length),
      (gs'[k]'hk').op.eval ((gs'[k]'hk').inputs.map fun j => val (gs.take k) x j) =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun j => val (gs.take k) x j)) :
    ∀ i, val gs' x i = val gs x i := by
  have key : ∀ k, k ≤ gs.length → ∀ i, val (gs'.take k) x i = val (gs.take k) x i := by
    intro k
    induction k with
    | zero => intro _ i; simp
    | succ k ih =>
      intro hk i
      have hk1 : k < gs.length := by omega
      have hk1' : k < gs'.length := by omega
      rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk1', val_snoc,
        val_snoc]
      have hl : (gs.take k).length = k := by simp; omega
      have hl' : (gs'.take k).length = k := by simp; omega
      rw [hl, hl']
      have hfun : (fun j => val (gs'.take k) x j) = fun j => val (gs.take k) x j :=
        funext (ih (by omega))
      split_ifs
      · rw [hfun]
        exact hgate k hk1 hk1'
      · exact ih (by omega) i
  intro i
  have := key gs.length le_rfl i
  rwa [List.take_of_length_le (by omega), List.take_of_length_le le_rfl] at this

/-- **Rewriting readers that see the constant changes nothing.** -/
theorem val_subGates {n : ℕ} (u : ℕ) (cst : ℕ → Bool) (E : Finset ℕ) (gs : List Gate)
    (x : Fin n → Bool)
    (hE : ∀ k ∈ E, ∀ hk : k < gs.length, ((gs[k]'hk).op = .and ∨ (gs[k]'hk).op = .or →
      u ∈ (gs[k]'hk).inputs) ∧ val (gs.take k) x u = cst k) :
    ∀ i, val (subGates u cst E gs) x i = val gs x i := by
  refine val_congr_gates gs _ (subGates_length u cst E gs) x fun k hk hk' => ?_
  rw [subGates_getElem]
  split_ifs with hkE
  · obtain ⟨hmem, hcst⟩ := hE k hkE hk
    exact eval_subRd u (cst k) _ _ hcst hmem
  · rfl

/-! ## Shrinking a correct circuit -/

section Shrink

variable {n m : ℕ}

/-- **A constant non-output gate can be removed**: rewrite all its readers for the constant (readers
that read it before it exists see `0`), then delete it as dead. -/
theorem shrink_of_const (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gs) {k : ℕ} (hk : k < gs.length) (c : Bool)
    (hc : ∀ x : Fin n → Bool, val gs x (n + k) = c) (out : Fin m → ℕ) (hout : ∀ w, out w ≠ n + k) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ), gs'.length + 1 = gs.length ∧
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧ AtMostOneNot gs' ∧
      ∀ (w : Fin m) (x : Fin n → Bool), val gs' x (out' w) = val gs x (out w) := by
  classical
  set u := n + k with hu
  set E : Finset ℕ := (Finset.range gs.length).filter fun k' =>
    ∃ hk' : k' < gs.length, u ∈ (gs[k']'hk').inputs with hE
  set cst : ℕ → Bool := fun k' => if k < k' then c else false with hcst
  set gs1 := subGates u cst E gs with hgs1
  have hval1 : ∀ (x : Fin n → Bool) i, val gs1 x i = val gs x i := by
    intro x
    refine val_subGates u cst E gs x fun k' hk'E hk' => ⟨fun _ => ?_, ?_⟩
    · obtain ⟨-, hk'', hmem⟩ := Finset.mem_filter.mp hk'E
      exact hmem
    · simp only [hcst]
      split_ifs with hkk
      · rw [← mr_val_take gs x k' u (by omega)]
        exact hc x
      · exact mr_val_ge (gs.take k') x u (by simp; omega)
  have hl1 : gs1.length = gs.length := subGates_length u cst E gs
  have hk1 : k < gs1.length := by omega
  have hno : ∀ g ∈ gs1, u ∉ g.inputs := by
    intro g hgm
    obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hgm
    have hk'' : k' < gs.length := by omega
    rw [subGates_getElem]
    split_ifs with hk'E
    · exact not_mem_subRd u _ _ (hg _ (List.getElem_mem hk'')).1
    · intro hmem
      exact hk'E (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk'', hk'', hmem⟩)
  refine ⟨dropGate gs1 k 0 n, fun w => redir u 0 (out w), ?_, dropGate_hg gs1 k 0 n
    (subGates_hg u cst E gs hg), dropGate_hU gs1 k 0 n hk1 (subGates_hU u cst E gs hU),
    fun w x => ?_⟩
  · have := dropGate_length gs1 k 0 n hk1
    omega
  · rw [val_dropDead gs1 k 0 hk1 hno x (out w) (hout w), hval1]

/-- **A gate copying an earlier wire can be removed** (as in `MinCE.clean`). -/
theorem shrink_of_copy (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gs) {k j : ℕ} (hk : k < gs.length) (hj : j < n + k)
    (hcopy : ∀ x : Fin n → Bool, val gs x (n + k) = val gs x j) (out : Fin m → ℕ) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ), gs'.length + 1 = gs.length ∧
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧ AtMostOneNot gs' ∧
      ∀ (w : Fin m) (x : Fin n → Bool), val gs' x (out' w) = val gs x (out w) :=
  ⟨dropGate gs k j n, fun w => redir (n + k) j (out w), dropGate_length gs k j n hk,
    dropGate_hg gs k j n hg, dropGate_hU gs k j n hk hU, fun w x => val_dropGate gs k j hk hj hcopy x (out w)⟩

/-- A wire computing `OR(R)` for a nonempty `R` is not constant. -/
theorem not_const_of_or {gs : List Gate} {R : Finset (Fin n)} (hR : R.Nonempty) {o : ℕ}
    (hev : ∀ x : Fin n → Bool, val gs x o = decide (∃ v ∈ R, x v = true)) (c : Bool) :
    ¬ ∀ x : Fin n → Bool, val gs x o = c := by
  intro h
  obtain ⟨v, hv⟩ := hR
  have h0 := h fun _ => false
  have h1 := h fun _ => true
  rw [hev] at h0 h1
  have e0 : decide (∃ v ∈ R, (fun _ => false : Fin n → Bool) v = true) = false := by simp
  have e1 : decide (∃ v ∈ R, (fun _ => true : Fin n → Bool) v = true) = true :=
    decide_eq_true ⟨v, hv, rfl⟩
  rw [e0] at h0
  rw [e1] at h1
  rw [← h0] at h1
  exact absurd h1 (by decide)

end Shrink

/-- A rewritten reader (AND/OR reading `u`, or NOT reading `u` first) is an AND/OR gate with at most
one input. -/
theorem subRd_shape (u : ℕ) (c : Bool) (g : Gate) (hl : g.inputs.length ≤ 2)
    (h : ((g.op = .and ∨ g.op = .or) ∧ u ∈ g.inputs) ∨ (g.op = .not ∧ g.inputs.head? = some u)) :
    ((subRd u c g).op = .and ∨ (subRd u c g).op = .or) ∧ (subRd u c g).inputs.length ≤ 1 := by
  obtain ⟨op, l⟩ := g
  have hl' : l.length ≤ 2 := hl
  have hlt : u ∈ l → (l.filter (· ≠ u)).length ≤ 1 := fun hu => by
    have h1 : (l.filter (· ≠ u)).length < l.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨u, hu, by simp⟩
    omega
  rcases h with ⟨hop, hu⟩ | ⟨hop, hh⟩
  · have hu' : u ∈ l := hu
    rcases hop with hop | hop <;> simp only at hop <;> subst hop
    · cases c
      · simp only [subRd, Bool.false_eq_true, ite_false]
        exact ⟨by simp, by simp⟩
      · simp only [subRd, ite_true]
        exact ⟨by simp, hlt hu'⟩
    · cases c
      · simp only [subRd, Bool.false_eq_true, ite_false]
        exact ⟨by simp, hlt hu'⟩
      · simp only [subRd, ite_true]
        exact ⟨by simp, by simp⟩
  · simp only at hop
    subst hop
    cases l with
    | nil => simp at hh
    | cons w l =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases c <;> simp [subRd]

/-- An AND/OR gate with at most one input is constant or a copy of an earlier wire. -/
theorem const_or_copy {n : ℕ} (gs : List Gate) {r : ℕ} (hr : r < gs.length)
    (h : ((gs[r]'hr).op = .and ∨ (gs[r]'hr).op = .or) ∧ (gs[r]'hr).inputs.length ≤ 1) :
    (∃ c, ∀ x : Fin n → Bool, val gs x (n + r) = c) ∨
      ∃ j < n + r, ∀ x : Fin n → Bool, val gs x (n + r) = val gs x j := by
  obtain ⟨hop, hl⟩ := h
  have hv := fun x : Fin n → Bool => mr_val_gate gs x r hr
  generalize hg : gs[r]'hr = g at hop hl hv
  obtain ⟨op, l⟩ := g
  simp only at hop hl
  match l, hl with
  | [], _ =>
    left
    rcases hop with rfl | rfl
    · exact ⟨true, fun x => by rw [hv x]; rfl⟩
    · exact ⟨false, fun x => by rw [hv x]; rfl⟩
  | [y], _ =>
    have hval : ∀ x : Fin n → Bool, val gs x (n + r) = val (gs.take r) x y := by
      intro x
      rw [hv x]
      rcases hop with rfl | rfl <;> simp [GateOp.eval]
    by_cases hy : y < n + r
    · right
      exact ⟨y, hy, fun x => by rw [hval x, ← mr_val_take gs x r y hy]⟩
    · left
      exact ⟨false, fun x => by rw [hval x]; exact mr_val_ge (gs.take r) x y (by simp; omega)⟩

/-! ## The MinCE facts -/

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- M0: a correct circuit with fewer gates and at most one NOT gate contradicts minimality. -/
theorem false_of_shorter (M : MinCE S gates out) (gs' : List Gate) (out' : Fin m → ℕ)
    (hlen : gs'.length < gates.length)
    (hg' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU' : AtMostOneNot gs')
    (hev' : ∀ (w : Fin m) (x : Fin n → Bool), val gs' x (out' w) = decide (∃ v ∈ S w, x v = true)) :
    False := by
  have := M.bound_lt n m S gs' out' hlen M.ce.h2 M.ce.hS hg' hU' hev'
  have := M.ce.hlt
  omega

/-- **R2** (`no_dup`): no two gates compute the same function. -/
theorem no_dup (M : MinCE S gates out) {k k' : ℕ} (hk : k < gates.length) (hk' : k' < gates.length)
    (hkk : k ≠ k') : ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x (n + k') := by
  intro h
  rcases Nat.lt_or_gt_of_ne hkk with hlt | hlt
  · exact M.clean k' (n + k) hk' (by omega) fun x => (h x).symm
  · exact M.clean k (n + k') hk (by omega) h

/-- **R3** (`no_var`): no gate computes an input variable. -/
theorem no_var (M : MinCE S gates out) {k : ℕ} (hk : k < gates.length) {i : ℕ} (hi : i < n) :
    ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x i :=
  M.clean k i hk (by omega)

/-- **R5'** (`not_used`): exactly one NOT gate, and replacing it by either constant gives an incorrect
circuit. -/
theorem not_used (M : MinCE S gates out) :
    (∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not) ∧ AtMostOneNot gates ∧
    (¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true)) ∧
    (¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true)) :=
  ⟨M.exists_not, M.ce.hU, M.essential.1, M.essential.2⟩

/-- **R+** (`observable`): substituting a constant `c` for a wire `u` on a nonempty set `E` of its
readers (AND/OR gates reading `u`, or NOT gates reading `u` first) gives an INCORRECT circuit. A
rewritten reader is constant or a copy of an earlier wire, so a correct substitution would shrink. -/
theorem observable (M : MinCE S gates out) (u : ℕ) (E : Finset ℕ) (hE : E.Nonempty)
    (hEr : ∀ k ∈ E, ∃ hk : k < gates.length,
      (((gates[k]'hk).op = .and ∨ (gates[k]'hk).op = .or) ∧ u ∈ (gates[k]'hk).inputs) ∨
        ((gates[k]'hk).op = .not ∧ (gates[k]'hk).inputs.head? = some u))
    (c : Bool) :
    ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (subGates u (fun _ => c) E gates) x (out w) = decide (∃ v ∈ S w, x v = true) := by
  intro hcor
  have C := M.ce
  have hl1 := subGates_length u (fun _ => c) E gates
  have hg1 := subGates_hg u (fun _ => c) E gates C.hg
  have hU1 := subGates_hU u (fun _ => c) E gates C.hU
  obtain ⟨r, hrE⟩ := hE
  obtain ⟨hr, hshape⟩ := hEr r hrE
  have hr1 : r < (subGates u (fun _ => c) E gates).length := by omega
  have hgr : (subGates u (fun _ => c) E gates)[r]'hr1 = subRd u c (gates[r]'hr) := by
    rw [subGates_getElem]; simp [hrE]
  have hshape' := subRd_shape u c (gates[r]'hr) (C.hg _ (List.getElem_mem hr)).2 hshape
  rw [← hgr] at hshape'
  rcases const_or_copy (n := n) _ hr1 hshape' with ⟨c0, hc0⟩ | ⟨j, hj, hcopy⟩
  · by_cases hout : ∃ w, out w = n + r
    · obtain ⟨w, hw⟩ := hout
      exact not_const_of_or (Finset.card_pos.mp (by have := C.h2 w; omega)) (hcor w) c0
        fun x => by rw [hw]; exact hc0 x
    · push Not at hout
      obtain ⟨gs', out', hlen, hg', hU', hval⟩ := shrink_of_const _ hg1 hU1 hr1 c0 hc0 out hout
      exact M.false_of_shorter gs' out' (by omega) hg' hU' fun w x => by rw [hval]; exact hcor w x
  · obtain ⟨gs', out', hlen, hg', hU', hval⟩ := shrink_of_copy _ hg1 hU1 hr1 hj hcopy out
    exact M.false_of_shorter gs' out' (by omega) hg' hU' fun w x => by rw [hval]; exact hcor w x

end MinCE

end PEqualNP.Outside.L_meta_951_aux
