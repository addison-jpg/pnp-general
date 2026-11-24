import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Cases
import PEqualNP.W951.Small3
import PEqualNP.Kernel.W951Off

/-!
# R0: point deletion (restriction `x_v := 0`), semantic form

A gate `k` is *dead on* `D = {x | x v = false}` if on `D` its wire equals an earlier wire
(`DCp`) or is constantly true (`DTr`).  (Constant false on `D` is a copy of the input wire `v`.)
`promise_bound`: a circuit that is correct only on `D` for a family avoiding `v` satisfies
`base + #dead ≤ #gates`, given the ordinary bound for shorter circuits.
`DC_lower`: in a correct circuit, `#dead ≥ deg v` when at most one set through `v` has size `≥ 3`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

theorem val_inp {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  have h := val_append [] gs x i (by simpa using hi)
  simp only [List.nil_append] at h
  rw [h, val_nil, dif_pos hi]

theorem val_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k i : ℕ) (hk : k ≤ gs.length)
    (hi : i < n + k) : val (gs.take k) x i = val gs x i := by
  have h := val_append (gs.take k) (gs.drop k) x i (by simp; omega)
  rw [List.take_append_drop] at h
  exact h.symm

theorem val_take_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k i : ℕ)
    (hi : n + k ≤ i) : val (gs.take k) x i = false :=
  val_ge _ _ _ (by simp; omega)

/-- An AND/OR/NOT gate that does not read wire `p` (AND/OR: `p` is not an input; NOT: `p` is not
its first input) is insensitive to `p`. -/
theorem insens_of_unread (p : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (h : ¬ (((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p ∈ g.inputs) ∨
      (g.op = GateOp.not ∧ ∃ rest, g.inputs = p :: rest))) : Insens p g := by
  intro f f' hff
  by_cases hn : g.op = GateOp.not
  · rw [hn]
    rcases hin : g.inputs with _ | ⟨a, rest⟩
    · rfl
    · have hap : a ≠ p := by rintro rfl; exact h (Or.inr ⟨hn, rest, hin⟩)
      simp [GateOp.eval, hff a hap]
  · exact congrArg _ (List.map_congr_left fun a ha =>
      hff a fun e => h (Or.inl ⟨hop.imp_right (·.resolve_right hn), e ▸ ha⟩))

/-- Inputs that agree off wire `p` agree at every wire but `p`, if every gate agrees outright or is
insensitive to `p` (`Kernel.listVal_rel_off` with `R = Eq`). -/
theorem val_congr_of_insens {n : ℕ} (p : ℕ) (gates : List Gate) (x y : Fin n → Bool)
    (hxy : ∀ j : Fin n, (j : ℕ) ≠ p → x j = y j)
    (h : ∀ (k : ℕ) (hk : k < gates.length),
      val gates x (n + k) = val gates y (n + k) ∨ Insens p (gates[k]'hk)) :
    ∀ i, i ≠ p → val gates x i = val gates y i :=
  Kernel.listVal_rel_off Eq (fun _ => rfl) p gates x y hxy h

theorem dropGate_hg (gates : List Gate) (k j n : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ dropGate gates k j n,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg0
  simp only [dropGate, List.mem_append, List.mem_map] at hg0
  rcases hg0 with h | ⟨g0, h0, rfl⟩
  · exact hg g (List.mem_of_mem_take h)
  · have := hg g0 (List.mem_of_mem_drop h0)
    simpa [redirG] using this

theorem dropGate_get' (gates : List Gate) (k j n : ℕ) (hk : k < gates.length) (i : ℕ)
    (hi : i < (dropGate gates k j n).length) :
    ∃ (i0 : ℕ) (h0 : i0 < gates.length), (i < k → i0 = i) ∧ (k ≤ i → i0 = i + 1) ∧
      ((dropGate gates k j n)[i]'hi).op = (gates[i0]'h0).op := by
  have hlen := dropGate_length gates k j n hk
  by_cases hik : i < k
  · refine ⟨i, by omega, fun _ => rfl, fun h => absurd h (by omega), ?_⟩
    simp [dropGate, List.getElem_append_left (show i < (gates.take k).length by simp; omega)]
  · refine ⟨i + 1, by omega, fun h => absurd h hik, fun _ => rfl, ?_⟩
    have hl : (gates.take k).length = k := by simp; omega
    have hge : ¬ i < (gates.take k).length := by rw [hl]; exact hik
    simp only [dropGate, List.getElem_append, hge, dite_false, List.getElem_map,
      List.getElem_drop, redirG]
    congr 2
    rw [hl]; omega

theorem dropGate_hU (gates : List Gate) (k j n : ℕ) (hk : k < gates.length)
    (hU : AtMostOneNot gates) : AtMostOneNot (dropGate gates k j n) := by
  intro i1 i2 hi1 hi2 e1 e2
  obtain ⟨a1, ha1, c1, d1, o1⟩ := dropGate_get' gates k j n hk i1 hi1
  obtain ⟨a2, ha2, c2, d2, o2⟩ := dropGate_get' gates k j n hk i2 hi2
  have := hU a1 a2 ha1 ha2 (o1 ▸ e1) (o2 ▸ e2)
  by_cases q1 : i1 < k <;> by_cases q2 : i2 < k
  · have := c1 q1; have := c2 q2; omega
  · have := c1 q1; have := d2 (by omega); omega
  · have := d1 (by omega); have := c2 q2; omega
  · have := d1 (by omega); have := d2 (by omega); omega

end PEqualNP.Outside.L_meta_951_aux
