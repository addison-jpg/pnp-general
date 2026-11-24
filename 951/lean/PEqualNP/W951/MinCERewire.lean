import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCERed

/-!
# MinCERewire: R6, rewiring (coord 14:13)

A local change that keeps every output correct, adds no NOT gate and leaves some gate unread saves a gate.
Since the unread gate can be dropped, this contradicts minimality.

* `MinCE.no_dead`: no correct circuit with at most `s` gates and at most one NOT has an unread non-output
  gate (drop it, `val_dropDead`, then `MinCE.false_of_shorter`).
* `rewire gates j pos f`: input number `pos` of gate `j` now reads wire `f`; `rewire_length`, `rewire_hg`,
  `rewire_hU` (no new NOT).
* **`MinCE.no_rewire`** (R6): in a minimal counterexample, no single rewire keeps every output correct
  and leaves a gate unread.

Data (cTAHG, board agents/cTAHG-ddcore.md §4, tools/kill_tests/rewire_r6.py): MATCH-C (the refutation of the
F2 step at non-local cubes under R1-R5' and R+) is NOT R6-irreducible. Its NOT gate may read the output
x_{u_0} ∨ x_{a_0} of P_0 instead of `h`, freeing the h tree, and a greedy R6 reduction ends at a circuit
where the F2 step holds. cxT2 (fc) is R+-clean and R6-irreducible.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- **Rewire** input number `pos` of gate `j` to the wire `f`. -/
def rewire (gates : List Gate) (j pos f : ℕ) : List Gate :=
  gates.modify j fun g => ⟨g.op, g.inputs.set pos f⟩

theorem rewire_length (gates : List Gate) (j pos f : ℕ) :
    (rewire gates j pos f).length = gates.length := by
  simp [rewire]

theorem rewire_getElem (gates : List Gate) (j pos f i : ℕ) (hi : i < (rewire gates j pos f).length) :
    (rewire gates j pos f)[i] =
      if j = i then ⟨(gates[i]'(by rw [rewire_length] at hi; exact hi)).op,
        (gates[i]'(by rw [rewire_length] at hi; exact hi)).inputs.set pos f⟩
      else gates[i]'(by rw [rewire_length] at hi; exact hi) := by
  simp only [rewire, List.getElem_modify]

theorem rewire_hg (gates : List Gate) (j pos f : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ rewire gates j pos f, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
  intro g hgm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgm
  have hi' : i < gates.length := by rw [rewire_length] at hi; exact hi
  have h := hg _ (List.getElem_mem hi')
  rw [rewire_getElem]
  split_ifs
  · exact ⟨h.1, by rw [List.length_set]; exact h.2⟩
  · exact h

theorem rewire_hU (gates : List Gate) (j pos f : ℕ) (hU : AtMostOneNot gates) :
    AtMostOneNot (rewire gates j pos f) := by
  intro i1 i2 h1 h2 e1 e2
  have h1' : i1 < gates.length := by rw [rewire_length] at h1; exact h1
  have h2' : i2 < gates.length := by rw [rewire_length] at h2; exact h2
  have op_eq : ∀ (i : ℕ) (hi : i < (rewire gates j pos f).length) (hi' : i < gates.length),
      ((rewire gates j pos f)[i]'hi).op = (gates[i]'hi').op := by
    intro i hi hi'
    rw [rewire_getElem]
    split_ifs <;> rfl
  rw [op_eq i1 h1 h1'] at e1
  rw [op_eq i2 h2 h2'] at e2
  exact hU i1 i2 h1' h2' e1 e2

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- **No dead gate in any correct circuit of size at most `s`**: drop it and get a shorter correct
circuit. -/
theorem no_dead (M : MinCE S gates out) (gs' : List Gate) (out' : Fin m → ℕ)
    (hlen : gs'.length ≤ gates.length)
    (hg' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU' : AtMostOneNot gs')
    (hev' : ∀ (w : Fin m) (x : Fin n → Bool), val gs' x (out' w) = decide (∃ v ∈ S w, x v = true))
    {k : ℕ} (hk : k < gs'.length) (hno : ∀ g ∈ gs', n + k ∉ g.inputs)
    (hout : ∀ w, out' w ≠ n + k) : False := by
  refine M.false_of_shorter (dropGate gs' k 0 n) (fun w => redir (n + k) 0 (out' w)) ?_
    (dropGate_hg gs' k 0 n hg') (dropGate_hU gs' k 0 n hk hU') fun w x => ?_
  · have := dropGate_length gs' k 0 n hk
    omega
  · rw [val_dropDead gs' k 0 hk hno x (out' w) (hout w)]
    exact hev' w x

/-- **R6 (rewiring)**: in a minimal counterexample, no single rewire of a gate input keeps every output
correct and leaves some non-output gate unread. -/
theorem no_rewire (M : MinCE S gates out) (j pos f : ℕ)
    (hev' : ∀ (w : Fin m) (x : Fin n → Bool),
      val (rewire gates j pos f) x (out w) = decide (∃ v ∈ S w, x v = true))
    {k : ℕ} (hk : k < gates.length) (hno : ∀ g ∈ rewire gates j pos f, n + k ∉ g.inputs)
    (hout : ∀ w, out w ≠ n + k) : False :=
  M.no_dead (rewire gates j pos f) out (by rw [rewire_length]) (rewire_hg gates j pos f M.ce.hg)
    (rewire_hU gates j pos f M.ce.hU) hev' (by rw [rewire_length]; exact hk) hno hout

end MinCE

end PEqualNP.Outside.L_meta_951_aux
