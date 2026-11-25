import Mathlib
import PEqualNP.W951.Open.FlipHall

/-!
# PointLemma: the sensitivity set at the all-zero point (B8, from B6 section 2)

`sens f` is the set of `u` where `f` at `e_u` differs from `f` at `0`. For a gate
`F = opB op (L ^^ s) (R ^^ t)` it is a union, intersection or difference of `sens L` and `sens R`;
a thin function meets each set in at most one point; and `sens (orS S) = S`.
-/

namespace PEqualNP.W951.PointLemma

open Finset PEqualNP.W951.FlipHall

variable {n : ℕ}

/-- the sensitivity set at the all-zero point -/
def sens (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun u => f (Function.update (fun _ => false) u true) ≠ f (fun _ => false))

lemma mem_sens (f : (Fin n → Bool) → Bool) (u : Fin n) :
    u ∈ sens f ↔ f (Function.update (fun _ => false) u true) ≠ f (fun _ => false) := by
  simp [sens]

/-- the gate lemma -/
theorem sens_gate (L R : (Fin n → Bool) → Bool) (op s t : Bool) :
    sens (fun x => opB op (L x ^^ s) (R x ^^ t)) = sens L ∪ sens R ∨
    sens (fun x => opB op (L x ^^ s) (R x ^^ t)) = sens L ∩ sens R ∨
    sens (fun x => opB op (L x ^^ s) (R x ^^ t)) = sens L \ sens R ∨
    sens (fun x => opB op (L x ^^ s) (R x ^^ t)) = sens R \ sens L := by
  cases hL0 : L (fun _ => false) <;> cases hR0 : R (fun _ => false) <;> cases op <;>
    cases s <;> cases t <;>
    first
    | (left; ext u; simp only [mem_union, mem_sens, hL0, hR0]
       generalize L (Function.update (fun _ => false) u true) = l1
       generalize R (Function.update (fun _ => false) u true) = r1
       cases l1 <;> cases r1 <;> simp [opB] <;> done)
    | (right; left; ext u; simp only [mem_inter, mem_sens, hL0, hR0]
       generalize L (Function.update (fun _ => false) u true) = l1
       generalize R (Function.update (fun _ => false) u true) = r1
       cases l1 <;> cases r1 <;> simp [opB] <;> done)
    | (right; right; left; ext u; simp only [mem_sdiff, mem_sens, hL0, hR0]
       generalize L (Function.update (fun _ => false) u true) = l1
       generalize R (Function.update (fun _ => false) u true) = r1
       cases l1 <;> cases r1 <;> simp [opB] <;> done)
    | (right; right; right; ext u; simp only [mem_sdiff, mem_sens, hL0, hR0]
       generalize L (Function.update (fun _ => false) u true) = l1
       generalize R (Function.update (fun _ => false) u true) = r1
       cases l1 <;> cases r1 <;> simp [opB] <;> done)

/-- a thin function meets each set in at most one sensitive point -/
theorem sens_thin_card (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (hf : Thin S f) :
    (sens f ∩ S).card ≤ 1 := by
  have h := hf (fun _ => false) (fun u _ => rfl)
  have : sens f ∩ S = dset S f (fun _ => false) := by
    ext u
    rw [mem_inter, mem_sens, dset, Finset.mem_filter]
    exact and_comm
  rw [this]; exact h

/-- the sensitivity set of `OR(S)` is `S` -/
theorem sens_orS (S : Finset (Fin n)) : sens (orS S) = S := by
  ext u
  rw [mem_sens]
  have h0 : orS S (fun _ => false) = false := orS_zero (fun u _ => rfl)
  rw [h0]
  by_cases hu : u ∈ S
  · have := orS_flip S (fun _ => false) hu
    simp only [FlipHall.flip] at this
    simp [this, hu]
  · have := orS_zero (isZero_flip (S := S) (Z := fun _ => false) (fun u _ => rfl) hu)
    simp only [FlipHall.flip] at this
    simp [this, hu]

end PEqualNP.W951.PointLemma
