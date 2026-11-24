/-
Config (I) (front-match w9/fb/cfgI.json), world-0 certificate, checked by the kernel from the circuit itself.
Python (export_witness.py) only suggested the statement; here every merge set is recomputed in Lean.
Merge set M_z(w) (Lemma M, w951 systems.system + merges): walk the gates in order; a gate that is 0 at z
"sees" the units u in S_w whose atom z + e_u makes it 1; if those units lie in >= 2 union-find blocks, the gate
merges them. Theorem: for S0 and S1, every zero point z with h(z) = 0 has gate 13 (= h) in M_z(w).
So if both 4-sets are charged only in h = 0 worlds, gate 13 carries load 2.
-/
namespace CfgI

inductive Op | and | or | not
deriving DecidableEq

def n : Nat := 9
def gates : List (Op × Nat × Nat) := [(.or, 1, 4), (.or, 2, 5), (.or, 3, 6), (.or, 9, 10), (.or, 12, 11), (.not, 13, 13), (.or, 13, 0), (.or, 0, 14), (.or, 16, 4), (.or, 17, 5), (.or, 18, 6), (.and, 15, 19), (.and, 7, 13), (.or, 21, 8), (.or, 22, 14), (.or, 7, 13), (.or, 24, 8), (.and, 23, 25), (.or, 0, 21), (.or, 27, 1), (.or, 28, 2), (.or, 16, 1), (.or, 30, 2), (.and, 29, 31), (.or, 32, 3)]

/-- values of all wires (inputs 0..n-1, then gates) at point x (bit i = x_i) -/
def eval (x : Nat) : List Bool :=
  gates.foldl (fun (w : List Bool) (g : Op × Nat × Nat) =>
    let a := w.getD g.2.1 false
    let b := w.getD g.2.2 false
    w ++ [match g.1 with | .and => a && b | .or => a || b | .not => !a])
    ((List.range n).map fun i => x.testBit i)

def hWire : Nat := 13

/-- union-find by relabelling: lab is a list of (unit, label) -/
def relabel (lab : List (Nat × Nat)) (old new : Nat) : List (Nat × Nat) :=
  lab.map fun p => if p.2 = old then (p.1, new) else p

def labelOf (lab : List (Nat × Nat)) (u : Nat) : Nat := ((lab.find? fun p => p.1 = u).map Prod.snd).getD u

/-- merge gates of set S at zero point z -/
def merges (S : List Nat) (z : Nat) : List Nat :=
  let wz := eval z
  let at_ := S.map fun u => (u, eval (z ||| (1 <<< u)))
  let step := fun (st : List (Nat × Nat) × List Nat) (k : Nat) =>
    let i := n + k
    if wz.getD i true then st else
      let b := (at_.filter fun p => p.2.getD i false).map Prod.fst
      let roots := (b.map (labelOf st.1)).eraseDups
      match roots with
      | r1 :: r2 :: _ => (relabel st.1 r2 r1, st.2 ++ [i])
      | _ => st
  ((List.range gates.length).foldl step (S.map fun u => (u, u), [])).2

def mask (S : List Nat) : Nat := S.foldl (fun m u => m ||| (1 <<< u)) 0

def S0 : List Nat := [0, 1, 2, 3]
def S1 : List Nat := [0, 4, 5, 6]

/-- the finite check: every zero point of S with h = 0 has gate 13 in its merge set -/
def check (S : List Nat) : Bool :=
  (List.range (2 ^ n)).all fun z =>
    !(z &&& mask S == 0) || (eval z).getD hWire true || (merges S z).contains hWire

theorem check_S0 : check S0 = true := by decide +kernel
theorem check_S1 : check S1 = true := by decide +kernel

theorem of_check {S : List Nat} (h : check S = true) :
    ∀ z < 2 ^ n, z &&& mask S = 0 → (eval z).getD hWire true = false → hWire ∈ merges S z := by
  intro z hz hm hh
  have h1 := List.all_eq_true.mp h z (List.mem_range.mpr hz)
  have h2 : (z &&& mask S == 0) = true := by simp [hm]
  rw [h2, hh] at h1
  exact List.contains_iff_mem.mp (by simpa using h1)

/-- World-0 certificate for both 4-sets of Config (I). -/
theorem world0_S0 : ∀ z < 2 ^ n, z &&& mask S0 = 0 → (eval z).getD hWire true = false → hWire ∈ merges S0 z :=
  of_check check_S0

theorem world0_S1 : ∀ z < 2 ^ n, z &&& mask S1 = 0 → (eval z).getD hWire true = false → hWire ∈ merges S1 z :=
  of_check check_S1

/-- sanity: the certificate is not vacuous (z = 0 is an h = 0 zero point of both sets) -/
theorem world0_nonvacuous : (eval 0).getD hWire true = false ∧ hWire ∈ merges S0 0 ∧ hWire ∈ merges S1 0 := by
  decide +kernel

/-! ## MergeFrac dual certificate
Price 1 on each gate of K = {12, 18, 33} (total 3). Every merge set of S0 and every merge set of S1 (all zero
points, no world restriction) meets K, so min_z |M_z(w) ∩ K| >= 1 for w = 0, 1 and the dual value is
>= 2 against |K| = 3 (MergeFrac L* >= 2/3). For S2 the minimum is 0: a zero point with merge set disjoint
from K is exhibited, so this K certifies exactly 2. -/

def S2 : List Nat := [7, 8]
def K : List Nat := [12, 18, 33]

/-- the finite check: every zero point of S has a merge gate in K -/
def checkK (S : List Nat) : Bool :=
  (List.range (2 ^ n)).all fun z =>
    !(z &&& mask S == 0) || (merges S z).any fun g => K.contains g

theorem checkK_S0 : checkK S0 = true := by decide +kernel
theorem checkK_S1 : checkK S1 = true := by decide +kernel

theorem of_checkK {S : List Nat} (h : checkK S = true) :
    ∀ z < 2 ^ n, z &&& mask S = 0 → ∃ g, g ∈ merges S z ∧ g ∈ K := by
  intro z hz hm
  have h1 := List.all_eq_true.mp h z (List.mem_range.mpr hz)
  have h2 : (z &&& mask S == 0) = true := by simp [hm]
  rw [h2] at h1
  have h3 : ((merges S z).any fun g => K.contains g) = true := by simpa using h1
  obtain ⟨g, hg, hk⟩ := List.any_eq_true.mp h3
  exact ⟨g, hg, List.contains_iff_mem.mp hk⟩

/-- MergeFrac dual certificate, set 0: every merge set of S0 meets K. -/
theorem mergefrac_S0 : ∀ z < 2 ^ n, z &&& mask S0 = 0 → ∃ g, g ∈ merges S0 z ∧ g ∈ K :=
  of_checkK checkK_S0

/-- MergeFrac dual certificate, set 1: every merge set of S1 meets K. -/
theorem mergefrac_S1 : ∀ z < 2 ^ n, z &&& mask S1 = 0 → ∃ g, g ∈ merges S1 z ∧ g ∈ K :=
  of_checkK checkK_S1

/-- Set 2 contributes 0: the zero point z = 0 of S2 has a merge set disjoint from K. -/
theorem mergefrac_S2_zero : 0 < 2 ^ n ∧ 0 &&& mask S2 = 0 ∧ ∀ g, g ∈ merges S2 0 → g ∉ K := by
  decide +kernel

/-- the count of zero points is the expected one (32 for the 4-sets): the checks are not vacuous -/
theorem zero_points_count :
    ((List.range (2 ^ n)).filter fun z => z &&& mask S0 == 0).length = 32 ∧
    ((List.range (2 ^ n)).filter fun z => z &&& mask S1 == 0).length = 32 ∧
    K.length = 3 := by
  decide +kernel

end CfgI

#print axioms CfgI.world0_S0
#print axioms CfgI.world0_S1
#print axioms CfgI.world0_nonvacuous
#print axioms CfgI.mergefrac_S0
#print axioms CfgI.mergefrac_S1
#print axioms CfgI.mergefrac_S2_zero
#print axioms CfgI.zero_points_count
