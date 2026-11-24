import PEqualNP.W951.SDRWitness

/-! SDRWitnessCorrect: the circuits of `SDRWitness` are correct (each output computes `OR (S w)`) and
satisfy the set conditions of 951 (sets of size at least 2, pairwise intersections of size at most 1),
checked by the kernel (`decide` over all inputs), bundled with MergeSDR. ADV3 (`n = 12`) is left out:
its correctness check over `2^12` inputs takes about 20 minutes (checked in Python, w951 `is_correct`).
Cost: about 2 minutes for the circuits below. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Config (I): correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrCfgI_correct :
    (∀ (w : Fin 3) (x : Fin 9 → Bool),
      val sdrCfgIGates x (sdrCfgIOut w) = decide (∃ v ∈ sdrCfgIS w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrCfgIS w).card) ∧ (∀ a b : Fin 3, a ≠ b → (sdrCfgIS a ∩ sdrCfgIS b).card ≤ 1) ∧
    MergeSDR sdrCfgIS sdrCfgIGates :=
  ⟨by decide, by decide, by decide, sdrCfgI⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- ADV4: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrAdv4_correct :
    (∀ (w : Fin 2) (x : Fin 8 → Bool),
      val sdrAdv4Gates x (sdrAdv4Out w) = decide (∃ v ∈ sdrAdv4S w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrAdv4S w).card) ∧ (∀ a b : Fin 2, a ≠ b → (sdrAdv4S a ∩ sdrAdv4S b).card ≤ 1) ∧
    MergeSDR sdrAdv4S sdrAdv4Gates :=
  ⟨by decide, by decide, by decide, sdrAdv4⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- payment/ce3: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrCe3_correct :
    (∀ (w : Fin 4) (x : Fin 8 → Bool),
      val sdrCe3Gates x (sdrCe3Out w) = decide (∃ v ∈ sdrCe3S w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrCe3S w).card) ∧ (∀ a b : Fin 4, a ≠ b → (sdrCe3S a ∩ sdrCe3S b).card ≤ 1) ∧
    MergeSDR sdrCe3S sdrCe3Gates :=
  ⟨by decide, by decide, by decide, sdrCe3⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- HARD4: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrHard4_correct :
    (∀ (w : Fin 2) (x : Fin 6 → Bool),
      val sdrHard4Gates x (sdrHard4Out w) = decide (∃ v ∈ sdrHard4S w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrHard4S w).card) ∧ (∀ a b : Fin 2, a ≠ b → (sdrHard4S a ∩ sdrHard4S b).card ≤ 1) ∧
    MergeSDR sdrHard4S sdrHard4Gates :=
  ⟨by decide, by decide, by decide, sdrHard4⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- cxr: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrCxr_correct :
    (∀ (w : Fin 2) (x : Fin 8 → Bool),
      val sdrCxrGates x (sdrCxrOut w) = decide (∃ v ∈ sdrCxrS w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrCxrS w).card) ∧ (∀ a b : Fin 2, a ≠ b → (sdrCxrS a ∩ sdrCxrS b).card ≤ 1) ∧
    MergeSDR sdrCxrS sdrCxrGates :=
  ⟨by decide, by decide, by decide, sdrCxr⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- scaffold's HARD4: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrHard4s_correct :
    (∀ (w : Fin 2) (x : Fin 6 → Bool),
      val sdrHard4sGates x (sdrHard4sOut w) = decide (∃ v ∈ sdrHard4sS w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrHard4sS w).card) ∧ (∀ a b : Fin 2, a ≠ b → (sdrHard4sS a ∩ sdrHard4sS b).card ≤ 1) ∧
    MergeSDR sdrHard4sS sdrHard4sGates :=
  ⟨by decide, by decide, by decide, sdrHard4s⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- unique-SDR circuit 0: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrUniq0_correct :
    (∀ (w : Fin 3) (x : Fin 4 → Bool),
      val sdrUniq0Gates x (sdrUniq0Out w) = decide (∃ v ∈ sdrUniq0S w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrUniq0S w).card) ∧ (∀ a b : Fin 3, a ≠ b → (sdrUniq0S a ∩ sdrUniq0S b).card ≤ 1) ∧
    MergeSDR sdrUniq0S sdrUniq0Gates :=
  ⟨by decide, by decide, by decide, sdrUniq0⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- unique-SDR circuit 2: correct, (1,1)-disjoint sets of size at least 2, and MergeSDR. -/
theorem sdrUniq2_correct :
    (∀ (w : Fin 5) (x : Fin 4 → Bool),
      val sdrUniq2Gates x (sdrUniq2Out w) = decide (∃ v ∈ sdrUniq2S w, x v = true)) ∧
    (∀ w, 2 ≤ (sdrUniq2S w).card) ∧ (∀ a b : Fin 5, a ≠ b → (sdrUniq2S a ∩ sdrUniq2S b).card ≤ 1) ∧
    MergeSDR sdrUniq2S sdrUniq2Gates :=
  ⟨by decide, by decide, by decide, sdrUniq2⟩

end PEqualNP.Outside.L_meta_951_aux
