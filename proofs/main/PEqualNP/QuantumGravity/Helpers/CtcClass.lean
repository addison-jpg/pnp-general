import PEqualNP.Defs.QuantumGravityCtc
import PEqualNP.Defs.Classes
import PEqualNP.QuantumGravity.Helpers.Ctc
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.Transducer
import PEqualNP.Library.Machines.FirstGRun
import Mathlib.Data.Fintype.BigOperators

/-!
Helpers for L-qg-160 to L-qg-168: the class `PCTC` of a classical closed timelike curve.

* The register map: when the circuit returns a register of the right length, the cut-or-pad
  step does nothing.
* Brun's counter: `bitsSucc` read through the binary value of the register is `+ 1` in
  `ZMod (2 ^ m)`, so the counter search map on `m`-bit registers is conjugate to
  `ctcSearchMap`, and row L-qg-009 carries over.
* Landing on a cycle: after `Fintype.card S` steps every orbit is on a cycle, and the uniform
  distribution on that cycle is consistent.
* Machines: the polynomial-time functions the rows need, built from the combinators in
  `Library/Machines` (`cpt_comp`, `cpt_fst`, `cpt_second`, `filterMap_polyTime`,
  `twoPass_polyTime`, `fst_polyTime`, `Gen.first_polyTime`).
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity

section Register

/-- When the circuit returns a register of exactly `m` bits, the register map keeps it. -/
theorem ctcRegisterMap_toList {next : List Bool × List Bool → List Bool} {x : List Bool} {m : ℕ}
    (r : List.Vector Bool m) (h : (next (x, r.toList)).length = m) :
    (ctcRegisterMap next x m r).toList = next (x, r.toList) :=
  List.take_left' h

/-- A register of `m` bits always exists. -/
instance instNonemptyVector (m : ℕ) : Nonempty (List.Vector Bool m) :=
  ⟨List.Vector.replicate m false⟩

/-- Every register map has a Deutsch-consistent distribution. -/
theorem exists_consistent_register (next : List Bool × List Bool → List Bool) (x : List Bool)
    (m : ℕ) : ∃ μ : PMF (List.Vector Bool m), DeutschConsistent (ctcRegisterMap next x m) μ :=
  exists_consistent _

end Register

section Counter

/-- The binary value of a register, least significant bit first. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: r => b.toNat + 2 * bval r

theorem bitsSucc_length : ∀ r : List Bool, (bitsSucc r).length = r.length
  | [] => rfl
  | false :: _ => rfl
  | true :: r => by simp [bitsSucc, bitsSucc_length r]

theorem bval_lt : ∀ r : List Bool, bval r < 2 ^ r.length
  | [] => by simp [bval]
  | b :: r => by
    have := bval_lt r
    cases b <;> simp [bval, pow_succ] <;> omega

theorem bval_bitsSucc : ∀ r : List Bool, bval (bitsSucc r) = (bval r + 1) % 2 ^ r.length
  | [] => by simp [bval, bitsSucc]
  | false :: r => by
    have := bval_lt r
    simp only [bitsSucc, bval, Bool.toNat_true, Bool.toNat_false, List.length_cons, pow_succ]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  | true :: r => by
    simp only [bitsSucc, bval, Bool.toNat_true, Bool.toNat_false, List.length_cons, pow_succ,
      bval_bitsSucc r]
    rw [show 1 + 2 * bval r + 1 = 2 * (bval r + 1) by ring, mul_comm (2 ^ r.length) 2,
      Nat.mul_mod_mul_left]
    ring

theorem bval_inj : ∀ r s : List Bool, r.length = s.length → bval r = bval s → r = s
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: r, b :: s, h, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [bval] at hv
    have hab : a = b := by
      cases a <;> cases b <;> first
        | rfl
        | (simp only [Bool.toNat_true, Bool.toNat_false] at hv; omega)
    subst hab
    have : bval r = bval s := by omega
    rw [bval_inj r s h this]

/-- The binary value of an `m`-bit register, in `ZMod (2 ^ m)`. -/
def regVal (m : ℕ) (r : List.Vector Bool m) : ZMod (2 ^ m) :=
  (bval r.toList : ZMod (2 ^ m))

theorem regVal_injective (m : ℕ) : Function.Injective (regVal m) := by
  intro r s h
  have hr := bval_lt r.toList
  have hs := bval_lt s.toList
  rw [List.Vector.toList_length] at hr hs
  have h' := congrArg ZMod.val h
  simp only [regVal, ZMod.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at h'
  exact List.Vector.eq _ _ (bval_inj _ _ (by simp) h')

theorem regVal_bijective (m : ℕ) : Function.Bijective (regVal m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨regVal_injective m, by simp [card_vector]⟩

/-- The binary value of the registers, as an equivalence with `ZMod (2 ^ m)`. -/
noncomputable def regEquiv (m : ℕ) : List.Vector Bool m ≃ ZMod (2 ^ m) :=
  Equiv.ofBijective _ (regVal_bijective m)

/-- `bitsSucc` on an `m`-bit register. -/
def vSucc {m : ℕ} (r : List.Vector Bool m) : List.Vector Bool m :=
  ⟨bitsSucc r.toList, (bitsSucc_length _).trans r.toList_length⟩

theorem regVal_vSucc {m : ℕ} (r : List.Vector Bool m) : regVal m (vSucc r) = regVal m r + 1 := by
  simp only [regVal, vSucc, List.Vector.toList_mk, bval_bitsSucc, List.Vector.toList_length]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- Brun's counter search: if some register satisfies `ψ`, every Deutsch-consistent distribution
of the map that keeps a register satisfying `ψ` and adds one to any other charges only registers
that satisfy `ψ`. -/
theorem counter_consistent_support {m : ℕ} (ψ : List.Vector Bool m → Bool)
    (F : List.Vector Bool m → List.Vector Bool m)
    (hF : ∀ r, F r = if ψ r = true then r else vSucc r) (hs : ∃ s, ψ s = true)
    {μ : PMF (List.Vector Bool m)} (hμ : DeutschConsistent F μ) {y : List.Vector Bool m}
    (hy : y ∈ μ.support) : ψ y = true := by
  let e := regEquiv m
  let φ : ZMod (2 ^ m) → Bool := fun z => ψ (e.symm z)
  have he : ∀ r, e r = regVal m r := fun _ => rfl
  have hsemi : Function.Semiconj e F (ctcSearchMap φ) := by
    intro r
    rw [hF r]
    simp only [ctcSearchMap, φ, Equiv.symm_apply_apply]
    split_ifs
    · rfl
    · rw [he, he, regVal_vSucc]
  have hφ : ∃ z, φ z = true := by
    obtain ⟨s, hs⟩ := hs
    exact ⟨e s, by simpa [φ] using hs⟩
  obtain ⟨x, rfl⟩ := mem_range_iterate_of_consistent hμ (2 ^ m) hy
  have key := ctcSearchMap_iterate_sat hφ (e x)
  rw [← hsemi.iterate_right (2 ^ m) x] at key
  simpa [φ] using key

/-- The counter search map written as a register map: on input `x`, keep the register `r` when
`φ (x, r)` holds, otherwise add one to it. -/
theorem counter_register_support (φ : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ)
    (hs : ∃ s : List.Vector Bool m, φ (x, s.toList) = true)
    {μ : PMF (List.Vector Bool m)}
    (hμ : DeutschConsistent
      (ctcRegisterMap (fun q => if φ q = true then q.2 else bitsSucc q.2) x m) μ)
    {y : List.Vector Bool m} (hy : y ∈ μ.support) : φ (x, y.toList) = true := by
  refine counter_consistent_support (fun r => φ (x, r.toList)) _ ?_ hs hμ hy
  intro r
  apply List.Vector.eq
  rw [ctcRegisterMap_toList]
  · split_ifs <;> rfl
  · split_ifs
    · exact r.toList_length
    · exact (bitsSucc_length _).trans r.toList_length

end Counter

section Cycle

variable {S : Type}

/-- After as many steps as there are points, every orbit is on a cycle. -/
theorem periodic_iterate_card [Fintype S] (f : S → S) (x : S) :
    ∃ q : ℕ, f^[q + 1] (f^[Fintype.card S] x) = f^[Fintype.card S] x := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card S + 1) => f^[i.val] x) (by simp)
  have key : ∀ a b : ℕ, a < b → b ≤ Fintype.card S → f^[a] x = f^[b] x →
      ∃ q : ℕ, f^[q + 1] (f^[Fintype.card S] x) = f^[Fintype.card S] x := by
    intro a b hab hb he
    refine ⟨b - a - 1, ?_⟩
    have hk : ∀ k, f^[a + k] x = f^[b + k] x := by
      intro k
      rw [Nat.add_comm a k, Nat.add_comm b k, Function.iterate_add_apply,
        Function.iterate_add_apply, he]
    rw [← Function.iterate_add_apply, show b - a - 1 + 1 + Fintype.card S =
      b + (Fintype.card S - a) by omega, ← hk, show a + (Fintype.card S - a) = Fintype.card S by
      omega]
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h (by omega) heq
  · exact key j i h (by omega) heq.symm

/-- The uniform distribution on the cycle through `y` charges `y`. -/
theorem consistent_of_periodic_mem (f : S → S) (y : S) (q : ℕ) (hy : f^[q + 1] y = y) :
    ∃ μ : PMF S, DeutschConsistent f μ ∧ y ∈ μ.support := by
  have hq : ((q + 1 : ℕ) : ENNReal) ≠ 0 := by simp
  have hsum : ∑ _a : Fin (q + 1), ((q + 1 : ℕ) : ENNReal)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hq (ENNReal.natCast_ne_top _)
  let ν := PMF.ofFintype (fun _ : Fin (q + 1) => ((q + 1 : ℕ) : ENNReal)⁻¹) hsum
  let orbit : Fin (q + 1) → S := fun i => f^[i.val] y
  refine ⟨ν.map orbit, ?_, ?_⟩
  · have hrot : f ∘ orbit = orbit ∘ finRotate (q + 1) := by
      funext i
      simp only [Function.comp_apply, orbit]
      rw [coe_finRotate]
      split_ifs with hi
      · subst hi
        rw [← Function.iterate_succ_apply' f, Fin.val_last, Function.iterate_zero_apply]
        exact hy
      · exact (Function.iterate_succ_apply' f i.val y).symm
    unfold DeutschConsistent
    rw [PMF.map_comp, hrot, ← PMF.map_comp, map_equiv_ofFintype_const]
  · rw [PMF.support_map]
    refine ⟨0, ?_, rfl⟩
    simp [ν, PMF.support_ofFintype]

/-- After as many steps as there are points, the orbit of every point is charged by some
Deutsch-consistent distribution. -/
theorem consistent_mem_iterate_card [Fintype S] (f : S → S) (x : S) :
    ∃ μ : PMF S, DeutschConsistent f μ ∧ f^[Fintype.card S] x ∈ μ.support := by
  obtain ⟨q, hq⟩ := periodic_iterate_card f x
  exact consistent_of_periodic_mem f _ q hq

end Cycle

section Machines

open PEqualNP.Library PEqualNP.Library.Machines

/-- A function of the input alone, read off the pair (input, register). -/
theorem cpt_of_fst {f : List Bool → Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool f) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => f q.1) :=
  cpt_comp cpt_fst hf

/-- The circuit that always returns the empty string. -/
theorem cpt_nil :
    ComputableInPolyTime encodePair (fun y : List Bool => y)
      (fun _ : List Bool × List Bool => ([] : List Bool)) :=
  filterMap_polyTime _ _ _ (fun _ : Bool ⊕ Bool => (none : Option Bool))
    (fun q => (Gen.filterMap_const_none (encodePair q)).symm)

/-- Negating the answer bit. -/
theorem cpt_not :
    ComputableInPolyTime Computability.encodeBool Computability.encodeBool (fun b : Bool => !b) :=
  filterMap_polyTime _ _ _ (fun b : Bool => some (!b)) (fun _ => rfl)

/-! ### Reading the first bit of the register -/

/-- The transducer that skips the input and writes the first bit of the register, or `false`
when the register is empty. The state says whether the bit has been written. -/
def headDelta : Bool → Bool ⊕ Bool → Bool × Option Bool
  | false, Sum.inl _ => (false, none)
  | false, Sum.inr b => (true, some b)
  | true, _ => (true, none)

/-- At the end: `false` when the register was empty. -/
def headFin : Bool → Option Bool
  | false => some false
  | true => none

theorem fstRun_head_done (l : List (Bool ⊕ Bool)) : fstRun headDelta headFin true l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, headDelta, ih]

theorem fstRun_head_reg (r : List Bool) :
    fstRun headDelta headFin false (r.map Sum.inr) = [r.headD false] := by
  cases r with
  | nil => rfl
  | cons b r => simp [fstRun, headDelta, fstRun_head_done]

theorem fstRun_head_inp (x : List Bool) (l : List (Bool ⊕ Bool)) :
    fstRun headDelta headFin false (x.map Sum.inl ++ l) = fstRun headDelta headFin false l := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [fstRun, headDelta] using ih

/-- Reading the first bit of the register. -/
theorem cpt_regHead :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => q.2.headD false) :=
  fst_polyTime _ _ _ headDelta headFin false (fun q => by
    rw [encodePair, fstRun_head_inp, fstRun_head_reg]; rfl)

/-! ### Decoding a witness from the register -/

/-- The witness a register stands for: drop the leading `false` bits and the first `true`
bit. Every string of length at most `k` is the witness of some register of `k + 1` bits. -/
def regWitness : List Bool → List Bool
  | [] => []
  | false :: r => regWitness r
  | true :: r => r

/-- The transducer for `regWitness`: the state says whether the first `true` bit was read. -/
def witDelta : Bool → Bool → Bool × Option Bool
  | false, b => (b, none)
  | true, b => (true, some b)

theorem fstRun_wit_copy (l : List Bool) :
    fstRun witDelta (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, witDelta, ih]

theorem fstRun_wit (l : List Bool) :
    fstRun witDelta (fun _ => none) false l = regWitness l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a
    · simpa [fstRun, witDelta, regWitness] using ih
    · simp [fstRun, witDelta, regWitness, fstRun_wit_copy]

theorem cpt_regWitness :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) regWitness :=
  fst_polyTime _ _ _ witDelta (fun _ => none) false (fun l => (fstRun_wit l).symm)

theorem regWitness_length : ∀ r : List Bool, (regWitness r).length ≤ r.length - 1
  | [] => by simp [regWitness]
  | false :: r => by
    have := regWitness_length r
    simp only [regWitness, List.length_cons]
    omega
  | true :: r => by simp [regWitness]

theorem regWitness_pad (w : List Bool) :
    ∀ k : ℕ, regWitness (List.replicate k false ++ true :: w) = w
  | 0 => rfl
  | k + 1 => by
    simp only [List.replicate_succ, List.cons_append, regWitness]
    exact regWitness_pad w k

/-! ### The counter step: keep the register or add one to it -/

/-- The transducer that reads the answer bit `b` first, then copies the register when `b`
holds and adds one to it otherwise. States: `none` before the bit, `some false` copying,
`some true` carrying. -/
def selDelta : Option Bool → Bool ⊕ Bool → Option Bool × Option Bool
  | none, Sum.inl b => (some (!b), none)
  | none, Sum.inr _ => (none, none)
  | some c, Sum.inl _ => (some c, none)
  | some false, Sum.inr a => (some false, some a)
  | some true, Sum.inr a => (some a, some (!a))

theorem fstRun_sel_copy (r : List Bool) :
    fstRun selDelta (fun _ => none) (some false) (r.map Sum.inr) = r := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [fstRun, selDelta, ih]

theorem fstRun_sel_carry (r : List Bool) :
    fstRun selDelta (fun _ => none) (some true) (r.map Sum.inr) = bitsSucc r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases a
    · simp [fstRun, selDelta, bitsSucc, fstRun_sel_copy]
    · simp [fstRun, selDelta, bitsSucc, ih]

/-- The counter step `(b, r) ↦ if b then r else r + 1`, the answer bit first. -/
theorem cpt_sel :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun y : List Bool => y)
      (fun p : Bool × List Bool => if p.1 = true then p.2 else bitsSucc p.2)) :=
  fst_polyTime _ _ _ selDelta (fun _ => none) none (fun p => by
    obtain ⟨b, r⟩ := p
    cases b
    · simp [Gen.gpair, Computability.encodeBool, fstRun, selDelta, fstRun_sel_carry]
    · simp [Gen.gpair, Computability.encodeBool, fstRun, selDelta, fstRun_sel_copy])

/-- Copying the register next to the pair. -/
theorem cpt_copyReg :
    Nonempty (Turing.TM2ComputableInPolyTime encodePair
      (fun p : (List Bool × List Bool) × List Bool => Gen.gpair (encodePair p.1, p.2))
      (fun q : List Bool × List Bool => (q, q.2))) := by
  refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s))
    (fun s => Sum.elim (fun _ => none) (fun b => some (Sum.inr b)) s) ?_
  rintro ⟨x, r⟩
  simp [Gen.gpair, encodePair, List.filterMap_append, List.filterMap_map, Function.comp_def]

/-- The counter circuit: on the pair (input, register), keep the register when the
polynomial-time test `fv` holds and add one to it otherwise. -/
theorem cpt_counter {fv : List Bool × List Bool → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool fv) :
    ComputableInPolyTime encodePair (fun y : List Bool => y)
      (fun q : List Bool × List Bool => if fv q = true then q.2 else bitsSucc q.2) := by
  obtain ⟨c⟩ := hv
  have h23 := Gen.first_polyTime (C := Bool) encodePair Computability.encodeBool fv c
  exact cpt_comp (cpt_comp cpt_copyReg h23) cpt_sel

end Machines

section Class

open PEqualNP.Library PEqualNP.Library.Machines

/-- P is inside `PCTC`: answer from the input alone, with an empty circuit on the curve. -/
theorem P_subset_PCTC : P ⊆ PCTC := by
  intro L hL
  obtain ⟨f, hf, hc⟩ := hL
  refine ⟨0, fun q => f q.1, fun _ => [], cpt_of_fst hc, cpt_nil, ?_⟩
  intro x _ _ _ _
  exact (hf x).symm

/-- NP is inside `PCTC`: Brun's counter on a register of `p + 1` bits, each register standing
for the witness `regWitness r`. -/
theorem NP_subset_PCTC : NP ⊆ PCTC := by
  intro L hL
  obtain ⟨R, p, ⟨fR, hfR, hc⟩, hLR⟩ := hL
  let φ : List Bool × List Bool → Bool := fun q => fR (q.1, regWitness q.2)
  have hφ : ComputableInPolyTime encodePair Computability.encodeBool φ :=
    cpt_comp (cpt_second cpt_regWitness) hc
  refine ⟨p + 1, φ, fun q => if φ q = true then q.2 else bitsSucc q.2, hφ, cpt_counter hφ, ?_⟩
  intro x μ hμ r hr
  have hm : (p + 1).eval x.length = p.eval x.length + 1 := by simp
  constructor
  · intro h
    rw [hLR]
    refine ⟨regWitness r.toList, ?_, (hfR _).mpr h⟩
    have h1 := regWitness_length r.toList
    have h2 : r.toList.length = p.eval x.length + 1 := r.toList_length.trans hm
    omega
  · intro hx
    obtain ⟨w, hw, hwR⟩ := (hLR x).mp hx
    refine counter_register_support φ x _ ?_ hμ hr
    refine ⟨⟨List.replicate (p.eval x.length - w.length) false ++ true :: w, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons, hm]
      omega
    · show fR (x, regWitness (List.replicate _ false ++ true :: w)) = true
      rw [regWitness_pad]
      exact (hfR _).mp hwR

/-- `PCTC` is closed under complement: negate the read-out. -/
theorem PCTC_compl {L : Language Bool} (hL : L ∈ PCTC) : Lᶜ ∈ PCTC := by
  obtain ⟨p, ans, next, ha, hn, h⟩ := hL
  refine ⟨p, fun q => !ans q, next, cpt_comp ha cpt_not, hn, ?_⟩
  intro x μ hμ r hr
  change (!ans (x, r.toList)) = true ↔ ¬ x ∈ L
  rw [← h x μ hμ r hr]
  cases ans (x, r.toList) <;> simp

/-- coNP is inside `PCTC`. -/
theorem coNP_subset_PCTC : coNP ⊆ PCTC := by
  intro L hL
  have := PCTC_compl (NP_subset_PCTC hL)
  rwa [compl_compl] at this

/-- With "some consistent distribution" in place of "every", every language would be decided:
leave a one-bit register unchanged and read the bit. -/
theorem some_consistent_decides (L : Language Bool) :
    ∃ (p : Polynomial ℕ) (ans : List Bool × List Bool → Bool)
      (next : List Bool × List Bool → List Bool),
      ComputableInPolyTime encodePair Computability.encodeBool ans ∧
        ComputableInPolyTime encodePair (fun y : List Bool => y) next ∧
        ∀ x : List Bool, ∃ μ : PMF (List.Vector Bool (p.eval x.length)),
          DeutschConsistent (ctcRegisterMap next x (p.eval x.length)) μ ∧
            ∀ r ∈ μ.support, (ans (x, r.toList) = true ↔ x ∈ L) := by
  classical
  refine ⟨1, fun q => q.2.headD false, fun q => q.2, cpt_regHead, cpt_snd, fun x => ?_⟩
  let v : List.Vector Bool ((1 : Polynomial ℕ).eval x.length) :=
    List.Vector.replicate _ (decide (x ∈ L))
  refine ⟨PMF.pure v, ?_, ?_⟩
  · unfold DeutschConsistent
    rw [PMF.pure_map]
    congr 1
    exact List.Vector.eq _ _ (ctcRegisterMap_toList v v.toList_length)
  · intro r hr
    rw [PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [v, List.Vector.replicate, List.Vector.toList]

/-- The exponential-time decision rule: run the register map `2 ^ m` times from any register
and read the answer there. -/
theorem PCTC_iterate_rule {L : Language Bool} (hL : L ∈ PCTC) :
    ∃ (p : Polynomial ℕ) (ans : List Bool × List Bool → Bool)
      (next : List Bool × List Bool → List Bool),
      ComputableInPolyTime encodePair Computability.encodeBool ans ∧
        ComputableInPolyTime encodePair (fun y : List Bool => y) next ∧
        ∀ (x : List Bool) (r₀ : List.Vector Bool (p.eval x.length)),
          (x ∈ L ↔ ans (x, ((ctcRegisterMap next x (p.eval x.length))^[2 ^ p.eval x.length]
            r₀).toList) = true) := by
  obtain ⟨p, ans, next, ha, hn, h⟩ := hL
  refine ⟨p, ans, next, ha, hn, fun x r₀ => ?_⟩
  obtain ⟨μ, hμ, hmem⟩ := consistent_mem_iterate_card (ctcRegisterMap next x (p.eval x.length)) r₀
  rw [card_vector, Fintype.card_bool] at hmem
  exact (h x μ hμ _ hmem).symm

end Class

end PEqualNP.QuantumGravity.Helpers
