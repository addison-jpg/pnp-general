import PEqualNP.QuantumGravity.Helpers.CtcClass
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Evasion.SpaceDraft

/-!
# PSPACE ⊆ P_CTC, the deterministic Aaronson–Watrous construction, up to one named lemma

Aaronson and Watrous (arXiv:0808.2669, deterministic case): the curve register holds an answer
bit and a configuration of a space-bounded machine. One step of the circuit:

* if the configuration has halted, write its answer into the answer bit and reset the
  configuration to the initial one;
* otherwise, run one machine step and keep the answer bit.

Proved here, standard axioms only:

* `answer_eventually_const`: for a finite step system in which every configuration reaches a
  halted one, after a fixed number `T` of steps of the reset map the answer bit is the answer of
  the first halted configuration on the orbit of `start`, whatever the starting point. With
  `mem_range_iterate_of_consistent` this charges every Deutsch-consistent distribution only on
  registers whose bit is that answer (`consistent_support_answer`).
* `PCTC_of_stepEncoding`: the reset map is built as a polynomial-time circuit on the repo's
  exact `PCTC` (cut-or-pad register map, `encodePair` input, `encodeBool` read-out) from any
  `StepEncoding` of `L`: polynomial-time functions for the initial configuration, one step,
  the halting test and the answer, sound in the sense of `EncodingSound`.
* `PSPACE_subset_PCTC_of_stepEncoding`: PSPACE ⊆ PCTC given `PspaceStepEncodingLemma`.

Open (the named lemma), `PspaceStepEncodingLemma`: every language of `Library.PSPACE`
(`Evasion/SpaceDraft.lean`, a draft definition on Mathlib's `Turing.FinTM2`) has a
`StepEncoding`. Its content: write the configurations of a polynomial-space `FinTM2` machine,
together with a clock of polynomially many bits, as bit strings of one polynomial length; one
step (machine step, clock tick, halting when the machine halts or the clock overflows) is
polynomial-time; from the initial configuration the machine halts before the clock overflows
(a pigeonhole bound on the at most `2 ^ poly` configurations of bounded space).

With L169 (`PCTC ⊆ EXP`) this gives PSPACE ⊆ PCTC ⊆ EXP modulo the lemma; the equality
P_CTC = PSPACE also needs PCTC ⊆ PSPACE, which is not in the repository.
-/

namespace PEqualNP.QuantumGravity.Open.PspaceCtc

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Helpers

local notation "CPTb" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Part 1: the reset map with an answer bit, on any finite type -/

section Reset

variable {α : Type} (step : α → α) (halted out : α → Bool) (start : α)

/-- The reset map: on a halted configuration write its answer and go back to `start`; otherwise
step and keep the bit. -/
def resetAns (z : Bool × α) : Bool × α :=
  if halted z.2 then (out z.2, start) else (z.1, step z.2)

theorem resetAns_iterate_of_not_halted (b : Bool) (c : α) :
    ∀ j, (∀ i < j, halted (step^[i] c) = false) →
      (resetAns step halted out start)^[j] (b, c) = (b, step^[j] c)
  | 0, _ => rfl
  | j + 1, h => by
    rw [Function.iterate_succ_apply',
      resetAns_iterate_of_not_halted b c j (fun i hi => h i (by omega)),
      Function.iterate_succ_apply']
    simp [resetAns, h j (by omega)]

theorem resetAns_iterate_first_halt (b : Bool) (c : α) (t : ℕ)
    (ht : halted (step^[t] c) = true) (hmin : ∀ i < t, halted (step^[i] c) = false) :
    (resetAns step halted out start)^[t + 1] (b, c) = (out (step^[t] c), start) := by
  rw [Function.iterate_succ_apply', resetAns_iterate_of_not_halted step halted out start b c t hmin]
  simp [resetAns, ht]

/-- After a fixed number of steps the answer bit of the reset map is the answer of the first
halted configuration on the orbit of `start`, from every point. -/
theorem answer_eventually_const [Fintype α] (hreach : ∀ c, ∃ t, halted (step^[t] c) = true)
    (v : Bool)
    (hv : ∀ t, halted (step^[t] start) = true → (∀ i < t, halted (step^[i] start) = false) →
      out (step^[t] start) = v) :
    ∃ T, ∀ z, ((resetAns step halted out start)^[T] z).1 = v := by
  classical
  set F := resetAns step halted out start with hF
  let τ : α → ℕ := fun a => Nat.find (hreach a)
  have hτ : ∀ a, halted (step^[τ a] a) = true := fun a => Nat.find_spec (hreach a)
  have hmin : ∀ a, ∀ i < τ a, halted (step^[i] a) = false := by
    intro a i hi
    simpa using Nat.find_min (hreach a) hi
  set t0 := τ start
  let Good : Bool × α → Prop := fun z => z.1 = v ∧ ∃ j ≤ t0, z.2 = step^[j] start
  have hinv : ∀ z, Good z → Good (F z) := by
    rintro ⟨b, c⟩ ⟨hb, j, hj, rfl⟩
    by_cases hh : halted (step^[j] start) = true
    · have hjt : j = t0 := by
        by_contra hne
        have := hmin start j (by omega)
        rw [this] at hh
        exact absurd hh (by simp)
      have hout := hv j hh (fun i hi => hmin start i (by omega))
      refine ⟨?_, 0, Nat.zero_le _, ?_⟩
      · simp [hF, resetAns, hh, hout]
      · simp [hF, resetAns, hh]
    · have hh' : halted (step^[j] start) = false := by simpa using hh
      have hjt : j < t0 := by
        rcases Nat.lt_or_ge j t0 with h | h
        · exact h
        · exfalso
          have : j = t0 := by omega
          rw [this] at hh
          exact hh (hτ start)
      refine ⟨?_, j + 1, by omega, ?_⟩
      · simp [hF, resetAns, hh', hb]
      · simp [hF, resetAns, hh', Function.iterate_succ_apply']
  have hinvN : ∀ n z, Good z → Good (F^[n] z) := by
    intro n
    induction n with
    | zero => intro z hz; exact hz
    | succ n ih => intro z hz; rw [Function.iterate_succ_apply']; exact hinv _ (ih z hz)
  have hreachGood : ∀ z, Good (F^[(t0 + 1) + (τ z.2 + 1)] z) := by
    rintro ⟨b, c⟩
    rw [Function.iterate_add_apply,
      resetAns_iterate_first_halt step halted out start b c (τ c) (hτ c) (hmin c),
      resetAns_iterate_first_halt step halted out start _ start t0 (hτ start) (hmin start)]
    exact ⟨hv t0 (hτ start) (hmin start), 0, Nat.zero_le _, rfl⟩
  let M := Finset.univ.sup τ
  refine ⟨M + (t0 + 2), fun z => ?_⟩
  have hle : τ z.2 ≤ M := Finset.le_sup (f := τ) (Finset.mem_univ _)
  have e : M + (t0 + 2) = (M - τ z.2) + ((t0 + 1) + (τ z.2 + 1)) := by omega
  rw [e, Function.iterate_add_apply]
  exact (hinvN _ _ (hreachGood z)).1

end Reset

/-! ### Part 2: the reset map as a polynomial-time register circuit -/

section Register

variable (initL : List Bool → List Bool) (stepL : List Bool × List Bool → List Bool)
  (haltL outL : List Bool × List Bool → Bool)

/-- The circuit on the curve: the register is the answer bit followed by the configuration. -/
def nextL (q : List Bool × List Bool) : List Bool :=
  if haltL (q.1, q.2.tail) then outL (q.1, q.2.tail) :: initL q.1
  else q.2.headD false :: stepL (q.1, q.2.tail)

/-- The read-out: the answer bit. -/
def ansL (q : List Bool × List Bool) : Bool := q.2.headD false

/-- The start configuration, cut or padded to `m` bits. -/
def startV (x : List Bool) (m : ℕ) : List.Vector Bool m :=
  ⟨(initL x ++ List.replicate m false).take m, by simp⟩

/-- Soundness of an encoding on input `x` with configurations of `m` bits: every configuration
reaches a halted one, and the first halted configuration from the start answers `x ∈ L`. -/
def EncodingSound (L : Language Bool) (x : List Bool) (m : ℕ) : Prop :=
  (∀ c : List.Vector Bool m, ∃ t,
      haltL (x, ((ctcRegisterMap stepL x m)^[t] c).toList) = true) ∧
    ∀ t, haltL (x, ((ctcRegisterMap stepL x m)^[t] (startV initL x m)).toList) = true →
      (∀ i < t, haltL (x, ((ctcRegisterMap stepL x m)^[i] (startV initL x m)).toList) = false) →
      (outL (x, ((ctcRegisterMap stepL x m)^[t] (startV initL x m)).toList) = true ↔ x ∈ L)

theorem take_pad_succ (l : List Bool) (m : ℕ) :
    (l ++ List.replicate (m + 1) false).take m = (l ++ List.replicate m false).take m := by
  simp only [List.take_append, List.take_replicate]
  congr 2
  omega

/-- The register map of the circuit is the reset map, read through (bit, rest). -/
theorem registerMap_eq (x : List Bool) (m : ℕ) (r : List.Vector Bool (m + 1)) :
    ctcRegisterMap (nextL initL stepL haltL outL) x (m + 1) r =
      List.Vector.cons
        (resetAns (ctcRegisterMap stepL x m) (fun c => haltL (x, c.toList))
          (fun c => outL (x, c.toList)) (startV initL x m) (r.head, r.tail)).1
        (resetAns (ctcRegisterMap stepL x m) (fun c => haltL (x, c.toList))
          (fun c => outL (x, c.toList)) (startV initL x m) (r.head, r.tail)).2 := by
  have hr : r.toList = r.head :: r.tail.toList := by
    conv_lhs => rw [← List.Vector.cons_head_tail r]
    rw [List.Vector.toList_cons]
  apply List.Vector.eq
  rw [List.Vector.toList_cons]
  simp only [ctcRegisterMap, List.Vector.toList_mk, hr, nextL, resetAns, List.tail_cons,
    List.headD_cons]
  split_ifs with h
  · simp [startV, take_pad_succ]
  · simp [take_pad_succ]

theorem consistent_support_answer (x : List Bool) (m : ℕ) (L : Language Bool)
    (hs : EncodingSound initL stepL haltL outL L x m)
    (μ : PMF (List.Vector Bool (m + 1)))
    (hμ : DeutschConsistent (ctcRegisterMap (nextL initL stepL haltL outL) x (m + 1)) μ)
    (r : List.Vector Bool (m + 1)) (hr : r ∈ μ.support) :
    ansL (x, r.toList) = true ↔ x ∈ L := by
  classical
  obtain ⟨hreach, hcorr⟩ := hs
  set F := resetAns (ctcRegisterMap stepL x m) (fun c => haltL (x, c.toList))
    (fun c => outL (x, c.toList)) (startV initL x m) with hF
  obtain ⟨T, hT⟩ := answer_eventually_const (ctcRegisterMap stepL x m)
    (fun c => haltL (x, c.toList)) (fun c => outL (x, c.toList)) (startV initL x m) hreach
    (decide (x ∈ L)) (fun t ht hmin => by
      have := hcorr t ht hmin
      by_cases hx : x ∈ L <;> simp_all)
  set G := ctcRegisterMap (nextL initL stepL haltL outL) x (m + 1)
  let dec : List.Vector Bool (m + 1) → Bool × List.Vector Bool m := fun r => (r.head, r.tail)
  have hsemi : Function.Semiconj dec G F := by
    intro r
    show dec (G r) = F (dec r)
    rw [show G r = _ from registerMap_eq initL stepL haltL outL x m r]
    simp [dec, hF]
  obtain ⟨y, rfl⟩ := mem_range_iterate_of_consistent hμ T hr
  have h1 : dec (G^[T] y) = F^[T] (dec y) := hsemi.iterate_right T y
  have h2 : (G^[T] y).head = decide (x ∈ L) := by
    have := congrArg Prod.fst h1
    simp only [dec] at this
    rw [this, hT]
  have h3 : (G^[T] y).toList.headD false = (G^[T] y).head := by
    conv_lhs => rw [← List.Vector.cons_head_tail (G^[T] y)]
    rw [List.Vector.toList_cons]
    rfl
  simp only [ansL, h3, h2, decide_eq_true_iff]

/-! #### The circuit is polynomial-time -/

theorem cpt_congr' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_bitL :
    ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => [b]) :=
  filterMap_polyTime _ _ _ (fun b : Bool => some b) (fun b => by
    simp [Computability.encodeBool])

variable {initL stepL haltL outL}

theorem cpt_nextL (hinit : CPTb initL)
    (hstep : ComputableInPolyTime encodePair (fun y : List Bool => y) stepL)
    (hhalt : ComputableInPolyTime encodePair Computability.encodeBool haltL)
    (hout : ComputableInPolyTime encodePair Computability.encodeBool outL) :
    ComputableInPolyTime encodePair (fun y : List Bool => y)
      (nextL initL stepL haltL outL) := by
  have hP : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s : List Bool => ((unpairB s).1, (unpairB s).2.tail)) :=
    cpt_comp cpt_unpairB (cpt_second cpt_tail)
  have hFl : CPTb (fun s => if haltL ((unpairB s).1, (unpairB s).2.tail) then [true] else []) :=
    cpt_comp hP (cpt_bitFlag hhalt)
  have hA : CPTb (fun s => [outL ((unpairB s).1, (unpairB s).2.tail)] ++ initL (unpairB s).1) :=
    cpt_app2 (cpt_comp (cpt_comp hP hout) cpt_bitL) (cpt_comp cpt_unpairB1 hinit)
  have hB : CPTb (fun s => [(unpairB s).2.headD false] ++
      stepL ((unpairB s).1, (unpairB s).2.tail)) :=
    cpt_app2 (cpt_comp (cpt_comp cpt_unpairB cpt_regHead) cpt_bitL) (cpt_comp hP hstep)
  have hN := cpt_sel hFl hB hA
  refine cpt_congr' (cpt_comp cpt_pairB hN) ?_
  rintro ⟨x, r⟩
  simp only [unpairB_pairB, nextL]
  split_ifs with h <;> simp [sel]

end Register

/-! ### Part 3: the class statement -/

/-- A step encoding of `L`: polynomial-time initial configuration, step, halting test and
answer on configurations of `p (length of x)` bits, sound on every input. -/
def StepEncoding (L : Language Bool) : Prop :=
  ∃ (p : Polynomial ℕ) (initL : List Bool → List Bool)
    (stepL : List Bool × List Bool → List Bool) (haltL outL : List Bool × List Bool → Bool),
    CPTb initL ∧
      ComputableInPolyTime encodePair (fun y : List Bool => y) stepL ∧
      ComputableInPolyTime encodePair Computability.encodeBool haltL ∧
      ComputableInPolyTime encodePair Computability.encodeBool outL ∧
      ∀ x : List Bool, EncodingSound initL stepL haltL outL L x (p.eval x.length)

/-- Every language with a step encoding is in `PCTC`. -/
theorem PCTC_of_stepEncoding {L : Language Bool} (h : StepEncoding L) : L ∈ PCTC := by
  obtain ⟨p, initL, stepL, haltL, outL, hi, hs, hh, ho, hsound⟩ := h
  refine ⟨p + 1, ansL, nextL initL stepL haltL outL, cpt_regHead,
    cpt_nextL hi hs hh ho, fun x μ hμ r hr => ?_⟩
  have hm : (p + 1).eval x.length = p.eval x.length + 1 := by simp
  revert μ r
  rw [hm]
  intro μ hμ r hr
  exact consistent_support_answer initL stepL haltL outL x _ L (hsound x) μ hμ r hr

/-- The named open lemma: every language of the draft `PSPACE` has a step encoding. -/
def PspaceStepEncodingLemma : Prop := ∀ L ∈ PSPACE, StepEncoding L

/-- PSPACE ⊆ PCTC, given the step-encoding lemma. -/
theorem PSPACE_subset_PCTC_of_stepEncoding (h : PspaceStepEncodingLemma) : PSPACE ⊆ PCTC :=
  fun L hL => PCTC_of_stepEncoding (h L hL)

end PEqualNP.QuantumGravity.Open.PspaceCtc
