import PEqualNP.QuantumGravity.Open.PspaceCtc
import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.L055

/-!
# The clock lemma for the PSPACE ⊆ P_CTC encoding

`stepEncoding_of_timed` (O3 sub-lemma, clock): a deterministic step system on `p (|x|)` bit
configurations (polynomial-time initial configuration, step, halting test and answer) whose
orbit from the start configuration halts within `2 ^ q (|x|)` steps, with the answer correct at
the first halt, has a `StepEncoding`. The new register is a counter of `q (|x|)` bits followed
by the old configuration; one step ticks the counter with `bitsSucc` and steps the old
configuration; the system halts when the old one halts or the counter is all ones. From every
register the counter reaches all ones, which gives the "every register halts" half of
`EncodingSound`; from the start the counter reads `t` at time `t`, so it never fires before the
old halt.

Standard axioms only.
-/

namespace PEqualNP.QuantumGravity.Open.PspaceClock

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Helpers PEqualNP.QuantumGravity.Open.PspaceCtc

local notation "CPTb" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Plain facts on lists and counters -/

theorem take_pad_le (l : List Bool) (m a : ℕ) (h : m ≤ a) :
    (l ++ List.replicate a false).take m = (l ++ List.replicate m false).take m := by
  simp only [List.take_append, List.take_replicate]
  congr 2
  omega

theorem length_bitsSucc_iterate (c : List Bool) : ∀ t, (bitsSucc^[t] c).length = c.length
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', bitsSucc_length, length_bitsSucc_iterate c t]

theorem bval_bitsSucc_iterate (c : List Bool) :
    ∀ t, bval (bitsSucc^[t] c) = (bval c + t) % 2 ^ c.length
  | 0 => by simp [Nat.mod_eq_of_lt (bval_lt c)]
  | t + 1 => by
    rw [Function.iterate_succ_apply', bval_bitsSucc, length_bitsSucc_iterate,
      bval_bitsSucc_iterate c t, Nat.mod_add_mod]
    rfl

theorem all_iff_bval : ∀ c : List Bool, c.all id = true ↔ bval c + 1 = 2 ^ c.length
  | [] => by simp [bval]
  | b :: r => by
    have ih := all_iff_bval r
    cases b
    · simp [bval, pow_succ]; omega
    · simp [bval, pow_succ, ih]; omega

theorem bval_replicate_false : ∀ n : ℕ, bval (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, bval, bval_replicate_false n]

/-- Split a register at `n`: the first inner list of the self-delimiting pair whose first part
has length `n`. -/
def splitN (n : ℕ) (r : List Bool) : List Bool × List Bool :=
  unpairB (List.replicate n true ++ false :: r)

theorem splitN_eq (n : ℕ) (r : List Bool) (h : n ≤ r.length) :
    splitN n r = (r.take n, r.drop n) := by
  have e : pairB (r.take n) (r.drop n) = List.replicate n true ++ false :: r := by
    simp [pairB, un, List.length_take, min_eq_left h]
  rw [splitN, ← e, unpairB_pairB]

/-! ### The semantic core -/

section Core

variable {n m : ℕ}

/-- The old configuration inside a register of `n + m` bits. -/
def dropV (n m : ℕ) (v : List.Vector Bool (n + m)) : List.Vector Bool m :=
  ⟨v.toList.drop n, by simp⟩

@[simp] theorem dropV_toList (v : List.Vector Bool (n + m)) :
    (dropV n m v).toList = v.toList.drop n := rfl

variable (stepL : List Bool × List Bool → List Bool) (stepL' : List Bool × List Bool → List Bool)
  (x : List Bool)

theorem step_toList
    (hstep : ∀ r : List Bool, n ≤ r.length →
      stepL' (x, r) = bitsSucc (r.take n) ++ stepL (x, r.drop n))
    (v : List.Vector Bool (n + m)) :
    (ctcRegisterMap stepL' x (n + m) v).toList =
      bitsSucc (v.toList.take n) ++ (ctcRegisterMap stepL x m (dropV n m v)).toList := by
  have hv : n ≤ v.toList.length := by simp
  have hl : (bitsSucc (v.toList.take n)).length = n := by
    rw [bitsSucc_length]; simp
  simp only [ctcRegisterMap, List.Vector.toList_mk, dropV]
  rw [hstep _ hv, List.append_assoc, List.take_append, hl, List.take_of_length_le (by omega)]
  congr 1
  rw [show n + m - n = m by omega]
  exact take_pad_le _ _ _ (by omega)

theorem take_iterate
    (hstep : ∀ r : List Bool, n ≤ r.length →
      stepL' (x, r) = bitsSucc (r.take n) ++ stepL (x, r.drop n)) :
    ∀ (t : ℕ) (v : List.Vector Bool (n + m)),
      ((ctcRegisterMap stepL' x (n + m))^[t] v).toList.take n = bitsSucc^[t] (v.toList.take n)
  | 0, v => rfl
  | t + 1, v => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      step_toList stepL stepL' x hstep, ← take_iterate hstep t v,
      List.take_left' (by rw [bitsSucc_length]; simp)]

theorem dropV_step
    (hstep : ∀ r : List Bool, n ≤ r.length →
      stepL' (x, r) = bitsSucc (r.take n) ++ stepL (x, r.drop n))
    (v : List.Vector Bool (n + m)) :
    dropV n m (ctcRegisterMap stepL' x (n + m) v) =
      ctcRegisterMap stepL x m (dropV n m v) := by
  apply List.Vector.eq
  have hl : (bitsSucc (v.toList.take n)).length = n := by
    rw [bitsSucc_length]; simp
  simp only [dropV, List.Vector.toList_mk]
  rw [step_toList stepL stepL' x hstep, List.drop_left' hl]
  rfl

theorem dropV_iterate
    (hstep : ∀ r : List Bool, n ≤ r.length →
      stepL' (x, r) = bitsSucc (r.take n) ++ stepL (x, r.drop n)) :
    ∀ (t : ℕ) (v : List.Vector Bool (n + m)),
      dropV n m ((ctcRegisterMap stepL' x (n + m))^[t] v) =
        (ctcRegisterMap stepL x m)^[t] (dropV n m v)
  | 0, v => rfl
  | t + 1, v => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      dropV_step stepL stepL' x hstep, dropV_iterate hstep t v]

end Core

/-- The semantic core: soundness of the clocked encoding, for arbitrary functions meeting the
pointwise specification at the input `x`. -/
theorem core {L : Language Bool} (n m : ℕ) (x : List Bool)
    (initL : List Bool → List Bool) (stepL : List Bool × List Bool → List Bool) (haltL outL : List Bool × List Bool → Bool)
    (initL' : List Bool → List Bool) (stepL' : List Bool × List Bool → List Bool)
    (haltL' outL' : List Bool × List Bool → Bool)
    (hinit : initL' x = List.replicate n false ++ initL x)
    (hstep : ∀ r : List Bool, n ≤ r.length →
      stepL' (x, r) = bitsSucc (r.take n) ++ stepL (x, r.drop n))
    (hhalt : ∀ r : List Bool, n ≤ r.length →
      haltL' (x, r) = (haltL (x, r.drop n) || (r.take n).all id))
    (hout : ∀ r : List Bool, n ≤ r.length → outL' (x, r) = outL (x, r.drop n))
    (htime : ∃ t < 2 ^ n, haltL (x, ((ctcRegisterMap stepL x m)^[t]
      (startV initL x m)).toList) = true)
    (hcorr : ∀ t, haltL (x, ((ctcRegisterMap stepL x m)^[t] (startV initL x m)).toList) = true →
      (∀ i < t, haltL (x, ((ctcRegisterMap stepL x m)^[i] (startV initL x m)).toList) = false) →
      (outL (x, ((ctcRegisterMap stepL x m)^[t] (startV initL x m)).toList) = true ↔ x ∈ L)) :
    EncodingSound initL' stepL' haltL' outL' L x (n + m) := by
  refine ⟨fun c => ?_, ?_⟩
  · -- every register halts: the counter reaches all ones
    have hlen : n ≤ c.toList.length := by simp
    have hb := bval_lt (c.toList.take n)
    rw [List.length_take, min_eq_left hlen] at hb
    refine ⟨2 ^ n - 1 - bval (c.toList.take n), ?_⟩
    set t := 2 ^ n - 1 - bval (c.toList.take n) with ht
    have hlenT : n ≤ ((ctcRegisterMap stepL' x (n + m))^[t] c).toList.length := by simp
    rw [hhalt _ hlenT, take_iterate stepL stepL' x hstep t c]
    have hv := bval_bitsSucc_iterate (c.toList.take n) t
    rw [List.length_take, min_eq_left hlen] at hv
    have : bval (bitsSucc^[t] (c.toList.take n)) + 1 =
        2 ^ (bitsSucc^[t] (c.toList.take n)).length := by
      rw [length_bitsSucc_iterate, List.length_take, min_eq_left hlen, hv,
        Nat.mod_eq_of_lt (by omega)]
      omega
    simp [(all_iff_bval _).mpr this]
  · intro t ht hmin
    set c0 := startV initL' x (n + m) with hc0
    have hc0l : c0.toList = List.replicate n false ++ (startV initL x m).toList := by
      simp only [hc0, startV, List.Vector.toList_mk, hinit, List.append_assoc]
      rw [List.take_append, List.take_of_length_le (by simp)]
      simp only [List.length_replicate, Nat.add_sub_cancel_left]
      congr 1
      exact take_pad_le _ _ _ (by omega)
    have hdrop : dropV n m c0 = startV initL x m := by
      apply List.Vector.eq
      simp only [dropV, hc0l, List.Vector.toList_mk]
      rw [List.drop_left' (by simp)]
    have htk : c0.toList.take n = List.replicate n false := by
      rw [hc0l, List.take_left' (by simp)]
    -- the old orbit and the counter at time `i`
    have hH : ∀ i, haltL' (x, ((ctcRegisterMap stepL' x (n + m))^[i] c0).toList) =
        (haltL (x, ((ctcRegisterMap stepL x m)^[i] (startV initL x m)).toList) ||
          (bitsSucc^[i] (List.replicate n false)).all id) := by
      intro i
      have hlenI : n ≤ ((ctcRegisterMap stepL' x (n + m))^[i] c0).toList.length := by simp
      rw [hhalt _ hlenI, take_iterate stepL stepL' x hstep i c0, htk]
      have := congrArg (fun v : List.Vector Bool m => v.toList)
        (dropV_iterate stepL stepL' x hstep i c0)
      rw [hdrop] at this
      simp only [dropV_toList] at this
      rw [this]
    have hcnt : ∀ i, i < 2 ^ n →
        ((bitsSucc^[i] (List.replicate n false)).all id = true ↔ i + 1 = 2 ^ n) := by
      intro i hi
      rw [all_iff_bval, length_bitsSucc_iterate, bval_bitsSucc_iterate]
      simp only [List.length_replicate, bval_replicate_false, zero_add]
      rw [Nat.mod_eq_of_lt hi]
    obtain ⟨t1, ht1, hh1⟩ := htime
    have hH1 := hH t1
    have hle : t ≤ t1 := by
      by_contra hlt
      have := hmin t1 (by omega)
      rw [hH1, hh1] at this
      simp at this
    have hold : haltL (x, ((ctcRegisterMap stepL x m)^[t] (startV initL x m)).toList) = true := by
      rw [hH t] at ht
      rcases Bool.or_eq_true_iff.mp ht with h | h
      · exact h
      · have := (hcnt t (by omega)).mp h
        have : t = t1 := by omega
        subst this
        exact hh1
    have hmin' : ∀ i < t,
        haltL (x, ((ctcRegisterMap stepL x m)^[i] (startV initL x m)).toList) = false := by
      intro i hi
      have := hmin i hi
      rw [hH i] at this
      exact (Bool.or_eq_false_iff.mp this).1
    have hlenT : n ≤ ((ctcRegisterMap stepL' x (n + m))^[t] c0).toList.length := by simp
    rw [hout _ hlenT]
    have := congrArg (fun v : List.Vector Bool m => v.toList)
      (dropV_iterate stepL stepL' x hstep t c0)
    rw [hdrop] at this
    simp only [dropV_toList] at this
    rw [this]
    exact hcorr t hold hmin'


/-! ### The clocked system -/

section Clocked

variable (q : Polynomial ℕ) (initL : List Bool → List Bool)
  (stepL : List Bool × List Bool → List Bool) (haltL outL : List Bool × List Bool → Bool)

/-- Counter of `q (|x|)` zero bits, then the old initial configuration. -/
def initC (x : List Bool) : List Bool := List.replicate (q.eval x.length) false ++ initL x

/-- Tick the counter, step the old configuration. -/
def stepC (p : List Bool × List Bool) : List Bool :=
  bitsSucc (splitN (q.eval p.1.length) p.2).1 ++
    stepL (p.1, (splitN (q.eval p.1.length) p.2).2)

/-- 1 if all bits are `true`, as a flag string. -/
def flagA (c : List Bool) : List Bool := if c.all id then [true] else []

/-- Halt when the old configuration halts or the counter is all ones. -/
def haltC (p : List Bool × List Bool) : Bool :=
  !((if haltL (p.1, (splitN (q.eval p.1.length) p.2).2) then [true] else []) ++
    flagA (splitN (q.eval p.1.length) p.2).1).isEmpty

/-- The answer of the old configuration. -/
def outC (p : List Bool × List Bool) : Bool :=
  outL (p.1, (splitN (q.eval p.1.length) p.2).2)

theorem haltC_eq (x r : List Bool) (h : q.eval x.length ≤ r.length) :
    haltC q haltL (x, r) =
      (haltL (x, r.drop (q.eval x.length)) || (r.take (q.eval x.length)).all id) := by
  simp only [haltC, splitN_eq _ _ h, flagA]
  cases haltL (x, r.drop (q.eval x.length)) <;>
    cases (r.take (q.eval x.length)).all id <;> simp

end Clocked

/-! ### Polynomial time -/

private def flagD : Bool → Bool → Bool × Option Bool := fun s b => (s && b, none)

private theorem flagD_run (s : Bool) (l : List Bool) :
    fstRun flagD (fun s => if s then some true else none) s l =
      if (s && l.all id) = true then [true] else [] := by
  induction l generalizing s with
  | nil => cases s <;> simp [fstRun]
  | cons b l ih =>
    simp only [fstRun, flagD, Option.toList_none, List.nil_append, ih, List.all_cons, id,
      Bool.and_assoc]
    rfl

theorem cpt_flagA : CPTb flagA :=
  fst_polyTime _ _ _ flagD (fun s => if s then some true else none) true (fun l => by
    rw [flagD_run]; simp [flagA])

theorem cpt_congr'' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := cpt_congr' h e

section Poly

variable (q : Polynomial ℕ) {initL : List Bool → List Bool}
  {stepL : List Bool × List Bool → List Bool} {haltL outL : List Bool × List Bool → Bool}

private theorem cpt_cnt : CPTb (fun s : List Bool =>
    (splitN (q.eval (unpairB s).1.length) (unpairB s).2).1) := by
  have hK : CPTb (fun s : List Bool => List.replicate (q.eval (unpairB s).1.length) true) :=
    cpt_comp cpt_unpairB1 (L055 q)
  have hSp : CPTb (fun s : List Bool =>
      List.replicate (q.eval (unpairB s).1.length) true ++ false :: (unpairB s).2) :=
    cpt_app2 hK (cpt_congr' (cpt_app2 (cpt_const [false]) cpt_unpairB2) (fun s => rfl))
  exact cpt_congr' (cpt_comp hSp cpt_unpairB1) (fun s => rfl)

private theorem cpt_conf : CPTb (fun s : List Bool =>
    (splitN (q.eval (unpairB s).1.length) (unpairB s).2).2) := by
  have hK : CPTb (fun s : List Bool => List.replicate (q.eval (unpairB s).1.length) true) :=
    cpt_comp cpt_unpairB1 (L055 q)
  have hSp : CPTb (fun s : List Bool =>
      List.replicate (q.eval (unpairB s).1.length) true ++ false :: (unpairB s).2) :=
    cpt_app2 hK (cpt_congr' (cpt_app2 (cpt_const [false]) cpt_unpairB2) (fun s => rfl))
  exact cpt_congr' (cpt_comp hSp cpt_unpairB2) (fun s => rfl)

private theorem cpt_xconf : ComputableInPolyTime (fun x : List Bool => x) encodePair
    (fun s : List Bool => ((unpairB s).1,
      (splitN (q.eval (unpairB s).1.length) (unpairB s).2).2)) :=
  cpt_pairG cpt_unpairB1 (cpt_conf q)

/-- Lift a plain polynomial-time function of `pairB x r` to the pair encoding. -/
private theorem lift {β βΓ : Type} {eb : β → List βΓ} {g : List Bool → β}
    (hg : ComputableInPolyTime (fun x : List Bool => x) eb g)
    {f : List Bool × List Bool → β} (e : ∀ x r, g (pairB x r) = f (x, r)) :
    ComputableInPolyTime encodePair eb f :=
  cpt_congr' (cpt_comp cpt_pairB hg) (by rintro ⟨x, r⟩; exact e x r)

theorem cpt_initC (hi : CPTb initL) : CPTb (initC q initL) := by
  refine cpt_congr' (cpt_app2 (cpt_comp (L055 q) cpt_blank) hi) (fun x => ?_)
  simp [initC, blank, List.map_replicate]

theorem cpt_stepC (hs : ComputableInPolyTime encodePair (fun y : List Bool => y) stepL) :
    ComputableInPolyTime encodePair (fun y : List Bool => y) (stepC q stepL) := by
  have hv : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => p.1.isEmpty) := cpt_comp cpt_fst cpt_isEmpty
  have hBS : CPTb (fun s : List Bool => bitsSucc
      (splitN (q.eval (unpairB s).1.length) (unpairB s).2).1) :=
    cpt_congr' (cpt_comp (cpt_pairG (cpt_const [true]) (cpt_cnt q)) (cpt_counter hv))
      (fun s => by simp)
  have hsP : CPTb (fun s : List Bool => stepL ((unpairB s).1,
      (splitN (q.eval (unpairB s).1.length) (unpairB s).2).2)) :=
    cpt_comp (cpt_xconf q) hs
  exact lift (cpt_app2 hBS hsP) (fun x r => by simp [stepC, unpairB_pairB])

theorem cpt_haltC (hh : ComputableInPolyTime encodePair Computability.encodeBool haltL) :
    ComputableInPolyTime encodePair Computability.encodeBool (haltC q haltL) := by
  have hH : CPTb (fun s : List Bool => if haltL ((unpairB s).1,
      (splitN (q.eval (unpairB s).1.length) (unpairB s).2).2) then [true] else []) :=
    cpt_comp (cpt_xconf q) (cpt_bitFlag hh)
  have hW := cpt_app2 hH (cpt_comp (cpt_cnt q) cpt_flagA)
  have hNe : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun w : List Bool => !w.isEmpty) := cpt_comp cpt_isEmpty cpt_not
  exact lift (cpt_comp hW hNe) (fun x r => by simp [haltC, unpairB_pairB])

theorem cpt_outC (ho : ComputableInPolyTime encodePair Computability.encodeBool outL) :
    ComputableInPolyTime encodePair Computability.encodeBool (outC q outL) :=
  lift (cpt_comp (cpt_xconf q) ho) (fun x r => by simp [outC, unpairB_pairB])

end Poly

/-- **The clock lemma.** A step system on `p (|x|)` bit configurations that halts from the start
within `2 ^ q (|x|)` steps, with the answer correct at the first halt, has a `StepEncoding`:
prepend a `q (|x|)`-bit counter ticked with `bitsSucc`, and halt also on all ones. -/
theorem stepEncoding_of_timed {L : Language Bool} (p q : Polynomial ℕ)
    (initL : List Bool → List Bool) (stepL : List Bool × List Bool → List Bool)
    (haltL outL : List Bool × List Bool → Bool) (hi : CPTb initL)
    (hs : ComputableInPolyTime encodePair (fun y : List Bool => y) stepL)
    (hh : ComputableInPolyTime encodePair Computability.encodeBool haltL)
    (ho : ComputableInPolyTime encodePair Computability.encodeBool outL)
    (htime : ∀ x : List Bool, ∃ t < 2 ^ q.eval x.length,
      haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true)
    (hcorr : ∀ (x : List Bool) (t : ℕ),
      haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true →
      (∀ i < t, haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[i]
        (startV initL x (p.eval x.length))).toList) = false) →
      (outL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true ↔ x ∈ L)) :
    StepEncoding L := by
  refine ⟨q + p, initC q initL, stepC q stepL, haltC q haltL, outC q outL, cpt_initC q hi,
    cpt_stepC q hs, cpt_haltC q hh, cpt_outC q ho, fun x => ?_⟩
  have hm : (q + p).eval x.length = q.eval x.length + p.eval x.length := by simp
  rw [hm]
  refine core (q.eval x.length) (p.eval x.length) x initL stepL haltL outL (initC q initL)
    (stepC q stepL) (haltC q haltL) (outC q outL) rfl ?_ ?_ ?_ (htime x) (hcorr x)
  · intro r hr
    simp [stepC, splitN_eq _ _ hr]
  · intro r hr
    exact haltC_eq q haltL x r hr
  · intro r hr
    simp [outC, splitN_eq _ _ hr]

end PEqualNP.QuantumGravity.Open.PspaceClock
