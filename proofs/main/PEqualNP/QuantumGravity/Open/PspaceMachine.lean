import PEqualNP.QuantumGravity.Open.PspaceCtc
import PEqualNP.QuantumGravity.Open.PspaceClock
import PEqualNP.Library.Universal.CompileBool
import PEqualNP.Library.Universal.Verify
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Universal.PrimsCPT


/-!
# The PSPACE machine encoding (O3 sub-lemma, machine)

Every `L ∈ Library.PSPACE` (`Turing.FinTM2` with `UsesSpace`) has the data of the hypotheses of
`PspaceClock.stepEncoding_of_timed`; with the clock lemma this proves `PspaceStepEncodingLemma`
and `PSPACE ⊆ PCTC` (`PSPACE_subset_PCTC`).

Construction. The machine is compiled to the micro-instruction code of `Universal.CompileBool`
(`codeBool`). A configuration is the bit string `encCfg prog X` (program, program counter, state
in unary, stacks as numbers in unary), padded with `false` bits to `p (|x|)` bits; the padding is
a run of extra empty stacks (`extCfg`, `encCfg_ext`), which no instruction of the compiled code
touches (`codeBool_wf`), so the padded orbit of `ctcRegisterMap sstep` follows the code
(`orbit_eq`). One step is `sstep` (`cpt_stepS`, from `Universal.cpt_sstep`), the halting test
reads the program counter (`cpt_haltS`), the answer read-out tests that the output stack is
`[1]` (`cpt_outS`), the start configuration is `initS` (`cpt_initS_nil`). The length bound
(`pspace_timedData`) comes from three facts: every number of a run is bounded by the sum of the
numbers of the program (`Bd`, `step_bd`); every stack stays within `n ^ k + k + |flatList| + 3`
at every micro step, not only at machine-step boundaries (`sim_run_bd`, `compileBool_bd`);
the encoding length is linear in the stack lengths (`encCfg_length_le`). Halting within `2 ^ p`
steps is pigeonhole on the `2 ^ p` registers (`exists_time`).

Standard axioms only.
-/

namespace PEqualNP.QuantumGravity.Open.PspaceMachine
open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines PEqualNP.QuantumGravity
  PEqualNP.QuantumGravity.Open.PspaceClock

/-- The stack an instruction touches. -/
def stkIdx : Instr → Option ℕ
  | .push k _ _ => some k
  | .pop k _ _ _ => some k
  | .peek k _ _ _ => some k
  | _ => none

/-- Every stack index of the instruction is below `n`. -/
def InstrWF (n : ℕ) (i : Instr) : Prop := ∀ k, stkIdx i = some k → k < n

/-- Extra stacks appended at the end. -/
def extCfg (X : Cfg) (R : List (List ℕ)) : Cfg := ⟨X.pc, X.state, X.stk ++ R⟩

theorem exec_ext (i : Instr) (v : ℕ) (S R : List (List ℕ)) (h : InstrWF S.length i) :
    exec i v (S ++ R) = extCfg (exec i v S) R := by
  cases i with
  | push k tbl next =>
    have hk : k < S.length := h k rfl
    simp [exec, extCfg, List.set_append_left _ _ hk, List.getElem?_append_left hk]
  | pop k tbl w next =>
    have hk : k < S.length := h k rfl
    simp [exec, extCfg, List.set_append_left _ _ hk, List.getElem?_append_left hk]
  | peek k tbl w next =>
    have hk : k < S.length := h k rfl
    simp [exec, extCfg, List.getElem?_append_left hk]
  | load tbl next => simp [exec, extCfg]
  | branch tbl n1 n2 => simp [exec, extCfg]
  | goto tbl => simp [exec, extCfg]
  | halt => simp [exec, extCfg]

theorem step_ext (P : List Instr) (X : Cfg) (R : List (List ℕ))
    (hP : ∀ i ∈ P, InstrWF X.stk.length i) :
    step P (extCfg X R) = extCfg (step P X) R := by
  obtain ⟨pc, v, S⟩ := X
  cases pc with
  | none => simp [step, extCfg]
  | some n =>
    simp only [extCfg, step]
    cases hn : P[n]? with
    | none => simp
    | some i =>
      simp only
      exact exec_ext i v S R (hP i (List.mem_of_getElem? hn))

theorem exec_len (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).stk.length = S.length := by
  cases i <;> simp [exec]

theorem step_len (P : List Instr) (X : Cfg) : (step P X).stk.length = X.stk.length := by
  obtain ⟨pc, v, S⟩ := X
  cases pc with
  | none => simp [step]
  | some n =>
    simp only [step]
    cases hn : P[n]? with
    | none => simp
    | some i => exact exec_len i v S

theorem iterate_step_len (P : List Instr) (X : Cfg) (t : ℕ) :
    ((step P)^[t] X).stk.length = X.stk.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', step_len, ih]

theorem iterate_step_ext (P : List Instr) (X : Cfg) (R : List (List ℕ))
    (hP : ∀ i ∈ P, InstrWF X.stk.length i) (t : ℕ) :
    (step P)^[t] (extCfg X R) = extCfg ((step P)^[t] X) R := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    apply step_ext
    rw [iterate_step_len]; exact hP

theorem encLL_replicate_nil (j : ℕ) : encLL (List.replicate j ([] : List ℕ)) = List.replicate j false := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, encLL_cons, ih]; simp [encNs]; rfl

theorem pairB_append_right (a b c : List Bool) : pairB a (b ++ c) = pairB a b ++ c := by
  simp [pairB]

theorem encCfg_ext (P : List Instr) (X : Cfg) (j : ℕ) :
    encCfg P (extCfg X (List.replicate j [])) = encCfg P X ++ List.replicate j false := by
  simp only [encCfg, extCfg, encLL_append, encLL_replicate_nil, pairB_append_right]


open PEqualNP.QuantumGravity.Open.PspaceCtc

/-- The step on register strings. -/
def stepS (q : List Bool × List Bool) : List Bool := sstep q.2
/-- The halting test on register strings. -/
def haltS (q : List Bool × List Bool) : Bool := haltedS q.2
/-- The answer read-out: the output stack is exactly `[1]`. -/
def outS (kout : ℕ) (q : List Bool × List Bool) : Bool := outOne (un kout) (stkS q.2)

theorem take_pad (A : List Bool) (j m : ℕ) (hA : A.length ≤ m) :
    (A ++ List.replicate j false ++ List.replicate m false).take m =
      A ++ List.replicate (m - A.length) false := by
  rw [List.append_assoc, ← List.replicate_add, List.take_append, List.take_of_length_le hA,
    List.take_replicate]
  congr 2
  omega

theorem orbit_eq (P : List Instr) (X0 : Cfg) (hP : ∀ i ∈ P, InstrWF X0.stk.length i)
    (initL : List Bool → List Bool) (x : List Bool) (hinit : initL x = encCfg P X0) (m T : ℕ)
    (hfit : ∀ t ≤ T, (encCfg P ((step P)^[t] X0)).length ≤ m) :
    ∀ t ≤ T, ((ctcRegisterMap stepS x m)^[t] (startV initL x m)).toList =
      encCfg P ((step P)^[t] X0) ++
        List.replicate (m - (encCfg P ((step P)^[t] X0)).length) false := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [Function.iterate_zero, id, startV, List.Vector.toList_mk, hinit]
    have := hfit 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id] at this ⊢
    rw [List.take_append, List.take_of_length_le this, List.take_replicate]
    congr 2
    omega
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := hfit (t + 1) ht
    have e : (step P)^[t + 1] X0 = step P ((step P)^[t] X0) := Function.iterate_succ_apply' _ _ _
    rw [e] at h2 ⊢
    rw [Function.iterate_succ_apply']
    set Xt := (step P)^[t] X0 with hXt
    have hP' : ∀ i ∈ P, InstrWF Xt.stk.length i := by
      rw [hXt, iterate_step_len]; exact hP
    simp only [ctcRegisterMap, List.Vector.toList_mk]
    rw [h1, ← encCfg_ext, stepS, sstep_encCfg, step_ext P Xt _ hP', encCfg_ext]
    exact take_pad _ _ _ h2


theorem haltS_pad (x : List Bool) (P : List Instr) (X : Cfg) (j : ℕ) :
    haltS (x, encCfg P X ++ List.replicate j false) = true ↔ X.pc = none := by
  rw [← encCfg_ext]
  exact haltedS_encCfg P (extCfg X (List.replicate j []))

theorem outS_pad (x : List Bool) (P : List Instr) (X : Cfg) (j kout : ℕ)
    (hk : kout < X.stk.length) :
    outS kout (x, encCfg P X ++ List.replicate j false) = true ↔ X.stk.getD kout [] = [1] := by
  rw [← encCfg_ext, outS]
  simp only [stkS_encCfg, outOne_spec, extCfg]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem exists_time {V : Type} [Fintype V] (F : V → V) (h : V → Prop) (v : V)
    (hT : ∃ T, h (F^[T] v)) : ∃ t < Fintype.card V, h (F^[t] v) := by
  classical
  let T := Nat.find hT
  have hTspec : h (F^[T] v) := Nat.find_spec hT
  have hmin : ∀ t < T, ¬ h (F^[t] v) := fun t ht => Nat.find_min hT ht
  by_cases hlt : T < Fintype.card V
  · exact ⟨T, hlt, hTspec⟩
  · exfalso
    rw [not_lt] at hlt
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card V + 1) => F^[i.val] v) (by simp)
    have key : ∃ i d, 0 < d ∧ i + d ≤ Fintype.card V ∧ F^[i + d] v = F^[i] v := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h1 | h1
      · exact ⟨a.val, b.val - a.val, by omega, by have := b.isLt; omega, by
          have : a.val + (b.val - a.val) = b.val := by omega
          rw [this]; exact he.symm⟩
      · exact ⟨b.val, a.val - b.val, by omega, by have := a.isLt; omega, by
          have : b.val + (a.val - b.val) = a.val := by omega
          rw [this]; exact he⟩
    obtain ⟨i, d, hd, hid, hper⟩ := key
    have hsh : ∀ s, F^[i + s + d] v = F^[i + s] v := by
      intro s
      calc F^[i + s + d] v = F^[s] (F^[i + d] v) := by
            rw [← Function.iterate_add_apply]; congr 1; omega
        _ = F^[s] (F^[i] v) := by rw [hper]
        _ = F^[i + s] v := by rw [← Function.iterate_add_apply]; congr 1; omega
    have : F^[T - d] v = F^[T] v := by
      have e1 : T = (T - d - i) + i + d := by omega
      have h2 := hsh (T - d - i)
      rw [show i + (T - d - i) + d = T by omega, show i + (T - d - i) = T - d by omega] at h2
      exact h2.symm
    exact hmin (T - d) (by omega) (this ▸ hTspec)


/-! ### Polynomial-time computability of the encoding functions -/

local notation "CPTs" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem cpt_of_str {β βΓ : Type} {eb : β → List βΓ} {f : List Bool × List Bool → β}
    {g : List Bool → β}
    (hg : ComputableInPolyTime (fun x : List Bool => x) eb g)
    (e : ∀ p, f p = g (pairB p.1 p.2)) : ComputableInPolyTime encodePair eb f := by
  have h := cpt_comp cpt_pairB hg
  obtain rfl : f = fun p => g (pairB p.1 p.2) := funext e
  exact h

theorem cpt_u1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => (unpairB (f s)).1) :=
  cpt_comp (g := fun s => (unpairB s).1) hf cpt_unpairB1

theorem cpt_u2 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => (unpairB (f s)).2) :=
  cpt_comp (g := fun s => (unpairB s).2) hf cpt_unpairB2

theorem cpt_stepS : ComputableInPolyTime encodePair (fun y : List Bool => y) stepS :=
  cpt_of_str (g := fun s => sstep (unpairB s).2) (cpt_comp cpt_unpairB2 cpt_sstep)
    (fun p => by simp [stepS, unpairB_pairB])

private def emD : Bool → Bool → Bool × Option Bool := fun _ _ => (true, none)

private theorem em_true (l : List Bool) :
    fstRun emD (fun q => some (!q)) true l = [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [fstRun, emD] using ih

theorem cpt_isEmpty : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
    (fun l : List Bool => l.isEmpty) :=
  fst_polyTime _ _ _ emD (fun q => some (!q)) false (fun l => by
    cases l with
    | nil => rfl
    | cons b l => simp [fstRun, emD, em_true, Computability.encodeBool])

private theorem ne_true' (l : List Bool) :
    fstRun emD (fun q => some q) true l = [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [fstRun, emD] using ih

theorem cpt_notEmpty : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
    (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ emD (fun q => some q) false (fun l => by
    cases l with
    | nil => rfl
    | cons b l => simp [fstRun, emD, ne_true', Computability.encodeBool])

theorem cpt_haltS : ComputableInPolyTime encodePair Computability.encodeBool haltS :=
  cpt_of_str (g := fun s => (unpairB (unpairB (unpairB s).2).2).1.isEmpty)
    (cpt_comp (cpt_u1 (cpt_u2 cpt_unpairB2)) cpt_isEmpty)
    (fun p => by simp [haltS, haltedS, unpairB_pairB])

private inductive O4 : Type
  | s0 | s1 | s2 | s3 | ok | bad
  deriving DecidableEq

private instance : Fintype O4 :=
  Fintype.ofList [.s0, .s1, .s2, .s3, .ok, .bad] (fun x => by cases x <;> simp)

private def o4D : O4 → Bool → O4 × Option Bool
  | .s0, true => (.s1, none)
  | .s1, true => (.s2, none)
  | .s2, false => (.s3, none)
  | .s3, false => (.ok, none)
  | .ok, _ => (.ok, none)
  | _, _ => (.bad, none)

private def o4F : O4 → Option Bool
  | .ok => some true
  | _ => none

private theorem o4_ok (l : List Bool) : fstRun o4D o4F .ok l = [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_bad (l : List Bool) : fstRun o4D o4F .bad l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_run (l : List Bool) :
    fstRun o4D o4F .s0 l = if l.take 4 = [true, true, false, false] then [true] else [] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [fstRun, o4F]
  · cases a <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> cases d <;> simp [fstRun, o4D, o4_ok, o4_bad]

private theorem cpt_o4 :
    CPTs (fun l : List Bool => if l.take 4 = [true, true, false, false] then [true] else []) :=
  fst_polyTime _ _ _ o4D o4F .s0 (fun s => (o4_run s).symm)

theorem cpt_outS (kout : ℕ) :
    ComputableInPolyTime encodePair Computability.encodeBool (outS kout) := by
  have h1 : CPTs (fun s => (unpairB (unpairB (unpairB (unpairB s).2).2).2).2) :=
    cpt_u2 (cpt_u2 (cpt_u2 cpt_unpairB2))
  have h2 := cpt_iterLen cpt_dropL dropL_length (cpt_const (un kout)) h1
  have h3 := cpt_comp (cpt_comp h2 cpt_o4) cpt_notEmpty
  refine cpt_of_str h3 (fun p => ?_)
  simp only [outS, outOne, stkS, unpairB_pairB, un_length]
  split_ifs with h <;> simp [h]

theorem cpt_initS_nil (c : Code) :
    CPTs (fun x => initS (encCode c) x []) := by
  have hnew : CPTs (fun x => inSyms x []) :=
    cpt_app2 (cpt_comp cpt_spread cpt_bump) (cpt_const _)
  have hins : ∀ (k sk : List Bool), CPTs (fun x => insK k (inSyms x []) sk) := fun k sk =>
    cpt_sel (cpt_const _) (cpt_const _)
      (cpt_app2 (cpt_const _) (cpt_app2 hnew (cpt_const _)))
  exact cpt_pairB2 (cpt_const _) (cpt_pairB2 (cpt_const _) (cpt_pairB2 (cpt_const _) (hins _ _)))


/-! ### Assembly for an abstract compiled code -/

local notation "CPTb" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-- The hypotheses of the clock lemma (`stepEncoding_of_timed`, board line O3 clock), as data. -/
structure TimedData (L : Language Bool) : Prop where
  ex : ∃ (p q : Polynomial ℕ) (initL : List Bool → List Bool)
    (stepL : List Bool × List Bool → List Bool) (haltL outL : List Bool × List Bool → Bool),
    CPTb initL ∧
    ComputableInPolyTime encodePair (fun y : List Bool => y) stepL ∧
    ComputableInPolyTime encodePair Computability.encodeBool haltL ∧
    ComputableInPolyTime encodePair Computability.encodeBool outL ∧
    (∀ x : List Bool, ∃ t < 2 ^ q.eval x.length,
      haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true) ∧
    (∀ (x : List Bool) (t : ℕ),
      haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true →
      (∀ i < t, haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[i]
        (startV initL x (p.eval x.length))).toList) = false) →
      (outL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t]
        (startV initL x (p.eval x.length))).toList) = true ↔ x ∈ L))

theorem timedData_of_code (L : Language Bool) (code : Code) (f : List Bool → Bool)
    (hLf : ∀ x, x ∈ L ↔ f x = true) (p : Polynomial ℕ)
    (hWF : ∀ i ∈ code.prog, InstrWF code.nstk i) (hkout : code.kout < code.nstk)
    (hrun : ∀ x : List Bool, ∃ T0 : ℕ,
      (code.run (x.map fun b => cond b 1 0) T0).pc = none ∧
      (code.run (x.map fun b => cond b 1 0) T0).stk.getD code.kout [] = [bitCode (f x)] ∧
      ∀ t ≤ T0, (encCfg code.prog (code.run (x.map fun b => cond b 1 0) t)).length ≤
        p.eval x.length) :
    TimedData L := by
  refine ⟨⟨p, p, fun x => initS (encCode code) x [], stepS, haltS, outS code.kout,
    cpt_initS_nil code, cpt_stepS, cpt_haltS, cpt_outS _, ?_, ?_⟩⟩
  · intro x
    obtain ⟨T0, hpc, hout, hfit⟩ := hrun x
    set m := p.eval x.length with hm
    have hinit : initS (encCode code) x [] =
        encCfg code.prog (code.init (x.map fun b => cond b 1 0)) := by
      rw [initS_spec]; simp
    have hlen0 : (code.init (x.map fun b => cond b 1 0)).stk.length = code.nstk := by
      simp [Code.init]
    have horb := orbit_eq code.prog (code.init (x.map fun b => cond b 1 0))
      (by rw [hlen0]; exact hWF) (fun x => initS (encCode code) x []) x hinit m T0
      (fun t ht => hfit t ht)
    have hT : ∃ T, haltS (x, ((ctcRegisterMap stepS x m)^[T]
        (startV (fun x => initS (encCode code) x []) x m)).toList) = true := by
      refine ⟨T0, ?_⟩
      rw [horb T0 le_rfl, haltS_pad]
      exact hpc
    obtain ⟨t, ht, hh⟩ := exists_time (ctcRegisterMap stepS x m)
      (fun r => haltS (x, r.toList) = true) (startV (fun x => initS (encCode code) x []) x m) hT
    refine ⟨t, ?_, hh⟩
    simpa using ht
  · intro x t hh hmin
    obtain ⟨T0, hpc, hout, hfit⟩ := hrun x
    set m := p.eval x.length with hm
    have hinit : initS (encCode code) x [] =
        encCfg code.prog (code.init (x.map fun b => cond b 1 0)) := by
      rw [initS_spec]; simp
    have hlen0 : (code.init (x.map fun b => cond b 1 0)).stk.length = code.nstk := by
      simp [Code.init]
    have horb := orbit_eq code.prog (code.init (x.map fun b => cond b 1 0))
      (by rw [hlen0]; exact hWF) (fun x => initS (encCode code) x []) x hinit m T0
      (fun t ht => hfit t ht)
    have htle : t ≤ T0 := by
      by_contra hc
      have := hmin T0 (by omega)
      rw [horb T0 le_rfl] at this
      have h2 : haltS (x, encCfg code.prog ((step code.prog)^[T0]
          (code.init (x.map fun b => cond b 1 0))) ++ List.replicate
          (m - (encCfg code.prog ((step code.prog)^[T0]
          (code.init (x.map fun b => cond b 1 0)))).length) false) = true :=
        (haltS_pad _ _ _ _).2 hpc
      rw [h2] at this
      exact absurd this (by simp)
    rw [horb t htle] at hh ⊢
    have hpt := (haltS_pad x _ _ _).1 hh
    set Xt := (step code.prog)^[t] (code.init (x.map fun b => cond b 1 0)) with hXt
    have hXT : (step code.prog)^[T0] (code.init (x.map fun b => cond b 1 0)) = Xt := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le htle
      rw [hs, Nat.add_comm, Function.iterate_add_apply]
      exact iterate_step_of_pc_none _ _ hpt s
    have hkl : code.kout < Xt.stk.length := by
      rw [hXt, iterate_step_len, hlen0]; exact hkout
    rw [outS_pad x _ _ _ _ hkl]
    have hout' : Xt.stk.getD code.kout [] = [bitCode (f x)] := by
      rw [← hXT]; exact hout
    rw [hout', hLf]
    cases hb : f x <;> simp [bitCode]


/-! ### Static bounds on a micro-instruction run -/

/-- All the numbers an instruction mentions (jump targets and table entries). -/
def entries : Instr → List ℕ
  | .push _ tbl next => next :: tbl
  | .pop _ tbl _ next => next :: tbl
  | .peek _ tbl _ next => next :: tbl
  | .load tbl next => next :: tbl
  | .branch tbl n1 n2 => n1 :: n2 :: tbl
  | .goto tbl => tbl
  | .halt => []

/-- Every number of a configuration is at most `N`. -/
def Bd (N : ℕ) (X : Cfg) : Prop :=
  (∀ n, X.pc = some n → n ≤ N) ∧ X.state ≤ N ∧ ∀ j e, e ∈ X.stk.getD j [] → e ≤ N

theorem getD_set_eq (S : List (List ℕ)) (k j : ℕ) (a : List ℕ) :
    (S.set k a).getD j [] = if j = k then (if k < S.length then a else []) else S.getD j [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = k
  · subst h; by_cases h2 : j < S.length <;> simp [h2]
  · have : ¬ k = j := fun e => h e.symm
    simp [h, this]

theorem getD_tbl_le {tbl : List ℕ} {N : ℕ} (h : ∀ e ∈ tbl, e ≤ N) (i : ℕ) : tbl.getD i 0 ≤ N := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : tbl[i]? with
  | none => simp
  | some e => simpa using h e (List.mem_of_getElem? hi)

theorem exec_bd (N : ℕ) (i : Instr) (v : ℕ) (S : List (List ℕ)) (hv : v ≤ N)
    (hS : ∀ j e, e ∈ S.getD j [] → e ≤ N) (hi : ∀ e ∈ entries i, e ≤ N) :
    Bd N (exec i v S) := by
  have hmem : ∀ j, ∀ e ∈ (S.getD j []).tail, e ≤ N := fun j e he =>
    hS j e (List.mem_of_mem_tail he)
  cases i with
  | push k tbl next =>
    simp only [entries, List.mem_cons, forall_eq_or_imp] at hi
    refine ⟨fun n hn => ?_, hv, fun j e he => ?_⟩
    · simp only [exec, Option.some.injEq] at hn; omega
    · simp only [exec, getD_set_eq] at he
      split_ifs at he with h1 h2
      · rcases List.mem_cons.1 he with rfl | he
        · exact getD_tbl_le hi.2 _
        · exact hS _ _ he
      · simp at he
      · exact hS _ _ he
  | pop k tbl w next =>
    simp only [entries, List.mem_cons, forall_eq_or_imp] at hi
    refine ⟨fun n hn => ?_, getD_tbl_le hi.2 _, fun j e he => ?_⟩
    · simp only [exec, Option.some.injEq] at hn; omega
    · simp only [exec, getD_set_eq] at he
      split_ifs at he with h1 h2
      · exact hmem _ _ he
      · simp at he
      · exact hS _ _ he
  | peek k tbl w next =>
    simp only [entries, List.mem_cons, forall_eq_or_imp] at hi
    refine ⟨fun n hn => ?_, getD_tbl_le hi.2 _, fun j e he => hS j e he⟩
    simp only [exec, Option.some.injEq] at hn; omega
  | load tbl next =>
    simp only [entries, List.mem_cons, forall_eq_or_imp] at hi
    refine ⟨fun n hn => ?_, getD_tbl_le hi.2 _, fun j e he => hS j e he⟩
    simp only [exec, Option.some.injEq] at hn; omega
  | branch tbl n1 n2 =>
    simp only [entries, List.mem_cons, forall_eq_or_imp] at hi
    refine ⟨fun n hn => ?_, hv, fun j e he => hS j e he⟩
    simp only [exec, Option.some.injEq] at hn
    split_ifs at hn <;> omega
  | goto tbl =>
    refine ⟨fun n hn => ?_, hv, fun j e he => hS j e he⟩
    simp only [exec, Option.some.injEq] at hn
    rw [← hn]; exact getD_tbl_le hi _
  | halt =>
    exact ⟨fun n hn => by simp [exec] at hn, hv, fun j e he => hS j e he⟩

theorem step_bd (N : ℕ) (P : List Instr) (hP : ∀ i ∈ P, ∀ e ∈ entries i, e ≤ N) (X : Cfg)
    (hX : Bd N X) : Bd N (step P X) := by
  obtain ⟨pc, v, S⟩ := X
  obtain ⟨_, hv, hS⟩ := hX
  cases pc with
  | none => simp only [step]; exact ⟨fun n hn => by simp at hn, hv, hS⟩
  | some n =>
    simp only [step]
    cases hn : P[n]? with
    | none => exact ⟨fun n hn => by simp at hn, hv, hS⟩
    | some i => exact exec_bd N i v S hv hS (hP i (List.mem_of_getElem? hn))

theorem iterate_step_bd (N : ℕ) (P : List Instr) (hP : ∀ i ∈ P, ∀ e ∈ entries i, e ≤ N)
    (X : Cfg) (hX : Bd N X) (t : ℕ) : Bd N ((step P)^[t] X) := by
  induction t with
  | zero => exact hX
  | succ t ih => rw [Function.iterate_succ_apply']; exact step_bd N P hP _ ih

theorem exec_stk_len (i : Instr) (v : ℕ) (S : List (List ℕ)) (j : ℕ) :
    ((exec i v S).stk.getD j []).length ≤ (S.getD j []).length + 1 := by
  cases i with
  | push k tbl next =>
    simp only [exec, getD_set_eq]
    split_ifs with h1 h2
    · subst h1; simp
    · simp
    · simp
  | pop k tbl w next =>
    simp only [exec, getD_set_eq]
    split_ifs with h1 h2
    · subst h1; simp; omega
    · simp
    · simp
  | peek k tbl w next => simp [exec]
  | load tbl next => simp [exec]
  | branch tbl n1 n2 => simp [exec]
  | goto tbl => simp [exec]
  | halt => simp [exec]

theorem step_stk_len (P : List Instr) (X : Cfg) (j : ℕ) :
    ((step P X).stk.getD j []).length ≤ (X.stk.getD j []).length + 1 := by
  obtain ⟨pc, v, S⟩ := X
  cases pc with
  | none => simp [step]
  | some n =>
    simp only [step]
    cases hn : P[n]? with
    | none => simp
    | some i => exact exec_stk_len i v S j

theorem iterate_step_stk_len (P : List Instr) (X : Cfg) (j t : ℕ) :
    (((step P)^[t] X).stk.getD j []).length ≤ (X.stk.getD j []).length + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := step_stk_len P ((step P)^[t] X) j
    omega

theorem encN_length (n : ℕ) : (encN n).length = n + 2 := by simp [encN]

theorem encNs_length_le (l : List ℕ) (N : ℕ) (h : ∀ e ∈ l, e ≤ N) :
    (encNs l).length ≤ l.length * (N + 2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [encNs_cons, List.length_append, encN_length, List.length_cons]
    have h1 := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    have h2 := h a (List.mem_cons_self)
    nlinarith

theorem encLL_length_le (S : List (List ℕ)) (M N : ℕ)
    (h : ∀ s ∈ S, s.length ≤ M ∧ ∀ e ∈ s, e ≤ N) :
    (encLL S).length ≤ S.length * (M * (N + 2) + 1) := by
  induction S with
  | nil => simp
  | cons a S ih =>
    rw [encLL_cons, List.length_append, List.length_cons, List.length_cons]
    have h1 := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    obtain ⟨ha1, ha2⟩ := h a List.mem_cons_self
    have h2 := encNs_length_le a N ha2
    nlinarith

theorem encCfg_length_le (P : List Instr) (X : Cfg) (N M : ℕ) (hB : Bd N X)
    (hM : ∀ j, (X.stk.getD j []).length ≤ M) :
    (encCfg P X).length ≤ 2 * (encP P).length + 2 * N + 2 * N + 5 + X.stk.length * (M * (N + 2) + 1)
      + 2 := by
  have hs : ∀ s ∈ X.stk, s.length ≤ M ∧ ∀ e ∈ s, e ≤ N := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hs
    have : X.stk.getD j [] = X.stk[j] := by simp [List.getD_eq_getElem?_getD, hj]
    exact ⟨this ▸ hM j, fun e he => hB.2.2 j e (this ▸ he)⟩
  have h1 := encLL_length_le X.stk M N hs
  have h2 : (encPc X.pc).length ≤ N + 1 := by
    cases hp : X.pc with
    | none => simp [encPc]
    | some n => have := hB.1 n hp; simp [encPc, un]; omega
  have h3 := hB.2.1
  simp only [encCfg, pairB_length, un_length]
  omega


/-! ### The simulation with a bound on the stack lengths at every micro step -/

section Sim

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (E : Env K Γ Λ σ)

theorem rel_len (hsurj : ∀ i < E.nK, ∃ k, E.numK k = i) (s : ℕ) {c : TM2.Cfg Γ Λ σ} {X : Cfg}
    (hr : E.Rel c X) (hc : ∀ k, (c.stk k).length ≤ s) (j : ℕ) :
    (X.stk.getD j []).length ≤ s := by
  obtain ⟨_, _, hlen, hrel⟩ := hr
  by_cases hj : j < E.nK
  · obtain ⟨k, rfl⟩ := hsurj j hj
    have := (hrel k).length_eq
    rw [this]; exact hc k
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem sim_run_bd (hsurj : ∀ i < E.nK, ∃ k, E.numK k = i) (s : ℕ) :
    ∀ (n : ℕ) (c c' : TM2.Cfg Γ Λ σ) (X : Cfg),
      (flip bind (TM2.step E.M))^[n] (some c) = some c' → E.Rel c X →
      (∀ i ≤ n, ∀ c'', (flip bind (TM2.step E.M))^[i] (some c) = some c'' →
        ∀ k, (c''.stk k).length ≤ s) →
      ∃ t ≤ E.L.length * n, E.Rel c' ((step E.P)^[t] X) ∧
        ∀ t' ≤ t, ∀ j, (((step E.P)^[t'] X).stk.getD j []).length ≤ s + E.L.length := by
  intro n
  induction n with
  | zero =>
    intro c c' X h hr hb
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    refine ⟨0, by simp, hr, fun t' ht' j => ?_⟩
    have : t' = 0 := by omega
    subst this
    have := rel_len E hsurj s hr (hb 0 le_rfl _ rfl) j
    simpa using Nat.le_add_right_of_le this
  | succ n ih =>
    intro c c' X h hr hb
    have hb0 := rel_len E hsurj s hr (hb 0 (Nat.zero_le _) _ rfl)
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    obtain ⟨pc, a, T⟩ := X
    obtain ⟨h1, h2, h3⟩ := hr
    simp only at h1 h2 h3
    subst h1 h2
    cases l with
    | none =>
      have : flip bind (TM2.step E.M) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
      rw [this, Env.iterate_bind_none] at h
      cases h
    | some l =>
      have hfl : flip bind (TM2.step E.M) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
          some (TM2.stepAux (E.M l) v S) := rfl
      rw [hfl] at h
      obtain ⟨t₁, ht₁, T', hs, hr'⟩ := E.sim_stmt (E.M l) (E.start l) v S T (E.placed_start l) h3
      have hle := (E.placed_start l).le
      obtain ⟨t₂, ht₂, hfin, hbd⟩ := ih _ c' ((step E.P)^[t₁] ⟨some (E.start l), E.num v, T⟩) h
        (by rw [hs]; exact ⟨rfl, rfl, hr'⟩) (fun i hi c'' hc'' k => by
          refine hb (i + 1) (by omega) c'' ?_ k
          rw [Function.iterate_succ_apply, hfl]; exact hc'')
      refine ⟨t₂ + t₁, ?_, ?_, fun t' ht' j => ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]; exact hfin
      · by_cases hc : t' ≤ t₁
        · have := iterate_step_stk_len E.P ⟨some (E.pcOf (some l)), E.num v, T⟩ j t'
          have h0 := hb0 j
          simp only at this h0
          omega
        · have e : t' = (t' - t₁) + t₁ := by omega
          rw [e, Function.iterate_add_apply]
          exact hbd (t' - t₁) (by omega) j

end Sim


/-! ### The compiled code of a machine, with bounds -/

section Compiled

open Turing

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

/-- The compiled code of `compileBool`. -/
noncomputable def codeBool : Code :=
  let E := envOfBool tm eIn eOut
  ⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩

theorem envOfBool_surj : ∀ i < (envOfBool tm eIn eOut).nK,
    ∃ k, (envOfBool tm eIn eOut).numK k = i := by
  intro i hi
  refine ⟨(kEquiv tm).symm ⟨i, hi⟩, ?_⟩
  simp [envOfBool]

theorem codeBool_wf : ∀ i ∈ (codeBool tm eIn eOut).prog, InstrWF (codeBool tm eIn eOut).nstk i := by
  intro i hi
  simp only [codeBool, Env.P, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi
  · obtain ⟨p, hp, rfl⟩ := List.mem_mapIdx.1 hi
    intro k hk
    generalize (envOfBool tm eIn eOut).L[p] = q at hk
    cases q <;> simp [Env.instrOf, stkIdx] at hk <;> subst hk <;> exact Env.numK_lt _ _
  · subst hi; intro k hk; simp [stkIdx] at hk; subst hk; exact Env.numK_lt _ _
  · subst hi; intro k hk; simp [stkIdx] at hk; subst hk; exact Env.numK_lt _ _
  · subst hi; intro k hk; simp [stkIdx] at hk

theorem codeBool_kout : (codeBool tm eIn eOut).kout < (codeBool tm eIn eOut).nstk :=
  Env.numK_lt (envOfBool tm eIn eOut) tm.k₁

theorem compileBool_bd (s : ℕ) (l : List Bool) (b : Bool) (n : ℕ)
    (hrun : (flip bind (TM2.step tm.m))^[n] (some (initList tm (l.map eIn.invFun))) =
      some (haltList tm [eOut.invFun b]))
    (hsp : ∀ i ≤ n, ∀ c'',
      (flip bind (TM2.step tm.m))^[i] (some (initList tm (l.map eIn.invFun))) = some c'' →
        ∀ k, (c''.stk k).length ≤ s) :
    ((codeBool tm eIn eOut).run (l.map fun b => cond b 1 0)
        (((flatList tm).length + 3) * n + ((flatList tm).length + 3))).pc = none ∧
    ((codeBool tm eIn eOut).run (l.map fun b => cond b 1 0)
        (((flatList tm).length + 3) * n + ((flatList tm).length + 3))).stk.getD
          (codeBool tm eIn eOut).kout [] = [bitCode b] ∧
    ∀ t ≤ ((flatList tm).length + 3) * n + ((flatList tm).length + 3), ∀ j,
      (((codeBool tm eIn eOut).run (l.map fun b => cond b 1 0) t).stk.getD j []).length ≤
        s + ((flatList tm).length + 3) := by
  let E := envOfBool tm eIn eOut
  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y)
      (l.map (fun b => cond b 1 0)) (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have hlt : (cond x 1 0 : ℕ) < 4 := by cases x <;> simp
    have := E.decode_in hlt
    cases x <;> simpa [E, envOfBool] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map (fun b => cond b 1 0))⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hrel2, hbd⟩ := sim_run_bd E (envOfBool_surj tm eIn eOut) s n _ _ _ hrun hrel hsp
  obtain ⟨hpc, hst, hsr⟩ := hrel2
  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr hbd
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s', hs, hy⟩ : ∃ s', T.getD (E.numK tm.k₁) [] = [s'] ∧
      E.decode tm.k₁ s' = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOfBool]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s'
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  have hfin' := hfin
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin'
  rw [hbit] at hT'
  have hL : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
  have e3 : (E.L.length + 3) * n = E.L.length * n + 3 * n := by ring
  have hT0 : 3 + t ≤ (E.L.length + 3) * n + (E.L.length + 3) := by omega
  have hhalt : ∀ u, 3 + t ≤ u → (step E.P)^[u] ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map (fun b => cond b 1 0))⟩ =
      ⟨none, bitCode b, T'⟩ := by
    intro u hu
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hu
    rw [Nat.add_comm, Function.iterate_add_apply, hfin']
    exact iterate_step_of_pc_none _ _ rfl r
  have hbound3 : ∀ j, (T'.getD j []).length ≤ s + (E.L.length + 3) := by
    intro j
    have h1 := hbd t le_rfl j
    rw [hX] at h1
    have h2 := iterate_step_stk_len E.P ⟨some E.L.length, a, T⟩ j 3
    rw [hfin] at h2
    simp only at h1 h2
    omega
  refine ⟨?_, ?_, fun t' ht' j => ?_⟩
  · exact congrArg Cfg.pc (hhalt _ hT0)
  · have := congrArg (fun X : Cfg => X.stk.getD (E.numK tm.k₁) []) (hhalt _ hT0)
    exact this.trans hT'
  · change (((step E.P)^[t'] ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map (fun b => cond b 1 0))⟩).stk.getD j
          []).length ≤ s + (E.L.length + 3)
    by_cases hc : t' ≤ t
    · have := hbd t' hc j
      omega
    · by_cases hc2 : t' < 3 + t
      · have e : t' = (t' - t) + t := by omega
        rw [e, Function.iterate_add_apply]
        have h1 := iterate_step_stk_len E.P ((step E.P)^[t] ⟨some (E.start tm.main),
          E.num tm.initialState, (List.replicate E.nK []).set (E.numK tm.k₀)
            (l.map (fun b => cond b 1 0))⟩) j (t' - t)
        have h3 := hbd t le_rfl j
        omega
      · rw [hhalt t' (by omega)]
        exact hbound3 j

end Compiled



/-! ### Every language of `PSPACE` has the timed data -/

theorem reach_of_iterate (tm : Turing.FinTM2) (init : tm.Cfg) :
    ∀ (i : ℕ) (c'' : tm.Cfg), (flip bind (Turing.TM2.step tm.m))^[i] (some init) = some c'' →
      Relation.ReflTransGen (fun x y => y ∈ tm.step x) init c'' := by
  intro i
  induction i with
  | zero =>
    intro c'' h
    simp only [Function.iterate_zero, id] at h
    have h' := Option.some.inj h
    subst h'; exact Relation.ReflTransGen.refl
  | succ i ih =>
    intro c'' h
    rw [Function.iterate_succ_apply'] at h
    cases hc : (flip bind (Turing.TM2.step tm.m))^[i] (some init) with
    | none => rw [hc] at h; simp [flip] at h
    | some c1 =>
      rw [hc] at h
      refine Relation.ReflTransGen.tail (ih c1 hc) ?_
      have h' : Turing.TM2.step tm.m c1 = some c'' := by simpa [flip] using h
      exact h'

theorem pspace_timedData (L : Language Bool) (hL : L ∈ PSPACE) : TimedData L := by
  obtain ⟨k, f, hf, c, hsp⟩ := hL
  let tm := c.tm
  let eIn := c.inputAlphabet
  let eOut := c.outputAlphabet
  let code := codeBool tm eIn eOut
  let E := envOfBool tm eIn eOut
  let N : ℕ := (code.prog.flatMap entries).sum + code.pc₀ + code.state₀ + 1
  let B : ℕ := code.nstk * (N + 2)
  let A : ℕ := 2 * (encP code.prog).length + 4 * N + 7 +
    code.nstk * (((flatList tm).length + 3) * (N + 2) + 1)
  let p : Polynomial ℕ := Polynomial.C A + Polynomial.C B * (Polynomial.X ^ k + Polynomial.C k)
  have hP : ∀ i ∈ code.prog, ∀ e ∈ entries i, e ≤ N := by
    intro i hi e he
    have h1 : e ∈ code.prog.flatMap entries := List.mem_flatMap.2 ⟨i, hi, he⟩
    have := List.le_sum_of_mem h1
    omega
  refine timedData_of_code L code f hf p (codeBool_wf tm eIn eOut) (codeBool_kout tm eIn eOut)
    (fun x => ?_)
  -- the machine run
  have hout := c.outputsFun x
  have heval : (flip bind (Turing.TM2.step tm.m))^[hout.steps]
      (some (Turing.initList tm (x.map eIn.invFun))) =
        some (Turing.haltList tm [eOut.invFun (f x)]) := by
    have := hout.evals_in_steps
    simp [Computability.encodeBool, tm, eIn, eOut] at this
    exact this
  have hspace : ∀ i ≤ hout.steps, ∀ c'', (flip bind (Turing.TM2.step tm.m))^[i]
      (some (Turing.initList tm (x.map eIn.invFun))) = some c'' →
        ∀ k', (c''.stk k').length ≤ x.length ^ k + k := by
    intro i _ c'' hc'' k'
    exact hsp x c'' (reach_of_iterate tm _ i c'' hc'') k'
  obtain ⟨hpc, hstk, hbound⟩ := compileBool_bd tm eIn eOut _ x (f x) hout.steps heval hspace
  refine ⟨((flatList tm).length + 3) * hout.steps + ((flatList tm).length + 3), hpc, hstk,
    fun t ht => ?_⟩
  -- the length of the encoded configuration
  have hlen0 : (code.init (x.map fun b => cond b 1 0)).stk.length = code.nstk := by
    simp [Code.init]
  have hBd0 : Bd N (code.init (x.map fun b => cond b 1 0)) := by
    refine ⟨fun n hn => ?_, ?_, fun j e he => ?_⟩
    · simp only [Code.init, Option.some.injEq] at hn; subst hn; omega
    · simp only [Code.init]; omega
    · simp only [Code.init, getD_set_eq] at he
      split_ifs at he with h1 h2
      · simp only [List.mem_map] at he
        obtain ⟨b, _, rfl⟩ := he
        cases b <;> simp <;> omega
      · simp at he
      · simp [List.getD_eq_getElem?_getD] at he
  have hBd := iterate_step_bd N code.prog hP _ hBd0 t
  have hlen := encCfg_length_le code.prog ((step code.prog)^[t]
    (code.init (x.map fun b => cond b 1 0))) N (x.length ^ k + k + ((flatList tm).length + 3))
    hBd (fun j => hbound t ht j)
  rw [iterate_step_len, hlen0] at hlen
  show (encCfg code.prog ((step code.prog)^[t] (code.init (x.map fun b => cond b 1 0)))).length ≤
    p.eval x.length
  have hev : p.eval x.length = A + B * (x.length ^ k + k) := by simp [p]
  rw [hev]
  have e1 : code.nstk * ((x.length ^ k + k + ((flatList tm).length + 3)) * (N + 2) + 1) =
      B * (x.length ^ k + k) + code.nstk * (((flatList tm).length + 3) * (N + 2) + 1) := by
    simp only [B]; ring
  omega


/-- The step-encoding lemma: every language of `PSPACE` has a `StepEncoding`. -/
theorem pspace_stepEncoding : PspaceStepEncodingLemma := by
  intro L hL
  obtain ⟨⟨p, q, initL, stepL, haltL, outL, hi, hs, hh, ho, ht, hc⟩⟩ := pspace_timedData L hL
  exact stepEncoding_of_timed p q initL stepL haltL outL hi hs hh ho ht hc

/-- PSPACE ⊆ PCTC. -/
theorem PSPACE_subset_PCTC : PSPACE ⊆ PCTC :=
  PSPACE_subset_PCTC_of_stepEncoding pspace_stepEncoding

end PEqualNP.QuantumGravity.Open.PspaceMachine
