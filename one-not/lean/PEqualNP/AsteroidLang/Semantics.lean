import Mathlib
import PEqualNP.AsteroidLang.Eval
import PEqualNP.AsteroidLang.CoreEq
/-!
# asteroid: what a verdict means

`AsteroidLang/Eval.lean` is the evaluator the executable runs. This file says what a `true`
verdict is a statement about: the project's own definitions (`Circuit.eval`, `F2`, `baseDQ`, the
hypotheses of the main theorem). `denote` is the meaning of a claim; `eval_sound` says that a claim
the evaluator calls true holds. The checkers behind the evaluator are the light copies of
`AsteroidLang/Core.lean`; `CoreEq.lean` proves them equal to the project's, and the lemmas of
section 1 here carry that equality across the translation of a circuit
(`CoreEq.CoreEq.toProject`: the circuit of the executable as a circuit of the project).

Forms with a soundness theorem: `correct(c)`, `hyps(c)`, `forall cubes slack(c) >= 0`, and
comparisons between `gates`, `base`, `orwitness`, `slack` and whole numbers, also under `not`.
Forms with none are listed in `asteroid/NATIVE.md`.
-/
namespace AsteroidLang.Semantics
open AsteroidLang
open PEqualNP.CircuitLowerBounds (Circuit GateOp)
open PEqualNP.Outside.L_meta_951_aux (F2 baseDQ baseDQ_empty AtMostOneNot)

/-! ## 1. The copy of a checker on the circuit of the project is the checker -/

section Map
variable {γ δ : Type} (f : δ → γ)

theorem tt_map (op a b : γ → Nat) (full : Nat) (ws : List Nat) (gs : List δ) :
    Core.tt op a b full ws (gs.map f) = Core.tt (op ∘ f) (a ∘ f) (b ∘ f) full ws gs := by
  simp [Core.tt, List.foldl_map, Function.comp_def]

theorem tables_map (n : Nat) (op a b : γ → Nat) (gs : List δ) :
    Core.tables n (gs.map f) op a b = Core.tables n gs (op ∘ f) (a ∘ f) (b ∘ f) := by
  simp [Core.tables, tt_map]

theorem orTables_map (n : Nat) (op a b : γ → Nat) (gs : List δ) :
    Core.orTables n (gs.map f) op a b = Core.orTables n gs (op ∘ f) (a ∘ f) (b ∘ f) := by
  simp [Core.orTables, tables_map, List.zip_map_right, List.filter_map, Function.comp_def]

theorem notCount_map (op : γ → Nat) (gs : List δ) (d : δ) :
    Core.notCount (gs.map f) op (f d) = Core.notCount gs (op ∘ f) d := by
  simp [Core.notCount, List.getD_eq_getElem?_getD, List.getElem?_map]

end Map


theorem correct_bridge (C : Core.Circ) : SearchCheck.correctB (CoreEq.toProject C) = C.correct := by
  rw [CoreEq.correctB_eq]
  simp only [CoreEq.toProject, Core.Circ.correct, Core.correctB, tables_map]
  rfl

theorem slackNonnegAll_bridge (C : Core.Circ) :
    SearchCheck.slackNonnegAll (CoreEq.toProject C) = C.slackNonneg := by
  rw [CoreEq.slackNonnegAll_eq]
  simp only [CoreEq.toProject, Core.Circ.slackNonneg, Core.slackNonnegAll, orTables_map]
  rfl

theorem setsOk_bridge (C : Core.Circ) : SearchCheck.setsOkB (CoreEq.toProject C) = C.setsOk := rfl

theorem hypsB_map {γ δ : Type} (f : δ → γ) (n : Nat) (sets : List (List Nat)) (outs : List Nat)
    (gs : List δ) (op : γ → Nat) (d : δ) :
    Core.hypsB n sets outs (gs.map f) op (f d) = Core.hypsB n sets outs gs (op ∘ f) d := by
  unfold Core.hypsB
  rw [notCount_map]
  simp

theorem hypsB_bridge (C : Core.Circ) : SearchCheck.hypsB (CoreEq.toProject C) = C.hyps := by
  rw [CoreEq.hypsB_eq]
  exact hypsB_map (fun g : Core.Gate => (⟨g.op, g.a, g.b⟩ : SearchCheck.Gate)) C.n C.sets C.outs
    C.gates SearchCheck.Gate.op ⟨0, 0, 0⟩

theorem orWitness_bridge (C : Core.Circ) (q : Nat) :
    SearchCheck.orWitnessAt (CoreEq.toProject C) q = C.orWitness q := by
  rw [CoreEq.orWitnessAt_eq]
  simp only [CoreEq.toProject, Core.Circ.orWitness, Core.orWitnessAt, orTables_map]
  rfl

theorem base_bridge (C : Core.Circ) (q : Nat) : SearchCheck.baseAt (CoreEq.toProject C) q = C.base q := rfl

/-! ## 2. The meaning of a claim -/

/-- the hypotheses of the main theorem, for a circuit of the project, in the exact shape of
`SearchCheck.hypsB_sound` -/
def Hyps (C : SearchCheck.Circ) : Prop :=
  C.SetsOk ∧ C.sets.length ≤ C.outs.length ∧
  (∀ i : Fin C.sets.length, 2 ≤ (C.setFin i).card) ∧
  (∀ i j : Fin C.sets.length, i ≠ j → (C.setFin i ∩ C.setFin j).card ≤ 1) ∧
  AtMostOneNot C.toGates ∧
  (∃ ι : Fin 1 → Fin C.toGates.length, ∀ i : Fin C.toGates.length,
    (C.toGates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)

/-- `correct(c)`: the project's `Circuit.eval` on `C.toGates` computes the OR of every set on
every input (and there is an output wire for every set) -/
def Correct (C : SearchCheck.Circ) : Prop :=
  C.sets.length ≤ C.outs.length ∧
  ∀ (w : Fin C.sets.length) (x : Fin C.n → Bool),
    Circuit.eval ⟨C.toGates, C.outs.getD w 0⟩ (List.ofFn x) = decide (∃ v ∈ C.setFin w, x v = true)

/-- `forall cubes slack(c) >= 0`: at every cube `Q`, the base is at most the number of OR gates
with a real witness -/
def SlackAll (C : SearchCheck.Circ) : Prop :=
  ∀ Q : Finset (Fin C.n), baseDQ C.setFin ∅ Q ≤ (F2 C.toGates C.setFin Q).card

/-- `true` exactly on the NOT operation -/
def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

/-- the value of a count, in the project's definitions; `none` for the counts that have no
statement here yet -/
noncomputable def semFunc (f : Func) (C : SearchCheck.Circ) : Option Int :=
  match f with
  | .gates => some (C.toGates.length : Int)
  | .nots => some ((C.toGates.countP fun g => isNotOp g.op) : Int)
  | .base => some ((∑ w, ((C.setFin w).card - 1) : Nat) : Int)
  | .orwitness => some ((F2 C.toGates C.setFin ∅).card : Int)
  | .slack => some (((F2 C.toGates C.setFin ∅).card : Int) - ((∑ w, ((C.setFin w).card - 1) : Nat) : Int))
  | _ => none

/-- a comparison of integers as a proposition -/
def relOp : Op → Int → Int → Prop
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
  | .gt, x, y => x > y
  | .ge, x, y => x ≥ y

theorem holds_iff (op : Op) (x y : Int) : op.holds x y = true ↔ relOp op x y := by
  cases op <;> simp [Op.holds, relOp]

/-- the value of a term in the project's definitions -/
noncomputable def semTerm (env : Env) : Term → Option Int
  | .int k => some k
  | .app f name => (env.circ? name).bind fun C => semFunc f (CoreEq.toProject C)

/-- **The meaning of a claim**, as a proposition about the project's own definitions. -/
def denote (env : Env) : Expr → Prop
  | .correct name => ∃ C, env.circ? name = some C ∧ Correct (CoreEq.toProject C)
  | .hyps name _ => ∃ C, env.circ? name = some C ∧ Hyps (CoreEq.toProject C)
  | .forallCubes name => ∃ C, env.circ? name = some C ∧ SlackAll (CoreEq.toProject C)
  | .cmp l op r => ∃ x y, semTerm env l = some x ∧ semTerm env r = some y ∧ relOp op x y
  | .not e => ¬ denote env e

/-- the terms that have a statement in the project's definitions -/
def goodT : Term → Bool
  | .int _ => true
  | .app .gates _ => true
  | .app .nots _ => true
  | .app .base _ => true
  | .app .orwitness _ => true
  | .app .slack _ => true
  | .app _ _ => false

/-- the comparisons whose verdict is `true` exactly when the statement holds -/
def exactE : Expr → Bool
  | .cmp l _ r => goodT l && goodT r
  | _ => false

/-- the claims for which `eval_sound` is proved (comparisons of `gates`, `nots`, `base`, `orwitness`,
`slack` and integers) -/
def coveredE : Expr → Bool
  | .correct _ => true
  | .hyps _ want => want
  | .forallCubes _ => true
  | e@(.cmp ..) => exactE e
  | .not e => exactE e

/-! ## 3. Soundness -/

theorem setsOk_of_circ? {env : Env} {name : String} {C : Core.Circ} (h : env.circ? name = some C) :
    C.setsOk = true := by
  unfold Env.circ? at h
  split at h
  · rename_i C' _
    split at h
    · rename_i hs; cases h; exact hs
    · simp at h
  · simp at h

theorem setsOkP {env : Env} {name : String} {C : Core.Circ} (h : env.circ? name = some C) :
    (CoreEq.toProject C).SetsOk :=
  SearchCheck.setsOk_of_setsOkB _ (by rw [setsOk_bridge]; exact setsOk_of_circ? h)

/-- counting by position is counting the list -/
theorem range_filter_getD_length {α : Type} (l : List α) (p : α → Bool) (d : α) :
    ((List.range l.length).filter fun k => p (l.getD k d)).length = l.countP p := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.countP_cons]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero]
    split <;> simp_all

theorem isNotOp_toGate (g : SearchCheck.Gate) : isNotOp g.toGate.op = decide (2 ≤ g.op) := by
  rcases g with ⟨op, a, b⟩
  match op with
  | 0 => simp [SearchCheck.Gate.toGate, isNotOp]
  | 1 => simp [SearchCheck.Gate.toGate, isNotOp]
  | k + 2 => simp [SearchCheck.Gate.toGate, isNotOp]

/-- the evaluator's NOT count is the number of NOT gates of the project gate list -/
theorem nots_bridge (C : Core.Circ) :
    C.nots = (CoreEq.toProject C).toGates.countP fun g => isNotOp g.op := by
  have h := range_filter_getD_length C.gates (fun g : Core.Gate => decide (2 ≤ g.op)) ⟨0, 0, 0⟩
  rw [Core.Circ.nots, Core.notCount, h]
  simp only [CoreEq.toProject, SearchCheck.Circ.toGates, List.map_map, List.countP_map]
  exact List.countP_congr fun g _ => by simp [Function.comp_def, isNotOp_toGate]

theorem func_sem {env : Env} {name : String} {C : Core.Circ} (h : env.circ? name = some C)
    (f : Func) (v : Int) (hv : semFunc f (CoreEq.toProject C) = some v) : f.eval C = v := by
  have hC := setsOkP h
  have hF := SearchCheck.card_F2_eq_orWitnessAt (CoreEq.toProject C) hC ∅
  have hB := SearchCheck.baseAt_eq_baseDQ (CoreEq.toProject C) hC ∅
  rw [SearchCheck.maskOf_empty] at hF hB
  rw [baseDQ_empty] at hB
  rw [orWitness_bridge] at hF
  cases f <;> simp only [semFunc, Option.some.injEq, reduceCtorEq] at hv
  · subst hv; simp [Func.eval, CoreEq.toProject, SearchCheck.Circ.toGates]
  · subst hv; simp only [Func.eval]; rw [nots_bridge]
  · subst hv
    simp only [Func.eval]
    rw [← hB]; rfl
  · subst hv; simp only [Func.eval]; rw [hF]
  · subst hv; simp only [Func.eval]; rw [hF, ← hB]; rfl
  all_goals simp at hv

theorem term_sem {env : Env} (t : Term) (x : Int) (hx : semTerm env t = some x) : t.eval env = some x := by
  cases t with
  | int k => simpa [semTerm, Term.eval] using hx
  | app f name =>
    simp only [semTerm, Option.bind_eq_some_iff] at hx
    obtain ⟨C, hC, hv⟩ := hx
    simp [Term.eval, hC, func_sem hC f x hv]

theorem cmp_iff (env : Env) (l r : Term) (op : Op) (x y : Int)
    (hx : semTerm env l = some x) (hy : semTerm env r = some y) :
    (Expr.cmp l op r).eval env = some (op.holds x y) := by
  simp [Expr.eval, term_sem l x hx, term_sem r y hy]

theorem term_ex {env : Env} (t : Term) (ht : goodT t = true) (x : Int)
    (hx : t.eval env = some x) : semTerm env t = some x := by
  cases t with
  | int k => simpa [semTerm, Term.eval] using hx
  | app f name =>
    simp only [Term.eval, Option.map_eq_some_iff] at hx
    obtain ⟨C, hC, hfx⟩ := hx
    have : ∃ v, semFunc f (CoreEq.toProject C) = some v := by
      cases f <;> simp [goodT, semFunc] at ht ⊢
    obtain ⟨v, hv⟩ := this
    have := func_sem hC f v hv
    simp only [semTerm, hC, Option.bind_some, hv]
    rw [← hfx, this]

theorem cmp_ex {env : Env} {l r : Term} {op : Op} (h : exactE (.cmp l op r) = true) {b : Bool}
    (hev : (Expr.cmp l op r).eval env = some b) :
    ∃ x y, semTerm env l = some x ∧ semTerm env r = some y ∧ b = op.holds x y := by
  simp only [exactE, Bool.and_eq_true] at h
  unfold Expr.eval at hev
  cases hx : Term.eval env l with
  | none => simp [hx] at hev
  | some x =>
    cases hy : Term.eval env r with
    | none => simp [hx, hy] at hev
    | some y =>
      refine ⟨x, y, term_ex l h.1 x hx, term_ex r h.2 y hy, ?_⟩
      simp [hx, hy] at hev
      exact hev.symm

/-- **Soundness.** A covered claim that the evaluator calls true holds, as a statement about the
project's own definitions. -/
theorem eval_sound (env : Env) (e : Expr) (hcov : coveredE e = true) (hev : e.eval env = some true) :
    denote env e := by
  cases e with
  | correct name =>
    simp only [Expr.eval, Option.map_eq_some_iff, Bool.and_eq_true, decide_eq_true_eq] at hev
    obtain ⟨C, hC, hc, hlen⟩ := hev
    refine ⟨C, hC, hlen, fun w x => ?_⟩
    exact SearchCheck.correctB_sound_project _ (by rw [correct_bridge]; exact hc) hlen w x
  | hyps name want =>
    simp only [coveredE] at hcov
    subst hcov
    simp only [Expr.eval, Option.map_eq_some_iff, beq_iff_eq] at hev
    obtain ⟨C, hC, hh⟩ := hev
    exact ⟨C, hC, SearchCheck.hypsB_sound _ (by rw [hypsB_bridge]; exact hh)⟩
  | forallCubes name =>
    simp only [Expr.eval, Option.map_eq_some_iff] at hev
    obtain ⟨C, hC, hs⟩ := hev
    exact ⟨C, hC, fun Q => SearchCheck.slackNonnegAll_sound _ (setsOkP hC)
      (by rw [slackNonnegAll_bridge]; exact hs) Q⟩
  | cmp l op r =>
    obtain ⟨x, y, hx, hy, hb⟩ := cmp_ex (by simpa [coveredE] using hcov) hev
    exact ⟨x, y, hx, hy, (holds_iff op x y).1 (hb ▸ rfl)⟩
  | not e =>
    cases e with
    | cmp l op r =>
      have hcov' : exactE (.cmp l op r) = true := by simpa [coveredE] using hcov
      simp only [Expr.eval, Option.map_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at hev
      obtain ⟨b, hb, hbf⟩ := hev
      obtain ⟨x, y, hx, hy, hxy⟩ := cmp_ex hcov' hb
      rintro ⟨x', y', hx', hy', hr⟩
      rw [hx] at hx'; rw [hy] at hy'
      cases hx'; cases hy'
      have := (holds_iff op x y).2 hr
      rw [← hxy] at this
      rw [this] at hbf
      cases hbf
    | _ => simp [coveredE, exactE] at hcov

end AsteroidLang.Semantics
