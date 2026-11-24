import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Machines.FirstGRun

/-!
# A clocked run: any machine, cut off after a linear number of steps

Given a machine `M` and a constant `c`, the machine `CM M c d z` copies the input back and forth
while writing `c` fuel marks per input symbol, then runs `M`, spending one fuel mark per step of
`M`. If `M` halts first, the remaining fuel is erased and the output of `M` is kept. If the fuel
runs out, every stack of `M` is erased and the single symbol `z` is written.

Consequence (`clocked`): for any machine computing `g`, some `f` is computed within a linear
time bound and agrees with `g` on every input on which `M` halts within `c` steps per input
symbol.
-/

namespace PEqualNP.General.Kannan.Clk

open Turing PEqualNP.Library.Machines

variable (M : FinTM2)

/-- Stacks: those of `M`, the fuel (`inr false`) and a temporary stack (`inr true`). -/
abbrev XK : Type := M.K ⊕ Bool

@[reducible] def XΓ : XK M → Type
  | Sum.inl k => M.Γ k
  | Sum.inr false => Unit
  | Sum.inr true => M.Γ M.k₀

/-- Number of stacks of `M`. -/
noncomputable def mK : ℕ := @Fintype.card M.K M.kFin

noncomputable def eK : M.K ≃ Fin (mK M) := @Fintype.equivFin M.K M.kFin

/-- Labels: those of `M`; `some false` (load fuel), `some true` (restore input), `none` (erase
fuel); erasing stage `i`. -/
abbrev XΛ : Type := M.Λ ⊕ (Option Bool ⊕ Fin (mK M + 1))

abbrev Xσ : Type := M.σ × Option (M.Γ M.k₀) × Bool

variable {M}

def lA : XΛ M := Sum.inr (Sum.inl (some false))
def lB : XΛ M := Sum.inr (Sum.inl (some true))
def lE : XΛ M := Sum.inr (Sum.inl none)
def er (i : Fin (mK M + 1)) : XΛ M := Sum.inr (Sum.inr i)

/-- A statement of `M` inside the clocked machine. Halting becomes erasing the fuel. -/
def trC : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (XΓ M) (XΛ M) (Xσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trC q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trC q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trC q₁) (trC q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => lE)

/-- `c` fuel pushes. -/
def pushF : ℕ → TM2.Stmt (XΓ M) (XΛ M) (Xσ M) → TM2.Stmt (XΓ M) (XΛ M) (Xσ M)
  | 0, q => q
  | c + 1, q => .push (Sum.inr false) (fun _ => ()) (pushF c q)

variable (M)

/-- The program. -/
noncomputable def xprog (c : ℕ) (d : M.Γ M.k₀) (z : M.Γ M.k₁) :
    XΛ M → TM2.Stmt (XΓ M) (XΛ M) (Xσ M)
  | Sum.inl l => .pop (Sum.inr false) (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (trC (M.m l)) (.goto fun _ => er 0))
  | Sum.inr (Sum.inl (some false)) => .pop (Sum.inl M.k₀) (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push (Sum.inr true) (fun s => s.2.1.getD d) (pushF c (.goto fun _ => lA)))
        (.goto fun _ => lB))
  | Sum.inr (Sum.inl (some true)) => .pop (Sum.inr true) (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push (Sum.inl M.k₀) (fun s => s.2.1.getD d) (.goto fun _ => lB))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr (Sum.inl none) => .pop (Sum.inr false) (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (.goto fun _ => lE) .halt)
  | Sum.inr (Sum.inr i) =>
      if h : i.val < mK M then
        .pop (Sum.inl ((eK M).symm ⟨i.val, h⟩)) (fun s o => (s.1, s.2.1, o.isSome))
          (.branch (fun s => s.2.2) (.goto fun _ => er i) (.goto fun _ => er ⟨i.val + 1, by omega⟩))
      else
        .load (fun _ => (M.initialState, none, false)) (.push (Sum.inl M.k₁) (fun _ => z) .halt)

/-- The clocked machine. -/
noncomputable def CM (c : ℕ) (d : M.Γ M.k₀) (z : M.Γ M.k₁) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  haveI := M.Γk₀Fin
  { K := XK M
    k₀ := Sum.inl M.k₀
    k₁ := Sum.inl M.k₁
    Γ := XΓ M
    Λ := XΛ M
    main := lA
    σ := Xσ M
    initialState := (M.initialState, none, false)
    Γk₀Fin := M.Γk₀Fin
    m := xprog M c d z }

variable {M}

abbrev XCfg (M : FinTM2) : Type := TM2.Cfg (XΓ M) (XΛ M) (Xσ M)

/-- The stacks of the clocked machine. -/
def cst (X : ∀ k, List (M.Γ k)) (f : ℕ) (t : List (M.Γ M.k₀)) : ∀ k, List (XΓ M k)
  | Sum.inl k => X k
  | Sum.inr false => List.replicate f ()
  | Sum.inr true => t

theorem cst_upd_inl (X : ∀ k, List (M.Γ k)) (f : ℕ) (t : List (M.Γ M.k₀)) (k : M.K)
    (l : List (M.Γ k)) :
    Function.update (cst X f t) (Sum.inl k) l = cst (Function.update X k l) f t := by
  funext j
  rcases j with j | _ | _
  · by_cases h : j = k
    · subst h; simp [cst]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [cst, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem cst_upd_F (X : ∀ k, List (M.Γ k)) (f : ℕ) (t : List (M.Γ M.k₀)) (f' : ℕ) :
    Function.update (cst X f t) (Sum.inr false) (List.replicate f' ()) = cst X f' t := by
  funext j
  rcases j with j | _ | _
  · rw [Function.update_of_ne (by simp)]; rfl
  · simp [cst]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem cst_upd_T (X : ∀ k, List (M.Γ k)) (f : ℕ) (t t' : List (M.Γ M.k₀)) :
    Function.update (cst X f t) (Sum.inr true) t' = cst X f t' := by
  funext j
  rcases j with j | _ | _
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · simp [cst]

/-- A configuration of `M` inside the clocked machine with `f` fuel marks. -/
def emb (b : Bool) (f : ℕ) (c : TM2.Cfg M.Γ M.Λ M.σ) : XCfg M :=
  ⟨some (c.l.elim lE Sum.inl), (c.var, none, b), cst c.stk f []⟩

theorem simC (b : Bool) (f : ℕ) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (X : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trC q) ((v, none, b) : Xσ M) (cst X f []) = emb b f (TM2.stepAux q v X) := by
  induction q generalizing v X with
  | push k g q ih =>
    have := ih v (Function.update X k (g v :: X k))
    simp only [trC, TM2.stepAux]
    rw [show (cst X f [] : ∀ k, List (XΓ M k)) (Sum.inl k) = X k from rfl, cst_upd_inl]
    exact this
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
    have := ih (g v (X k).head?) (Function.update X k (X k).tail)
    simp only [trC, TM2.stepAux]
    rw [show (cst X f [] : ∀ k, List (XΓ M k)) (Sum.inl k) = X k from rfl, cst_upd_inl]
    exact this
  | load a q ih => exact ih _ _
  | branch g q₁ q₂ ih₁ ih₂ =>
    simp only [trC, TM2.stepAux]
    cases g v
    · exact ih₂ v X
    · exact ih₁ v X
  | goto g => rfl
  | halt => rfl

variable (c : ℕ) (d : M.Γ M.k₀) (z : M.Γ M.k₁)

theorem stepC (b : Bool) (f : ℕ) (x y : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m x = some y) :
    TM2.step (xprog M c d z) (emb b (f + 1) x) = some (emb true f y) := by
  obtain ⟨l, v, S⟩ := x
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb, Option.elim, TM2.step, xprog, TM2.stepAux]
    rw [show (cst S (f + 1) [] : ∀ k, List (XΓ M k)) (Sum.inr false) =
      List.replicate (f + 1) () from rfl]
    simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
      Bool.cond_true]
    rw [cst_upd_F]
    exact congrArg some (simC true f (M.m l) v S)

theorem runC : ∀ (j : ℕ) (x y : TM2.Cfg M.Γ M.Λ M.σ) (b : Bool) (f : ℕ),
    (flip bind (TM2.step M.m))^[j] (some x) = some y →
    ∃ b', (flip bind (TM2.step (xprog M c d z)))^[j] (some (emb b (f + j) x)) =
      some (emb b' f y) := by
  intro j
  induction j with
  | zero =>
    intro x y b f h
    have : x = y := Option.some.inj h
    subst this
    exact ⟨b, rfl⟩
  | succ j ih =>
    intro x y b f h
    rw [Function.iterate_succ_apply] at h
    cases hx : TM2.step M.m x with
    | none =>
      have e : flip bind (TM2.step M.m) (some x) = none := hx
      rw [e, iterate_none] at h
      exact absurd h (by simp)
    | some x' =>
      have e : flip bind (TM2.step M.m) (some x) = some x' := hx
      rw [e] at h
      obtain ⟨b', hb'⟩ := ih x' y true f h
      refine ⟨b', ?_⟩
      rw [Function.iterate_succ_apply]
      have e2 : flip bind (TM2.step (xprog M c d z)) (some (emb b (f + (j + 1)) x)) =
          some (emb true (f + j) x') := by
        rw [show f + (j + 1) = (f + j) + 1 by omega]
        exact stepC c d z b (f + j) x x' hx
      rw [e2, hb']

/-! ### Loading the fuel -/

theorem pushF_stepAux (n : ℕ) (q : TM2.Stmt (XΓ M) (XΛ M) (Xσ M)) (v : Xσ M)
    (X : ∀ k, List (M.Γ k)) (f : ℕ) (t : List (M.Γ M.k₀)) :
    TM2.stepAux (pushF n q) v (cst X f t) = TM2.stepAux q v (cst X (f + n) t) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [pushF, TM2.stepAux]
    rw [show (cst X f t : ∀ k, List (XΓ M k)) (Sum.inr false) = List.replicate f () from rfl,
      show (() :: List.replicate f ()) = List.replicate (f + 1) () from rfl, cst_upd_F, ih]
    rw [show f + 1 + n = f + (n + 1) by omega]

theorem loopA (v : M.σ) (X : ∀ k, List (M.Γ k)) (hX : X M.k₀ = []) :
    ∀ (l : List (M.Γ M.k₀)) (f : ℕ) (t : List (M.Γ M.k₀)) (o : Option (M.Γ M.k₀)) (b : Bool),
      (flip bind (TM2.step (xprog M c d z)))^[l.length + 1]
          (some (⟨some lA, (v, o, b), cst (Function.update X M.k₀ l) f t⟩ : XCfg M)) =
        some ⟨some lB, (v, none, b), cst X (f + c * l.length) (l.reverse ++ t)⟩ := by
  intro l
  induction l with
  | nil =>
    intro f t o b
    show some _ = some _
    simp only [lA, xprog, TM2.stepAux]
    rw [show (cst (Function.update X M.k₀ []) f t : ∀ k, List (XΓ M k)) (Sum.inl M.k₀) = [] by
      simp [cst]]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_inl, Function.update_idem]
    rw [Function.update_eq_self_iff.mpr hX.symm]
    simp [lB]
  | cons a l ih =>
    intro f t o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d z))
        (some (⟨some lA, (v, o, b), cst (Function.update X M.k₀ (a :: l)) f t⟩ : XCfg M)) =
        some ⟨some lA, (v, some a, b), cst (Function.update X M.k₀ l) (f + c) (a :: t)⟩ := by
      show some _ = some _
      simp only [lA, xprog, TM2.stepAux]
      rw [show (cst (Function.update X M.k₀ (a :: l)) f t : ∀ k, List (XΓ M k)) (Sum.inl M.k₀) =
        a :: l by simp [cst]]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some]
      rw [cst_upd_inl, Function.update_idem]
      rw [show (cst (Function.update X M.k₀ l) f t : ∀ k, List (XΓ M k)) (Sum.inr true) = t
        from rfl, cst_upd_T, pushF_stepAux]
      rfl
    rw [e, ih]
    congr 3
    · ring
    · simp

theorem loopB (v : M.σ) (X : ∀ k, List (M.Γ k)) (f : ℕ) :
    ∀ (t u : List (M.Γ M.k₀)) (o : Option (M.Γ M.k₀)) (b : Bool),
      (flip bind (TM2.step (xprog M c d z)))^[t.length + 1]
          (some (⟨some lB, (v, o, b), cst (Function.update X M.k₀ u) f t⟩ : XCfg M)) =
        some ⟨some (Sum.inl M.main), (v, none, b),
          cst (Function.update X M.k₀ (t.reverse ++ u)) f []⟩ := by
  intro t
  induction t with
  | nil =>
    intro u o b
    show some _ = some _
    simp only [lB, xprog, TM2.stepAux]
    rw [show (cst (Function.update X M.k₀ u) f [] : ∀ k, List (XΓ M k)) (Sum.inr true) = []
      from rfl]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_T]
    simp
  | cons a t ih =>
    intro u o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d z))
        (some (⟨some lB, (v, o, b), cst (Function.update X M.k₀ u) f (a :: t)⟩ : XCfg M)) =
        some ⟨some lB, (v, some a, b), cst (Function.update X M.k₀ (a :: u)) f t⟩ := by
      show some _ = some _
      simp only [lB, xprog, TM2.stepAux]
      rw [show (cst (Function.update X M.k₀ u) f (a :: t) : ∀ k, List (XΓ M k)) (Sum.inr true) =
        a :: t from rfl]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some]
      rw [cst_upd_T]
      rw [show (cst (Function.update X M.k₀ u) f t : ∀ k, List (XΓ M k)) (Sum.inl M.k₀) = u by
        simp [cst]]
      rw [cst_upd_inl, Function.update_idem]
    rw [e, ih]
    simp


/-! ### Erasing the fuel, failing, erasing the stacks -/

theorem loopE (v : M.σ) (X : ∀ k, List (M.Γ k)) :
    ∀ (f : ℕ) (b : Bool),
      (flip bind (TM2.step (xprog M c d z)))^[f + 1]
          (some (⟨some lE, (v, none, b), cst X f []⟩ : XCfg M)) =
        some ⟨none, (v, none, false), cst X 0 []⟩ := by
  intro f
  induction f with
  | zero =>
    intro b
    show some _ = some _
    simp only [lE, xprog, TM2.stepAux]
    rw [show (cst X 0 [] : ∀ k, List (XΓ M k)) (Sum.inr false) = List.replicate 0 () from rfl]
    simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.tail_nil]
    rw [show ([] : List Unit) = List.replicate 0 () from rfl, cst_upd_F]
  | succ f ih =>
    intro b
    rw [Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d z))
        (some (⟨some lE, (v, none, b), cst X (f + 1) []⟩ : XCfg M)) =
        some ⟨some lE, (v, none, true), cst X f []⟩ := by
      show some _ = some _
      simp only [lE, xprog, TM2.stepAux]
      rw [show (cst X (f + 1) [] : ∀ k, List (XΓ M k)) (Sum.inr false) =
        List.replicate (f + 1) () from rfl]
      simp only [List.replicate_succ, List.head?_cons, Option.isSome_some, Bool.cond_true,
        List.tail_cons]
      rw [cst_upd_F]
    rw [e, ih]

theorem stepFail (b : Bool) (x : TM2.Cfg M.Γ M.Λ M.σ) (hx : x.l ≠ none) :
    TM2.step (xprog M c d z) (emb b 0 x) =
      some ⟨some (er 0), (x.var, none, false), cst x.stk 0 []⟩ := by
  obtain ⟨l, v, S⟩ := x
  cases l with
  | none => exact absurd rfl hx
  | some l =>
    simp only [emb, Option.elim, TM2.step, xprog, TM2.stepAux]
    rw [show (cst S 0 [] : ∀ k, List (XΓ M k)) (Sum.inr false) = List.replicate 0 () from rfl]
    simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.tail_nil]
    rw [show ([] : List Unit) = List.replicate 0 () from rfl, cst_upd_F]

theorem eraseOne (v : M.σ) (i : ℕ) (hi : i < mK M) (X : ∀ k, List (M.Γ k)) :
    ∀ (l : List (M.Γ ((eK M).symm ⟨i, hi⟩))) (b : Bool),
      (flip bind (TM2.step (xprog M c d z)))^[l.length + 1]
          (some (⟨some (er ⟨i, by omega⟩), (v, none, b),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) l) 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨i + 1, by omega⟩), (v, none, false),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) []) 0 []⟩ := by
  intro l
  induction l with
  | nil =>
    intro b
    show some _ = some _
    simp only [er, xprog, hi, dite_eq_left, TM2.stepAux]
    rw [show (cst (Function.update X ((eK M).symm ⟨i, hi⟩) []) 0 [] : ∀ k, List (XΓ M k))
      (Sum.inl ((eK M).symm ⟨i, hi⟩)) = [] by simp [cst]]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_inl, Function.update_idem]
  | cons a l ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d z))
        (some (⟨some (er ⟨i, by omega⟩), (v, none, b),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) (a :: l)) 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨i, by omega⟩), (v, none, true),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) l) 0 []⟩ := by
      show some _ = some _
      simp only [er, xprog, hi, dite_eq_left, TM2.stepAux]
      rw [show (cst (Function.update X ((eK M).symm ⟨i, hi⟩) (a :: l)) 0 [] :
        ∀ k, List (XΓ M k)) (Sum.inl ((eK M).symm ⟨i, hi⟩)) = a :: l by simp [cst]]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
      rw [cst_upd_inl, Function.update_idem]
    rw [e, ih]

theorem eraseAll (v : M.σ) (B : ℕ) : ∀ (r i : ℕ) (hi : i + r = mK M) (X : ∀ k, List (M.Γ k))
    (b : Bool), (∀ k, (X k).length ≤ B) → (∀ k, ((eK M) k).val < i → X k = []) →
    ∃ n, n ≤ r * (B + 1) ∧ ∃ b',
      (flip bind (TM2.step (xprog M c d z)))^[n]
          (some (⟨some (er ⟨i, by omega⟩), (v, none, b), cst X 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨mK M, by omega⟩), (v, none, b'), cst (fun _ => []) 0 []⟩ := by
  intro r
  induction r with
  | zero =>
    intro i hi X b _ hX
    refine ⟨0, by omega, b, ?_⟩
    have hX' : X = fun _ => [] := by
      funext k; exact hX k (by have := ((eK M) k).isLt; omega)
    subst hX'
    simp only [Function.iterate_zero, id]
    congr 4
    simp only [Fin.mk.injEq]; omega
  | succ r ih =>
    intro i hi X b hB hX
    have hi' : i < mK M := by omega
    set k0 := (eK M).symm ⟨i, hi'⟩
    have hXe : X = Function.update X k0 (X k0) := (Function.update_eq_self _ _).symm
    have h1 := eraseOne c d z v i hi' X (X k0) b
    rw [← hXe] at h1
    obtain ⟨n, hn, b', h2⟩ := ih (i + 1) (by omega) (Function.update X k0 []) false
      (fun k => by
        by_cases h : k = k0
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hB k)
      (fun k hk => by
        by_cases h : k = k0
        · subst h; simp
        · rw [Function.update_of_ne h]
          apply hX k
          have : (eK M) k ≠ ⟨i, hi'⟩ := by
            intro e; apply h; simp only [k0, ← e, Equiv.symm_apply_apply]
          have : ((eK M) k).val ≠ i := fun e => this (Fin.ext e)
          omega)
    refine ⟨n + ((X k0).length + 1), ?_, b', ?_⟩
    · have := hB k0
      have : r * (B + 1) + (B + 1) = (r + 1) * (B + 1) := by ring
      omega
    · rw [Function.iterate_add_apply, h1]
      exact h2

theorem stepLast (v : Xσ M) :
    TM2.step (xprog M c d z)
        (⟨some (er ⟨mK M, by omega⟩), v, cst (fun _ => []) 0 []⟩ : XCfg M) =
      some ⟨none, (M.initialState, none, false),
        cst (Function.update (fun _ => []) M.k₁ [z]) 0 []⟩ := by
  simp only [er, TM2.step, xprog, lt_irrefl, dite_eq_right, not_false_eq_true, TM2.stepAux]
  rw [show (cst (fun _ => []) 0 [] : ∀ k, List (XΓ M k)) (Sum.inl M.k₁) = [] from rfl,
    cst_upd_inl]

/-! ### The initial and final configurations -/

theorem cst_nil : (cst (fun _ => []) 0 [] : ∀ k, List (XΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | _ | _ <;> rfl

theorem init_CM (a : List (M.Γ M.k₀)) :
    initList (CM M c d z) a =
      ⟨some lA, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₀ a) 0 []⟩ := by
  refine (initList_eq (CM M c d z) a).trans ?_
  show (⟨_, _, Function.update (fun _ => []) (Sum.inl M.k₀) a⟩ : XCfg M) = _
  rw [← cst_upd_inl, cst_nil]
  rfl

theorem halt_CM (o : List (M.Γ M.k₁)) :
    haltList (CM M c d z) o =
      ⟨none, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₁ o) 0 []⟩ := by
  refine (haltList_eq (CM M c d z) o).trans ?_
  show (⟨_, _, Function.update (fun _ => []) (Sum.inl M.k₁) o⟩ : XCfg M) = _
  rw [← cst_upd_inl, cst_nil]
  rfl

/-- The start of the clocked machine. -/
def startC (a : List (M.Γ M.k₀)) : XCfg M :=
  ⟨some lA, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₀ a) 0 []⟩

/-- A halted clocked machine. -/
def stopC (o : List (M.Γ M.k₁)) : XCfg M :=
  ⟨none, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₁ o) 0 []⟩

/-- Loading the fuel and restoring the input. -/
theorem run_load (a : List (M.Γ M.k₀)) :
    (flip bind (TM2.step (xprog M c d z)))^[(a.length + 1) + (a.length + 1)]
        (some (startC a)) =
      some (emb false (c * a.length)
        ⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ a⟩) := by
  rw [Function.iterate_add_apply]
  have h1 := loopA c d z M.initialState (fun _ => []) rfl a 0 [] none false
  rw [startC, h1]
  have h2 := loopB c d z M.initialState (fun _ => []) (0 + c * a.length) a.reverse [] none false
  simp only [List.length_reverse, List.append_nil, List.reverse_reverse] at h2
  have hX : Function.update (fun _ => []) M.k₀ [] = (fun _ => [] : ∀ k, List (M.Γ k)) := by
    simp
  rw [hX] at h2
  rw [List.append_nil, h2]
  simp [emb]

/-- Success: `M` halts within the fuel. -/
theorem run_ok (a : List (M.Γ M.k₀)) (o : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M a)) = some (haltList M o))
    (hs : s ≤ c * a.length) :
    (flip bind (TM2.step (xprog M c d z)))^[(c * a.length - s + 1) + (s +
        ((a.length + 1) + (a.length + 1)))] (some (startC a)) = some (stopC o) := by
  have h1 := run_load c d z a
  rw [initList_eq] at h
  obtain ⟨b', h2⟩ := runC c d z s _ _ false (c * a.length - s) h
  rw [show c * a.length - s + s = c * a.length by omega] at h2
  have h3 := loopE c d z M.initialState (Function.update (fun _ => []) M.k₁ o)
    (c * a.length - s) b'
  refine Gen.iter_trans _ (Gen.iter_trans _ h1 h2) ?_
  rw [haltList_eq]
  exact h3

/-- Failure: `M` is still running when the fuel runs out. -/
theorem run_fail (a : List (M.Γ M.k₀)) (x : TM2.Cfg M.Γ M.Λ M.σ) (B : ℕ)
    (h : (flip bind (TM2.step M.m))^[c * a.length] (some (initList M a)) = some x)
    (hx : x.l ≠ none) (hB : ∀ k, (x.stk k).length ≤ B) :
    ∃ n, n ≤ (a.length + 1) + (a.length + 1) + c * a.length + 1 + mK M * (B + 1) + 1 ∧
      (flip bind (TM2.step (xprog M c d z)))^[n] (some (startC a)) = some (stopC [z]) := by
  have h1 := run_load c d z a
  rw [initList_eq] at h
  obtain ⟨b', h2⟩ := runC c d z (c * a.length) _ _ false 0 h
  rw [Nat.zero_add] at h2
  have h3 : (flip bind (TM2.step (xprog M c d z)))^[1] (some (emb b' 0 x)) =
      some ⟨some (er 0), (x.var, none, false), cst x.stk 0 []⟩ := stepFail c d z b' x hx
  obtain ⟨n4, hn4, b4, h4⟩ := eraseAll c d z x.var B (mK M) 0 (by omega) x.stk false hB
    (fun k hk => absurd hk (by omega))
  have h5 : (flip bind (TM2.step (xprog M c d z)))^[1]
      (some (⟨some (er ⟨mK M, by omega⟩), (x.var, none, b4), cst (fun _ => []) 0 []⟩ : XCfg M)) =
      some (stopC [z]) := stepLast c d z _
  refine ⟨1 + (n4 + (1 + (c * a.length + ((a.length + 1) + (a.length + 1))))), by omega, ?_⟩
  exact Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ h1 h2) h3) h4) h5


/-! ### Packaging -/

theorem running_before {σ : Type} (f : σ → Option σ) (y w : σ) (s0 j : ℕ) (hj : j < s0)
    (h : (flip bind f)^[s0] (some y) = some w) :
    ∃ x, (flip bind f)^[j] (some y) = some x ∧ f x ≠ none := by
  obtain ⟨i, rfl⟩ : ∃ i, s0 = i + 1 + j := ⟨s0 - j - 1, by omega⟩
  rw [Function.iterate_add_apply] at h
  cases hx : (flip bind f)^[j] (some y) with
  | none => rw [hx, iterate_none] at h; exact absurd h (by simp)
  | some x =>
    refine ⟨x, rfl, fun hfx => ?_⟩
    rw [hx, Function.iterate_succ_apply] at h
    have e : flip bind f (some x) = none := hfx
    rw [e, iterate_none] at h
    exact absurd h (by simp)

theorem initList_stk_length (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm s).stk k).length ≤ s.length := by
  rw [initList_eq]
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [Function.update_of_ne h]

end PEqualNP.General.Kannan.Clk

namespace PEqualNP.General.Kannan

open Turing PEqualNP.Library PEqualNP.Library.Machines Clk

/-- A machine computing `f`, with a bound `B a` on the length of the run on each input. -/
structure PRun {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (B : α → ℕ) where
  tm : FinTM2
  ia : tm.Γ tm.k₀ ≃ αΓ
  oa : tm.Γ tm.k₁ ≃ βΓ
  run : ∀ a, ∃ n, n ≤ B a ∧ (flip bind (TM2.step tm.m))^[n]
    (some (initList tm ((ea a).map ia.invFun))) = some (haltList tm ((eb (f a)).map oa.invFun))

/-- A machine computing `g`, cut off after `c` steps per input symbol: some `f` is computed in
linear time and agrees with `g` wherever the machine halts within `c` steps per symbol. -/
theorem clocked {α αΓ : Type} [Inhabited αΓ] (ea : α → List αΓ) (g : α → Bool) (B : α → ℕ)
    (cm : PRun ea Computability.encodeBool g B) (c : ℕ) :
    ∃ (f : α → Bool) (K : ℕ),
      (∀ a, B a ≤ c * (ea a).length → f a = g a) ∧
      ComputableInTime ea Computability.encodeBool f (fun l => K * l + K) := by
  classical
  set M := cm.tm
  let d : M.Γ M.k₀ := cm.ia.invFun default
  let z : M.Γ M.k₁ := cm.oa.invFun false
  let P : α → Prop := fun a => ∃ n, n ≤ c * (ea a).length ∧
        (flip bind (TM2.step M.m))^[n]
            (some (initList M ((ea a).map cm.ia.invFun))) =
          some (haltList M ((Computability.encodeBool (g a)).map cm.oa.invFun))
  let f : α → Bool := fun a => if P a then g a else false
  let K : ℕ := c + 2 + mK M * (1 + maxPush M * c) + mK M + 4
  refine ⟨f, K, fun a ha => by
    obtain ⟨n, hn, hr⟩ := cm.run a
    simp only [f]; exact if_pos ⟨n, by omega, hr⟩, ?_⟩
  have key : ∀ a, ∃ n, n ≤ K * (ea a).length + K ∧
      (flip bind (TM2.step (xprog M c d z)))^[n]
          (some (startC ((ea a).map cm.ia.invFun))) =
        some (stopC ((Computability.encodeBool (f a)).map cm.oa.invFun)) := by
    intro a
    set l := (ea a).map cm.ia.invFun with hl
    have hll : l.length = (ea a).length := by simp [hl]
    by_cases hP : P a
    · obtain ⟨n, hn, hrun⟩ := hP
      have hf : f a = g a := by simp only [f, if_pos (show P a from ⟨n, hn, hrun⟩)]
      rw [hf]
      refine ⟨_, ?_, run_ok c d z l _ n hrun (by rw [hll]; exact hn)⟩
      rw [hll]
      have : K * (ea a).length ≥ (c + 2) * (ea a).length :=
        Nat.mul_le_mul_right _ (by omega)
      have : (c + 2) * (ea a).length = c * (ea a).length + 2 * (ea a).length := by ring
      omega
    · have hf : f a = false := by simp only [f, if_neg hP]
      rw [hf]
      obtain ⟨s0, -, hr0⟩ := cm.run a
      have hs0 : c * l.length < s0 := by
        by_contra hc
        exact hP ⟨s0, by rw [hll] at hc; omega, hr0⟩
      obtain ⟨x, hx, hxs⟩ := running_before (TM2.step M.m) _ _ s0 (c * l.length) hs0 hr0
      have hxl : x.l ≠ none := by
        intro h0
        apply hxs
        obtain ⟨l0, v0, S0⟩ := x
        simp only at h0
        subst h0
        rfl
      have hB : ∀ k, (x.stk k).length ≤ l.length + maxPush M * (c * l.length) := by
        intro k
        have := run_length M k _ _ _ hx
        exact this.trans (Nat.add_le_add_right (initList_stk_length _ _ _) _)
      obtain ⟨n, hn, hrun⟩ := run_fail c d z l x _ hx hxl hB
      refine ⟨n, ?_, hrun⟩
      rw [hll] at hn
      set L := (ea a).length
      set A := mK M * (1 + maxPush M * c) with hA
      have e1 : mK M * (L + maxPush M * (c * L) + 1) = A * L + mK M := by rw [hA]; ring
      have e2 : K * L = (c + 2) * L + A * L + (mK M + 4) * L := by
        simp only [K, A]; ring
      have e3 : (c + 2) * L = c * L + 2 * L := by ring
      have hK : mK M + 4 ≤ K := by simp only [K]; omega
      rw [e1] at hn
      have := Nat.zero_le ((mK M + 4) * L)
      linarith
  exact ⟨{
    tm := CM M c d z
    inputAlphabet := cm.ia
    outputAlphabet := cm.oa
    time := fun l => K * l + K
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), by
          have h1 : initList (CM M c d z) ((ea a).map cm.ia.invFun) =
              startC ((ea a).map cm.ia.invFun) := init_CM c d z _
          have h2 : haltList (CM M c d z)
              ((Computability.encodeBool (f a)).map cm.oa.invFun) =
              stopC ((Computability.encodeBool (f a)).map cm.oa.invFun) :=
            halt_CM c d z _
          rw [Option.map_some, h1, h2]
          exact (Classical.choose_spec (key a)).2⟩,
        by simpa using (Classical.choose_spec (key a)).1⟩ }, fun _ => le_rfl⟩

end PEqualNP.General.Kannan
