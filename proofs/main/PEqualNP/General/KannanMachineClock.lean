import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Machines.FirstGRun

/-!
# A clocked run: any machine, cut off after a linear number of steps

Given a machine `M` and a constant `c`, the machine `CM M c d dec enc` copies the input back and forth
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
abbrev XΛ : Type := M.Λ ⊕ ((Option Bool ⊕ Option Bool) ⊕ Fin (mK M + 1))

abbrev Xσ : Type := M.σ × Option (M.Γ M.k₀) × Bool

variable {M}

def lA : XΛ M := Sum.inr (Sum.inl (Sum.inl (some false)))
def lB : XΛ M := Sum.inr (Sum.inl (Sum.inl (some true)))
def lE : XΛ M := Sum.inr (Sum.inl (Sum.inl none))
def lEK : XΛ M := Sum.inr (Sum.inl (Sum.inr none))
def lFin : XΛ M := Sum.inr (Sum.inl (Sum.inr (some false)))
def lDr : XΛ M := Sum.inr (Sum.inl (Sum.inr (some true)))
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
noncomputable def xprog (c : ℕ) (d : M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool) (enc : Bool → M.Γ M.k₁) :
    XΛ M → TM2.Stmt (XΓ M) (XΛ M) (Xσ M)
  | Sum.inl l => .pop (Sum.inr false) (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (trC (M.m l)) (.goto fun _ => lEK))
  | Sum.inr (Sum.inl (Sum.inl (some false))) => .pop (Sum.inl M.k₀) (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push (Sum.inr true) (fun s => s.2.1.getD d) (pushF c (.goto fun _ => lA)))
        (.goto fun _ => lB))
  | Sum.inr (Sum.inl (Sum.inl (some true))) => .pop (Sum.inr true) (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push (Sum.inl M.k₀) (fun s => s.2.1.getD d) (.goto fun _ => lB))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr (Sum.inl (Sum.inl none)) => .pop (Sum.inr false) (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (.goto fun _ => lE) (.goto fun _ => er 0))
  | Sum.inr (Sum.inl (Sum.inr none)) => .pop (Sum.inl M.k₁) (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (.goto fun _ => lEK) (.goto fun _ => er 0))
  | Sum.inr (Sum.inl (Sum.inr (some false))) =>
      .pop (Sum.inl M.k₁)
        (fun s o => (s.1, (if (o.map dec).getD false then some d else none), s.2.2))
        (.goto fun _ => lDr)
  | Sum.inr (Sum.inl (Sum.inr (some true))) =>
      .pop (Sum.inl M.k₁) (fun s o => (s.1, s.2.1, o.isSome))
        (.branch (fun s => s.2.2) (.goto fun _ => lDr)
          (.push (Sum.inl M.k₁) (fun s => enc s.2.1.isSome)
            (.load (fun _ => (M.initialState, none, false)) .halt)))
  | Sum.inr (Sum.inr i) =>
      if h : i.val < mK M then
        if (eK M).symm ⟨i.val, h⟩ = M.k₁ then .goto fun _ => er ⟨i.val + 1, by omega⟩ else
        .pop (Sum.inl ((eK M).symm ⟨i.val, h⟩)) (fun s o => (s.1, s.2.1, o.isSome))
          (.branch (fun s => s.2.2) (.goto fun _ => er i) (.goto fun _ => er ⟨i.val + 1, by omega⟩))
      else
        .goto fun _ => lFin

/-- The clocked machine. -/
noncomputable def CM (c : ℕ) (d : M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool) (enc : Bool → M.Γ M.k₁) : FinTM2 :=
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
    m := xprog M c d dec enc }

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

variable (c : ℕ) (d : M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool) (enc : Bool → M.Γ M.k₁)

theorem stepC (b : Bool) (f : ℕ) (x y : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m x = some y) :
    TM2.step (xprog M c d dec enc) (emb b (f + 1) x) = some (emb true f y) := by
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
    ∃ b', (flip bind (TM2.step (xprog M c d dec enc)))^[j] (some (emb b (f + j) x)) =
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
      have e2 : flip bind (TM2.step (xprog M c d dec enc)) (some (emb b (f + (j + 1)) x)) =
          some (emb true (f + j) x') := by
        rw [show f + (j + 1) = (f + j) + 1 by omega]
        exact stepC c d dec enc b (f + j) x x' hx
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
      (flip bind (TM2.step (xprog M c d dec enc)))^[l.length + 1]
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
    have e : flip bind (TM2.step (xprog M c d dec enc))
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
      (flip bind (TM2.step (xprog M c d dec enc)))^[t.length + 1]
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
    have e : flip bind (TM2.step (xprog M c d dec enc))
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
      (flip bind (TM2.step (xprog M c d dec enc)))^[f + 1]
          (some (⟨some lE, (v, none, b), cst X f []⟩ : XCfg M)) =
        some ⟨some (er 0), (v, none, false), cst X 0 []⟩ := by
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
    have e : flip bind (TM2.step (xprog M c d dec enc))
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
    TM2.step (xprog M c d dec enc) (emb b 0 x) =
      some ⟨some lEK, (x.var, none, false), cst x.stk 0 []⟩ := by
  obtain ⟨l, v, S⟩ := x
  cases l with
  | none => exact absurd rfl hx
  | some l =>
    simp only [emb, Option.elim, TM2.step, xprog, TM2.stepAux]
    rw [show (cst S 0 [] : ∀ k, List (XΓ M k)) (Sum.inr false) = List.replicate 0 () from rfl]
    simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.tail_nil]
    rw [show ([] : List Unit) = List.replicate 0 () from rfl, cst_upd_F]

theorem loopEK (v : M.σ) (X : ∀ k, List (M.Γ k)) :
    ∀ (l : List (M.Γ M.k₁)) (b : Bool),
      (flip bind (TM2.step (xprog M c d dec enc)))^[l.length + 1]
          (some (⟨some lEK, (v, none, b), cst (Function.update X M.k₁ l) 0 []⟩ : XCfg M)) =
        some ⟨some (er 0), (v, none, false), cst (Function.update X M.k₁ []) 0 []⟩ := by
  intro l
  induction l with
  | nil =>
    intro b
    show some _ = some _
    simp only [lEK, xprog, TM2.stepAux]
    rw [show (cst (Function.update X M.k₁ []) 0 [] : ∀ k, List (XΓ M k)) (Sum.inl M.k₁) = [] by
      simp [cst]]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_inl, Function.update_idem]
  | cons a l ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d dec enc))
        (some (⟨some lEK, (v, none, b), cst (Function.update X M.k₁ (a :: l)) 0 []⟩ : XCfg M)) =
        some ⟨some lEK, (v, none, true), cst (Function.update X M.k₁ l) 0 []⟩ := by
      show some _ = some _
      simp only [lEK, xprog, TM2.stepAux]
      rw [show (cst (Function.update X M.k₁ (a :: l)) 0 [] : ∀ k, List (XΓ M k)) (Sum.inl M.k₁) =
        a :: l by simp [cst]]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
      rw [cst_upd_inl, Function.update_idem]
    rw [e, ih]

theorem eraseOne (v : M.σ) (i : ℕ) (hi : i < mK M) (hk : (eK M).symm ⟨i, hi⟩ ≠ M.k₁)
    (X : ∀ k, List (M.Γ k)) :
    ∀ (l : List (M.Γ ((eK M).symm ⟨i, hi⟩))) (b : Bool),
      (flip bind (TM2.step (xprog M c d dec enc)))^[l.length + 1]
          (some (⟨some (er ⟨i, by omega⟩), (v, none, b),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) l) 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨i + 1, by omega⟩), (v, none, false),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) []) 0 []⟩ := by
  intro l
  induction l with
  | nil =>
    intro b
    show some _ = some _
    simp only [er, xprog, hi, dite_eq_left, hk, if_false, TM2.stepAux]
    rw [show (cst (Function.update X ((eK M).symm ⟨i, hi⟩) []) 0 [] : ∀ k, List (XΓ M k))
      (Sum.inl ((eK M).symm ⟨i, hi⟩)) = [] by simp [cst]]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_inl, Function.update_idem]
  | cons a l ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d dec enc))
        (some (⟨some (er ⟨i, by omega⟩), (v, none, b),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) (a :: l)) 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨i, by omega⟩), (v, none, true),
            cst (Function.update X ((eK M).symm ⟨i, hi⟩) l) 0 []⟩ := by
      show some _ = some _
      simp only [er, xprog, hi, dite_eq_left, hk, if_false, TM2.stepAux]
      rw [show (cst (Function.update X ((eK M).symm ⟨i, hi⟩) (a :: l)) 0 [] :
        ∀ k, List (XΓ M k)) (Sum.inl ((eK M).symm ⟨i, hi⟩)) = a :: l by simp [cst]]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
      rw [cst_upd_inl, Function.update_idem]
    rw [e, ih]

theorem skipOne (v : Xσ M) (i : ℕ) (hi : i < mK M) (hk : (eK M).symm ⟨i, hi⟩ = M.k₁)
    (S : ∀ k, List (XΓ M k)) :
    (flip bind (TM2.step (xprog M c d dec enc)))^[1]
        (some (⟨some (er ⟨i, by omega⟩), v, S⟩ : XCfg M)) =
      some ⟨some (er ⟨i + 1, by omega⟩), v, S⟩ := by
  show some _ = some _
  simp only [er, xprog, hi, dite_eq_left, hk, if_true, TM2.stepAux]

theorem eraseAll (v : M.σ) (B : ℕ) : ∀ (r i : ℕ) (hi : i + r = mK M) (X : ∀ k, List (M.Γ k))
    (b : Bool), (∀ k, (X k).length ≤ B) → (∀ k, ((eK M) k).val < i → k ≠ M.k₁ → X k = []) →
    ∃ n, n ≤ r * (B + 1) ∧ ∃ b',
      (flip bind (TM2.step (xprog M c d dec enc)))^[n]
          (some (⟨some (er ⟨i, by omega⟩), (v, none, b), cst X 0 []⟩ : XCfg M)) =
        some ⟨some (er ⟨mK M, by omega⟩), (v, none, b'),
          cst (Function.update (fun _ => []) M.k₁ (X M.k₁)) 0 []⟩ := by
  intro r
  induction r with
  | zero =>
    intro i hi X b _ hX
    refine ⟨0, by omega, b, ?_⟩
    have hX' : X = Function.update (fun _ => []) M.k₁ (X M.k₁) := by
      funext k
      by_cases h : k = M.k₁
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hX k (by have := ((eK M) k).isLt; omega) h
    rw [← hX']
    simp only [Function.iterate_zero, id]
    congr 4
    simp only [Fin.mk.injEq]; omega
  | succ r ih =>
    intro i hi X b hB hX
    have hi' : i < mK M := by omega
    set k0 := (eK M).symm ⟨i, hi'⟩ with hk0
    have hne : ∀ k, (eK M) k = ⟨i, hi'⟩ → k = k0 := by
      intro k e; simp only [k0, ← e, Equiv.symm_apply_apply]
    by_cases hk : k0 = M.k₁
    · have h1 := skipOne c d dec enc (v, none, b) i hi' hk (cst X 0 [])
      obtain ⟨n, hn, b', h2⟩ := ih (i + 1) (by omega) X b hB
        (fun k hk' hk1 => by
          by_cases h : ((eK M) k).val = i
          · exact absurd (hk ▸ hne k (Fin.ext h)) hk1
          · exact hX k (by omega) hk1)
      refine ⟨n + 1, ?_, b', ?_⟩
      · have : r * (B + 1) + (B + 1) = (r + 1) * (B + 1) := by ring
        omega
      · rw [Function.iterate_add_apply, h1]
        exact h2
    · have hXe : X = Function.update X k0 (X k0) := (Function.update_eq_self _ _).symm
      have h1 := eraseOne c d dec enc v i hi' hk X (X k0) b
      rw [← hXe] at h1
      obtain ⟨n, hn, b', h2⟩ := ih (i + 1) (by omega) (Function.update X k0 []) false
        (fun k => by
          by_cases h : k = k0
          · subst h; simp
          · rw [Function.update_of_ne h]; exact hB k)
        (fun k hk' hk1 => by
          by_cases h : k = k0
          · subst h; simp
          · rw [Function.update_of_ne h]
            apply hX k _ hk1
            have : ((eK M) k).val ≠ i := fun e => h (hne k (Fin.ext e))
            omega)
      have hk1 : Function.update X k0 [] M.k₁ = X M.k₁ := by
        rw [Function.update_of_ne (Ne.symm hk)]
      rw [hk1] at h2
      refine ⟨n + ((X k0).length + 1), ?_, b', ?_⟩
      · have := hB k0
        have : r * (B + 1) + (B + 1) = (r + 1) * (B + 1) := by ring
        omega
      · rw [Function.iterate_add_apply, h1]
        exact h2

/-- The output bit read off the output stack. -/
def outBit (l : List (M.Γ M.k₁)) : Bool := (l.head?.map dec).getD false

theorem loopDr (v : M.σ) :
    ∀ (l : List (M.Γ M.k₁)) (t : Option (M.Γ M.k₀)) (b : Bool),
      (flip bind (TM2.step (xprog M c d dec enc)))^[l.length + 1]
          (some (⟨some lDr, (v, t, b), cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ :
            XCfg M)) =
        some ⟨none, (M.initialState, none, false),
          cst (Function.update (fun _ => []) M.k₁ [enc t.isSome]) 0 []⟩ := by
  intro l
  induction l with
  | nil =>
    intro t b
    show some _ = some _
    simp only [lDr, xprog, TM2.stepAux]
    rw [show (cst (Function.update (fun _ => []) M.k₁ []) 0 [] : ∀ k, List (XΓ M k))
      (Sum.inl M.k₁) = [] by simp [cst]]
    simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
    rw [cst_upd_inl, Function.update_idem, cst_upd_inl, Function.update_idem]
    simp [cst]
  | cons a l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (xprog M c d dec enc))
        (some (⟨some lDr, (v, t, b), cst (Function.update (fun _ => []) M.k₁ (a :: l)) 0 []⟩ :
          XCfg M)) =
        some ⟨some lDr, (v, t, true), cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ := by
      show some _ = some _
      simp only [lDr, xprog, TM2.stepAux]
      rw [show (cst (Function.update (fun _ => []) M.k₁ (a :: l)) 0 [] : ∀ k, List (XΓ M k))
        (Sum.inl M.k₁) = a :: l by simp [cst]]
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
      rw [cst_upd_inl, Function.update_idem]
    rw [e, ih]

theorem finish (v : M.σ) (t : Option (M.Γ M.k₀)) (b : Bool) (l : List (M.Γ M.k₁)) :
    (flip bind (TM2.step (xprog M c d dec enc)))^[(l.tail.length + 1) + 1 + 1]
        (some (⟨some (er ⟨mK M, by omega⟩), (v, t, b),
          cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ : XCfg M)) =
      some ⟨none, (M.initialState, none, false),
        cst (Function.update (fun _ => []) M.k₁ [enc (outBit dec l)]) 0 []⟩ := by
  have h1 : (flip bind (TM2.step (xprog M c d dec enc)))^[1]
      (some (⟨some (er ⟨mK M, by omega⟩), (v, t, b),
        cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ : XCfg M)) =
      some ⟨some lFin, (v, t, b), cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ := by
    show some _ = some _
    simp only [er, xprog, lt_irrefl, dite_eq_right, not_false_eq_true, TM2.stepAux]
  have h2 : (flip bind (TM2.step (xprog M c d dec enc)))^[1]
      (some (⟨some lFin, (v, t, b), cst (Function.update (fun _ => []) M.k₁ l) 0 []⟩ : XCfg M)) =
      some ⟨some lDr, (v, (if outBit dec l then some d else none), b),
        cst (Function.update (fun _ => []) M.k₁ l.tail) 0 []⟩ := by
    show some _ = some _
    simp only [lFin, xprog, TM2.stepAux]
    rw [show (cst (Function.update (fun _ => []) M.k₁ l) 0 [] : ∀ k, List (XΓ M k))
      (Sum.inl M.k₁) = l by simp [cst]]
    rw [cst_upd_inl, Function.update_idem]
    rfl
  have h3 := loopDr c d dec enc v l.tail (if outBit dec l then some d else none) b
  have e : (if outBit dec l then some d else none).isSome = outBit dec l := by
    cases outBit dec l <;> rfl
  rw [e] at h3
  rw [Function.iterate_add_apply, Function.iterate_add_apply, h1, h2, h3]

/-- From the first erasing stage to the end. -/
theorem tail_run (v : M.σ) (b : Bool) (X : ∀ k, List (M.Γ k)) (B : ℕ)
    (hB : ∀ k, (X k).length ≤ B) :
    ∃ n, n ≤ mK M * (B + 1) + (B + 3) ∧
      (flip bind (TM2.step (xprog M c d dec enc)))^[n]
          (some (⟨some (er 0), (v, none, b), cst X 0 []⟩ : XCfg M)) =
        some ⟨none, (M.initialState, none, false),
          cst (Function.update (fun _ => []) M.k₁ [enc (outBit dec (X M.k₁))]) 0 []⟩ := by
  obtain ⟨n, hn, b', h1⟩ := eraseAll c d dec enc v B (mK M) 0 (by omega) X b hB
    (fun k hk => absurd hk (by omega))
  have h2 := finish c d dec enc v none b' (X M.k₁)
  refine ⟨((X M.k₁).tail.length + 1) + 1 + 1 + n, ?_, ?_⟩
  · have := hB M.k₁
    have : (X M.k₁).tail.length ≤ B := by simp; omega
    omega
  · rw [Function.iterate_add_apply]
    have e0 : (er 0 : XΛ M) = er ⟨0, by omega⟩ := rfl
    rw [e0, h1, h2]

/-! ### The initial and final configurations -/

theorem cst_nil : (cst (fun _ => []) 0 [] : ∀ k, List (XΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | _ | _ <;> rfl

theorem init_CM (a : List (M.Γ M.k₀)) :
    initList (CM M c d dec enc) a =
      ⟨some lA, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₀ a) 0 []⟩ := by
  refine (initList_eq (CM M c d dec enc) a).trans ?_
  show (⟨_, _, Function.update (fun _ => []) (Sum.inl M.k₀) a⟩ : XCfg M) = _
  rw [← cst_upd_inl, cst_nil]
  rfl

theorem halt_CM (o : List (M.Γ M.k₁)) :
    haltList (CM M c d dec enc) o =
      ⟨none, (M.initialState, none, false), cst (Function.update (fun _ => []) M.k₁ o) 0 []⟩ := by
  refine (haltList_eq (CM M c d dec enc) o).trans ?_
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
    (flip bind (TM2.step (xprog M c d dec enc)))^[(a.length + 1) + (a.length + 1)]
        (some (startC a)) =
      some (emb false (c * a.length)
        ⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ a⟩) := by
  rw [Function.iterate_add_apply]
  have h1 := loopA c d dec enc M.initialState (fun _ => []) rfl a 0 [] none false
  rw [startC, h1]
  have h2 := loopB c d dec enc M.initialState (fun _ => []) (0 + c * a.length) a.reverse [] none false
  simp only [List.length_reverse, List.append_nil, List.reverse_reverse] at h2
  have hX : Function.update (fun _ => []) M.k₀ [] = (fun _ => [] : ∀ k, List (M.Γ k)) := by
    simp
  rw [hX] at h2
  rw [List.append_nil, h2]
  simp [emb]

/-- Success: `M` halts within the fuel. -/
theorem run_ok (a : List (M.Γ M.k₀)) (x : TM2.Cfg M.Γ M.Λ M.σ) (s B : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M a)) = some x) (hx : x.l = none)
    (hs : s ≤ c * a.length) (hB : ∀ k, (x.stk k).length ≤ B) :
    ∃ n, n ≤ (a.length + 1) + (a.length + 1) + s + (c * a.length - s + 1) +
        (mK M * (B + 1) + (B + 3)) ∧
      (flip bind (TM2.step (xprog M c d dec enc)))^[n] (some (startC a)) =
        some (stopC [enc (outBit dec (x.stk M.k₁))]) := by
  have h1 := run_load c d dec enc a
  rw [initList_eq] at h
  obtain ⟨b', h2⟩ := runC c d dec enc s _ _ false (c * a.length - s) h
  rw [show c * a.length - s + s = c * a.length by omega] at h2
  obtain ⟨l, v, S⟩ := x
  simp only at hx
  subst hx
  have h3 := loopE c d dec enc v S (c * a.length - s) b'
  obtain ⟨n4, hn4, h4⟩ := tail_run c d dec enc v false S B hB
  refine ⟨n4 + ((c * a.length - s + 1) + (s + ((a.length + 1) + (a.length + 1)))), by omega, ?_⟩
  exact Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ h1 h2) h3) h4

/-- Failure: `M` is still running when the fuel runs out. -/
theorem run_fail (a : List (M.Γ M.k₀)) (x : TM2.Cfg M.Γ M.Λ M.σ) (B : ℕ)
    (h : (flip bind (TM2.step M.m))^[c * a.length] (some (initList M a)) = some x)
    (hx : x.l ≠ none) (hB : ∀ k, (x.stk k).length ≤ B) :
    ∃ n, n ≤ (a.length + 1) + (a.length + 1) + c * a.length + 1 + (B + 1) +
        (mK M * (B + 1) + (B + 3)) ∧
      (flip bind (TM2.step (xprog M c d dec enc)))^[n] (some (startC a)) =
        some (stopC [enc false]) := by
  have h1 := run_load c d dec enc a
  rw [initList_eq] at h
  obtain ⟨b', h2⟩ := runC c d dec enc (c * a.length) _ _ false 0 h
  rw [Nat.zero_add] at h2
  have h3 : (flip bind (TM2.step (xprog M c d dec enc)))^[1] (some (emb b' 0 x)) =
      some ⟨some lEK, (x.var, none, false), cst x.stk 0 []⟩ := stepFail c d dec enc b' x hx
  have h4 := loopEK c d dec enc x.var x.stk (x.stk M.k₁) false
  rw [Function.update_eq_self] at h4
  obtain ⟨n5, hn5, h5⟩ := tail_run c d dec enc x.var false (Function.update x.stk M.k₁ []) B
    (fun k => by
      by_cases hk : k = M.k₁
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hB k)
  have e : outBit dec (Function.update x.stk M.k₁ [] M.k₁) = false := by simp [outBit]
  rw [e] at h5
  refine ⟨n5 + ((x.stk M.k₁).length + 1 + (1 + (c * a.length + ((a.length + 1) +
    (a.length + 1))))), ?_, ?_⟩
  · have := hB M.k₁; omega
  · exact Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ h1 h2) h3) h4) h5

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

theorem none_before {σ : Type} (f : σ → Option σ) (y : σ) : ∀ j,
    (flip bind f)^[j] (some y) = none → ∃ j', j' < j ∧ ∃ x,
      (flip bind f)^[j'] (some y) = some x ∧ f x = none := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by simp)
  | succ j ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h
    cases hj : (flip bind f)^[j] (some y) with
    | none =>
      obtain ⟨j', hj', x, hx, hfx⟩ := ih hj
      exact ⟨j', by omega, x, hx, hfx⟩
    | some x =>
      rw [hj] at h
      exact ⟨j, by omega, x, hj, h⟩

theorem halted_unique (tm : FinTM2) (y : TM2.Cfg tm.Γ tm.Λ tm.σ) (j j' : ℕ)
    (x x' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : (flip bind (TM2.step tm.m))^[j] (some y) = some x) (hx : x.l = none)
    (h' : (flip bind (TM2.step tm.m))^[j'] (some y) = some x') (hx' : x'.l = none) : x = x' := by
  have key : ∀ (j j' : ℕ) (x x' : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[j] (some y) = some x → x.l = none →
      (flip bind (TM2.step tm.m))^[j'] (some y) = some x' → j < j' → False := by
    intro j j' x x' h hx h' hlt
    obtain ⟨i, rfl⟩ : ∃ i, j' = i + 1 + j := ⟨j' - j - 1, by omega⟩
    rw [Function.iterate_add_apply, h, Function.iterate_succ_apply] at h'
    have e : flip bind (TM2.step tm.m) (some x) = none := by
      obtain ⟨l, v, S⟩ := x
      simp only at hx
      subst hx
      rfl
    rw [e, iterate_none] at h'
    exact absurd h' (by simp)
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · exact (key j j' x x' h hx h' hlt).elim
  · rw [h] at h'; exact Option.some.inj h'
  · exact (key j' j x' x h' hx' h hlt).elim

theorem stepNone_l (tm : FinTM2) (x : TM2.Cfg tm.Γ tm.Λ tm.σ) (h : TM2.step tm.m x = none) :
    x.l = none := by
  obtain ⟨l, v, S⟩ := x
  cases l with
  | none => rfl
  | some l => simp [TM2.step] at h

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

/-- A machine cut off after `c` steps per input symbol: some `f` is computed in linear time and
agrees with `g` on every input of `G`, where the machine halts with the answer `g a` within `c`
steps per input symbol. Nothing is asked of the machine outside `G`. -/
theorem clocked {α αΓ : Type} [Inhabited αΓ] (ea : α → List αΓ) (tm : FinTM2)
    (ia : tm.Γ tm.k₀ ≃ αΓ) (oa : tm.Γ tm.k₁ ≃ Bool) (g : α → Bool) (G : α → Prop) (c : ℕ)
    (hG : ∀ a, G a → ∃ n, n ≤ c * (ea a).length ∧
      (flip bind (TM2.step tm.m))^[n] (some (initList tm ((ea a).map ia.invFun))) =
        some (haltList tm [oa.invFun (g a)])) :
    ∃ (f : α → Bool) (K : ℕ), (∀ a, G a → f a = g a) ∧
      ComputableInTime ea Computability.encodeBool f (fun l => K * l + K) := by
  classical
  let M := tm
  let d : M.Γ M.k₀ := ia.invFun default
  let dec : M.Γ M.k₁ → Bool := oa
  let enc : Bool → M.Γ M.k₁ := oa.invFun
  let ini : α → TM2.Cfg M.Γ M.Λ M.σ := fun a => initList M ((ea a).map ia.invFun)
  let Hd : α → Prop := fun a => ∃ j, j ≤ c * (ea a).length ∧ ∃ x : TM2.Cfg M.Γ M.Λ M.σ,
    (flip bind (TM2.step M.m))^[j] (some (ini a)) = some x ∧ x.l = none
  let xOf : ∀ a, Hd a → TM2.Cfg M.Γ M.Λ M.σ := fun a h =>
    Classical.choose (Classical.choose_spec h).2
  have xOf_spec : ∀ a (h : Hd a), (flip bind (TM2.step M.m))^[Classical.choose h]
      (some (ini a)) = some (xOf a h) ∧ (xOf a h).l = none :=
    fun a h => Classical.choose_spec (Classical.choose_spec h).2
  have xOf_le : ∀ a (h : Hd a), Classical.choose h ≤ c * (ea a).length :=
    fun a h => (Classical.choose_spec h).1
  let f : α → Bool := fun a => if h : Hd a then outBit dec ((xOf a h).stk M.k₁) else false
  let K : ℕ := c + 2 + (mK M + 2) * (1 + maxPush M * c) + mK M + 7
  refine ⟨f, K, fun a ha => ?_, ?_⟩
  · obtain ⟨n, hn, hr⟩ := hG a ha
    have hH : Hd a := ⟨n, hn, _, hr, by rw [haltList_eq]⟩
    simp only [f, dif_pos hH]
    have := halted_unique M (ini a) _ _ _ _ (xOf_spec a hH).1 (xOf_spec a hH).2 hr
      (by rw [haltList_eq])
    rw [this, haltList_eq]
    show (Option.map (⇑oa) (Function.update (fun _ => []) tm.k₁ [oa.symm (g a)] tm.k₁).head?).getD
      false = g a
    simp
  have key : ∀ a, ∃ n, n ≤ K * (ea a).length + K ∧
      (flip bind (TM2.step (xprog M c d dec enc)))^[n]
          (some (startC ((ea a).map ia.invFun))) =
        some (stopC ((Computability.encodeBool (f a)).map oa.invFun)) := by
    intro a
    set l := (ea a).map ia.invFun with hl
    obtain ⟨L, hL⟩ : ∃ L, (ea a).length = L := ⟨_, rfl⟩
    have hll : l.length = L := by simp [hl, hL]
    have hBnd : ∀ j (x : TM2.Cfg M.Γ M.Λ M.σ), j ≤ c * L →
        (flip bind (TM2.step M.m))^[j] (some (ini a)) = some x →
        ∀ k, (x.stk k).length ≤ L + maxPush M * c * L := by
      intro j x hj hx k
      have h1 := run_length M k _ _ _ hx
      have h2 := initList_stk_length M l k
      have h3 : maxPush M * j ≤ maxPush M * c * L := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hj
      simp only [ini] at h1
      rw [← hl] at h1
      rw [hll] at h2
      omega
    have hKL : (c + 2) * L + (L + maxPush M * c * L) * (mK M + 2) + mK M + 7 ≤ K * L + K := by
      have e1 : K * L = (c + 2 + (mK M + 2) * (1 + maxPush M * c)) * L + (mK M + 7) * L := by
        simp only [K]; ring
      have e2 : (c + 2) * L + (L + maxPush M * c * L) * (mK M + 2) =
          (c + 2 + (mK M + 2) * (1 + maxPush M * c)) * L := by ring
      have e3 : mK M + 7 ≤ K := by simp only [K]; omega
      rw [e2]
      have := Nat.zero_le ((mK M + 7) * L)
      linarith
    by_cases hH : Hd a
    · have hf : f a = outBit dec ((xOf a hH).stk M.k₁) := by simp only [f, dif_pos hH]
      obtain ⟨hr, hx⟩ := xOf_spec a hH
      have hj : Classical.choose hH ≤ c * L :=
        calc _ ≤ c * (ea a).length := xOf_le a hH
          _ = c * L := by rw [hL]
      obtain ⟨n, hn, hrun⟩ := run_ok c d dec enc l (xOf a hH) _ (L + maxPush M * c * L) hr hx
        (by rw [hll]; exact hj) (hBnd _ _ hj hr)
      refine ⟨n, ?_, ?_⟩
      · rw [hll] at hn
        rw [hL]
        have e0 : Classical.choose hH + (c * L - Classical.choose hH + 1) = c * L + 1 := by omega
        have e1 : (L + maxPush M * c * L) * (mK M + 2) =
            mK M * (L + maxPush M * c * L) + 2 * (L + maxPush M * c * L) := by ring
        have e2 : mK M * (L + maxPush M * c * L + 1) = mK M * (L + maxPush M * c * L) + mK M := by
          ring
        have e3 : (c + 2) * L = c * L + 2 * L := by ring
        have := Nat.zero_le (maxPush M * c * L)
        linarith
      · rw [hrun, hf]; rfl
    · have hf : f a = false := by simp only [f, dif_neg hH]
      have hrun0 : ∃ x : TM2.Cfg M.Γ M.Λ M.σ,
          (flip bind (TM2.step M.m))^[c * (ea a).length] (some (ini a)) = some x ∧ x.l ≠ none := by
        cases hc : (flip bind (TM2.step M.m))^[c * (ea a).length] (some (ini a)) with
        | none =>
          obtain ⟨j', hj', x, hx, hfx⟩ := none_before _ _ _ hc
          exact absurd ⟨j', by omega, x, hx, stepNone_l M x hfx⟩ hH
        | some x =>
          refine ⟨x, rfl, fun hx => hH ⟨c * (ea a).length, le_rfl, x, hc, hx⟩⟩
      obtain ⟨x, hx, hxl⟩ := hrun0
      have hcl : c * l.length = c * (ea a).length := by rw [hll, hL]
      have hcl' : c * (ea a).length ≤ c * L := by rw [hL]
      obtain ⟨n, hn, hrun⟩ := run_fail c d dec enc l x (L + maxPush M * c * L) (by rw [hcl]; exact hx)
        hxl (hBnd _ _ hcl' hx)
      refine ⟨n, ?_, ?_⟩
      · rw [hll] at hn
        rw [hL]
        have e1 : (L + maxPush M * c * L) * (mK M + 2) =
            mK M * (L + maxPush M * c * L) + 2 * (L + maxPush M * c * L) := by ring
        have e2 : mK M * (L + maxPush M * c * L + 1) = mK M * (L + maxPush M * c * L) + mK M := by
          ring
        have e3 : (c + 2) * L = c * L + 2 * L := by ring
        have := Nat.zero_le (maxPush M * c * L)
        linarith
      · rw [hrun, hf]; rfl
  exact ⟨{
    tm := CM M c d dec enc
    inputAlphabet := ia
    outputAlphabet := oa
    time := fun l => K * l + K
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), by
          have h1 : initList (CM M c d dec enc) ((ea a).map ia.invFun) =
              startC ((ea a).map ia.invFun) := init_CM c d dec enc _
          have h2 : haltList (CM M c d dec enc)
              ((Computability.encodeBool (f a)).map oa.invFun) =
              stopC ((Computability.encodeBool (f a)).map oa.invFun) :=
            halt_CM c d dec enc _
          rw [Option.map_some, h1, h2]
          exact (Classical.choose_spec (key a)).2⟩,
        by simpa using (Classical.choose_spec (key a)).1⟩ }, fun _ => le_rfl⟩

end PEqualNP.General.Kannan
