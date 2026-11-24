import PEqualNP.General.KannanMachineRun
import PEqualNP.General.KannanMachineReduce

/-!
# Cutting the data regions out of a witness, in linear time

The machine `zipM` reads a pair `(u, w)`. It pushes `u` on a stack `U` (so `U` holds
`u.reverse`, its last symbol on top), then for each symbol of `w` pops one symbol of `U` and
keeps the symbol of `w` when the popped symbol is `true`. It then writes the kept symbols and
what is left of `U`. Result: `zipF (u, w) = ((u.reverse.drop |w|).reverse, zipSel u.reverse w)`,
in at most `3 * (|u| + |w|) + 3` steps.
-/

namespace PEqualNP.General.Kannan.Zip

open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- Stacks: input, the mask, the kept symbols, output. -/
inductive ZK : Type
  | I
  | U
  | T
  | O
  deriving DecidableEq

instance : Fintype ZK :=
  Fintype.ofList [ZK.I, ZK.U, ZK.T, ZK.O] (fun x => by cases x <;> simp)

@[reducible] def ZΓ : ZK → Type
  | .I => Bool ⊕ Bool
  | .U => Bool
  | .T => Bool
  | .O => Bool ⊕ Bool

/-- Labels: split and select, write the kept symbols, write the rest of the mask. -/
inductive ZL : Type
  | s
  | t
  | u
  deriving DecidableEq

instance : Fintype ZL :=
  Fintype.ofList [ZL.s, ZL.t, ZL.u] (fun x => by cases x <;> simp)

abbrev Zσ : Type := Option (Bool ⊕ Bool) × Option Bool

def bitOf : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b
  | none => false

def isL : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

def zprog : ZL → TM2.Stmt ZΓ ZL Zσ
  | .s =>
    .pop ZK.I (fun s o => (o, s.2))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => isL s.1)
          (.push ZK.U (fun s => bitOf s.1) (.goto fun _ => .s))
          (.pop ZK.U (fun s o => (s.1, o))
            (.branch (fun s => s.2 == some true)
              (.push ZK.T (fun s => bitOf s.1) (.goto fun _ => .s))
              (.goto fun _ => .s))))
        (.goto fun _ => .t))
  | .t =>
    .pop ZK.T (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push ZK.O (fun s => Sum.inr (s.2.getD false)) (.goto fun _ => .t))
        (.goto fun _ => .u))
  | .u =>
    .pop ZK.U (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push ZK.O (fun s => Sum.inl (s.2.getD false)) (.goto fun _ => .u))
        (.load (fun _ => (none, none)) .halt))

def zipM : FinTM2 where
  K := ZK
  k₀ := ZK.I
  k₁ := ZK.O
  Γ := ZΓ
  Λ := ZL
  main := .s
  σ := Zσ
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := zprog

def zst (i : List (Bool ⊕ Bool)) (u t : List Bool) (o : List (Bool ⊕ Bool)) : ∀ k, List (ZΓ k)
  | .I => i
  | .U => u
  | .T => t
  | .O => o

theorem zst_I (i i' : List (Bool ⊕ Bool)) (u t : List Bool) (o : List (Bool ⊕ Bool)) :
    Function.update (zst i u t o) ZK.I i' = zst i' u t o := by
  funext k; cases k <;> simp [zst]

theorem zst_U (i : List (Bool ⊕ Bool)) (u u' t : List Bool) (o : List (Bool ⊕ Bool)) :
    Function.update (zst i u t o) ZK.U u' = zst i u' t o := by
  funext k; cases k <;> simp [zst]

theorem zst_T (i : List (Bool ⊕ Bool)) (u t t' : List Bool) (o : List (Bool ⊕ Bool)) :
    Function.update (zst i u t o) ZK.T t' = zst i u t' o := by
  funext k; cases k <;> simp [zst]

theorem zst_O (i : List (Bool ⊕ Bool)) (u t : List Bool) (o o' : List (Bool ⊕ Bool)) :
    Function.update (zst i u t o) ZK.O o' = zst i u t o' := by
  funext k; cases k <;> simp [zst]

abbrev ZCfg : Type := TM2.Cfg ZΓ ZL Zσ

abbrev zstep : Option ZCfg → Option ZCfg := flip bind (TM2.step zprog)

theorem loopL (t : List Bool) (o : List (Bool ⊕ Bool)) (rest : List (Bool ⊕ Bool)) :
    ∀ (u' U0 : List Bool) (v : Zσ),
      ∃ v', zstep^[u'.length] (some (⟨some .s, v, zst (u'.map Sum.inl ++ rest) U0 t o⟩ : ZCfg)) =
        some ⟨some .s, v', zst rest (u'.reverse ++ U0) t o⟩ := by
  intro u'
  induction u' with
  | nil => intro U0 v; exact ⟨v, by simp⟩
  | cons b u' ih =>
    intro U0 v
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zstep (some (⟨some .s, v, zst ((b :: u').map Sum.inl ++ rest) U0 t o⟩ : ZCfg)) =
        some ⟨some .s, (some (Sum.inl b), v.2), zst (u'.map Sum.inl ++ rest) (b :: U0) t o⟩ := by
      show some _ = some _
      simp only [zprog, TM2.stepAux, zst, List.map_cons, List.cons_append, List.head?_cons,
        Option.isSome_some, isL, bitOf, Bool.cond_true, List.tail_cons]
      rw [zst_I, show zst (List.map Sum.inl u' ++ rest) U0 t o ZK.U = U0 from rfl, zst_U]
    rw [e]
    obtain ⟨v', h⟩ := ih (b :: U0) (some (Sum.inl b), v.2)
    exact ⟨v', by rw [h]; simp⟩

theorem loopR (o : List (Bool ⊕ Bool)) :
    ∀ (w U0 t : List Bool) (v : Zσ),
      ∃ v', zstep^[w.length] (some (⟨some .s, v, zst (w.map Sum.inr) U0 t o⟩ : ZCfg)) =
        some ⟨some .s, v', zst [] (U0.drop w.length) ((zipSel U0 w).reverse ++ t) o⟩ := by
  intro w
  induction w with
  | nil => intro U0 t v; exact ⟨v, by simp [zipSel_nil_right]⟩
  | cons a w ih =>
    intro U0 t v
    rw [List.length_cons, Function.iterate_succ_apply]
    cases U0 with
    | nil =>
      have e : zstep (some (⟨some .s, v, zst ((a :: w).map Sum.inr) [] t o⟩ : ZCfg)) =
          some ⟨some .s, (some (Sum.inr a), none), zst (w.map Sum.inr) [] t o⟩ := by
        show some _ = some _
        simp only [zprog, TM2.stepAux, zst, List.map_cons, List.head?_cons,
          Option.isSome_some, isL, Bool.cond_true, Bool.cond_false, List.tail_cons,
          List.head?_nil, List.tail_nil]
        rw [zst_I, show zst (List.map Sum.inr w) [] t o ZK.U = [] from rfl, zst_U]
        rfl
      rw [e]
      obtain ⟨v', h⟩ := ih [] t (some (Sum.inr a), none)
      refine ⟨v', ?_⟩
      rw [h]
      simp [zipSel]
    | cons b U0 =>
      cases b with
      | true =>
        have e : zstep (some (⟨some .s, v, zst ((a :: w).map Sum.inr) (true :: U0) t o⟩ :
            ZCfg)) =
            some ⟨some .s, (some (Sum.inr a), some true), zst (w.map Sum.inr) U0 (a :: t) o⟩ := by
          show some _ = some _
          simp only [zprog, TM2.stepAux, zst, List.map_cons, List.head?_cons,
            Option.isSome_some, isL, Bool.cond_true, Bool.cond_false, List.tail_cons]
          rw [zst_I, show zst (List.map Sum.inr w) (true :: U0) t o ZK.U = true :: U0 from rfl,
            zst_U]
          simp only [List.head?_cons, List.tail_cons, beq_self_eq_true, Bool.cond_true, bitOf]
          rw [show zst (List.map Sum.inr w) U0 t o ZK.T = t from rfl, zst_T]
        rw [e]
        obtain ⟨v', h⟩ := ih U0 (a :: t) (some (Sum.inr a), some true)
        refine ⟨v', ?_⟩
        rw [h]
        simp [zipSel]
      | false =>
        have e : zstep (some (⟨some .s, v, zst ((a :: w).map Sum.inr) (false :: U0) t o⟩ :
            ZCfg)) =
            some ⟨some .s, (some (Sum.inr a), some false), zst (w.map Sum.inr) U0 t o⟩ := by
          show some _ = some _
          simp only [zprog, TM2.stepAux, zst, List.map_cons, List.head?_cons,
            Option.isSome_some, isL, Bool.cond_true, Bool.cond_false, List.tail_cons]
          rw [zst_I, show zst (List.map Sum.inr w) (false :: U0) t o ZK.U = false :: U0 from rfl,
            zst_U]
          simp
        rw [e]
        obtain ⟨v', h⟩ := ih U0 t (some (Sum.inr a), some false)
        refine ⟨v', ?_⟩
        rw [h]
        simp [zipSel]

theorem stepS_nil (U0 t : List Bool) (o : List (Bool ⊕ Bool)) (v : Zσ) :
    zstep (some (⟨some .s, v, zst [] U0 t o⟩ : ZCfg)) =
      some ⟨some .t, (none, v.2), zst [] U0 t o⟩ := by
  show some _ = some _
  simp only [zprog, TM2.stepAux, zst, List.head?_nil, Option.isSome_none, Bool.cond_false,
    List.tail_nil]
  rw [zst_I]

theorem loopT (U0 : List Bool) :
    ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (v : Zσ),
      ∃ v', zstep^[t.length + 1] (some (⟨some .t, v, zst [] U0 t o⟩ : ZCfg)) =
        some ⟨some .u, v', zst [] U0 [] ((t.map Sum.inr).reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil =>
    intro o v
    refine ⟨(none, none), ?_⟩
    show some _ = some _
    simp only [zprog, TM2.stepAux, zst, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.tail_nil]
    rw [zst_T]; rfl
  | cons a t ih =>
    intro o v
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zstep (some (⟨some .t, v, zst [] U0 (a :: t) o⟩ : ZCfg)) =
        some ⟨some .t, (none, some a), zst [] U0 t (Sum.inr a :: o)⟩ := by
      show some _ = some _
      simp only [zprog, TM2.stepAux, zst, List.head?_cons, Option.isSome_some, Bool.cond_true,
        List.tail_cons, Option.getD_some]
      rw [zst_T, show zst [] U0 t o ZK.O = o from rfl, zst_O]
    rw [e]
    obtain ⟨v', h⟩ := ih (Sum.inr a :: o) (none, some a)
    refine ⟨v', ?_⟩
    rw [h]
    simp

theorem loopU :
    ∀ (r : List Bool) (o : List (Bool ⊕ Bool)) (v : Zσ),
      zstep^[r.length + 1] (some (⟨some .u, v, zst [] r [] o⟩ : ZCfg)) =
        some ⟨none, (none, none), zst [] [] [] ((r.map Sum.inl).reverse ++ o)⟩ := by
  intro r
  induction r with
  | nil =>
    intro o v
    show some _ = some _
    simp only [zprog, TM2.stepAux, zst, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.tail_nil]
    rw [zst_U]; rfl
  | cons a r ih =>
    intro o v
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zstep (some (⟨some .u, v, zst [] (a :: r) [] o⟩ : ZCfg)) =
        some ⟨some .u, (none, some a), zst [] r [] (Sum.inl a :: o)⟩ := by
      show some _ = some _
      simp only [zprog, TM2.stepAux, zst, List.head?_cons, Option.isSome_some, Bool.cond_true,
        List.tail_cons, Option.getD_some]
      rw [zst_U, show zst [] r [] o ZK.O = o from rfl, zst_O]
    rw [e, ih]
    simp

/-- What the machine computes. -/
def zipF (p : List Bool × List Bool) : List Bool × List Bool :=
  ((p.1.reverse.drop p.2.length).reverse, zipSel p.1.reverse p.2)

theorem zip_run (u w : List Bool) :
    ∃ n, n ≤ 3 * (u.length + w.length) + 3 ∧
      zstep^[n] (some (initList zipM (encodePair (u, w)))) =
        some (haltList zipM (encodePair (zipF (u, w)))) := by
  have hi : initList zipM (encodePair (u, w)) =
      (⟨some .s, (none, none), zst (u.map Sum.inl ++ w.map Sum.inr) [] [] []⟩ : ZCfg) := by
    refine (initList_eq zipM _).trans ?_
    show (⟨_, _, _⟩ : ZCfg) = _
    congr 1
    funext k; cases k <;> rfl
  have hh : haltList zipM (encodePair (zipF (u, w))) =
      (⟨none, (none, none), zst [] [] [] (encodePair (zipF (u, w)))⟩ : ZCfg) := by
    refine (haltList_eq zipM _).trans ?_
    show (⟨_, _, _⟩ : ZCfg) = _
    congr 1
    funext k; cases k <;> rfl
  obtain ⟨v1, h1⟩ := loopL [] [] (w.map Sum.inr) u [] (none, none)
  obtain ⟨v2, h2⟩ := loopR [] w (u.reverse ++ []) [] v1
  have h3 := stepS_nil ((u.reverse ++ []).drop w.length)
    ((zipSel (u.reverse ++ []) w).reverse ++ []) [] v2
  obtain ⟨v4, h4⟩ := loopT ((u.reverse ++ []).drop w.length)
    ((zipSel (u.reverse ++ []) w).reverse ++ []) [] (none, v2.2)
  have h5 := loopU ((u.reverse ++ []).drop w.length)
    ((((zipSel (u.reverse ++ []) w).reverse ++ []).map Sum.inr).reverse ++ []) v4
  have h3' : zstep^[1] (some (⟨some .s, v2, zst [] ((u.reverse ++ []).drop w.length)
      ((zipSel (u.reverse ++ []) w).reverse ++ []) []⟩ : ZCfg)) = _ := h3
  have chain := Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ h1 h2)
    h3') h4) h5
  refine ⟨(((u.reverse ++ []).drop w.length).length + 1) +
    (((((zipSel (u.reverse ++ []) w).reverse ++ [])).length + 1) +
    (1 + (w.length + u.length))), ?_, ?_⟩
  · have a1 : ((u.reverse ++ []).drop w.length).length ≤ u.length := by simp
    have a2 : (zipSel (u.reverse ++ []) w).length ≤ w.length := by
      have : ∀ (a b : List Bool), (zipSel a b).length ≤ b.length := by
        intro a
        induction a with
        | nil => intro b; cases b <;> simp [zipSel]
        | cons x a ih =>
          intro b
          cases b with
          | nil => simp [zipSel]
          | cons y b =>
            have := ih b
            cases x <;> simp [zipSel] <;> omega
      exact this _ _
    simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero] at *
    omega
  · refine (congrArg (fun c => zstep^[_] (some c)) hi).trans
      (Eq.trans ?_ (congrArg some hh).symm)
    simp only [List.map_nil, List.append_nil] at chain ⊢
    rw [chain]
    simp [zipF, encodePair]
    rfl

end PEqualNP.General.Kannan.Zip

namespace PEqualNP.General.Kannan

open Turing PEqualNP.Library PEqualNP.Library.Machines Zip

/-- The cutting machine, with its run length. -/
noncomputable def zipRun :
    PRun encodePair encodePair zipF (fun p => 3 * (p.1.length + p.2.length) + 3) :=
  ⟨zipM, Equiv.refl _, Equiv.refl _, fun p => by
    obtain ⟨u, w⟩ := p
    obtain ⟨n, hn, h⟩ := zip_run u w
    refine ⟨n, hn, ?_⟩
    simp only [Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl]
    erw [List.map_id, List.map_id]
    exact h⟩

end PEqualNP.General.Kannan
