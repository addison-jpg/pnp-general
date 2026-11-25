import PEqualNP.General.KannanMachineRun

/-!
# Cutting the data regions out of the witness, in linear time

The machine `cutM` reads a pair `(u, w)` with `u = 1 ^ D ++ 0 :: x` and `|w| = 3 s`, `D ≤ s`.
It writes the pair `(x, w[0, D) ++ w[s, s + D) ++ w[2 s, 2 s + D))`. It only has to work on such
inputs (`CutGood`), in at most `4 * (|u| + |w|) + 20` steps.

Stacks: input `I`, output `O`, and seven stacks of bits: `A` (`D` marks), `A2` (its copy),
`X` (`x` reversed), `W` (`w` reversed), `C` (`|w|` marks), `S` (`s`, then `s - D` marks), `S2`
(its copy). Labels:
* `sp`: split the input;
* `dv`: three marks of `C` make one mark of `S`;
* `sb`: `S` loses `D` marks while `A` moves to `A2`;
* `k1`/`k2`, `k3`/`k4`: the three blocks from the end of `w`: skip `s - D` symbols, keep `D`
  symbols (written to `O`), the counters moving back and forth;
* `ox`: `x` goes to `O`; `eA`, `eS`: the two counters left over are erased.
-/

namespace PEqualNP.General.Kannan.Cut

open Turing PEqualNP.Library PEqualNP.Library.Machines

inductive CK : Type
  | I | O | A | A2 | X | W | C | S | S2
  deriving DecidableEq

instance : Fintype CK :=
  Fintype.ofList [CK.I, CK.O, CK.A, CK.A2, CK.X, CK.W, CK.C, CK.S, CK.S2]
    (fun x => by cases x <;> simp)

@[reducible] def CΓ : CK → Type
  | .I => Bool ⊕ Bool
  | .O => Bool ⊕ Bool
  | _ => Bool

inductive CL : Type
  | sp | dv | sb | k1 | k2 | k3 | k4 | ox | eA | eS
  deriving DecidableEq

instance : Fintype CL :=
  Fintype.ofList [CL.sp, CL.dv, CL.sb, CL.k1, CL.k2, CL.k3, CL.k4, CL.ox, CL.eA, CL.eS]
    (fun x => by cases x <;> simp)

/-- Internal state: symbol read from the input, bit popped, mode (after the `0` of `u`), flag
(second pass through `k1`/`k2`). -/
abbrev Cσ : Type := Option (Bool ⊕ Bool) × Option Bool × Bool × Bool

def bitOf : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b
  | none => false

def isL : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

def cprog : CL → TM2.Stmt CΓ CL Cσ
  | .sp =>
    .pop CK.I (fun s o => (o, s.2))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => isL s.1)
          (.branch (fun s => s.2.2.1)
            (.push CK.X (fun s => bitOf s.1) (.goto fun _ => .sp))
            (.branch (fun s => bitOf s.1)
              (.push CK.A (fun _ => true) (.goto fun _ => .sp))
              (.load (fun s => (s.1, s.2.1, true, s.2.2.2)) (.goto fun _ => .sp))))
          (.push CK.W (fun s => bitOf s.1) (.push CK.C (fun _ => true) (.goto fun _ => .sp))))
        (.goto fun _ => .dv))
  | .dv =>
    .pop CK.C (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.pop CK.C (fun s _ => s) (.pop CK.C (fun s _ => s)
          (.push CK.S (fun _ => true) (.goto fun _ => .dv))))
        (.goto fun _ => .sb))
  | .sb =>
    .pop CK.A (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.A2 (fun _ => true) (.pop CK.S (fun s _ => s) (.goto fun _ => .sb)))
        (.goto fun _ => .k1))
  | .k1 =>
    .pop CK.S (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.S2 (fun _ => true) (.pop CK.W (fun s _ => s) (.goto fun _ => .k1)))
        (.goto fun _ => .k2))
  | .k2 =>
    .pop CK.A2 (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.A (fun _ => true) (.pop CK.W (fun s o => (s.1, o, s.2.2))
          (.push CK.O (fun s => Sum.inr (s.2.1.getD false)) (.goto fun _ => .k2))))
        (.branch (fun s => s.2.2.2)
          (.goto fun _ => .ox)
          (.load (fun s => (s.1, s.2.1, s.2.2.1, true)) (.goto fun _ => .k3))))
  | .k3 =>
    .pop CK.S2 (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.S (fun _ => true) (.pop CK.W (fun s _ => s) (.goto fun _ => .k3)))
        (.goto fun _ => .k4))
  | .k4 =>
    .pop CK.A (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.A2 (fun _ => true) (.pop CK.W (fun s o => (s.1, o, s.2.2))
          (.push CK.O (fun s => Sum.inr (s.2.1.getD false)) (.goto fun _ => .k4))))
        (.goto fun _ => .k1))
  | .ox =>
    .pop CK.X (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push CK.O (fun s => Sum.inl (s.2.1.getD false)) (.goto fun _ => .ox))
        (.goto fun _ => .eA))
  | .eA =>
    .pop CK.A (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome) (.goto fun _ => .eA) (.goto fun _ => .eS))
  | .eS =>
    .pop CK.S2 (fun s o => (s.1, o, s.2.2))
      (.branch (fun s => s.2.1.isSome) (.goto fun _ => .eS)
        (.load (fun _ => (none, none, false, false)) .halt))

def cutM : FinTM2 where
  K := CK
  k₀ := CK.I
  k₁ := CK.O
  Γ := CΓ
  Λ := CL
  main := .sp
  σ := Cσ
  initialState := (none, none, false, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := cprog

/-- The stacks. -/
def cs (i : List (Bool ⊕ Bool)) (a a2 x w c s s2 : List Bool) (o : List (Bool ⊕ Bool)) :
    ∀ k, List (CΓ k)
  | .I => i
  | .O => o
  | .A => a
  | .A2 => a2
  | .X => x
  | .W => w
  | .C => c
  | .S => s
  | .S2 => s2

section upd
variable (i : List (Bool ⊕ Bool)) (a a2 x w c s s2 : List Bool) (o : List (Bool ⊕ Bool))

@[simp] theorem cs_I : cs i a a2 x w c s s2 o CK.I = i := rfl
@[simp] theorem cs_O : cs i a a2 x w c s s2 o CK.O = o := rfl
@[simp] theorem cs_A : cs i a a2 x w c s s2 o CK.A = a := rfl
@[simp] theorem cs_A2 : cs i a a2 x w c s s2 o CK.A2 = a2 := rfl
@[simp] theorem cs_X : cs i a a2 x w c s s2 o CK.X = x := rfl
@[simp] theorem cs_W : cs i a a2 x w c s s2 o CK.W = w := rfl
@[simp] theorem cs_C : cs i a a2 x w c s s2 o CK.C = c := rfl
@[simp] theorem cs_S : cs i a a2 x w c s s2 o CK.S = s := rfl
@[simp] theorem cs_S2 : cs i a a2 x w c s s2 o CK.S2 = s2 := rfl

@[simp] theorem up_I (l : List (Bool ⊕ Bool)) :
    Function.update (cs i a a2 x w c s s2 o) CK.I l = cs l a a2 x w c s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_O (l : List (Bool ⊕ Bool)) :
    Function.update (cs i a a2 x w c s s2 o) CK.O l = cs i a a2 x w c s s2 l := by
  funext k; cases k <;> rfl
@[simp] theorem up_A (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.A l = cs i l a2 x w c s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_A2 (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.A2 l = cs i a l x w c s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_X (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.X l = cs i a a2 l w c s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_W (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.W l = cs i a a2 x l c s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_C (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.C l = cs i a a2 x w l s s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_S (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.S l = cs i a a2 x w c l s2 o := by
  funext k; cases k <;> rfl
@[simp] theorem up_S2 (l : List Bool) :
    Function.update (cs i a a2 x w c s s2 o) CK.S2 l = cs i a a2 x w c s l o := by
  funext k; cases k <;> rfl

end upd

abbrev CCfg : Type := TM2.Cfg CΓ CL Cσ

abbrev cstep : Option CCfg → Option CCfg := flip bind (TM2.step cprog)

/-- `n` true marks. -/
abbrev mk (n : ℕ) : List Bool := List.replicate n true

/-! ### Split -/

theorem spA (rest : List (Bool ⊕ Bool)) (a2 x w c s s2 : List Bool) (o : List (Bool ⊕ Bool))
    (p : Option Bool) (fl : Bool) :
    ∀ (D : ℕ) (a : List Bool) (q : Option (Bool ⊕ Bool)),
      ∃ q', cstep^[D] (some (⟨some .sp, (q, p, false, fl),
          cs ((mk D).map Sum.inl ++ rest) a a2 x w c s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (q', p, false, fl), cs rest (mk D ++ a) a2 x w c s s2 o⟩ := by
  intro D
  induction D with
  | zero => intro a q; exact ⟨q, by simp⟩
  | succ D ih =>
    intro a q
    rw [Function.iterate_succ_apply]
    have e : cstep (some (⟨some .sp, (q, p, false, fl),
        cs ((mk (D + 1)).map Sum.inl ++ rest) a a2 x w c s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (some (Sum.inl true), p, false, fl),
          cs ((mk D).map Sum.inl ++ rest) (true :: a) a2 x w c s s2 o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, isL, bitOf, List.replicate_succ]
    rw [e]
    obtain ⟨q', h⟩ := ih (true :: a) (some (Sum.inl true))
    refine ⟨q', ?_⟩
    rw [h]
    simp [List.replicate_succ']

theorem spF (rest : List (Bool ⊕ Bool)) (a a2 x w c s s2 : List Bool) (o : List (Bool ⊕ Bool))
    (q : Option (Bool ⊕ Bool)) (p : Option Bool) (fl : Bool) :
    cstep (some (⟨some .sp, (q, p, false, fl),
        cs (Sum.inl false :: rest) a a2 x w c s s2 o⟩ : CCfg)) =
      some ⟨some .sp, (some (Sum.inl false), p, true, fl), cs rest a a2 x w c s s2 o⟩ := by
  show some _ = some _
  simp [cprog, TM2.stepAux, isL, bitOf]

theorem spX (rest : List (Bool ⊕ Bool)) (a a2 w c s s2 : List Bool) (o : List (Bool ⊕ Bool))
    (p : Option Bool) (fl : Bool) :
    ∀ (y X0 : List Bool) (q : Option (Bool ⊕ Bool)),
      ∃ q', cstep^[y.length] (some (⟨some .sp, (q, p, true, fl),
          cs (y.map Sum.inl ++ rest) a a2 X0 w c s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (q', p, true, fl), cs rest a a2 (y.reverse ++ X0) w c s s2 o⟩ := by
  intro y
  induction y with
  | nil => intro X0 q; exact ⟨q, by simp⟩
  | cons b y ih =>
    intro X0 q
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : cstep (some (⟨some .sp, (q, p, true, fl),
        cs ((b :: y).map Sum.inl ++ rest) a a2 X0 w c s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (some (Sum.inl b), p, true, fl),
          cs (y.map Sum.inl ++ rest) a a2 (b :: X0) w c s s2 o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, isL, bitOf]
    rw [e]
    obtain ⟨q', h⟩ := ih (b :: X0) (some (Sum.inl b))
    exact ⟨q', by rw [h]; simp⟩

theorem spW (a a2 x s s2 : List Bool) (o : List (Bool ⊕ Bool)) (p : Option Bool) (md fl : Bool) :
    ∀ (y W0 C0 : List Bool) (q : Option (Bool ⊕ Bool)),
      ∃ q', cstep^[y.length] (some (⟨some .sp, (q, p, md, fl),
          cs (y.map Sum.inr) a a2 x W0 C0 s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (q', p, md, fl), cs [] a a2 x (y.reverse ++ W0) (mk y.length ++ C0) s s2 o⟩ := by
  intro y
  induction y with
  | nil => intro W0 C0 q; exact ⟨q, by simp⟩
  | cons b y ih =>
    intro W0 C0 q
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : cstep (some (⟨some .sp, (q, p, md, fl),
        cs ((b :: y).map Sum.inr) a a2 x W0 C0 s s2 o⟩ : CCfg)) =
        some ⟨some .sp, (some (Sum.inr b), p, md, fl),
          cs (y.map Sum.inr) a a2 x (b :: W0) (true :: C0) s s2 o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, isL, bitOf]
    rw [e]
    obtain ⟨q', h⟩ := ih (b :: W0) (true :: C0) (some (Sum.inr b))
    refine ⟨q', ?_⟩
    rw [h]
    simp [List.replicate_succ']

theorem spEnd (a a2 x w c s s2 : List Bool) (o : List (Bool ⊕ Bool)) (v : Cσ) :
    cstep (some (⟨some .sp, v, cs [] a a2 x w c s s2 o⟩ : CCfg)) =
      some ⟨some .dv, (none, v.2), cs [] a a2 x w c s s2 o⟩ := by
  show some _ = some _
  simp [cprog, TM2.stepAux]

/-! ### Division by three, subtraction -/

theorem dvL (a a2 x w s2 : List Bool) (o : List (Bool ⊕ Bool)) :
    ∀ (q : ℕ) (S0 : List Bool) (v : Cσ),
      ∃ v', cstep^[q + 1] (some (⟨some .dv, v, cs [] a a2 x w (mk (3 * q)) S0 s2 o⟩ : CCfg)) =
        some ⟨some .sb, v', cs [] a a2 x w [] (mk q ++ S0) s2 o⟩ ∧ v'.2.2 = v.2.2 := by
  intro q
  induction q with
  | zero =>
    intro S0 v
    refine ⟨(v.1, none, v.2.2), ?_, rfl⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | succ q ih =>
    intro S0 v
    rw [Function.iterate_succ_apply]
    have e : cstep (some (⟨some .dv, v, cs [] a a2 x w (mk (3 * (q + 1))) S0 s2 o⟩ : CCfg)) =
        some ⟨some .dv, (v.1, some true, v.2.2), cs [] a a2 x w (mk (3 * q)) (true :: S0) s2 o⟩ := by
      show some _ = some _
      rw [show 3 * (q + 1) = 3 * q + 1 + 1 + 1 by ring]
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [e]
    obtain ⟨v', h, hv⟩ := ih (true :: S0) (v.1, some true, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

theorem sbL (x w c s2 : List Bool) (o : List (Bool ⊕ Bool)) (e : ℕ) :
    ∀ (D : ℕ) (A20 : List Bool) (v : Cσ),
      ∃ v', cstep^[D + 1] (some (⟨some .sb, v, cs [] (mk D) A20 x w c (mk (D + e)) s2 o⟩ : CCfg)) =
        some ⟨some .k1, v', cs [] [] (mk D ++ A20) x w c (mk e) s2 o⟩ ∧ v'.2.2 = v.2.2 := by
  intro D
  induction D with
  | zero =>
    intro A20 v
    refine ⟨(v.1, none, v.2.2), ?_, rfl⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | succ D ih =>
    intro A20 v
    rw [Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .sb, v, cs [] (mk (D + 1)) A20 x w c (mk (D + 1 + e)) s2 o⟩ :
        CCfg)) =
        some ⟨some .sb, (v.1, some true, v.2.2), cs [] (mk D) (true :: A20) x w c (mk (D + e)) s2 o⟩ := by
      show some _ = some _
      rw [show D + 1 + e = D + e + 1 by ring]
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    obtain ⟨v', h, hv⟩ := ih (true :: A20) (v.1, some true, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

/-! ### The blocks -/

/-- Skip: `S` to `S2`, popping `W`. -/
theorem k1L (a a2 x c : List Bool) (o : List (Bool ⊕ Bool)) :
    ∀ (y W0 S20 : List Bool) (v : Cσ),
      ∃ v', cstep^[y.length + 1] (some (⟨some .k1, v, cs [] a a2 x (y ++ W0) c (mk y.length) S20 o⟩ :
          CCfg)) =
        some ⟨some .k2, v', cs [] a a2 x W0 c [] (mk y.length ++ S20) o⟩ ∧ v'.2.2 = v.2.2 := by
  intro y
  induction y with
  | nil =>
    intro W0 S20 v
    refine ⟨(v.1, none, v.2.2), ?_, rfl⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | cons b y ih =>
    intro W0 S20 v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .k1, v, cs [] a a2 x (b :: y ++ W0) c (mk (y.length + 1)) S20 o⟩ :
        CCfg)) =
        some ⟨some .k1, (v.1, some true, v.2.2), cs [] a a2 x (y ++ W0) c (mk y.length) (true :: S20) o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    obtain ⟨v', h, hv⟩ := ih W0 (true :: S20) (v.1, some true, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

/-- Keep: `A2` to `A`, popping `W` onto `O`. The loop ends at `k2`'s exit. -/
theorem k2L (a x c s : List Bool) (S20 : List Bool) :
    ∀ (y W0 : List Bool) (o : List (Bool ⊕ Bool)) (v : Cσ),
      ∃ v', cstep^[y.length] (some (⟨some .k2, v, cs [] a (mk y.length) x (y ++ W0) c s S20 o⟩ :
          CCfg)) =
        some ⟨some .k2, v', cs [] (mk y.length ++ a) [] x W0 c s S20 ((y.map Sum.inr).reverse ++ o)⟩ ∧
          v'.2.2 = v.2.2 := by
  intro y
  induction y generalizing a with
  | nil => intro W0 o v; exact ⟨v, by simp, rfl⟩
  | cons b y ih =>
    intro W0 o v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .k2, v, cs [] a (mk (y.length + 1)) x (b :: y ++ W0) c s S20 o⟩ :
        CCfg)) =
        some ⟨some .k2, (v.1, some b, v.2.2), cs [] (true :: a) (mk y.length) x (y ++ W0) c s S20
          (Sum.inr b :: o)⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    obtain ⟨v', h, hv⟩ := ih (true :: a) W0 (Sum.inr b :: o) (v.1, some b, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

theorem k2Exit0 (a x w c s s2 : List Bool) (o : List (Bool ⊕ Bool)) (q : Option (Bool ⊕ Bool))
    (p : Option Bool) (md : Bool) :
    cstep (some (⟨some .k2, (q, p, md, false), cs [] a [] x w c s s2 o⟩ : CCfg)) =
      some ⟨some .k3, (q, none, md, true), cs [] a [] x w c s s2 o⟩ := by
  show some _ = some _
  simp [cprog, TM2.stepAux]

theorem k2Exit1 (a x w c s s2 : List Bool) (o : List (Bool ⊕ Bool)) (q : Option (Bool ⊕ Bool))
    (p : Option Bool) (md : Bool) :
    cstep (some (⟨some .k2, (q, p, md, true), cs [] a [] x w c s s2 o⟩ : CCfg)) =
      some ⟨some .ox, (q, none, md, true), cs [] a [] x w c s s2 o⟩ := by
  show some _ = some _
  simp [cprog, TM2.stepAux]

/-- Skip: `S2` to `S`, popping `W`. -/
theorem k3L (a a2 x c : List Bool) (o : List (Bool ⊕ Bool)) :
    ∀ (y W0 S0 : List Bool) (v : Cσ),
      ∃ v', cstep^[y.length + 1] (some (⟨some .k3, v, cs [] a a2 x (y ++ W0) c S0 (mk y.length) o⟩ :
          CCfg)) =
        some ⟨some .k4, v', cs [] a a2 x W0 c (mk y.length ++ S0) [] o⟩ ∧ v'.2.2 = v.2.2 := by
  intro y
  induction y with
  | nil =>
    intro W0 S0 v
    refine ⟨(v.1, none, v.2.2), ?_, rfl⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | cons b y ih =>
    intro W0 S0 v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .k3, v, cs [] a a2 x (b :: y ++ W0) c S0 (mk (y.length + 1)) o⟩ :
        CCfg)) =
        some ⟨some .k3, (v.1, some true, v.2.2), cs [] a a2 x (y ++ W0) c (true :: S0) (mk y.length) o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    obtain ⟨v', h, hv⟩ := ih W0 (true :: S0) (v.1, some true, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

/-- Keep: `A` to `A2`, popping `W` onto `O`, then back to `k1`. -/
theorem k4L (x c s S20 : List Bool) :
    ∀ (y a2 W0 : List Bool) (o : List (Bool ⊕ Bool)) (v : Cσ),
      ∃ v', cstep^[y.length + 1] (some (⟨some .k4, v, cs [] (mk y.length) a2 x (y ++ W0) c s S20 o⟩ :
          CCfg)) =
        some ⟨some .k1, v', cs [] [] (mk y.length ++ a2) x W0 c s S20
          ((y.map Sum.inr).reverse ++ o)⟩ ∧ v'.2.2 = v.2.2 := by
  intro y
  induction y with
  | nil =>
    intro a2 W0 o v
    refine ⟨(v.1, none, v.2.2), ?_, rfl⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | cons b y ih =>
    intro a2 W0 o v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .k4, v, cs [] (mk (y.length + 1)) a2 x (b :: y ++ W0) c s S20 o⟩ :
        CCfg)) =
        some ⟨some .k4, (v.1, some b, v.2.2), cs [] (mk y.length) (true :: a2) x (y ++ W0) c s S20
          (Sum.inr b :: o)⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    obtain ⟨v', h, hv⟩ := ih (true :: a2) W0 (Sum.inr b :: o) (v.1, some b, v.2.2)
    refine ⟨v', ?_, hv⟩
    rw [h]
    simp [List.replicate_succ']

/-! ### Output and erasing -/

theorem oxL (a s2 : List Bool) :
    ∀ (y : List Bool) (o : List (Bool ⊕ Bool)) (v : Cσ),
      ∃ v', cstep^[y.length + 1] (some (⟨some .ox, v, cs [] a [] y [] [] [] s2 o⟩ : CCfg)) =
        some ⟨some .eA, v', cs [] a [] [] [] [] [] s2 ((y.map Sum.inl).reverse ++ o)⟩ := by
  intro y
  induction y with
  | nil =>
    intro o v
    refine ⟨(v.1, none, v.2.2), ?_⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | cons b y ih =>
    intro o v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .ox, v, cs [] a [] (b :: y) [] [] [] s2 o⟩ : CCfg)) =
        some ⟨some .ox, (v.1, some b, v.2.2), cs [] a [] y [] [] [] s2 (Sum.inl b :: o)⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux]
    rw [h1]
    obtain ⟨v', h⟩ := ih (Sum.inl b :: o) (v.1, some b, v.2.2)
    exact ⟨v', by rw [h]; simp⟩

theorem eAL (s2 : List Bool) (o : List (Bool ⊕ Bool)) :
    ∀ (D : ℕ) (v : Cσ),
      ∃ v', cstep^[D + 1] (some (⟨some .eA, v, cs [] (mk D) [] [] [] [] [] s2 o⟩ : CCfg)) =
        some ⟨some .eS, v', cs [] [] [] [] [] [] [] s2 o⟩ := by
  intro D
  induction D with
  | zero =>
    intro v
    refine ⟨(v.1, none, v.2.2), ?_⟩
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | succ D ih =>
    intro v
    rw [Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .eA, v, cs [] (mk (D + 1)) [] [] [] [] [] s2 o⟩ : CCfg)) =
        some ⟨some .eA, (v.1, some true, v.2.2), cs [] (mk D) [] [] [] [] [] s2 o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    exact ih _

theorem eSL (o : List (Bool ⊕ Bool)) :
    ∀ (e : ℕ) (v : Cσ),
      cstep^[e + 1] (some (⟨some .eS, v, cs [] [] [] [] [] [] [] (mk e) o⟩ : CCfg)) =
        some ⟨none, (none, none, false, false), cs [] [] [] [] [] [] [] [] o⟩ := by
  intro e
  induction e with
  | zero =>
    intro v
    show some _ = some _
    simp [cprog, TM2.stepAux]
  | succ e ih =>
    intro v
    rw [Function.iterate_succ_apply]
    have h1 : cstep (some (⟨some .eS, v, cs [] [] [] [] [] [] [] (mk (e + 1)) o⟩ : CCfg)) =
        some ⟨some .eS, (v.1, some true, v.2.2), cs [] [] [] [] [] [] [] (mk e) o⟩ := by
      show some _ = some _
      simp [cprog, TM2.stepAux, List.replicate_succ]
    rw [h1]
    exact ih _

/-! ### The run on a good input -/

theorem cut_run (D s : ℕ) (x y1 y2 y3 : List Bool) (h1 : y1.length = s) (h2 : y2.length = s)
    (h3 : y3.length = s) (hD : D ≤ s) :
    ∃ n, n ≤ 4 * ((mk D ++ false :: x).length + (y1 ++ y2 ++ y3).length) + 20 ∧
      cstep^[n] (some (⟨some .sp, (none, none, false, false),
          cs (encodePair (mk D ++ false :: x, y1 ++ y2 ++ y3)) [] [] [] [] [] [] [] []⟩ : CCfg)) =
        some ⟨none, (none, none, false, false),
          cs [] [] [] [] [] [] [] [] (encodePair (x, y1.take D ++ y2.take D ++ y3.take D))⟩ := by
  set e := s - D with he
  have hse : s = D + e := by omega
  have henc : encodePair (mk D ++ false :: x, y1 ++ y2 ++ y3) =
      (mk D).map Sum.inl ++ (Sum.inl false :: (x.map Sum.inl ++ (y1 ++ y2 ++ y3).map Sum.inr)) := by
    simp [encodePair]
  rw [henc]
  -- split
  obtain ⟨q1, r1⟩ := spA (Sum.inl false :: (x.map Sum.inl ++ (y1 ++ y2 ++ y3).map Sum.inr))
    [] [] [] [] [] [] [] none false D [] none
  have r2 := spF (x.map Sum.inl ++ (y1 ++ y2 ++ y3).map Sum.inr) (mk D ++ []) [] [] [] [] [] [] []
    q1 none false
  obtain ⟨q3, r3⟩ := spX ((y1 ++ y2 ++ y3).map Sum.inr) (mk D ++ []) [] [] [] [] [] [] none false
    x [] (some (Sum.inl false))
  obtain ⟨q4, r4⟩ := spW (mk D ++ []) [] (x.reverse ++ []) [] [] [] none true false
    (y1 ++ y2 ++ y3) [] [] q3
  have r5 := spEnd (mk D ++ []) [] (x.reverse ++ []) ((y1 ++ y2 ++ y3).reverse ++ [])
    (mk (y1 ++ y2 ++ y3).length ++ []) [] [] [] (q4, none, true, false)
  have hlen : (y1 ++ y2 ++ y3).length = 3 * s := by simp; omega
  simp only [List.append_nil, hlen] at r1 r2 r3 r4 r5
  -- divide, subtract
  obtain ⟨v6, r6, hv6⟩ := dvL (mk D) [] x.reverse (y1 ++ y2 ++ y3).reverse [] [] s [] (none, none, true, false)
  simp only [List.append_nil] at r6
  obtain ⟨v7, r7, hv7⟩ := sbL x.reverse (y1 ++ y2 ++ y3).reverse [] [] [] e D [] v6
  rw [← hse] at r7
  simp only [List.append_nil] at r7
  -- the witness, reversed, block by block
  set a3 := (y3.drop D).reverse
  set b3 := (y3.take D).reverse
  set a2' := (y2.drop D).reverse
  set b2 := (y2.take D).reverse
  set a1 := (y1.drop D).reverse
  set b1 := (y1.take D).reverse
  have hW : (y1 ++ y2 ++ y3).reverse = a3 ++ (b3 ++ (a2' ++ (b2 ++ (a1 ++ b1)))) := by
    have e1 : ∀ y : List Bool, y.reverse = (y.drop D).reverse ++ (y.take D).reverse :=
      fun y => by rw [← List.reverse_append, List.take_append_drop]
    simp only [List.reverse_append, List.append_assoc]
    rw [e1 y3, e1 y2, e1 y1]
    simp only [List.append_assoc]
    rfl
  have l3d : a3.length = e := by simp [a3]; omega
  have l3t : b3.length = D := by simp [b3]; omega
  have l2d : a2'.length = e := by simp [a2']; omega
  have l2t : b2.length = D := by simp [b2]; omega
  have l1d : a1.length = e := by simp [a1]; omega
  have l1t : b1.length = D := by simp [b1]; omega
  rw [hW] at r4 r5 r6 r7
  have hv7' : v7.2.2 = (true, false) := by rw [hv7, hv6]
  -- block three
  obtain ⟨v8, r8, hv8⟩ := k1L [] (mk D) x.reverse [] [] a3 (b3 ++ (a2' ++ (b2 ++ (a1 ++ b1)))) [] v7
  rw [l3d] at r8
  simp only [List.append_nil] at r8
  obtain ⟨v9, r9, hv9⟩ := k2L [] x.reverse [] [] (mk e) b3 (a2' ++ (b2 ++ (a1 ++ b1))) [] v8
  rw [l3t] at r9
  simp only [List.append_nil] at r9
  have hv9' : v9.2.2 = (true, false) := by rw [hv9, hv8, hv7']
  obtain ⟨q9, p9, md9, fl9⟩ := v9
  simp only [Prod.mk.injEq] at hv9'
  obtain ⟨rfl, rfl⟩ := hv9'
  have r10 := k2Exit0 (mk D) x.reverse (a2' ++ (b2 ++ (a1 ++ b1))) [] [] (mk e)
    ((b3.map Sum.inr).reverse) q9 p9 true
  -- block two
  obtain ⟨v11, r11, hv11⟩ := k3L (mk D) [] x.reverse [] ((b3.map Sum.inr).reverse) a2'
    (b2 ++ (a1 ++ b1)) [] (q9, none, true, true)
  rw [l2d] at r11
  simp only [List.append_nil] at r11
  obtain ⟨v12, r12, hv12⟩ := k4L x.reverse [] (mk e) [] b2 [] (a1 ++ b1)
    ((b3.map Sum.inr).reverse) v11
  rw [l2t] at r12
  simp only [List.append_nil] at r12
  -- block one
  obtain ⟨v13, r13, hv13⟩ := k1L [] (mk D) x.reverse []
    ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse) a1 b1 [] v12
  rw [l1d] at r13
  simp only [List.append_nil] at r13
  obtain ⟨v14, r14, hv14⟩ := k2L [] x.reverse [] [] (mk e) b1 []
    ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse) v13
  rw [l1t] at r14
  simp only [List.append_nil] at r14
  have hv14' : v14.2.2 = (true, true) := by rw [hv14, hv13, hv12, hv11]
  obtain ⟨q14, p14, md14, fl14⟩ := v14
  simp only [Prod.mk.injEq] at hv14'
  obtain ⟨rfl, rfl⟩ := hv14'
  have r15 := k2Exit1 (mk D) x.reverse [] [] [] (mk e)
    ((b1.map Sum.inr).reverse ++ ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse))
    q14 p14 true
  -- output and erase
  obtain ⟨v16, r16⟩ := oxL (mk D) (mk e) x.reverse
    ((b1.map Sum.inr).reverse ++ ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse))
    (q14, none, true, true)
  obtain ⟨v17, r17⟩ := eAL (mk e) ((x.reverse.map Sum.inl).reverse ++
    ((b1.map Sum.inr).reverse ++ ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse))) D v16
  have r18 := eSL ((x.reverse.map Sum.inl).reverse ++
    ((b1.map Sum.inr).reverse ++ ((b2.map Sum.inr).reverse ++ (b3.map Sum.inr).reverse))) e v17
  have r2' : cstep^[1] _ = _ := r2
  have r5' : cstep^[1] _ = _ := r5
  have r10' : cstep^[1] _ = _ := r10
  have r15' : cstep^[1] _ = _ := r15
  have chain := Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _
    (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _
    (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _
    (Gen.iter_trans _ (Gen.iter_trans _ (Gen.iter_trans _ r1 r2') r3) r4) r5') r6) r7) r8) r9)
    r10') r11) r12) r13) r14) r15') r16) r17) r18
  refine ⟨_, ?_, chain.trans ?_⟩
  · simp
    omega
  · simp [encodePair, b1, b2, b3, List.map_reverse]

end PEqualNP.General.Kannan.Cut
