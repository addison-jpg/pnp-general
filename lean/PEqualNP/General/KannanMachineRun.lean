import PEqualNP.General.KannanMachineClock
import PEqualNP.Library.Machines.FirstPoly

/-!
# Machines with a run-length bound on every input

`PRun ea eb f B`: a machine computing `f` whose run on `a` takes at most `B a` steps. Such
machines compose (`PRun.comp`), every machine of `TM2ComputableInTime` is one, and acting on
the first component of a pair is one (`PRun.first`).
-/

namespace PEqualNP.General.Kannan

open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- Composition, with the run lengths added up. -/
noncomputable def PRun.comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} {B1 : α → ℕ} {B2 : β → ℕ}
    (P1 : PRun ea eb f B1) (P2 : PRun eb ec g B2) :
    PRun ea ec (fun a => g (f a)) (fun a => B1 a + (2 * (eb (f a)).length + 2) + B2 (f a)) := by
  classical
  let φ : P1.tm.Γ P1.tm.k₁ → P2.tm.Γ P2.tm.k₀ := fun x => P2.ia.invFun (P1.oa x)
  let d : Option (P2.tm.Γ P2.tm.k₀) :=
    if h : Nonempty (P2.tm.Γ P2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (P2.tm.Γ P2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (P2.tm.Γ P2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  refine ⟨Machines.comp P1.tm P2.tm φ d, P1.ia, P2.oa, fun a => ?_⟩
  obtain ⟨s1, hs1, r1⟩ := P1.run a
  obtain ⟨s2, hs2, r2⟩ := P2.run (f a)
  have hφ : (List.map P1.oa.invFun (eb (f a))).map φ = List.map P2.ia.invFun (eb (f a)) := by
    rw [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    show P2.ia.invFun (P1.oa (P1.oa.invFun y)) = _
    exact congrArg _ (P1.oa.right_inv y)
  rw [← hφ] at r2
  obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ s1 s2 r1 r2
  refine ⟨n, ?_, hrun⟩
  simp only [List.length_map] at hn
  omega

/-- A machine of `TM2ComputableInTime` bounds its runs by its time function. -/
noncomputable def PRun.ofTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (c : TM2ComputableInTime ea eb f) :
    PRun ea eb f (fun a => c.time (ea a).length) :=
  ⟨c.tm, c.inputAlphabet, c.outputAlphabet, fun a =>
    ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩⟩

/-- Acting on the first component of a pair. -/
noncomputable def PRun.first {f : List Bool → List Bool} {B : List Bool → ℕ}
    (P : PRun (fun x : List Bool => x) (fun x : List Bool => x) f B) :
    PRun encodePair encodePair (fun p : List Bool × List Bool => (f p.1, p.2))
      (fun p => B p.1 + 2 * p.1.length + 2 * p.2.length + 2 * (f p.1).length + 5) := by
  let e₀ : Bool → P.tm.Γ P.tm.k₀ := P.ia.invFun
  let e₁ : P.tm.Γ P.tm.k₁ → Bool := P.oa
  refine ⟨firstM P.tm e₀ e₁, Equiv.refl _, Equiv.refl _, fun p => ?_⟩
  obtain ⟨x, w⟩ := p
  obtain ⟨s, hs, h⟩ := P.run x
  obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
  have hm : (List.map P.oa.invFun (f x)).map e₁ = f x := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (f x)]
    exact List.map_congr_left fun y _ => P.oa.right_inv y
  rw [hm] at hrun
  refine ⟨n, ?_, ?_⟩
  · simp only [List.length_map] at hn; dsimp only; omega
  · simp only [Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl]
    erw [List.map_id, List.map_id]
    exact hrun

/-- Weakening the bound. -/
def PRun.mono {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {B B' : α → ℕ} (P : PRun ea eb f B) (h : ∀ a, B a ≤ B' a) : PRun ea eb f B' :=
  ⟨P.tm, P.ia, P.oa, fun a => by
    obtain ⟨n, hn, hr⟩ := P.run a
    exact ⟨n, hn.trans (h a), hr⟩⟩

/-- Changing the function to an equal one. -/
def PRun.congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f f' : α → β}
    {B : α → ℕ} (P : PRun ea eb f B) (h : ∀ a, f a = f' a) : PRun ea eb f' B :=
  ⟨P.tm, P.ia, P.oa, fun a => by rw [← h a]; exact P.run a⟩

end PEqualNP.General.Kannan
