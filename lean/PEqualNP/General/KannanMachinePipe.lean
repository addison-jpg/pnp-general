import PEqualNP.General.KannanMachineCut
import PEqualNP.General.KannanMachineReduce
import PEqualNP.Library.Machines.Clock
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Helpers.PolyExp

/-!
# The linear-time check, from a polynomial-time check on the data regions

`kannan_of_core`: if `(x, sel) ↦ CoreFn k x sel` is polynomial-time computable on pairs, then
`KL k ∈ SigmaP 3`.

The machine: write `1 ^ D ++ 0 :: x` in place of `x` (`D = blk k |x|`, polynomial time in `|x|`),
cut the three data regions out of the witness (`cutM`, linear time), then run the polynomial-time
check on `(x, regions)`, whose length is `|x| + 3 D`. With blocks of length `s = K n ^ K + K`
for `K` large, the polynomial parts are below `s`, so on witnesses of the right length the whole
run is linear in `|x| + 3 s`; on all other inputs the clock (`clocked`) cuts the run off.
-/

namespace PEqualNP.General.Kannan

open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- A machine computing `f` on the inputs of `G`, with run lengths bounded by `B`. -/
structure GRun {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (B : α → ℕ) (G : α → Prop) where
  tm : FinTM2
  ia : tm.Γ tm.k₀ ≃ αΓ
  oa : tm.Γ tm.k₁ ≃ βΓ
  run : ∀ a, G a → ∃ n, n ≤ B a ∧ (flip bind (TM2.step tm.m))^[n]
    (some (initList tm ((ea a).map ia.invFun))) = some (haltList tm ((eb (f a)).map oa.invFun))

def GRun.ofP {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {B : α → ℕ} (P : PRun ea eb f B) (G : α → Prop) : GRun ea eb f B G :=
  ⟨P.tm, P.ia, P.oa, fun a _ => P.run a⟩

noncomputable def GRun.comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} {B1 : α → ℕ} {B2 : β → ℕ}
    {G1 : α → Prop} {G2 : β → Prop}
    (P1 : GRun ea eb f B1 G1) (P2 : GRun eb ec g B2 G2) :
    GRun ea ec (fun a => g (f a)) (fun a => B1 a + (2 * (eb (f a)).length + 2) + B2 (f a))
      (fun a => G1 a ∧ G2 (f a)) := by
  classical
  let φ : P1.tm.Γ P1.tm.k₁ → P2.tm.Γ P2.tm.k₀ := fun x => P2.ia.invFun (P1.oa x)
  let d : Option (P2.tm.Γ P2.tm.k₀) :=
    if h : Nonempty (P2.tm.Γ P2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (P2.tm.Γ P2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (P2.tm.Γ P2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  refine ⟨Machines.comp P1.tm P2.tm φ d, P1.ia, P2.oa, fun a ha => ?_⟩
  obtain ⟨s1, hs1, r1⟩ := P1.run a ha.1
  obtain ⟨s2, hs2, r2⟩ := P2.run (f a) ha.2
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

/-! ### The cutting machine as a stage -/

/-- What the cutting machine computes on good inputs. -/
def cutF (p : List Bool × List Bool) : List Bool × List Bool :=
  let D := (p.1.takeWhile id).length
  let s := p.2.length / 3
  ((p.1.dropWhile id).drop 1, p.2.take D ++ (p.2.drop s).take D ++ (p.2.drop (2 * s)).take D)

/-- Good inputs of the cutting machine. -/
def CutGood (p : List Bool × List Bool) : Prop :=
  ∃ (D s : ℕ) (x y1 y2 y3 : List Bool), p.1 = Cut.mk D ++ false :: x ∧
    p.2 = y1 ++ y2 ++ y3 ∧ y1.length = s ∧ y2.length = s ∧ y3.length = s ∧ D ≤ s

theorem cutF_good (D s : ℕ) (x y1 y2 y3 : List Bool) (h1 : y1.length = s) (h2 : y2.length = s)
    (h3 : y3.length = s) (hD : D ≤ s) :
    cutF (Cut.mk D ++ false :: x, y1 ++ y2 ++ y3) =
      (x, y1.take D ++ y2.take D ++ y3.take D) := by
  have ht : (Cut.mk D ++ false :: x).takeWhile id = Cut.mk D := by
    induction D with
    | zero => simp [Cut.mk]
    | succ D ih => simp [Cut.mk, List.replicate_succ] at ih ⊢
  have hd : (Cut.mk D ++ false :: x).dropWhile id = false :: x := by
    induction D with
    | zero => simp [Cut.mk]
    | succ D ih => simp [Cut.mk, List.replicate_succ] at ih ⊢
  have hl : (y1 ++ y2 ++ y3).length / 3 = s := by simp; omega
  have e1 : (y1 ++ y2 ++ y3) = y1 ++ (y2 ++ y3) := List.append_assoc _ _ _
  have a1 : (y1 ++ (y2 ++ y3)).take D = y1.take D := List.take_append_of_le_length (by omega)
  have a2 : (y1 ++ (y2 ++ y3)).drop s = y2 ++ y3 := List.drop_left' h1
  have a3 : (y1 ++ (y2 ++ y3)).drop (2 * s) = y3 := by
    rw [show 2 * s = s + s by ring, ← List.drop_drop, a2, List.drop_left' h2]
  have a4 : (y2 ++ y3).take D = y2.take D := List.take_append_of_le_length (by omega)
  have a5 : y3.take D = y3.take D := rfl
  unfold cutF
  simp only [ht, hd, hl, Cut.mk, List.length_replicate, List.drop_one, List.tail_cons]
  rw [e1, a1, a2, a3, a4]

noncomputable def cutRun :
    GRun encodePair encodePair cutF (fun p => 4 * (p.1.length + p.2.length) + 20) CutGood :=
  ⟨Cut.cutM, Equiv.refl _, Equiv.refl _, fun p hp => by
    obtain ⟨D, s, x, y1, y2, y3, hu, hw, h1, h2, h3, hD⟩ := hp
    obtain ⟨u, w⟩ := p
    simp only at hu hw
    subst hu hw
    obtain ⟨n, hn, h⟩ := Cut.cut_run D s x y1 y2 y3 h1 h2 h3 hD
    refine ⟨n, hn, ?_⟩
    simp only [Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl]
    erw [List.map_id, List.map_id]
    rw [cutF_good D s x y1 y2 y3 h1 h2 h3 hD]
    have hi : initList Cut.cutM (encodePair (Cut.mk D ++ false :: x, y1 ++ y2 ++ y3)) =
        (⟨some .sp, (none, none, false, false),
          Cut.cs (encodePair (Cut.mk D ++ false :: x, y1 ++ y2 ++ y3)) [] [] [] [] [] [] [] []⟩ :
          Cut.CCfg) := by
      refine (initList_eq Cut.cutM _).trans ?_
      show (⟨_, _, _⟩ : Cut.CCfg) = _
      congr 1
      funext k; cases k <;> rfl
    have hh : haltList Cut.cutM (encodePair (x, y1.take D ++ y2.take D ++ y3.take D)) =
        (⟨none, (none, none, false, false),
          Cut.cs [] [] [] [] [] [] [] [] (encodePair (x, y1.take D ++ y2.take D ++ y3.take D))⟩ :
          Cut.CCfg) := by
      refine (haltList_eq Cut.cutM _).trans ?_
      show (⟨_, _, _⟩ : Cut.CCfg) = _
      congr 1
      funext k; cases k <;> rfl
    exact (congrArg (fun c => Cut.cstep^[n] (some c)) hi).trans (h.trans (congrArg some hh).symm)⟩

end PEqualNP.General.Kannan
