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

/-! ### The assembly -/

theorem pow_le_blkK (kq K n : ℕ) (hK : kq ≤ K) (hK1 : 1 ≤ K) : n ^ kq + kq ≤ blkK K n := by
  unfold blkK
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rcases Nat.eq_zero_or_pos kq with h1 | h1
    · subst h1; simp; omega
    · rw [zero_pow (by omega)]; omega
  · have : n ^ kq ≤ n ^ K := Nat.pow_le_pow_right h0 hK
    have : n ^ K ≤ K * n ^ K := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The uniform half of Kannan's theorem, from a polynomial-time check on the data regions. -/
theorem kannan_of_core (k : ℕ)
    (hcore : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => CoreFn k p.1 p.2)) : KL k ∈ SigmaP 3 := by
  classical
  let pD : Polynomial ℕ := Polynomial.C (KK k) * Polynomial.X ^ (KK k) + Polynomial.C (KK k)
  have hpD : ∀ n, pD.eval n = blk k n := by intro n; simp [pD, blk]
  let f0 : List Bool → List Bool := fun x => Cut.mk (blk k x.length) ++ false :: x
  have hf0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f0 := by
    have hc := clock_polyTime Universal.cpt_const pD
    have h2 := Universal.cpt_app2 (Universal.cpt_const [false]) cpt_id
    have h3 := Universal.cpt_app2 hc h2
    have e : (fun s : List Bool => List.replicate (pD.eval s.length) true ++ ([false] ++ s)) = f0 := by
      funext x; simp [f0, hpD, Cut.mk]
    rw [e] at h3
    exact h3
  obtain ⟨p0, c0, hc0⟩ := time_of_polyTime hf0
  obtain ⟨p3, c3, hc3⟩ := time_of_polyTime hcore
  let S1 := GRun.ofP (PRun.first (PRun.ofTime c0)) (fun _ => True)
  let S3 := GRun.ofP (PRun.ofTime c3) (fun _ => True)
  let S := GRun.comp (GRun.comp S1 cutRun) S3
  let q : Polynomial ℕ := p0 + p3.comp (Polynomial.X + Polynomial.C 3 * pD)
  obtain ⟨kq, hkq⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add q
  let K := kq + KK k + 1
  let G : List Bool × List Bool → Prop := fun a => ∃ y1 y2 y3 : List Bool,
    a.2 = y1 ++ y2 ++ y3 ∧ y1.length = blkK K a.1.length ∧ y2.length = blkK K a.1.length ∧
      y3.length = blkK K a.1.length
  let g : List Bool × List Bool → Bool := fun a =>
    CoreFn k (cutF (f0 a.1, a.2)).1 (cutF (f0 a.1, a.2)).2
  have hG : ∀ a, G a → ∃ n, n ≤ 100 * (encodePair a).length ∧
      (flip bind (TM2.step S.tm.m))^[n] (some (initList S.tm ((encodePair a).map S.ia.invFun))) =
        some (haltList S.tm [S.oa.invFun (g a)]) := by
    rintro ⟨x, w⟩ ⟨y1, y2, y3, hw, h1, h2, h3⟩
    simp only at hw h1 h2 h3
    set s := blkK K x.length with hs
    set D := blk k x.length with hDdef
    have hDs : D ≤ s := blk_le_blkK k K x.length (by omega)
    have hgood : CutGood (f0 x, w) := ⟨D, s, x, y1, y2, y3, rfl, hw, h1, h2, h3, hDs⟩
    obtain ⟨n, hn, hrun⟩ := S.run (x, w) ⟨⟨trivial, hgood⟩, trivial⟩
    refine ⟨n, ?_, hrun⟩
    -- the bound
    have hcut : cutF (f0 x, w) = (x, y1.take D ++ y2.take D ++ y3.take D) := by
      rw [hw]; exact cutF_good D s x y1 y2 y3 h1 h2 h3 hDs
    have hwl : w.length = 3 * s := by rw [hw]; simp; omega
    have hsel : (y1.take D ++ y2.take D ++ y3.take D).length = 3 * D := by simp; omega
    have hf0l : (f0 x).length = D + 1 + x.length := by simp [f0, Cut.mk, hDdef]; omega
    have b0 : c0.time x.length ≤ p0.eval x.length := hc0 _
    have b3 : c3.time (x.length + 3 * D) ≤ p3.eval (x.length + 3 * D) := hc3 _
    have hq : p0.eval x.length + p3.eval (x.length + 3 * D) ≤ s := by
      have := hkq x.length
      have e : q.eval x.length = p0.eval x.length + p3.eval (x.length + 3 * D) := by
        simp [q, hDdef, ← hpD]
      have := pow_le_blkK kq K x.length (by omega) (by omega)
      omega
    have hs1 : 1 ≤ s := by simp only [hs, blkK]; omega
    simp only [S, GRun.comp, GRun.ofP, PRun.first, PRun.ofTime, cutRun] at hn
    simp only [encodePair_length, hcut, hsel, hf0l, hwl] at hn ⊢
    omega
  obtain ⟨f, K', hfg, hcomp⟩ := clocked encodePair S.tm S.ia S.oa g G 100 hG
  refine ⟨K, {p | f p = true}, K', ⟨f, fun _ => Iff.rfl, hcomp⟩, fun x => ?_⟩
  set s := blkK K x.length with hs
  set D := blk k x.length with hDdef
  have hDs : D ≤ s := blk_le_blkK k K x.length (by omega)
  have hge := blk_ge k x.length
  rw [mem_KL_iff_blocksS k x s (by omega), alt3]
  apply exists_congr; intro y1
  apply and_congr_right; intro h1
  apply forall_congr'; intro y2
  apply imp_congr_right; intro h2
  apply exists_congr; intro y3
  apply and_congr_right; intro h3
  have hGa : G (x, y1 ++ (y2 ++ y3)) := ⟨y1, y2, y3, by simp, h1, h2, h3⟩
  show _ ↔ f (x, y1 ++ (y2 ++ y3)) = true
  rw [hfg _ hGa]
  show _ ↔ CoreFn k (cutF (f0 x, y1 ++ (y2 ++ y3))).1 (cutF (f0 x, y1 ++ (y2 ++ y3))).2 = true
  rw [← List.append_assoc, cutF_good D s x y1 y2 y3 h1 h2 h3 hDs]
  simp only
  rw [List.append_assoc, ← zipSel_maskOf D s hDs y1 y2 y3 h1 h2 h3,
    CoreFn_blocks k x y1 y2 y3 s hDs h1 h2 h3]

end PEqualNP.General.Kannan
