import PEqualNP.W951.RunTransfer
import PEqualNP.Kernel.W951CubeKeep
import PEqualNP.W951.PureHeredity

/-! PureRestrict: the restricted circuit as an actual gate list (coord 11:59; the gap left open in
cTAHG's PureHeredity note, where the restricted instance's classes are modelled by evaluating the
original circuit at points of the subcube).

* `exists_restrict_runs` (any list circuit, any subcube `Cube Z ρ`): ONE restricted list `gates'`
  (`Kernel.list_restrictCube_keep`: constants propagated, the gates that are constant or copies of
  an earlier wire on the cube deleted, the others kept in order with their values on the cube) such
  that EVERY union-find run whose zero point and test points lie in the cube has the same final
  labelling on `gates'` and the same merge set up to renaming kept wire `n + t` to `n + e t`
  (`RunTransfer.run_transfer`: no merge at constants or copies).
* `exists_restrictedLift`: the lift `lift n p gates` (NOT gate replaced by the input `y`) restricted
  to `x_v := 0` for `v ∉ V`, `y` free (cTAHG's model: "NOT gate kept"). For every `R ⊆ V` and every
  restricted option (`RestrValid`), cTAHG's restricted class `restrCls gates p V R o` (the original
  run at subcube points) is the class `clsOn L V R o` of the run on the restricted list `L`,
  renamed. So the restricted instance's pure classes ARE pure-option runs on an actual gate list.
* `exists_restricted_correct`: the restricted real circuit for a family `F` with `S_w ⊆ V`
  (`list_restrictCube`, outputs `out w`, `w ∈ F`) computes `OR (S_w)` for every `w ∈ F` on EVERY
  input, keeps the 951 gate shape and at most one NOT gate, and has size
  `|gates_res| + #dead = |gates|` (the dead gates: constant or copied on the subcube, or outside
  every cone of the outputs of `F` after propagation), i.e. `|gates_res|` = the number of live gates.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## One restricted list for all runs in a cube -/

section General

variable {n : ℕ}

theorem exists_restrict_runs (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (Z : Finset (Fin n)) (ρ : Fin n → Bool) :
    ∃ (gates' : List Gate) (e : ℕ → ℕ), PEqualNP.Kernel.ShapeMap gates gates' e ∧
      (∀ t < gates'.length, ∀ x, PEqualNP.Kernel.Cube Z ρ x →
        val gates' x (n + t) = val gates x (n + e t)) ∧
      ∀ (z : Fin n → Bool) (pt : Fin n → Fin n → Bool) (R : Finset (Fin n)),
        (∀ u ∈ R, ∀ c, pt u c = true → z c = false → c = u) →
        PEqualNP.Kernel.Cube Z ρ z → (∀ u ∈ R, PEqualNP.Kernel.Cube Z ρ (pt u)) →
        runLT z pt R gates gates.length = runLT z pt R gates' gates'.length ∧
        runMT z pt R gates gates.length =
          (runMT z pt R gates' gates'.length).image (fun i => n + e (i - n)) := by
  obtain ⟨gates', e, hsh, hkeep, hdead⟩ := PEqualNP.Kernel.list_restrictCube_keep gates hops Z ρ
  refine ⟨gates', e, hsh, hkeep, fun z pt R hT hz hp => ?_⟩
  exact run_transfer z pt R gates gates' e (PEqualNP.Kernel.Cube Z ρ) hT hz hp hsh.1
    (fun t ht => (hsh.2 t ht).fst) hkeep hdead

end General

/-! ## The restricted lift: pure classes of the restricted instance -/

section Lift

variable {n : ℕ}

/-- The class of a pure option of the instance restricted to `V`, computed by a run on the
lifted list `L` (cTAHG's restricted points: `topIn V R` for `zero`). -/
noncomputable def clsOn (L : List Gate) (V R : Finset (Fin n)) : PureOpt n → Finset ℕ
  | .one Z => runMT (ext Z true) atom1 (liftSet R) L L.length
  | .zero m => runMT (ext (topIn V R) false) (atom0 m) (liftSet R) L L.length
  | .zeroAt z m => runMT (ext z false) (atom0 m) (liftSet R) L L.length
  | .oneAt Z A => runMT (ext Z true) (atom1W A) (liftSet R) L L.length

theorem restrCls_eq_clsOn (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) (o : PureOpt n) :
    restrCls gates p V R o = clsOn (lift n p gates) V R o := by
  cases o <;> rfl

/-- The lifted coordinates set to `0` by the restriction: `x_v`, `v ∉ V` (`y` stays free). -/
def offV (V : Finset (Fin n)) : Finset (Fin (n + 1)) := liftSet (Finset.univ \ V)

theorem cube_ext (V : Finset (Fin n)) (z : Fin n → Bool) (b : Bool)
    (hz : ∀ v, v ∉ V → z v = false) :
    PEqualNP.Kernel.Cube (offV V) (fun _ => false) (ext z b) := by
  intro t ht
  obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp ht
  rw [ext_castSucc]
  exact hz v (by simpa using hv)

theorem canonPt_off (V X : Finset (Fin n)) (hX : X ⊆ V) : ∀ v, v ∉ V → canonPt X v = false := by
  intro v hv
  cases h : canonPt X v
  · rfl
  · exact absurd (hX (canonPt_eq_true.mp h)) hv

theorem cube_atom1 (V R : Finset (Fin n)) (hRV : R ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom1 c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1_castSucc]
  exact cube_ext V _ true (canonPt_off V {u} (by simpa using hRV hu))

theorem cube_atom0 (V R : Finset (Fin n)) (hRV : R ⊆ V) (m : Fin n → Finset (Fin n))
    (hm : ∀ u ∈ R, m u ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom0 m c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom0_castSucc]
  exact cube_ext V _ false (canonPt_off V _ (Finset.insert_subset (hRV hu) (hm u hu)))

theorem cube_atom1W (V R : Finset (Fin n)) (hRV : R ⊆ V) (A : Fin n → Finset (Fin n))
    (hA : ∀ u ∈ R, A u ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom1W A c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1W_castSucc]
  exact cube_ext V _ true (canonPt_off V _ (Finset.insert_subset (hRV hu) (hA u hu)))

/-! Test-point conditions (`hT` of `runLT_inv`) for the lifted atoms. -/

theorem hT_atom1 (R : Finset (Fin n)) (Z : Fin n → Bool) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom1 c c' = true → ext Z true c' = false → c' = c := by
  intro c _ c' h1 h2
  rw [atom1, canonPt_eq_true, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact h1
  · rw [h1, ext_last] at h2
    exact absurd h2 (by decide)

theorem hT_atom0 (R : Finset (Fin n)) (z : Fin n → Bool) (m : Fin n → Finset (Fin n))
    (hmz : ∀ u ∈ R, ∀ v ∈ m u, v = u ∨ z v = true) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom0 m c c' = true → ext z false c' = false → c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom0_castSucc] at h1
  induction c' using Fin.lastCases with
  | last => rw [ext_last] at h1; exact absurd h1 (by decide)
  | cast v =>
    rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
    rw [ext_castSucc] at h2
    rcases h1 with rfl | h1
    · rfl
    · rcases hmz u hu v h1 with rfl | h3
      · rfl
      · rw [h3] at h2; exact absurd h2 (by decide)

theorem hT_atom1W (R : Finset (Fin n)) (Z : Fin n → Bool) (A : Fin n → Finset (Fin n))
    (hAZ : ∀ u ∈ R, ∀ v ∈ A u, v = u ∨ Z v = true) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom1W A c c' = true → ext Z true c' = false →
      c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1W_castSucc] at h1
  induction c' using Fin.lastCases with
  | last => rw [ext_last] at h2; exact absurd h2 (by decide)
  | cast v =>
    rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
    rw [ext_castSucc] at h2
    rcases h1 with rfl | h1
    · rfl
    · rcases hAZ u hu v h1 with rfl | h3
      · rfl
      · rw [h3] at h2; exact absurd h2 (by decide)

/-- The zero condition `topIn V R` for `zero m` options. -/
theorem topIn_mz (V R : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (hm : ∀ u ∈ R, ∀ v ∈ m u, v ∈ R → v = u) (hmV : ∀ u ∈ R, m u ⊆ V) :
    ∀ u ∈ R, ∀ v ∈ m u, v = u ∨ topIn V R v = true := by
  intro u hu v hv
  by_cases hvR : v ∈ R
  · exact Or.inl (hm u hu v hv hvR)
  · right
    rw [topIn, canonPt_eq_true, Finset.mem_sdiff]
    exact ⟨hmV u hu hv, hvR⟩

/-- **The restricted lift.** One list `L`: the lift restricted to `x_v := 0` off `V` (`y` free),
with kept-gate map `e`; for every `R ⊆ V` and every restricted option, the restricted class (the
original run at subcube points) is the run on `L`, renamed. -/
theorem exists_restrictedLift (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (V : Finset (Fin n)) :
    ∃ (L : List Gate) (e : ℕ → ℕ), PEqualNP.Kernel.ShapeMap (lift n p gates) L e ∧
      (∀ t < L.length, ∀ x, PEqualNP.Kernel.Cube (offV V) (fun _ => false) x →
        val L x (n + 1 + t) = val (lift n p gates) x (n + 1 + e t)) ∧
      ∀ R : Finset (Fin n), R ⊆ V → ∀ o : PureOpt n, RestrValid gates p V R o →
        restrCls gates p V R o = (clsOn L V R o).image (fun i => n + 1 + e (i - (n + 1))) := by
  have hops : ∀ g ∈ lift n p gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hgm => ((lift_ops gates p hp hg hU hN g hgm).1).elim Or.inl (fun h => Or.inr (Or.inl h))
  obtain ⟨L, e, hsh, hkeep, hrun⟩ := exists_restrict_runs (lift n p gates) hops (offV V)
    (fun _ => false)
  refine ⟨L, e, hsh, hkeep, fun R hRV o ho => ?_⟩
  rw [restrCls_eq_clsOn]
  cases o with
  | one Z =>
    obtain ⟨⟨hZR, -⟩, hZV⟩ := ho
    exact (hrun _ _ _ (hT_atom1 R Z) (cube_ext V Z true hZV) (cube_atom1 V R hRV)).2
  | zero m =>
    obtain ⟨⟨hm, -⟩, hmV⟩ := ho
    have hz : ∀ v, v ∉ V → topIn V R v = false :=
      canonPt_off V (V \ R) Finset.sdiff_subset
    exact (hrun _ _ _ (hT_atom0 R _ m (topIn_mz V R m hm hmV)) (cube_ext V _ false hz)
      (cube_atom0 V R hRV m hmV)).2
  | zeroAt z m =>
    obtain ⟨⟨-, hmz, -⟩, hzV, hmV⟩ := ho
    exact (hrun _ _ _ (hT_atom0 R z m hmz) (cube_ext V z false hzV)
      (cube_atom0 V R hRV m hmV)).2
  | oneAt Z A =>
    obtain ⟨⟨-, -, hAZ⟩, hZV, hAV⟩ := ho
    exact (hrun _ _ _ (hT_atom1W R Z A hAZ) (cube_ext V Z true hZV)
      (cube_atom1W V R hRV A hAV)).2

end Lift

/-! ## The restricted real circuit is a correct circuit for `F` -/

section Correct

variable {n m : ℕ}

theorem exists_restricted_correct (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (F : Finset (Fin m)) (V : Finset (Fin n)) (hFV : ∀ w ∈ F, S w ⊆ V)
    (h1 : ∀ w ∈ F, (S w).Nonempty) :
    ∃ (gates' : List Gate) (out' : Fin m → ℕ),
      gates'.length +
          (PEqualNP.Kernel.deadLC gates (Finset.univ \ V) (fun _ => false) (F.image out)).card =
        gates.length ∧
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates' ∧
      ∀ w ∈ F, ∀ x : Fin n → Bool, val gates' x (out' w) = decide (∃ v ∈ S w, x v = true) := by
  classical
  obtain ⟨gates', e, r, hlen, hsh, hout⟩ := PEqualNP.Kernel.list_restrictCube gates
    (fun g hgm => (hg g hgm).1) (Finset.univ \ V) (fun _ => false) (F.image out)
  refine ⟨gates', fun w => r (out w), hlen, hsh.hg hg, hsh.hU hU, fun w hw x => ?_⟩
  rcases hout (out w) (Finset.mem_image_of_mem out hw) with ⟨c, hc⟩ | h
  · exfalso
    obtain ⟨u, hu⟩ := h1 w hw
    have hcube : ∀ X : Finset (Fin n), X ⊆ V →
        PEqualNP.Kernel.Cube (Finset.univ \ V) (fun _ => false) (canonPt X) := by
      intro X hX t ht
      exact canonPt_off V X hX t (by simpa using ht)
    have e0 := hc (canonPt ∅) (hcube ∅ (Finset.empty_subset _))
    have e1 := hc (canonPt {u}) (hcube {u} (by simpa using hFV w hw hu))
    rw [hev] at e0 e1
    have : decide (∃ v ∈ S w, canonPt (∅ : Finset (Fin n)) v = true) = false := by
      simp [canonPt]
    have h' : decide (∃ v ∈ S w, canonPt ({u} : Finset (Fin n)) v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_singleton_self u)⟩
    rw [this] at e0
    rw [h', ← e0] at e1
    exact absurd e1 (by decide)
  · rw [h x, hev]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, hv, hxv⟩
      refine ⟨v, hv, ?_⟩
      rw [PEqualNP.Kernel.proj_notMem (Finset.univ \ V) (fun _ => false) x
        (by simpa using hFV w hw hv)] at hxv
      exact hxv
    · rintro ⟨v, hv, hxv⟩
      refine ⟨v, hv, ?_⟩
      rw [PEqualNP.Kernel.proj_notMem (Finset.univ \ V) (fun _ => false) x
        (by simpa using hFV w hw hv)]
      exact hxv

end Correct

end PEqualNP.Outside.L_meta_951_aux
