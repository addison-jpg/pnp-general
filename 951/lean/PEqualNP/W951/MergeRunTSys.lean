import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.GapG

-- `TestSys.merges`: the union-find run of MergeRunT.lean for one test system (GapG.lean), in the
-- masked circuit `mask σ.K gates`.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- (T2) Per test system: an explicit merge set inside the counted wires, of size at least
`|S| - 1`, with labellings `L` recording the merges, persistence, and the
joined-at-most-once property. The gate list is `mask σ.K gates`, as in `σ.cnt`. -/
theorem TestSys.merges {n : ℕ} {gates : List Gate} {S : Finset (Fin n)} {o : ℕ}
    (σ : TestSys n gates S o)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ S, x v = true)) :
    ∃ (L : ℕ → Fin n → Fin n) (M : Finset ℕ),
      M ⊆ σ.cnt ∧ S.card - 1 ≤ M.card ∧
      (∀ j, n + j ∈ M →
        (∃ u ∈ S, ∃ v ∈ S, val (mask σ.K gates) (σ.p u) (n + j) = true ∧
          val (mask σ.K gates) (σ.p v) (n + j) = true ∧ L j u ≠ L j v) ∧
        ∀ u ∈ S, ∀ v ∈ S, val (mask σ.K gates) (σ.p u) (n + j) = true →
          val (mask σ.K gates) (σ.p v) (n + j) = true → L (j + 1) u = L (j + 1) v) ∧
      (∀ j k u v, j ≤ k → L j u = L j v → L k u = L k v) ∧
      (∀ j j' u v, L (j + 1) u = L (j + 1) v → j < j' →
        (∀ w ∈ S, val (mask σ.K gates) (σ.p w) (n + j') = true → w = u ∨ w = v) →
          n + j' ∉ M) := by
  set gs := mask σ.K gates with hgs
  have hm : ∀ x : Fin n → Bool, val gs x o = val gates x o := fun x =>
    val_mask σ.K gates.length x gates le_rfl σ.hcl o σ.hout
  refine ⟨runLT σ.z σ.p S gs, runMT σ.z σ.p S gs gs.length,
    run_sub_DT σ.z σ.p S gs _, ?_, run_recordT σ.z σ.p S gs _,
    run_persistT σ.z σ.p S gs, fun j j' u v hj hjj htr =>
      run_onceT σ.z σ.p S gs _ j j' u v hj hjj htr⟩
  apply merge_countT σ.z σ.p S gs σ.hT σ.hgood o
  · rw [hm, hev, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv'⟩
    rw [σ.hzS v hv] at hv'
    exact absurd hv' (by simp)
  · intro u hu
    rw [hm, hev, decide_eq_true_eq]
    exact ⟨u, hu, σ.hpS u hu⟩

end PEqualNP.Outside.L_meta_951_aux
