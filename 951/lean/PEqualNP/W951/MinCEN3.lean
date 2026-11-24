import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCEFacts

/-!
# N3: the restriction `x_v := 1` (SORRY_DISSECTION §2)

The dead-gate development of Dead.lean is stated for an arbitrary constant `c : Bool`
(`DCpQ`/`DTQ`/`DCq`, `promise_boundQ`); here it is used with `c = true`.  On `{x v = 1}` a gate is
dead if it equals an earlier wire there or is constantly `0` there (a gate constantly `1` is a copy
of the input `x_v`).
`MinCE.liveBound1` (N3): in a minimal counterexample, `1 ≤ #DC1 v → ∑_{w ∌ v} d_w + #DC1 v ≤ s`,
where `DC1 v = DCq v true`, i.e. `#DC1 v ≤ ∑_{w ∋ v} d_w - σ`.  `geqV_sub_DC1`: gates `≥ x_v` are dead.
No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The gates dead under `x_v := 1`. -/
noncomputable abbrev DC1 {n : ℕ} (v : Fin n) (gates : List Gate) : Finset ℕ := DCq v true gates

open Classical in
/-- Gates `≥ x_v`. -/
noncomputable def GeqV {n : ℕ} (v : Fin n) (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter fun k =>
    ∀ x : Fin n → Bool, x v = true → val gates x (n + k) = true

/-- Every gate `≥ x_v` is dead on `x_v := 1` (it is a copy of the input `x_v`). -/
theorem geqV_sub_DC1 {n : ℕ} (v : Fin n) (gates : List Gate) : GeqV v gates ⊆ DC1 v gates := by
  classical
  intro k hk
  simp only [GeqV, DC1, DCq, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, deadQ_of_const v true gates k true hk.2⟩

/-- N3 (R0 quantitative, `x_v := 1`): in a minimal counterexample, for every point `v` with some
gate dead on `x_v := 1`, `∑_{w ∌ v} (|S w| - 1) + #DC1(v) ≤ #gates`,
i.e. `#DC1(v) ≤ ∑_{w ∋ v} d_w - σ`. -/
theorem MinCE.liveBound1 {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) (v : Fin n) (hDC : 1 ≤ (DC1 v gates).card) :
    ∑ w ∈ Finset.univ.filter (fun w => v ∉ S w), ((S w).card - 1) + (DC1 v gates).card ≤
      gates.length := by
  classical
  have C := M.ce
  let A := {w : Fin m // v ∉ S w}
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hpb := promise_boundQ v true gates.length
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) gates.length
    (Fintype.card A) (fun i => S (e i).1) gates (fun i => out (e i).1) rfl
    (fun i => (e i).2) (fun i => C.h2 _)
    (fun i j hij => C.hS _ _ (fun h => hij (e.injective (Subtype.ext h))))
    C.hg C.hU (fun i x _ => C.hev _ x) (by have : 1 ≤ (DCq v true gates).card := hDC; omega)
  have hsub : ∑ i : Fin (Fintype.card A), ((S (e i).1).card - 1) =
      ∑ w ∈ Finset.univ.filter (fun w => v ∉ S w), ((S w).card - 1) := by
    exact PEqualNP.Base.Matching.sum_equivFin_subtype (fun w => v ∉ S w) (fun w => (S w).card - 1)
  rw [hsub] at hpb
  exact hpb

end PEqualNP.Outside.L_meta_951_aux
