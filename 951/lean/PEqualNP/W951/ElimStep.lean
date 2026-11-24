import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCE

/-!
# ElimStep: what `gates < base` buys (coord 13:48 (b))

Lex-minimality makes every proper subfamily of the sets, computed by any correct circuit with at most
`s` gates, a NON-counterexample: `MinCE.sub_bound` (`base(T) ≤ s'` for a correct circuit of size
`s' ≤ s` for the subfamily `T`). So in a minimal counterexample the whole induction below the full
instance is free, and one elimination step closes it:

* **`no_minCE_of_elimStep`**: if every minimal counterexample has a proper subfamily `T` (the sets
  surviving a restriction, e.g. `x_v := 1`: the sets not through `v`) with a correct circuit of at most
  `s - ∑_{w ∉ T} d_w` gates, there is no minimal counterexample.

For `x_v := 1` the step reads `elim1(v) ≥ cost(v)`: the restriction (constant propagation, removal of
input copies, duplicates and dead gates) removes at least `∑_{w ∋ v} d_w` gates. In a MinCE every `v` has
`elim1(v) < cost(v)` (this file), so an F2 step at `Q = ∅` can only come from F2 gates that leave F2
WITHOUT being eliminated. Data (tools/kill_tests/elim_vs_gain.py): the elimination step holds at
`Q = ∅` on all 104 local correct circuits, MATCH-C and the twin trees included (where the F2 step fails);
the F2 step never holds without it.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section ElimStep

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- The base splits over a subfamily (given by an injection) and the removed sets. -/
theorem base_split {m' : ℕ} (S : Fin m → Finset (Fin n)) (ι : Fin m' → Fin m)
    (hι : Function.Injective ι) :
    ∑ w, ((S w).card - 1) = ∑ i, ((S (ι i)).card - 1) +
      ∑ w ∈ Finset.univ.filter (fun w => w ∉ Set.range ι), ((S w).card - 1) := by
  classical
  have himg : ∑ i, ((S (ι i)).card - 1) = ∑ w ∈ Finset.univ.image ι, ((S w).card - 1) :=
    (Finset.sum_image (f := fun w => (S w).card - 1) fun a _ b _ h => hι h).symm
  have hfil : Finset.univ.image ι = Finset.univ.filter (fun w => w ∈ Set.range ι) := by
    ext w
    simp
  rw [himg, hfil, Finset.sum_filter_add_sum_filter_not]

/-- **Lex-minimality on subfamilies**: in a minimal counterexample, a proper subfamily of the sets
computed by a correct circuit with at most `s` gates is not a counterexample. -/
theorem MinCE.sub_bound (M : MinCE S gates out) {m' : ℕ} (ι : Fin m' → Fin m)
    (hι : Function.Injective ι) (hproper : ∃ w, w ∉ Set.range ι) (gates' : List Gate)
    (out' : Fin m' → ℕ)
    (hg' : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU' : AtMostOneNot gates')
    (hev' : ∀ (i : Fin m') (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ S (ι i), x v = true))
    (hle : gates'.length ≤ gates.length) :
    ∑ i, ((S (ι i)).card - 1) ≤ gates'.length := by
  classical
  by_contra hlt
  push Not at hlt
  have C := M.ce
  have hce : IsCE (S ∘ ι) gates' out' :=
    { h2 := fun i => C.h2 (ι i)
      hS := fun i j hij => C.hS (ι i) (ι j) fun h => hij (hι h)
      hg := hg'
      hU := hU'
      hev := hev'
      hlt := hlt }
  apply M.min n m' (S ∘ ι) gates' out' hce
  rcases Nat.lt_or_ge gates'.length gates.length with h | h
  · exact Or.inl h
  · refine Or.inr ⟨le_antisymm hle h, ?_⟩
    obtain ⟨w0, hw0⟩ := hproper
    unfold ceSize
    have himg : ∑ i, (S (ι i)).card = ∑ w ∈ Finset.univ.image ι, (S w).card :=
      (Finset.sum_image (f := fun w => (S w).card) fun a _ b _ h => hι h).symm
    have hsub : Finset.univ.image ι ⊆ Finset.univ.erase w0 := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_erase.mpr ⟨fun h => hw0 ⟨i, h⟩, Finset.mem_univ _⟩
    have h1 : ∑ w ∈ Finset.univ.image ι, (S w).card ≤ ∑ w ∈ Finset.univ.erase w0, (S w).card :=
      Finset.sum_le_sum_of_subset hsub
    have h2 := Finset.sum_erase_add Finset.univ (fun w => (S w).card) (Finset.mem_univ w0)
    have h3 := C.h2 w0
    show ∑ i, (S (ι i)).card < ∑ w, (S w).card
    omega

/-- **In a minimal counterexample no restriction eliminates its cost**: a correct circuit for a proper
subfamily has more than `s - ∑_{removed} d_w` gates. (For `x_v := 1`: `elim1(v) < cost(v)`.) -/
theorem MinCE.elim_lt (M : MinCE S gates out) {m' : ℕ} (ι : Fin m' → Fin m)
    (hι : Function.Injective ι) (hproper : ∃ w, w ∉ Set.range ι) (gates' : List Gate)
    (out' : Fin m' → ℕ)
    (hg' : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU' : AtMostOneNot gates')
    (hev' : ∀ (i : Fin m') (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ S (ι i), x v = true)) :
    gates.length < gates'.length +
      ∑ w ∈ Finset.univ.filter (fun w => w ∉ Set.range ι), ((S w).card - 1) := by
  by_contra hge
  push Not at hge
  have hb := base_split S ι hι
  have hle : gates'.length ≤ gates.length := by omega
  have := M.sub_bound ι hι hproper gates' out' hg' hU' hev' hle
  have hlt := M.ce.hlt
  omega

end ElimStep

/-- **951 from one elimination step**: if every minimal counterexample has a proper subfamily of its
sets (e.g. the sets not through a point `v`, i.e. the restriction `x_v := 1`) with a correct circuit of
at most `s - ∑_{removed} d_w` gates, there is no minimal counterexample. -/
theorem no_minCE_of_elimStep
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (m' : ℕ) (ι : Fin m' → Fin m), Function.Injective ι ∧
        (∃ w, w ∉ Set.range ι) ∧ ∃ (gates' : List Gate) (out' : Fin m' → ℕ),
          (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
            g.inputs.length ≤ 2) ∧ AtMostOneNot gates' ∧
          (∀ (i : Fin m') (x : Fin n → Bool),
            val gates' x (out' i) = decide (∃ v ∈ S (ι i), x v = true)) ∧
          gates'.length + ∑ w ∈ Finset.univ.filter (fun w => w ∉ Set.range ι), ((S w).card - 1) ≤
            gates.length) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨m', ι, hι, hproper, gates', out', hg', hU', hev', hle⟩ := H n m S gates out M
  have := M.elim_lt ι hι hproper gates' out' hg' hU' hev'
  omega

end PEqualNP.Outside.L_meta_951_aux
