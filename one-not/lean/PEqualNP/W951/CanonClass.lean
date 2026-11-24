import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LiftCount

/-!
# CanonClass: canonical classes at a top zero point (lemmas GM, W0, W1, X)

The statements of `one-not/PROOF_PLAN_SUGGESTIONS.md` section 2, for an arbitrary monotone gate list
`gs` on `N` inputs. Everything is an instantiation of `LiftCount`: the size bound is
`lift_merges_pt`, and the disjointness is monotonicity of the wires (`val_le_of_le`). For a
circuit with one NOT gate, take `gs = lift n p gates` (`Lift.lean`, `N = n + 1`, the last input
is the value `y` of the NOT gate): world 1 is `y = true`, world 0 is `y = false`.

* `canon_size` (GM): for ANY zero point `z` and atoms `a`, not necessarily `z + e_u`, with every
  coordinate that is false at `z` true at one atom at most, there are `k - 1` gates in
  `orClz gs z a` (OR gates false at `z`, true at two atoms or more).
* `orClz_disjoint` (D): if of any two atoms of the first system one lies below the zero point of
  the second, the two classes are disjoint.
* `orClz_cross` (X): if a gate lies in both classes although the first system's atoms, moved to
  `a0`, satisfy the hypothesis of D, then the wire is true at an atom `a t` and false at its copy
  `a0 t`. With `a t` the world-1 atom and `a0 t` its world-0 copy: the wire depends on the NOT.
* `canonPt A`: the point whose true coordinates are those of `A`. Canonical atoms are
  `canonPt (insert (u t) m)` for an injective `u : Fin k → Fin N` into the set `S` and a base `m`
  (`m = ∅` or `{y}` in world 1, a minterm of the NOT input in world 0).
* `canon_atoms_le`, `canon_size_pt`, `canon_disjoint` (W0 and W1), `canon_cross` (X): the same
  for canonical atoms and sets `S`, `S'` with `|S ∩ S'| ≤ 1`. The zero point of the second system
  may be false on `S'` and on a further set `Y` (`Y = {y}` for a world-0 zero point).

Fully proved; nothing here is used by the open statement yet.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CanonClass

variable {N k k' : ℕ}

/-- **GM.** Lemma M for a general test system: zero point `z`, atoms `a t`, one distinguished
coordinate `u t` per atom, and every coordinate that is false at `z` and true at the atom `a t`
is `u t`. No order between `z` and the atoms is assumed. -/
theorem canon_size (gs : List Gate) (hm : MonoList gs) (z : Fin N → Bool)
    (a : Fin k → Fin N → Bool) (u : Fin k → Fin N) (hu : Function.Injective u)
    (hL : ∀ c : Fin N, z c = false → ∀ t, a t c = true → c = u t)
    (o : ℕ) (hzo : val gs z o = false) (hao : ∀ t, val gs (a t) o = true) :
    ∃ M : Finset ℕ, M ⊆ orClz gs z a ∧ k - 1 ≤ M.card := by
  obtain ⟨M, hM, hk, -⟩ := lift_merges_pt gs hm z a
    (fun c hc s t hs ht => hu ((hL c hc s hs).symm.trans (hL c hc t ht))) o hzo hao
  exact ⟨M, hM, hk⟩

/-- **D.** If of any two atoms of the first system one lies below the zero point of the second
system, the two classes are disjoint. -/
theorem orClz_disjoint (gs : List Gate) (hm : MonoList gs) (z z' : Fin N → Bool)
    (a : Fin k → Fin N → Bool) (a' : Fin k' → Fin N → Bool)
    (h : ∀ s t : Fin k, s ≠ t → a s ≤ z' ∨ a t ≤ z') :
    Disjoint (orClz gs z a) (orClz gs z' a') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨-, -, -, hc⟩ := mem_orClz.mp hj
  obtain ⟨-, -, hz', -⟩ := mem_orClz.mp hj'
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hc
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hm g hg).1
  rcases h s t hst with hle | hle
  · have hv := val_le_of_le gs hops hle (N + j)
    rw [mem_atomsAt.mp hs, hz'] at hv
    exact absurd hv (by decide)
  · have hv := val_le_of_le gs hops hle (N + j)
    rw [mem_atomsAt.mp ht, hz'] at hv
    exact absurd hv (by decide)

/-- **X.** A gate in both classes, where the copies `a0` of the first system's atoms satisfy the
hypothesis of `orClz_disjoint`, is true at some atom `a t` and false at its copy `a0 t`. -/
theorem orClz_cross (gs : List Gate) (hm : MonoList gs) (z z' : Fin N → Bool)
    (a a0 : Fin k → Fin N → Bool) (a' : Fin k' → Fin N → Bool)
    (h : ∀ s t : Fin k, s ≠ t → a0 s ≤ z' ∨ a0 t ≤ z') {j : ℕ}
    (hj : j ∈ orClz gs z a) (hj' : j ∈ orClz gs z' a') :
    ∃ t, val gs (a t) (N + j) = true ∧ val gs (a0 t) (N + j) = false := by
  by_contra hcon
  obtain ⟨hlt, hor, hz, hc⟩ := mem_orClz.mp hj
  have hsub : atomsAt gs a (N + j) ⊆ atomsAt gs a0 (N + j) := by
    intro t ht
    rw [mem_atomsAt] at ht ⊢
    by_contra hne
    exact hcon ⟨t, ht, by simpa using hne⟩
  have hc0 : 1 < (atomsAt gs a0 (N + j)).card := lt_of_lt_of_le hc (Finset.card_le_card hsub)
  have hj0 : j ∈ orClz gs z a0 := mem_orClz.mpr ⟨hlt, hor, hz, hc0⟩
  exact Finset.disjoint_left.mp (orClz_disjoint gs hm z z' a0 a' h) hj0 hj'

/-- The point whose true coordinates are exactly those of `A`. -/
def canonPt (A : Finset (Fin N)) : Fin N → Bool := fun c => decide (c ∈ A)

theorem canonPt_eq_true {A : Finset (Fin N)} {c : Fin N} : canonPt A c = true ↔ c ∈ A := by
  simp [canonPt]

/-- Canonical atoms `canonPt (insert (u t) m)`, `u` injective into `S`: if `|S ∩ S'| ≤ 1`, the base
`m` avoids `S'` and `Y`, no `u t` is in `Y`, and `z'` is false only on `S' ∪ Y`, then of any two
atoms one lies below `z'`. -/
theorem canon_atoms_le (S S' m Y : Finset (Fin N)) (hSS : (S ∩ S').card ≤ 1)
    (hmS' : Disjoint m S') (hmY : Disjoint m Y) (u : Fin k → Fin N)
    (hu : Function.Injective u) (huS : ∀ t, u t ∈ S) (huY : ∀ t, u t ∉ Y)
    (z' : Fin N → Bool) (hz' : ∀ c, z' c = false → c ∈ S' ∨ c ∈ Y) :
    ∀ s t : Fin k, s ≠ t → canonPt (insert (u s) m) ≤ z' ∨ canonPt (insert (u t) m) ≤ z' := by
  have key : ∀ t : Fin k, u t ∉ S' → canonPt (insert (u t) m) ≤ z' := by
    intro t ht c
    refine Bool.le_iff_imp.mpr fun hc => ?_
    by_contra hne
    have hcm : c ∈ insert (u t) m := canonPt_eq_true.mp hc
    rcases hz' c (by simpa using hne) with hS' | hY
    · rcases Finset.mem_insert.mp hcm with rfl | hcm
      · exact ht hS'
      · exact Finset.disjoint_left.mp hmS' hcm hS'
    · rcases Finset.mem_insert.mp hcm with rfl | hcm
      · exact huY t hY
      · exact Finset.disjoint_left.mp hmY hcm hY
  intro s t hst
  by_cases hs : u s ∈ S'
  · right
    refine key t fun ht => ?_
    have hsub : ({u s, u t} : Finset (Fin N)) ⊆ S ∩ S' := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact Finset.mem_inter.mpr ⟨huS s, hs⟩
      · rw [Finset.mem_singleton.mp hc]
        exact Finset.mem_inter.mpr ⟨huS t, ht⟩
    have h2 : ({u s, u t} : Finset (Fin N)).card = 2 := Finset.card_pair fun h => hst (hu h)
    have h3 := Finset.card_le_card hsub
    omega
  · exact Or.inl (key s hs)

/-- **GM for canonical atoms.** Zero point `z` false only on `S ∪ Y`, base `m` avoiding `S` and
`Y`: at least `k - 1` gates in the class. -/
theorem canon_size_pt (gs : List Gate) (hm : MonoList gs) (S m Y : Finset (Fin N))
    (hmS : Disjoint m S) (hmY : Disjoint m Y) (u : Fin k → Fin N)
    (hu : Function.Injective u) (z : Fin N → Bool) (hz : ∀ c, z c = false → c ∈ S ∨ c ∈ Y)
    (o : ℕ) (hzo : val gs z o = false)
    (hao : ∀ t, val gs (canonPt (insert (u t) m)) o = true) :
    ∃ M : Finset ℕ, M ⊆ orClz gs z (fun t => canonPt (insert (u t) m)) ∧ k - 1 ≤ M.card := by
  refine canon_size gs hm z _ u hu (fun c hc t ht => ?_) o hzo hao
  have hcm : c ∈ insert (u t) m := canonPt_eq_true.mp ht
  rcases Finset.mem_insert.mp hcm with h | h
  · exact h
  · rcases hz c hc with hS | hY
    · exact absurd hS (Finset.disjoint_left.mp hmS h)
    · exact absurd hY (Finset.disjoint_left.mp hmY h)

/-- **W0 and W1.** Canonical classes of two sets with `|S ∩ S'| ≤ 1` are disjoint when the base
`m` of the first avoids `S'`: `m = ∅` (or `{y}`) in world 1, a minterm of the NOT input that
avoids `S'` in world 0. -/
theorem canon_disjoint (gs : List Gate) (hm : MonoList gs) (S S' m Y : Finset (Fin N))
    (hSS : (S ∩ S').card ≤ 1) (hmS' : Disjoint m S') (hmY : Disjoint m Y) (u : Fin k → Fin N)
    (hu : Function.Injective u) (huS : ∀ t, u t ∈ S) (huY : ∀ t, u t ∉ Y)
    (z z' : Fin N → Bool) (hz' : ∀ c, z' c = false → c ∈ S' ∨ c ∈ Y)
    (a' : Fin k' → Fin N → Bool) :
    Disjoint (orClz gs z (fun t => canonPt (insert (u t) m))) (orClz gs z' a') :=
  orClz_disjoint gs hm z z' _ a' (canon_atoms_le S S' m Y hSS hmS' hmY u hu huS huY z' hz')

/-- **X for canonical atoms.** A gate in the class of `S` with base `m` and in a class with zero
point `z'` (false only on `S' ∪ Y`) is true at an atom with base `m` and false at the same atom
with base `m0`, where `m0` avoids `S'` and `Y`. With `m = {y}`, `m0 = ∅`, `Y = {y}`: the wire is
true at `e_u` with the NOT at 1 and false at `e_u` with the NOT at 0. -/
theorem canon_cross (gs : List Gate) (hm : MonoList gs) (S S' m m0 Y : Finset (Fin N))
    (hSS : (S ∩ S').card ≤ 1) (hm0S' : Disjoint m0 S') (hm0Y : Disjoint m0 Y)
    (u : Fin k → Fin N) (hu : Function.Injective u) (huS : ∀ t, u t ∈ S) (huY : ∀ t, u t ∉ Y)
    (z z' : Fin N → Bool) (hz' : ∀ c, z' c = false → c ∈ S' ∨ c ∈ Y)
    (a' : Fin k' → Fin N → Bool) {j : ℕ}
    (hj : j ∈ orClz gs z (fun t => canonPt (insert (u t) m))) (hj' : j ∈ orClz gs z' a') :
    ∃ t, val gs (canonPt (insert (u t) m)) (N + j) = true ∧
      val gs (canonPt (insert (u t) m0)) (N + j) = false :=
  orClz_cross gs hm z z' _ (fun t => canonPt (insert (u t) m0)) a'
    (canon_atoms_le S S' m0 Y hSS hm0S' hm0Y u hu huS huY z' hz') hj hj'

end CanonClass

end PEqualNP.Outside.L_meta_951_aux
