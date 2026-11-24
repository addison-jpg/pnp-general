import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Count

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Cleanup: deleting a gate that copies an earlier wire -/

def redir (p j i : ℕ) : ℕ := if i < p then i else if i = p then j else i - 1

def redirG (p j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redir p j)⟩

theorem getD_eraseIdx_redir (acc : List Bool) (p j i : ℕ) (hp : p < acc.length) (hj : j < p)
    (heq : acc.getD p false = acc.getD j false) :
    (acc.eraseIdx p).getD (redir p j i) false = acc.getD i false := by
  unfold redir
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases h1 : i < p
  · simp [h1]
  · by_cases h2 : i = p
    · subst h2
      simp only [List.getD_eq_getElem?_getD] at heq
      simp [hj, heq]
    · have h3 : ¬ (i - 1 < p) := by omega
      simp only [h1, h2, h3, if_false]
      congr 2
      omega

theorem eraseIdx_snoc (acc : List Bool) (b : Bool) (p : ℕ) (hp : p < acc.length) :
    (acc ++ [b]).eraseIdx p = acc.eraseIdx p ++ [b] := by
  rw [List.eraseIdx_append_of_lt_length hp]

/-- Generic induction behind `fold_redir` / `fold_redir_dead`: an invariant `I` on the remaining
gates and the accumulator that makes one `step` commute with `eraseIdx p`. -/
theorem fold_redir_gen (p j : ℕ) (I : List Gate → List Bool → Prop)
    (hstep : ∀ g rest acc, p < acc.length → I (g :: rest) acc →
      step (acc.eraseIdx p) (redirG p j g) = (step acc g).eraseIdx p)
    (hnext : ∀ g rest acc, p < acc.length → I (g :: rest) acc → I rest (step acc g)) :
    ∀ (rest : List Gate) (acc : List Bool), p < acc.length → I rest acc →
    (rest.map (redirG p j)).foldl step (acc.eraseIdx p) = (rest.foldl step acc).eraseIdx p := by
  intro rest
  induction rest with
  | nil => intro acc _ _; simp
  | cons g rest ih =>
    intro acc hp hI
    simp only [List.map_cons, List.foldl_cons]
    rw [hstep g rest acc hp hI]
    exact ih _ (by unfold step; simp; omega) (hnext g rest acc hp hI)

theorem fold_redir (p j : ℕ) (hj : j < p) : ∀ (rest : List Gate) (acc : List Bool),
    p < acc.length → acc.getD p false = acc.getD j false →
    (rest.map (redirG p j)).foldl step (acc.eraseIdx p) = (rest.foldl step acc).eraseIdx p := by
  refine fun rest acc hp heq => fold_redir_gen p j (fun _ acc => acc.getD p false = acc.getD j false)
    ?_ ?_ rest acc hp heq
  · intro g _ acc hp heq
    unfold step redirG
    rw [eraseIdx_snoc _ _ _ hp]
    congr 2
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact getD_eraseIdx_redir acc p j i hp hj heq
  · intro g _ acc hp heq
    unfold step
    simp only [List.getD_eq_getElem?_getD] at heq ⊢
    rw [List.getElem?_append_left hp, List.getElem?_append_left (by omega)]
    exact heq

theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_erase (w : List Bool) (g : Gate) : (step w g).eraseIdx w.length = w := by
  unfold step
  rw [List.eraseIdx_append_of_length_le (le_refl _)]
  simp

def dropGate (gates : List Gate) (k j : ℕ) (n : ℕ) : List Gate :=
  gates.take k ++ (gates.drop (k + 1)).map (redirG (n + k) j)

theorem dropGate_length (gates : List Gate) (k j n : ℕ) (hk : k < gates.length) :
    (dropGate gates k j n).length + 1 = gates.length := by
  unfold dropGate; simp; omega

theorem val_dropGate {n : ℕ} (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hj : j < n + k) (hcopy : ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (x : Fin n → Bool) (i : ℕ) :
    val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i := by
  have hsplit : gates = gates.take k ++ gates[k] :: gates.drop (k + 1) := by
    simp
  set A := gates.take k with hA
  set B := gates.drop (k + 1) with hB
  set g := gates[k] with hg
  have hAl : A.length = k := by rw [hA]; simp; omega
  set acc0 := step (A.foldl step (List.ofFn x)) g with hacc0
  have hlA : (A.foldl step (List.ofFn x)).length = n + k := by
    rw [fold_length]; simp [hAl]
  have hl0 : acc0.length = n + k + 1 := by
    rw [hacc0, step_length, hlA]
  have hfull : gates.foldl step (List.ofFn x) = B.foldl step acc0 := by
    conv_lhs => rw [hsplit]
    simp [List.foldl_append, hacc0]
  have herase : acc0.eraseIdx (n + k) = A.foldl step (List.ofFn x) := by
    rw [hacc0, ← hlA]; exact step_erase _ _
  obtain ⟨r, hr⟩ := fold_prefix B acc0
  have heq0 : acc0.getD (n + k) false = acc0.getD j false := by
    have h := hcopy x
    unfold val at h
    rw [hfull, hr] at h
    simp only [List.getD_eq_getElem?_getD] at h ⊢
    rwa [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at h
  have hdrop : (dropGate gates k j n).foldl step (List.ofFn x) =
      (B.foldl step acc0).eraseIdx (n + k) := by
    unfold dropGate
    rw [List.foldl_append, ← herase]
    exact fold_redir (n + k) j hj B acc0 (by omega) heq0
  unfold val
  rw [hdrop, hfull]
  have hpB : n + k < (B.foldl step acc0).length := by rw [hr]; simp; omega
  have heqB : (B.foldl step acc0).getD (n + k) false = (B.foldl step acc0).getD j false := by
    simp only [List.getD_eq_getElem?_getD] at heq0 ⊢
    rw [hr, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact heq0
  exact getD_eraseIdx_redir _ _ _ _ hpB hj heqB

theorem getD_eraseIdx_ne (acc : List Bool) (p j i : ℕ) (hi : i ≠ p) :
    (acc.eraseIdx p).getD (redir p j i) false = acc.getD i false := by
  unfold redir
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases h1 : i < p
  · simp [h1]
  · have h3 : ¬ (i - 1 < p) := by omega
    simp only [h1, hi, h3, if_false]
    congr 2
    omega

theorem fold_redir_dead (p j : ℕ) : ∀ (rest : List Gate) (acc : List Bool),
    p < acc.length → (∀ g ∈ rest, p ∉ g.inputs) →
    (rest.map (redirG p j)).foldl step (acc.eraseIdx p) = (rest.foldl step acc).eraseIdx p := by
  refine fold_redir_gen p j (fun rest _ => ∀ g ∈ rest, p ∉ g.inputs) ?_ ?_
  · intro g _ acc hp hno
    unfold step redirG
    rw [eraseIdx_snoc _ _ _ hp]
    congr 2
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ p := fun h => hno g (by simp) (h ▸ hi)
    exact getD_eraseIdx_ne acc p j i hne
  · intro g rest _ _ hno g' hg'
    exact hno g' (by simp [hg'])

theorem val_dropDead {n : ℕ} (gates : List Gate) (k j : ℕ) (hk : k < gates.length)
    (hno : ∀ g ∈ gates, (n + k) ∉ g.inputs) (x : Fin n → Bool) (i : ℕ) (hi : i ≠ n + k) :
    val (dropGate gates k j n) x (redir (n + k) j i) = val gates x i := by
  have hsplit : gates = gates.take k ++ gates[k] :: gates.drop (k + 1) := by simp
  set A := gates.take k with hA
  set B := gates.drop (k + 1) with hB
  set g := gates[k] with hg
  have hAl : A.length = k := by rw [hA]; simp; omega
  set acc0 := step (A.foldl step (List.ofFn x)) g with hacc0
  have hlA : (A.foldl step (List.ofFn x)).length = n + k := by
    rw [fold_length]; simp [hAl]
  have hl0 : acc0.length = n + k + 1 := by rw [hacc0, step_length, hlA]
  have hfull : gates.foldl step (List.ofFn x) = B.foldl step acc0 := by
    conv_lhs => rw [hsplit]
    simp [List.foldl_append, hacc0]
  have herase : acc0.eraseIdx (n + k) = A.foldl step (List.ofFn x) := by
    rw [hacc0, ← hlA]; exact step_erase _ _
  have hnoB : ∀ g' ∈ B, (n + k) ∉ g'.inputs := fun g' hg' => hno g' (List.mem_of_mem_drop hg')
  have hdrop : (dropGate gates k j n).foldl step (List.ofFn x) =
      (B.foldl step acc0).eraseIdx (n + k) := by
    unfold dropGate
    rw [List.foldl_append, ← herase]
    exact fold_redir_dead (n + k) j B acc0 (by omega) hnoB
  unfold val
  rw [hdrop, hfull]
  exact getD_eraseIdx_ne _ _ _ _ hi

end PEqualNP.Outside.L_meta_951_aux
