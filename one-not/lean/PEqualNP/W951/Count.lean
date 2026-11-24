import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MergeRunT

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

def Zof {n : ℕ} (Q : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ Q)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

/-- The counting lemma for general test systems: if every test point `p u` (`u ∈ R`) is false at
every coordinate where `z` is false, except at `u` itself, then the counted wires number at least
`|R|` minus the number of final classes. The final labelling of the union-find run
(`merge_runT`); its merge set lies in `DT`. -/
theorem main_invT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (gs : List Gate) (hgood : GoodT z p R gs) :
    ∃ l : Fin n → Fin n, InvT z p R gs l ∧ R.card ≤ (R.image l).card + (DT z p R gs).card := by
  obtain ⟨L, M, -, -, -, hinv, hcard, hsub, -⟩ := merge_runT z p R gs hT hgood
  exact ⟨L gs.length, hinv,
    (hcard gs.length).trans (Nat.add_le_add_left (Finset.card_le_card (hsub gs.length)) _)⟩

def Good {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (rest : List Gate), gs = pre ++ g :: rest →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
      g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true ∨
      ∀ u : Fin n, g.op.eval (g.inputs.map fun j => val pre (eof u) j) = false

def Inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof Q) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ Q ∧ (u ∈ R → v ∈ R → l u = l v)

def Cnt {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof Q) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ u ∈ R ∧ v ∈ R ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt Q R gs i

theorem D_mono {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D Q R gs ⊆ D Q R (gs ++ [g]) := DT_mono (Zof Q) eof R gs g

/-- Wires true at a unit test point `eof u` and false at `Zof Q` have `u ∈ Q`. -/
theorem mem_of_good {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs)
    (i : ℕ) (u : Fin n) (hz : val gs (Zof Q) i = false) (hu : val gs (eof u) i = true) :
    u ∈ Q := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    rw [val_nil] at hz hu
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu
      subst hu
      exact hz
    · simp [h] at hu
  | append_singleton gs g ih =>
    have hgood' : Good Q gs := by
      intro pre g' rest h
      exact hgood pre g' (rest ++ [g]) (by rw [h]; simp)
    have hg := hgood gs g [] (by simp)
    rw [val_snoc] at hz hu
    by_cases hi : i = n + gs.length
    · rw [if_pos hi] at hz hu
      obtain ⟨hop, hlen⟩ : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        rcases hg with h | h | h
        · exact h
        · exact absurd hz (by rw [h]; simp)
        · exact absurd hu (by rw [h u]; simp)
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof Q) with hall | ⟨a, b, hab⟩
      · exact absurd hu (by rw [hall (eof u)]; simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        rcases hy (eof u) hu with h | h
        · exact ih hgood' a ha h
        · exact ih hgood' b hb h
    · rw [if_neg hi] at hz hu
      exact ih hgood' i hz hu

theorem main_inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) :
    ∃ l : Fin n → Fin n, Inv Q R gs l ∧ R.card ≤ (R.image l).card + (D Q R gs).card := by
  have hT : ∀ u ∈ R, ∀ c : Fin n, eof u c = true → Zof Q c = false → c = u := by
    intro u _ c hc _
    simpa [eof] using hc
  have hG : GoodT (Zof Q) eof R gs := by
    intro pre g rest h
    rcases hgood pre g rest h with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr fun u _ v _ hu _ => ?_)
      rw [h1 u] at hu
      exact absurd hu (by simp)
  obtain ⟨l, hinv, hcard⟩ := main_invT (Zof Q) eof R hT gs hG
  exact ⟨l, fun i u v hz hu hv =>
    ⟨mem_of_good Q gs hgood i u hz hu, hinv i u v hz hu hv⟩, hcard⟩

end PEqualNP.Outside.L_meta_951_aux
