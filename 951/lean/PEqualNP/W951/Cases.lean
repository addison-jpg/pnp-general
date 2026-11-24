import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.Cone
import PEqualNP.Kernel.W951Extra

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Special case (b): every set is easy (`Good (S w) gates`) -/

/-! ## Reduction of `Good` to the NOT gates being true at the zero point -/

def NotQuiet {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ pre g rest, gs = pre ++ g :: rest → g.op = GateOp.not →
    g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true

theorem good_of_quiet {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hq : NotQuiet Q gs) : Good Q gs := by
  intro pre g rest h
  have hmem : g ∈ gs := by rw [h]; simp
  rcases (hg g hmem).1 with h1 | h1 | h1
  · exact Or.inl ⟨Or.inl h1, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr h1, (hg g hmem).2⟩
  · exact Or.inr (Or.inl (hq pre g rest h h1))

/-- Special case (a): every NOT gate reads a wire that does not exist yet (or nothing). -/
theorem notquiet_of_dangling {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate)
    (hd : ∀ pre g rest, gs = pre ++ g :: rest → g.op = GateOp.not →
      ∀ j, g.inputs.head? = some j → n + pre.length ≤ j) : NotQuiet Q gs := by
  intro pre g rest h hop
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons j r =>
    have hj := hd pre g rest h hop j (by simp [hi])
    simp [GateOp.eval, val_ge pre (Zof Q) j hj]

theorem mono_val {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  simpa using PEqualNP.Kernel.listVal_le gs id id x y hxy
    fun a ha _ _ hv => PEqualNP.Kernel.listOp_mono (hg a ha) _ hv

def AtMostOneNot (gates : List Gate) : Prop :=
  ∀ (i1 i2 : ℕ) (h1 : i1 < gates.length) (h2 : i2 < gates.length),
    (gates[i1]'h1).op = GateOp.not → (gates[i2]'h2).op = GateOp.not → i1 = i2

theorem hU_of_ι {gates : List Gate}
    (hι : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) : AtMostOneNot gates := by
  obtain ⟨ι, hι⟩ := hι
  intro i1 i2 h1 h2 e1 e2
  obtain ⟨j1, hj1⟩ := hι ⟨i1, h1⟩ (by simpa using e1)
  obtain ⟨j2, hj2⟩ := hι ⟨i2, h2⟩ (by simpa using e2)
  have : j1 = j2 := Subsingleton.elim _ _
  subst this
  have := congrArg Fin.val (hj1.symm.trans hj2)
  simpa using this

theorem not_index {gates : List Gate} (hU : AtMostOneNot gates)
    (p1 r1 p2 r2 : List Gate) (g1 g2 : Gate) (h1 : gates = p1 ++ g1 :: r1)
    (h2 : gates = p2 ++ g2 :: r2) (hn1 : g1.op = GateOp.not) (hn2 : g2.op = GateOp.not) :
    p1.length = p2.length := by
  have l1 : p1.length < gates.length := by rw [h1]; simp
  have l2 : p2.length < gates.length := by rw [h2]; simp
  apply hU _ _ l1 l2
  · have : gates[p1.length]'l1 = g1 := by subst h1; simp
    rw [this]; exact hn1
  · have : gates[p2.length]'l2 = g2 := by subst h2; simp
    rw [this]; exact hn2

/-- If the NOT gate is false at the all-false input, it is false at every unit input, so every
zero set is `Good`. -/
theorem good_all_of_dead {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hdead : ¬ NotQuiet (Finset.univ : Finset (Fin n)) gates) (Q : Finset (Fin n)) :
    Good Q gates := by
  classical
  unfold NotQuiet at hdead
  push_neg at hdead
  obtain ⟨pre0, g0, rest0, h0, hn0, hz0⟩ := hdead
  have hz0' : g0.op.eval (g0.inputs.map fun j => val pre0 (Zof (Finset.univ : Finset (Fin n))) j)
      = false := by simpa using hz0
  -- every gate before the NOT is AND/OR
  have hpre : ∀ g' ∈ pre0, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
    intro g' hm
    obtain ⟨p1, r1, hp⟩ := List.append_of_mem hm
    have hmem : g' ∈ gates := by rw [h0]; exact List.mem_append_left _ hm
    rcases (hg g' hmem).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hl := not_index hU p1 (r1 ++ g0 :: rest0) pre0 rest0 g' g0
        (by rw [h0, hp]; simp) h0 h hn0
      have : pre0.length = p1.length + 1 + r1.length := by rw [hp]; simp; omega
      omega
  -- the NOT is false at every unit input
  have hdeadu : ∀ u : Fin n,
      g0.op.eval (g0.inputs.map fun j => val pre0 (eof u) j) = false := by
    intro u
    rw [hn0] at hz0' ⊢
    cases hin : g0.inputs with
    | nil => rw [hin] at hz0'; simp [GateOp.eval] at hz0'
    | cons j r =>
      rw [hin] at hz0'
      simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_false'] at hz0' ⊢
      exact mono_val pre0 hpre _ _ (fun c hc => by simp [Zof] at hc) j hz0'
  intro pre g rest h
  have hmem : g ∈ gates := by rw [h]; simp
  rcases (hg g hmem).1 with ho | ho | ho
  · exact Or.inl ⟨Or.inl ho, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr ho, (hg g hmem).2⟩
  · right; right
    have hl := not_index hU pre rest pre0 rest0 g g0 h h0 ho hn0
    have hh : pre ++ g :: rest = pre0 ++ g0 :: rest0 := h.symm.trans h0
    obtain ⟨hp, ht⟩ := List.append_inj hh hl
    subst hp
    have : g = g0 := (List.cons.inj ht).1
    subst this
    exact hdeadu

/-- Theorem X: enlarged zero sets `Q w ⊇ S w`, every `Q w` good, and for each pair one of the
two cross intersections has at most one point. -/
theorem charge_of_pair {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (gates : List Gate)
    (hSQ : ∀ w, S w ⊆ Q w) (hgood : ∀ w, Good (Q w) gates)
    (hpair : ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1) :
    ChargeOK S gates := by
  classical
  refine ⟨Q, hSQ, hgood, ?_⟩
  have cross : ∀ a b : Fin m, ∀ i, i ∈ D (Q a) (S a) gates → val gates (Zof (Q b)) i = false →
      2 ≤ (S a ∩ Q b).card := by
    intro a b i hia hzb
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia
    obtain ⟨-, -, u, v, huv, huR, hvR, hu, hv⟩ := hia
    have hub := inv_mem (Q b) gates (hgood b) i u hzb hu
    have hvb := inv_mem (Q b) gates (hgood b) i v hzb hv
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨huR, hub⟩, v,
      Finset.mem_inter.mpr ⟨hvR, hvb⟩, huv⟩
  have side : ∀ a b : Fin m, a ≠ b → ∀ i, i ∈ D (Q a) (S a) gates →
      i ∈ D (Q b) (S b) gates → False := by
    intro a b hab i hia hib
    have hza : val gates (Zof (Q a)) i = false := by
      simp only [D, Finset.mem_filter] at hia; exact hia.2.1
    have hzb : val gates (Zof (Q b)) i = false := by
      simp only [D, Finset.mem_filter] at hib; exact hib.2.1
    have h1 := cross a b i hia hzb
    have h2 := cross b a i hib hza
    rcases hpair a b hab with h | h <;> omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Q a) (S a) gates) (D (Q b) (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    exact side a b hab i hia hib
  calc ∑ w, (D (Q w) (S w) gates).card
      ≤ (Finset.Ico n (n + gates.length)).card :=
        PEqualNP.Base.Matching.sum_card_le_of_pairwiseDisjoint _ _ _ hdisj fun w _ i hi => by
          simp only [D, Finset.mem_filter] at hi
          exact hi.1
    _ = gates.length := by simp

set_option linter.unusedVariables false in
/-- Special case (b) is `charge_of_pair` with `Q = S` (`out`, `hev` are kept for the callers). -/
theorem charge_of_good {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hgood : ∀ w, Good (S w) gates) : ChargeOK S gates :=
  charge_of_pair S S gates (fun _ => subset_rfl) hgood fun a b hab => Or.inl (hS a b hab)

/-- At most one hard set: easy sets keep `Q = S`, the hard set takes `Q = univ`
(its zero point is the all-false input). -/
theorem charge_one_hard {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (w0 : Fin m) (heasy : ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hzero : NotQuiet (Finset.univ : Finset (Fin n)) gates) : ChargeOK S gates := by
  classical
  let Q : Fin m → Finset (Fin n) := fun w => if w = w0 then Finset.univ else S w
  refine charge_of_pair S Q gates ?_ ?_ ?_
  · intro w
    by_cases h : w = w0
    · simp [Q, h]
    · simp [Q, h]
  · intro w
    by_cases h : w = w0
    · simp only [Q, h, if_true]; exact good_of_quiet _ _ hg hzero
    · simp only [Q, h, if_false]; exact good_of_quiet _ _ hg (heasy w h)
  · intro a b hab
    by_cases hb : b = w0
    · -- b is the hard set: use S b ∩ Q a = S b ∩ S a
      right
      have ha : a ≠ w0 := fun h => hab (h.trans hb.symm)
      simp only [Q, ha, if_false]
      exact hS b a (fun h => hab h.symm)
    · -- b is easy: S a ∩ Q b = S a ∩ S b
      left
      simp only [Q, hb, if_false]
      exact hS a b hab

def constNot (b : GateOp) : Gate → Gate
  | ⟨GateOp.not, _⟩ => ⟨b, []⟩
  | g => g

end PEqualNP.Outside.L_meta_951_aux
