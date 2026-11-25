import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.Cases

-- Two-World reduction (front's Opus C note w6_opusC.md, Theorem DD0), formalized.
-- C0 / C1 replace every NOT gate by the constant false / true. Every wire satisfies
-- C0 <= real <= C1 (sandwich), for any number of NOT gates. A set S is DD when
-- C1 is true at the zero point of S and C0 misses some unit vector of S. If no set is DD,
-- each set is counted either in C1 (zero point Z_S) or in C0 (unit vectors), the counts are
-- pairwise disjoint, and the gate bound follows.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The circuit with every NOT gate replaced by the constant false. -/
def C0 (gates : List Gate) : List Gate := gates.map (constNot GateOp.or)

/-- The circuit with every NOT gate replaced by the constant true. -/
def C1 (gates : List Gate) : List Gate := gates.map (constNot GateOp.and)

theorem sandwich {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x : Fin n → Bool) :
    ∀ i, (val (C0 gates) x i = true → val gates x i = true) ∧
      (val gates x i = true → val (C1 gates) x i = true) := by
  have h0 := PEqualNP.Kernel.listVal_le gates (constNot GateOp.or) id x x (fun _ h => h)
    fun a ha v v' hv => by
      obtain ⟨op, ins⟩ := a
      rcases hg _ ha with h | h | h <;> simp only at h <;> subst h
      · exact PEqualNP.Kernel.listOp_mono (Or.inl rfl) ins hv
      · exact PEqualNP.Kernel.listOp_mono (Or.inr rfl) ins hv
      · simp [constNot, GateOp.eval]
  have h1 := PEqualNP.Kernel.listVal_le gates id (constNot GateOp.and) x x (fun _ h => h)
    fun a ha v v' hv => by
      obtain ⟨op, ins⟩ := a
      rcases hg _ ha with h | h | h <;> simp only at h <;> subst h
      · exact PEqualNP.Kernel.listOp_mono (Or.inl rfl) ins hv
      · exact PEqualNP.Kernel.listOp_mono (Or.inr rfl) ins hv
      · simp [constNot, GateOp.eval]
  rw [List.map_id] at h0 h1
  exact fun i => ⟨h0 i, h1 i⟩

theorem good_const {n : ℕ} (b : GateOp) (hb : b = GateOp.and ∨ b = GateOp.or)
    (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (Q : Finset (Fin n)) : Good Q (gates.map (constNot b)) := by
  intro pre g rest h
  obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp (show g ∈ gates.map (constNot b) by rw [h]; simp)
  obtain ⟨hop, hlen⟩ := hg g0 h0
  obtain ⟨op, ins⟩ := g0
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> simp [constNot, hlen]

/-- One world: a circuit that is `Good` at `Z_S`, false there at the output, true at every unit
vector of `S`, counts at least `|S| - 1` wires. -/
theorem count_world {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (hgood : Good S gs) (hz : val gs (Zof S) o = false)
    (hu : ∀ u ∈ S, val gs (eof u) o = true) : S.card - 1 ≤ (D S S gs).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ := main_inv S S gs hgood
  have h1 : (S.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hb
    exact (hinv o u v hz (hu u hu') (hu v hv')).2 hu' hv'
  omega

/-- The world chosen for set `w`: C1 when C1 is false at `Z_S`, otherwise C0. -/
noncomputable def worldCount {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (w : Fin m) : Finset ℕ :=
  if val (C1 gates) (Zof (S w)) (out w) = false then D (S w) (S w) (C1 gates)
  else D (S w) (S w) (C0 gates)

theorem pair_card {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n) (huv : u ≠ v)
    (hu : u ∈ A ∩ B) (hv : v ∈ A ∩ B) : 2 ≤ (A ∩ B).card :=
  Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩

/-- If no set is DD, the gate bound holds (any number of NOT gates). -/
theorem bound_of_noDD {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hno : ∀ w, val (C1 gates) (Zof (S w)) (out w) = false ∨
      ∀ u ∈ S w, val (C0 gates) (eof u) (out w) = true) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  have hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hm => (hg g hm).1
  have sw := fun (x : Fin n → Bool) => sandwich gates hops x
  have g0 : ∀ Q : Finset (Fin n), Good Q (C0 gates) :=
    good_const GateOp.or (Or.inr rfl) gates hg
  have g1 : ∀ Q : Finset (Fin n), Good Q (C1 gates) :=
    good_const GateOp.and (Or.inl rfl) gates hg
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false :=
    zero_of_sub S S gates out hev (fun _ => subset_rfl)
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true :=
    fun w u hu => eof_true S gates out hev w u hu
  -- each world counts |S| - 1
  have hbound : ∀ w, (S w).card - 1 ≤ (worldCount S gates out w).card := by
    intro w
    unfold worldCount
    split_ifs with h1
    · exact count_world (S w) (C1 gates) (out w) (g1 _) h1
        (fun u hu => ((sw (eof u)) (out w)).2 (hE w u hu))
    · have h0 : val (C0 gates) (Zof (S w)) (out w) = false := by
        cases hc : val (C0 gates) (Zof (S w)) (out w)
        · rfl
        · have := ((sw (Zof (S w))) (out w)).1 hc
          rw [hZ w] at this
          exact absurd this (by simp)
      have hu : ∀ u ∈ S w, val (C0 gates) (eof u) (out w) = true := by
        rcases hno w with h | h
        · exact absurd h h1
        · exact h
      exact count_world (S w) (C0 gates) (out w) (g0 _) h0 hu
  -- membership facts
  have mem : ∀ w i, i ∈ worldCount S gates out w →
      i ∈ Finset.Ico n (n + gates.length) ∧
      ((val (C1 gates) (Zof (S w)) i = false ∧
          ∃ u v, u ≠ v ∧ u ∈ S w ∧ v ∈ S w ∧
            val (C1 gates) (eof u) i = true ∧ val (C1 gates) (eof v) i = true) ∨
        (val (C0 gates) (Zof (S w)) i = false ∧
          ∃ u v, u ≠ v ∧ u ∈ S w ∧ v ∈ S w ∧
            val (C0 gates) (eof u) i = true ∧ val (C0 gates) (eof v) i = true)) := by
    intro w i hi
    unfold worldCount at hi
    split_ifs at hi
    · simp only [D, Finset.mem_filter, Cnt, C1, List.length_map] at hi
      exact ⟨hi.1, Or.inl hi.2⟩
    · simp only [D, Finset.mem_filter, Cnt, C0, List.length_map] at hi
      exact ⟨hi.1, Or.inr hi.2⟩
  -- a wire counted for a (any world) is true in C1 at two units of S a
  have up : ∀ w i, i ∈ worldCount S gates out w →
      ∃ u v, u ≠ v ∧ u ∈ S w ∧ v ∈ S w ∧
        val (C1 gates) (eof u) i = true ∧ val (C1 gates) (eof v) i = true := by
    intro w i hi
    rcases (mem w i hi).2 with ⟨-, u, v, huv, hu, hv, h1, h2⟩ | ⟨-, u, v, huv, hu, hv, h1, h2⟩
    · exact ⟨u, v, huv, hu, hv, h1, h2⟩
    · exact ⟨u, v, huv, hu, hv, ((sw (eof u)) i).2 (((sw (eof u)) i).1 h1),
        ((sw (eof v)) i).2 (((sw (eof v)) i).1 h2)⟩
  have side : ∀ a b : Fin m, a ≠ b → ∀ i, i ∈ worldCount S gates out a →
      i ∈ worldCount S gates out b → False := by
    intro a b hab i ha hb
    -- if b is in world C1: a's C1-units lie in S b
    rcases (mem b i hb).2 with ⟨hzb, -⟩ | ⟨hzb0, ub, vb, huvb, hub, hvb, h1b, h2b⟩
    · obtain ⟨u, v, huv, hu, hv, h1, h2⟩ := up a i ha
      have hub := inv_mem (S b) (C1 gates) (g1 _) i u hzb h1
      have hvb := inv_mem (S b) (C1 gates) (g1 _) i v hzb h2
      have := pair_card (S a) (S b) u v huv (Finset.mem_inter.mpr ⟨hu, hub⟩)
        (Finset.mem_inter.mpr ⟨hv, hvb⟩)
      have := hS a b hab
      omega
    · -- b in world C0; look at a's world
      rcases (mem a i ha).2 with ⟨hza, -⟩ | ⟨hza0, -⟩
      · -- a in C1: b's C0-units are C1-units, so lie in S a
        have h1' := ((sw (eof ub)) i).2 (((sw (eof ub)) i).1 h1b)
        have h2' := ((sw (eof vb)) i).2 (((sw (eof vb)) i).1 h2b)
        have hua := inv_mem (S a) (C1 gates) (g1 _) i ub hza h1'
        have hva := inv_mem (S a) (C1 gates) (g1 _) i vb hza h2'
        have := pair_card (S a) (S b) ub vb huvb (Finset.mem_inter.mpr ⟨hua, hub⟩)
          (Finset.mem_inter.mpr ⟨hva, hvb⟩)
        have := hS a b hab
        omega
      · -- both in C0
        have hua := inv_mem (S a) (C0 gates) (g0 _) i ub hza0 h1b
        have hva := inv_mem (S a) (C0 gates) (g0 _) i vb hza0 h2b
        have := pair_card (S a) (S b) ub vb huvb (Finset.mem_inter.mpr ⟨hua, hub⟩)
          (Finset.mem_inter.mpr ⟨hva, hvb⟩)
        have := hS a b hab
        omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (worldCount S gates out a) (worldCount S gates out b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    exact fun i hia hib => side a b hab i hia hib
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, (worldCount S gates out w).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ ≤ (Finset.Ico n (n + gates.length)).card :=
        PEqualNP.Base.Matching.sum_card_le_of_pairwiseDisjoint _ _ _ hdisj fun w _ i hi => (mem w i hi).1
    _ = gates.length := by simp

end PEqualNP.Outside.L_meta_951_aux
