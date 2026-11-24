import PEqualNP.Base.Matching.Duality
import PEqualNP.W951.MatchBase

/-! Price form of the fractional matching charge.

* `PriceIneq S gates out`: for every nonnegative price vector `π` on wires there are test systems
  `σ w` and sets `M w ⊆ (σ w).cnt` of exactly `|S w| - 1` counted wires whose total price is at
  most the price of all gate wires. (The systems may depend on `π`.)
* `bound_of_priceIneq`: the instance `π = 1` is the bound.
* `fracMatch_iff_priceIneq`: LP duality, `FracMatch ↔ PriceIneq`. `FracMatch` (`FracMatch.lean`)
  is the only fractional-matching notion; the proof passes through a private normal form
  (`FracMatchR`: a fractional choice of load at most one among the options `wireOpts`, the sets
  of exactly `|S w| - 1` gate wires counted by some test system).
* `PriceIneqHard`, `hardCase_of_priceIneq`: the price target on the hard case closes it. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- The price inequality: every nonnegative pricing of the wires admits test systems with
`|S w| - 1` counted wires each, of total price at most the price of all gate wires. -/
def PriceIneq {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    ∃ (σ : ∀ w, TestSys n gates (S w) (out w)) (M : Fin m → Finset ℕ),
      (∀ w, M w ⊆ (σ w).cnt) ∧ (∀ w, (M w).card = (S w).card - 1) ∧
      ∑ w, ∑ g ∈ M w, π g ≤ ∑ g ∈ Finset.Ico n (n + gates.length), π g

/-- The price inequality at `π = 1` is the bound. -/
theorem bound_of_priceIneq {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hp : PriceIneq S gates out) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  obtain ⟨σ, M, -, hcard, h⟩ := hp (fun _ => 1) (fun _ => zero_le_one)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico, add_tsub_cancel_left,
    hcard] at h
  exact_mod_cast h

/-- Gate wire number `i` as a wire. -/
def wireEmb (n L : ℕ) : Fin L ↪ ℕ := ⟨fun i => n + i, fun a b h => Fin.ext (by simpa using h)⟩

@[simp] theorem wireEmb_apply (n L : ℕ) (i : Fin L) : wireEmb n L i = n + i := rfl

/-- Every set of gate wires is the image of a set of gate indices. -/
theorem exists_map_wireEmb {n L : ℕ} {M : Finset ℕ} (hM : M ⊆ Finset.Ico n (n + L)) :
    ∃ A : Finset (Fin L), A.map (wireEmb n L) = M := by
  classical
  refine ⟨Finset.univ.filter fun i => n + (i : ℕ) ∈ M, ?_⟩
  ext g
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, wireEmb_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hg
    have h := Finset.mem_Ico.1 (hM hg)
    exact ⟨⟨g - n, by omega⟩, by simpa [Nat.add_sub_cancel' h.1] using hg,
      Nat.add_sub_cancel' h.1⟩

theorem sum_Ico_eq_sum_fin (n L : ℕ) (π : ℕ → ℝ) :
    ∑ g ∈ Finset.Ico n (n + L), π g = ∑ a : Fin L, π (n + a) := by
  rw [Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i => π (n + i))]
  simp

open Classical in
/-- The options of set `w`: sets of `|S w| - 1` gate indices whose wires are all counted by one
test system for `S w`. -/
noncomputable def wireOpts {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (w : Fin m) : Finset (Finset (Fin gates.length)) :=
  Finset.univ.filter fun A => A.card = (S w).card - 1 ∧
    ∃ σ : TestSys n gates (S w) (out w), A.map (wireEmb n gates.length) ⊆ σ.cnt

/-- Normal form of `FracMatch` (private): every set has an option, and some probability mixture
of options per set loads every gate wire at most once. -/
private def FracMatchR {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) : Prop :=
  (∀ w, (wireOpts S gates out w).Nonempty) ∧
    ∃ lam : Fin m → Finset (Fin gates.length) → ℝ,
      IsFracChoice (wireOpts S gates out) lam ∧ ∀ a, load (wireOpts S gates out) lam a ≤ 1

/-- LP duality for the normal form. -/
private theorem priceIneq_iff_fracMatchR {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ) : PriceIneq S gates out ↔ FracMatchR S gates out := by
  classical
  constructor
  · intro hp
    -- options from a solution of the price inequality
    have hopt : ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) → ∃ A : Fin m → Finset (Fin gates.length),
        (∀ w, A w ∈ wireOpts S gates out w) ∧
        ∑ w, ∑ a ∈ A w, π (n + a) ≤ ∑ a : Fin gates.length, π (n + a) := by
      intro π hπ
      obtain ⟨σ, M, hsub, hcard, h⟩ := hp π hπ
      choose A hA using fun w => exists_map_wireEmb ((hsub w).trans (σ w).cnt_subset)
      refine ⟨A, fun w => ?_, ?_⟩
      · simp only [wireOpts, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, σ w, by rw [hA w]; exact hsub w⟩
        rw [← hcard w, ← hA w, Finset.card_map]
      · rw [← sum_Ico_eq_sum_fin]
        refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) h
        rw [← hA w, Finset.sum_map]
        rfl
    have hO : ∀ w, (wireOpts S gates out w).Nonempty := by
      obtain ⟨A, hA, -⟩ := hopt (fun _ => 0) (fun _ => le_rfl)
      exact fun w => ⟨A w, hA w⟩
    refine ⟨hO, (exists_frac_iff_prices _ hO).2 fun π' hπ' => ?_⟩
    set π : ℕ → ℝ := fun g => if h : g - n < gates.length then π' ⟨g - n, h⟩ else 0 with hπdef
    have hπ : ∀ g, 0 ≤ π g := by
      intro g
      simp only [hπdef]
      split_ifs
      · exact hπ' _
      · exact le_rfl
    have hπe : ∀ a : Fin gates.length, π (n + a) = π' a := by
      intro a
      simp [hπdef]
    obtain ⟨A, hA, h⟩ := hopt π hπ
    simp only [hπe] at h
    exact (Finset.sum_le_sum fun w _ => Finset.inf'_le _ (hA w)).trans h
  · rintro ⟨hO, lam, hlam, hload⟩ π hπ
    have hw := sum_inf'_le_of_frac hO hlam hload (π := fun a => π (n + a)) (fun a => hπ _)
    choose A hAO hA using fun w =>
      Finset.exists_mem_eq_inf' (hO w) (fun M => ∑ a ∈ M, π (n + (a : ℕ)))
    have hAO' : ∀ w, (A w).card = (S w).card - 1 ∧
        ∃ σ : TestSys n gates (S w) (out w), (A w).map (wireEmb n gates.length) ⊆ σ.cnt := by
      intro w
      simpa [wireOpts] using hAO w
    choose hcard σ hσ using hAO'
    refine ⟨σ, fun w => (A w).map (wireEmb n gates.length), hσ, fun w => by
      rw [Finset.card_map, hcard w], ?_⟩
    rw [sum_Ico_eq_sum_fin]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) hw
    rw [hA w, Finset.sum_map]
    rfl

/-- `FracMatch` is equivalent to its normal form: truncate every `M w j` to exactly `|S w| - 1`
wires and push the weights onto the options; conversely enumerate the options of each set. -/
private theorem fracMatch_iff_fracMatchR {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ) : FracMatch S gates out ↔ FracMatchR S gates out := by
  classical
  constructor
  · rintro ⟨k, σ, lam, M, hlam0, hlam1, hMsub, hMcard, hload⟩
    choose M' hM'sub hM'card using fun w j => Finset.exists_subset_card_eq (hMcard w j)
    choose A hA using fun w j =>
      exists_map_wireEmb (((hM'sub w j).trans (hMsub w j)).trans (σ w j).cnt_subset)
    have hAO : ∀ w j, A w j ∈ wireOpts S gates out w := by
      intro w j
      simp only [wireOpts, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, σ w j, by rw [hA w j]; exact (hM'sub w j).trans (hMsub w j)⟩
      rw [← hM'card w j, ← hA w j, Finset.card_map]
    have hk : ∀ w, 0 < k w := by
      intro w
      by_contra h0
      have hk0 : k w = 0 := by omega
      have h1 := hlam1 w
      have hempty : IsEmpty (Fin (k w)) := by rw [hk0]; infer_instance
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
      exact zero_ne_one h1
    refine ⟨fun w => ⟨A w ⟨0, hk w⟩, hAO w _⟩,
      fun w B => ∑ j, (if A w j = B then lam w j else 0), ⟨fun w B => ?_, fun w B hB => ?_,
        fun w => ?_⟩, fun a => ?_⟩
    · exact Finset.sum_nonneg fun j _ => by split_ifs; exacts [hlam0 w j, le_rfl]
    · refine Finset.sum_eq_zero fun j _ => ite_eq_right ?_
      rintro rfl
      exact hB (hAO w j)
    · rw [Finset.sum_comm, ← hlam1 w]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq, ite_eq_left (hAO w j)]
    · refine le_trans ?_ (hload (n + a))
      unfold load
      refine Finset.sum_le_sum fun w _ => ?_
      calc ∑ B ∈ wireOpts S gates out w,
            (∑ j, (if A w j = B then lam w j else 0)) * (if a ∈ B then (1 : ℝ) else 0)
          = ∑ j, ∑ B ∈ wireOpts S gates out w,
              (if A w j = B then lam w j * (if a ∈ B then (1 : ℝ) else 0) else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun B _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
        _ = ∑ j, lam w j * (if a ∈ A w j then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_ite_eq, ite_eq_left (hAO w j)]
        _ ≤ ∑ j, (if n + (a : ℕ) ∈ M w j then lam w j else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases ha : a ∈ A w j
            · have hmem : n + (a : ℕ) ∈ M w j := by
                apply hM'sub w j
                rw [← hA w j]
                exact Finset.mem_map_of_mem (wireEmb n gates.length) ha
              simp [ha, hmem]
            · rw [ite_eq_right ha, mul_zero]
              split_ifs
              exacts [hlam0 w j, le_rfl]
  · rintro ⟨-, lam, ⟨hlam0, -, hlam1⟩, hload⟩
    set O := wireOpts S gates out with hOdef
    let e : ∀ w, Fin (O w).card ≃ {B // B ∈ O w} := fun w => (O w).equivFin.symm
    have hspec : ∀ w (B : {B // B ∈ O w}), B.1.card = (S w).card - 1 ∧
        ∃ σ : TestSys n gates (S w) (out w), B.1.map (wireEmb n gates.length) ⊆ σ.cnt := by
      intro w B
      simpa [hOdef, wireOpts] using B.2
    choose hcard σ hσ using hspec
    -- sums over the enumeration are sums over the options
    have hsum : ∀ (w : Fin m) (F : Finset (Fin gates.length) → ℝ),
        ∑ j, F (e w j).1 = ∑ B ∈ O w, F B := by
      intro w F
      exact PEqualNP.Base.Matching.sum_equivFin (O w) F
    refine ⟨fun w => (O w).card, fun w j => σ w (e w j), fun w j => lam w (e w j).1,
      fun w j => (e w j).1.map (wireEmb n gates.length), fun w j => hlam0 w _, fun w => ?_,
      fun w j => hσ w _, fun w j => by rw [Finset.card_map, hcard], fun g => ?_⟩
    · rw [hsum w (lam w)]
      exact hlam1 w
    · by_cases hg : g ∈ Finset.Ico n (n + gates.length)
      · have h := Finset.mem_Ico.1 hg
        set a : Fin gates.length := ⟨g - n, by omega⟩ with ha
        refine le_of_eq_of_le ?_ (hload a)
        unfold load
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← hsum w fun B => lam w B * (if a ∈ B then (1 : ℝ) else 0)]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hiff : g ∈ (e w j).1.map (wireEmb n gates.length) ↔ a ∈ (e w j).1 := by
          have hga : g = wireEmb n gates.length a := by simp [ha]; omega
          rw [hga, Finset.mem_map' (wireEmb n gates.length)]
        simp only [hiff]
        split_ifs <;> simp
      · refine le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun j _ =>
          ite_eq_right fun hmem => hg ?_) zero_le_one
        exact (σ w (e w j)).cnt_subset (hσ w _ hmem)

/-- **LP duality for the charge**: a fractional matching exists iff the price inequality
holds. -/
theorem fracMatch_iff_priceIneq {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) : FracMatch S gates out ↔ PriceIneq S gates out :=
  (fracMatch_iff_fracMatchR S gates out).trans (priceIneq_iff_fracMatchR S gates out).symm

/-- The price inequality under the hard-case hypotheses (minus the size assumption).
A route, not the sorry. -/
def PriceIneqHard : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates),
    PriceIneq S gates out

/-- Proved bridge: the price inequality on the hard case closes the hard case. -/
theorem hardCase_of_priceIneq (hP : PriceIneqHard) : HardCase := by
  intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt
  have hb := bound_of_priceIneq S gates out
    (hP S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N)
  omega

end PEqualNP.Outside.L_meta_951_aux
