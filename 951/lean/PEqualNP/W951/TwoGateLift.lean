import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureLLift
import PEqualNP.W951.Augment

/-!
# TwoGateLift: front A1's Theorem 2G-LIFT (refereed 12:31, desktop Coord)

The two-gate case of the lifted price inequality. For a one-NOT circuit (NOT gate at `p`, `ν x` its
value) with `|S_i ∩ S_j| ≤ 1`, two gates `g, g'` and `m_w = min_{z zero point of S_w} |M_z(w) ∩ {g, g'}|`
(real merge sets): `∑_w m_w ≤ 2`, provided every triple of sets satisfies condition `C(b)` for some `b`.

**Condition `C(b)`** for a triple `S_i, S_j, S_k`, `U = S_i ∪ S_j ∪ S_k`, `b` vanishing on `U`,
`X_l = b ∪ (U \ S_l)` (`ceilPt`): for each `l` of the triple, `h(X_l) = 0` (the NOT gate is `1` at
`X_l`) or `h(b + e_u) = 1` for every `u ∈ U \ S_l`.

**Core** (`twoGate_triple`): under `C(b)` no three distinct sets can each meet `{g, g'}` in every
merge set. Steps (front's §9, all in the lifted monotone circuit through `val_lift`):
* ceilings: the merge set of `w_l` at `X_l` contains `G_l ∈ {g, g'}`, `0` at `P_l = (X_l, ν X_l)`, hence
  `0` at every point below `P_l` (`low_of_below`);
* pigeonhole: a base merge `H_a ∈ M_b(w_a)` is never low at `X_c`, `c ≠ a` (`notLow_base`), so
  `G_i = G_j = G_k = γ` and `H_i = H_j = H_k = γ' ≠ γ`;
* triangle: `γ'` is `1` at `b + e_c` (`c ∈ S_l`) only for `c` in a second set of the triple
  (`triangle`);
* odd cycle: one cover `(a₀, b₀)` of the merge gate `γ'` (`mr_coverT` over all points) and the
  union-find invariant split the two trace points of every run (`run_split`); the three runs give
  three pairwise distinct Booleans.

**Full statement** (`twoGate_lift`): `minHit gates S w g g' = m_w`; case A (some `m_w = 2`: both gates
are universal merges of `w`, so `m_v = 0` for `v ≠ w` by `disjoint_univMergeSet` at `Zof (S_v ∪ S_w)`),
case B (all `m_w ≤ 1`: at most two sets have `m_w = 1` by `twoGate_triple`). Uses only the one-NOT
structure, `|S_i ∩ S_j| ≤ 1` and `C(b)`: no correctness of the outputs, no `|S_w| ≥ 2`, no minimality.
Real merge sets are lifted classes (`mergeSet_eq_lift`), so this is a two-gate price inequality on a
sub-menu of `liftMenu` (MUL / LiftSDR).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section TwoGate

variable {n m : ℕ}

/-- `X_l = b ∪ (U \ S_l)`. -/
def ceilPt (b : Fin n → Bool) (U Sl : Finset (Fin n)) : Fin n → Bool :=
  fun c => b c || decide (c ∈ U ∧ c ∉ Sl)

theorem ceilPt_zero {b : Fin n → Bool} {U Sl : Finset (Fin n)} (hb : ∀ v ∈ U, b v = false)
    (hSU : Sl ⊆ U) : ∀ v ∈ Sl, ceilPt b U Sl v = false := by
  intro v hv
  simp [ceilPt, hb v (hSU hv), hv]

theorem upPt_le_ceilPt {b : Fin n → Bool} {U Sl : Finset (Fin n)} {u : Fin n} (hu : u ∈ U)
    (hul : u ∉ Sl) : upPt b u ≤ ceilPt b U Sl := by
  intro c
  refine Bool.le_iff_imp.mpr fun h => ?_
  by_cases hc : c = u
  · subst hc; simp [ceilPt, hu, hul]
  · rw [upPt, Function.update_of_ne hc] at h
    simp [ceilPt, h]

theorem upPt2_le_ceilPt {b : Fin n → Bool} {U Sl : Finset (Fin n)} {c u : Fin n} (hc : c ∈ U)
    (hcl : c ∉ Sl) (hu : u ∈ U) (hul : u ∉ Sl) : upPt (upPt b c) u ≤ ceilPt b U Sl := by
  intro x
  refine Bool.le_iff_imp.mpr fun h => ?_
  by_cases hxu : x = u
  · subst hxu; simp [ceilPt, hu, hul]
  · rw [upPt, Function.update_of_ne hxu] at h
    exact (Bool.le_iff_imp.mp (upPt_le_ceilPt hc hcl x)) h

/-- Facts of a real merge set element. -/
theorem mergeSet_facts (gates : List Gate) {R : Finset (Fin n)} {z : Fin n → Bool} {x : ℕ}
    (hx : x ∈ mergeSet gates R z) :
    val gates z x = false ∧ ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ val gates (upPt z u) x = true ∧
      val gates (upPt z v) x = true := by
  classical
  have h := mergeSet_subset_DT gates R z hx
  rw [DT, Finset.mem_filter] at h
  obtain ⟨-, hz, u, v, huv, hu, hv, h1, h2⟩ := h
  exact ⟨hz, u, hu, v, hv, huv, h1, h2⟩

theorem eq_of_inter {A B : Finset (Fin n)} (h : (A ∩ B).card ≤ 1) {u v : Fin n} (huA : u ∈ A)
    (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B) : u = v :=
  Finset.card_le_one.mp h u (Finset.mem_inter.mpr ⟨huA, huB⟩) v (Finset.mem_inter.mpr ⟨hvA, hvB⟩)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **Monotone comparison through the lift**: `y ≤ Y` and `ν y ≤ ν Y` ⇒ every real wire is smaller at
`y`. -/
theorem val_le_of_nu (x : ℕ) {y Y : Fin n → Bool} (hyY : y ≤ Y)
    (hnu : val gates y (n + p) ≤ val gates Y (n + p)) : val gates y x ≤ val gates Y x := by
  rw [val_lift (n := n) gates p hp y x, val_lift (n := n) gates p hp Y x]
  exact val_le_of_le _ (monoList_lift (n := n) gates p hp hg hU hN).andOr (ext_le_of_le hyY hnu) _

include hp hg hU hN in
/-- A wire `0` at `Y` is `0` at every `y ≤ Y` with `ν y ≤ ν Y`. -/
theorem low_of_below (x : ℕ) {y Y : Fin n → Bool} (hyY : y ≤ Y)
    (hnu : val gates Y (n + p) = false → val gates y (n + p) = false) (hY : val gates Y x = false) :
    val gates y x = false := by
  have hle : val gates y (n + p) ≤ val gates Y (n + p) := by
    cases hY' : val gates Y (n + p)
    · rw [hnu hY']
    · exact Bool.le_true _
  have h := val_le_of_nu gates p hp hg hU hN x hyY hle
  rw [hY] at h
  cases hv : val gates y x
  · rfl
  · rw [hv] at h; exact absurd h (by decide)

/-- **Condition `C(b)`** for one set `Sl` of the triple: `h(X_l) = 0` or `h(b + e_u) = 1` for every
`u ∈ U \ S_l` (in terms of the NOT gate). -/
def CondB (b : Fin n → Bool) (U Sl : Finset (Fin n)) : Prop :=
  val gates (ceilPt b U Sl) (n + p) = true ∨ ∀ u ∈ U, u ∉ Sl → val gates (upPt b u) (n + p) = false

include hp hg hU hN in
/-- **A base merge is never low at another ceiling.** -/
theorem notLow_base {b : Fin n → Bool} {U A C : Finset (Fin n)} (hAU : A ⊆ U)
    (hAC : (A ∩ C).card ≤ 1) (hcond : CondB gates p b U C) {x : ℕ} (hx : x ∈ mergeSet gates A b)
    (hlow : val gates (ceilPt b U C) x = false) : False := by
  obtain ⟨-, u, hu, v, hv, huv, h1, h2⟩ := mergeSet_facts gates hx
  have key : ∀ w ∈ A, val gates (upPt b w) x = true → w ∈ C := by
    intro w hw hwx
    by_contra hwC
    have := low_of_below gates p hp hg hU hN x (upPt_le_ceilPt (hAU hw) hwC) (fun h0 => by
      rcases hcond with h | h
      · rw [h0] at h; exact absurd h (by decide)
      · exact h w (hAU hw) hwC) hlow
    rw [this] at hwx; exact absurd hwx (by decide)
  exact huv (eq_of_inter hAC hu (key u hu h1) hv (key v hv h2))

include hp hg hU hN in
/-- **Triangle step.** If `γ` is low at the ceiling of `E` and every merge set of `A` meets
`{γ, γ'}`, then `γ'` is `1` at `b + e_c` (`c ∈ U`) only for `c ∈ A ∪ E`. -/
theorem triangle {b : Fin n → Bool} {U A E : Finset (Fin n)} (hb : ∀ v ∈ U, b v = false)
    (hAU : A ⊆ U) (hAE : (A ∩ E).card ≤ 1) (hcondE : CondB gates p b U E) {γ γ' : ℕ}
    (hγE : val gates (ceilPt b U E) γ = false)
    (hmA : ∀ z : Fin n → Bool, (∀ v ∈ A, z v = false) →
      ∃ x, (x = γ ∨ x = γ') ∧ x ∈ mergeSet gates A z)
    {c : Fin n} (hcU : c ∈ U) (hc : val gates (upPt b c) γ' = true) : c ∈ A ∨ c ∈ E := by
  by_contra hcon
  obtain ⟨hcA, hcE⟩ := not_or.mp hcon
  have hz : ∀ v ∈ A, upPt b c v = false := by
    intro v hv
    have hvc : v ≠ c := fun h => hcA (h ▸ hv)
    rw [upPt, Function.update_of_ne hvc]; exact hb v (hAU hv)
  obtain ⟨x, hxK, hxM⟩ := hmA _ hz
  have hx0 := (mergeSet_facts gates hxM).1
  have hxγ : x = γ := by
    rcases hxK with h | h
    · exact h
    · subst h; rw [hc] at hx0; exact absurd hx0 (by decide)
  subst hxγ
  obtain ⟨-, u, hu, v, hv, huv, h1, h2⟩ := mergeSet_facts gates hxM
  have key : ∀ w ∈ A, val gates (upPt (upPt b c) w) x = true → w ∈ E := by
    intro w hw hwx
    by_contra hwE
    have := low_of_below gates p hp hg hU hN x (upPt2_le_ceilPt hcU hcE (hAU hw) hwE) (fun h0 => by
      rcases hcondE with h | h
      · rw [h0] at h; exact absurd h (by decide)
      · exact not_false_of_le gates p hp hg hU hN (le_upPt _ w) (h c hcU hcE)) hγE
    rw [this] at hwx; exact absurd hwx (by decide)
  exact huv (eq_of_inter hAE hu (key u hu h1) hv (key v hv h2))

/-- **One run of the odd-cycle step.** A merge gate `n + k` of `L` at `b` whose trace lies in
`A ∪ E` (`|L ∩ A|, |L ∩ E| ≤ 1`), with a cover `(a₀, b₀)`: the two trace points, one in `A` and one in
`E`, take different values on `a₀`. -/
theorem run_split {L A E : Finset (Fin n)} (hLA : (L ∩ A).card ≤ 1) (hLE : (L ∩ E).card ≤ 1)
    {b : Fin n → Bool} {k : ℕ} (hk : n + k ∈ mergeSet gates L b)
    (htr : ∀ c ∈ L, val gates (upPt b c) (n + k) = true → c ∈ A ∨ c ∈ E) (a₀ b₀ : ℕ)
    (hcov : ∀ u : Fin n, val gates (upPt b u) (n + k) = true →
      (a₀ < n + k ∧ val gates b a₀ = false ∧ val gates (upPt b u) a₀ = true) ∨
      (b₀ < n + k ∧ val gates b b₀ = false ∧ val gates (upPt b u) b₀ = true)) :
    ∃ x ∈ L, x ∈ A ∧ ∃ y ∈ L, y ∈ E ∧ val gates (upPt b x) a₀ ≠ val gates (upPt b y) a₀ := by
  classical
  obtain ⟨j, hj, hjk, hmg⟩ := (runMT_mem b (upPt b) L gates gates.length (n + k)).mp hk
  have hjk' : j = k := by omega
  subst hjk'
  set l := runLT b (upPt b) L gates j with hl
  have hinv := runLT_inv b (upPt b) L gates (fun u _ c h1 h2 => upPt_hT b u c h1 h2) j
  have hmem : ∀ d, d ∈ trRT (upPt b) L gates (n + j) ↔ d ∈ L ∧ val gates (upPt b d) (n + j) = true :=
    fun d => Finset.mem_filter
  -- not every trace point has the `a₀`-condition, nor every one the `b₀`-condition
  have hone : ∀ w : ℕ, w < n + j → val gates b w = false →
      ¬ ∀ d ∈ trRT (upPt b) L gates (n + j), val gates (upPt b d) w = true := by
    intro w hw hwz hall
    have : ((trRT (upPt b) L gates (n + j)).image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hy
      exact hinv w hw hwz d ((hmem d).mp hd).1 d' ((hmem d').mp hd').1 (hall d hd) (hall d' hd')
    have := hmg.2
    omega
  -- a trace point without the `a₀`-condition, and one without the `b₀`-condition
  have hA : ∃ d ∈ trRT (upPt b) L gates (n + j),
      ¬ (a₀ < n + j ∧ val gates b a₀ = false ∧ val gates (upPt b d) a₀ = true) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨d0, hd0⟩ : (trRT (upPt b) L gates (n + j)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have := hmg.2
      rw [he] at this
      simp at this
    obtain ⟨h1, h2, -⟩ := hcon d0 hd0
    exact hone a₀ h1 h2 fun d hd => (hcon d hd).2.2
  have hB : ∃ d ∈ trRT (upPt b) L gates (n + j),
      ¬ (b₀ < n + j ∧ val gates b b₀ = false ∧ val gates (upPt b d) b₀ = true) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨d0, hd0⟩ : (trRT (upPt b) L gates (n + j)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have := hmg.2
      rw [he] at this
      simp at this
    obtain ⟨h1, h2, -⟩ := hcon d0 hd0
    exact hone b₀ h1 h2 fun d hd => (hcon d hd).2.2
  obtain ⟨d1, hd1, hna⟩ := hA
  obtain ⟨d2, hd2, hnb⟩ := hB
  obtain ⟨hd1L, hd1v⟩ := (hmem d1).mp hd1
  obtain ⟨hd2L, hd2v⟩ := (hmem d2).mp hd2
  have ha2 := (hcov d2 hd2v).resolve_right hnb
  have hv1 : val gates (upPt b d1) a₀ = false := by
    cases h : val gates (upPt b d1) a₀
    · rfl
    · exact absurd ⟨ha2.1, ha2.2.1, h⟩ hna
  have hdiff : val gates (upPt b d1) a₀ ≠ val gates (upPt b d2) a₀ := by
    rw [hv1, ha2.2.2]; decide
  have hd12 : d1 ≠ d2 := fun h => hdiff (h ▸ rfl)
  rcases htr d1 hd1L hd1v with h1A | h1E <;> rcases htr d2 hd2L hd2v with h2A | h2E
  · exact absurd (eq_of_inter hLA hd1L h1A hd2L h2A) hd12
  · exact ⟨d1, hd1L, h1A, d2, hd2L, h2E, hdiff⟩
  · exact ⟨d2, hd2L, h2A, d1, hd1L, h1E, fun h => hdiff h.symm⟩
  · exact absurd (eq_of_inter hLE hd1L h1E hd2L h2E) hd12

/-- The pigeonhole step on the six gates. -/
theorem pigeon_two {g g' Gi Gj Gk Hi Hj Hk : ℕ} (hGi : Gi = g ∨ Gi = g') (hGj : Gj = g ∨ Gj = g')
    (hGk : Gk = g ∨ Gk = g') (hHi : Hi = g ∨ Hi = g') (hHj : Hj = g ∨ Hj = g')
    (hHk : Hk = g ∨ Hk = g') (h1 : Hi ≠ Gj) (h2 : Hi ≠ Gk) (h3 : Hj ≠ Gi) (h4 : Hj ≠ Gk)
    (h5 : Hk ≠ Gi) (h6 : Hk ≠ Gj) :
    Gj = Gi ∧ Gk = Gi ∧ Hj = Hi ∧ Hk = Hi ∧ ∀ x, x = g ∨ x = g' → x = Gi ∨ x = Hi := by
  refine ⟨by omega, by omega, by omega, by omega, fun x hx => by omega⟩

include hp hg hU hN in
/-- **Theorem 2G-LIFT, core** (front A1 §9): under `C(b)` for a triple of distinct sets, the three sets
cannot each meet `{g, g'}` in every merge set. -/
theorem twoGate_triple (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (b : Fin n → Bool)
    (hb : ∀ v ∈ S i ∪ S j ∪ S k, b v = false)
    (hC : ∀ l, l = i ∨ l = j ∨ l = k → CondB gates p b (S i ∪ S j ∪ S k) (S l)) (g g' : ℕ)
    (hm : ∀ l, l = i ∨ l = j ∨ l = k → ∀ z : Fin n → Bool, (∀ v ∈ S l, z v = false) →
      ∃ x, (x = g ∨ x = g') ∧ x ∈ mergeSet gates (S l) z) : False := by
  classical
  set U := S i ∪ S j ∪ S k with hUdef
  have hsub : ∀ l, l = i ∨ l = j ∨ l = k → S l ⊆ U := by
    rintro l (rfl | rfl | rfl) x hx <;> simp [hUdef, hx]
  have hTi : i = i ∨ i = j ∨ i = k := Or.inl rfl
  have hTj : j = i ∨ j = j ∨ j = k := Or.inr (Or.inl rfl)
  have hTk : k = i ∨ k = j ∨ k = k := Or.inr (Or.inr rfl)
  -- ceilings and bases
  have hceil : ∀ l, l = i ∨ l = j ∨ l = k → ∃ G, (G = g ∨ G = g') ∧
      G ∈ mergeSet gates (S l) (ceilPt b U (S l)) := fun l hl =>
    hm l hl _ (ceilPt_zero hb (hsub l hl))
  have hbase : ∀ l, l = i ∨ l = j ∨ l = k → ∃ H, (H = g ∨ H = g') ∧ H ∈ mergeSet gates (S l) b :=
    fun l hl => hm l hl b fun v hv => hb v (hsub l hl hv)
  obtain ⟨Gi, hGi, hGiM⟩ := hceil i hTi
  obtain ⟨Gj, hGj, hGjM⟩ := hceil j hTj
  obtain ⟨Gk, hGk, hGkM⟩ := hceil k hTk
  obtain ⟨Hi, hHi, hHiM⟩ := hbase i hTi
  obtain ⟨Hj, hHj, hHjM⟩ := hbase j hTj
  obtain ⟨Hk, hHk, hHkM⟩ := hbase k hTk
  have lowG : ∀ {l G}, G ∈ mergeSet gates (S l) (ceilPt b U (S l)) →
      val gates (ceilPt b U (S l)) G = false := fun h => (mergeSet_facts gates h).1
  -- a base merge of `a` is not low at the ceiling of `c ≠ a`
  have hne : ∀ {a c : Fin m} {H G : ℕ}, (a = i ∨ a = j ∨ a = k) → (c = i ∨ c = j ∨ c = k) → a ≠ c →
      H ∈ mergeSet gates (S a) b → G ∈ mergeSet gates (S c) (ceilPt b U (S c)) → H ≠ G := by
    intro a c H G ha hc hac hH hG hHG
    subst hHG
    exact notLow_base gates p hp hg hU hN (hsub a ha) (hS a c hac) (hC c hc) hH (lowG hG)
  obtain ⟨hGj', hGk', hHj', hHk', hK⟩ := pigeon_two hGi hGj hGk hHi hHj hHk
    (hne hTi hTj hij hHiM hGjM) (hne hTi hTk hik hHiM hGkM) (hne hTj hTi hij.symm hHjM hGiM)
    (hne hTj hTk hjk hHjM hGkM) (hne hTk hTi hik.symm hHkM hGiM) (hne hTk hTj hjk.symm hHkM hGjM)
  rw [hGj'] at hGjM
  rw [hGk'] at hGkM
  rw [hHj'] at hHjM
  rw [hHk'] at hHkM
  -- `γ = Gi` is low at all three ceilings, `γ' = Hi` merges for all three sets at `b`
  have hmγ : ∀ l, l = i ∨ l = j ∨ l = k → ∀ z : Fin n → Bool, (∀ v ∈ S l, z v = false) →
      ∃ x, (x = Gi ∨ x = Hi) ∧ x ∈ mergeSet gates (S l) z := by
    intro l hl z hz
    obtain ⟨x, hx, hxM⟩ := hm l hl z hz
    exact ⟨x, hK x hx, hxM⟩
  -- the merge gate `γ'` and one cover of it, valid for all three runs
  obtain ⟨hHi0, u0, hu0, v0, hv0, huv0, hu0t, hv0t⟩ := mergeSet_facts gates hHiM
  obtain ⟨kk, -, hkk, -⟩ := (runMT_mem b (upPt b) (S i) gates gates.length Hi).mp hHiM
  subst hkk
  obtain ⟨a₀, b₀, hcov⟩ := (mr_coverT b (upPt b) Finset.univ gates
    (goodT_upPt gates hg hU b Finset.univ) kk hHi0).resolve_left fun h =>
    huv0 (h u0 (Finset.mem_univ _) v0 (Finset.mem_univ _) hu0t hv0t)
  -- the three runs
  have tri : ∀ {l a e : Fin m}, (l = i ∨ l = j ∨ l = k) → (a = i ∨ a = j ∨ a = k) →
      (e = i ∨ e = j ∨ e = k) → a ≠ e →
      ∀ c ∈ S l, val gates (upPt b c) (n + kk) = true → c ∈ S a ∨ c ∈ S e := by
    intro l a e hl ha he hae c hc hcv
    exact triangle gates p hp hg hU hN hb (hsub a ha) (hS a e hae) (hC e he)
      (show val gates (ceilPt b U (S e)) Gi = false from by
        rcases he with rfl | rfl | rfl
        · exact lowG hGiM
        · exact lowG hGjM
        · exact lowG hGkM)
      (hmγ a ha) (hsub l hl hc) hcv
  obtain ⟨x1, hx1i, hx1j, y1, hy1i, hy1k, h1⟩ := run_split gates (hS i j hij) (hS i k hik) hHiM
    (tri hTi hTj hTk hjk) a₀ b₀ hcov
  obtain ⟨x2, hx2j, hx2i, y2, hy2j, hy2k, h2⟩ := run_split gates (hS j i hij.symm) (hS j k hjk) hHjM
    (tri hTj hTi hTk hik) a₀ b₀ hcov
  obtain ⟨x3, hx3k, hx3i, y3, hy3k, hy3j, h3⟩ := run_split gates (hS k i hik.symm) (hS k j hjk.symm) hHkM
    (tri hTk hTi hTj hij) a₀ b₀ hcov
  have e12 : x1 = x2 := eq_of_inter (hS i j hij) hx1i hx1j hx2i hx2j
  have e13 : y1 = x3 := eq_of_inter (hS i k hik) hy1i hy1k hx3i hx3k
  have e23 : y2 = y3 := eq_of_inter (hS j k hjk) hy2j hy2k hy3j hy3k
  subst e12 e13 e23
  revert h1 h2 h3
  cases val gates (upPt b x1) a₀ <;> cases val gates (upPt b y1) a₀ <;>
    cases val gates (upPt b y2) a₀ <;> decide

/-- `m_w = min_{z zero point of S_w} |M_z(w) ∩ {g, g'}|` (real merge sets). -/
noncomputable def minHit (S : Fin m → Finset (Fin n)) (w : Fin m) (g g' : ℕ) : ℕ :=
  (zeroPts (S w)).inf' (zeroPts_nonempty (S w)) fun z => (mergeSet gates (S w) z ∩ {g, g'}).card

theorem minHit_le_two (S : Fin m → Finset (Fin n)) (w : Fin m) (g g' : ℕ) :
    minHit gates S w g g' ≤ 2 := by
  obtain ⟨z, hz⟩ := zeroPts_nonempty (S w)
  refine (Finset.inf'_le _ hz).trans ?_
  exact (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_le_two)

theorem one_le_minHit {S : Fin m → Finset (Fin n)} {w : Fin m} {g g' : ℕ}
    (h : 1 ≤ minHit gates S w g g') (z : Fin n → Bool) (hz : ∀ v ∈ S w, z v = false) :
    ∃ x, (x = g ∨ x = g') ∧ x ∈ mergeSet gates (S w) z := by
  have h1 := h.trans (Finset.inf'_le _ (mem_zeroPts.mpr hz))
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < _ from h1)
  obtain ⟨hxM, hxK⟩ := Finset.mem_inter.mp hx
  rcases Finset.mem_insert.mp hxK with rfl | hx'
  · exact ⟨_, Or.inl rfl, hxM⟩
  · exact ⟨x, Or.inr (Finset.mem_singleton.mp hx'), hxM⟩

include hp hg hU hN in
/-- **Theorem 2G-LIFT** (front A1 §§8–9, refereed 12:31): `∑_w m_w ≤ 2` for every two gates, if every
triple of distinct sets satisfies `C(b)` for some `b`. -/
theorem twoGate_lift (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hCall : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k → ∃ b : Fin n → Bool,
      (∀ v ∈ S i ∪ S j ∪ S k, b v = false) ∧
        ∀ l, l = i ∨ l = j ∨ l = k → CondB gates p b (S i ∪ S j ∪ S k) (S l))
    (g g' : ℕ) : ∑ w, minHit gates S w g g' ≤ 2 := by
  classical
  by_cases hA : ∃ w, 2 ≤ minHit gates S w g g'
  · -- case A: both gates are universal merges of `w`; every other set has `m_v = 0`
    obtain ⟨w, hw⟩ := hA
    have hboth : ∀ z ∈ zeroPts (S w), g ∈ mergeSet gates (S w) z ∧ g' ∈ mergeSet gates (S w) z := by
      intro z hz
      have h2 := hw.trans (Finset.inf'_le _ hz)
      have hK2 : ({g, g'} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      have hsub : mergeSet gates (S w) z ∩ {g, g'} = {g, g'} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact ⟨Finset.mem_of_mem_inter_left (hsub ▸ Finset.mem_insert_self g {g'}),
        Finset.mem_of_mem_inter_left (hsub ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self g'))⟩
    have huniv : ∀ x, (x = g ∨ x = g') → x ∈ univMergeSet S gates w := by
      rintro x (rfl | rfl)
      · exact (mem_univMergeSet S gates).mpr fun z hz => (hboth z hz).1
      · exact (mem_univMergeSet S gates).mpr fun z hz => (hboth z hz).2
    have hzero : ∀ v, v ≠ w → minHit gates S v g g' = 0 := by
      intro v hvw
      have hz : ∀ x ∈ S v ∪ S w, Zof (S v ∪ S w) x = false := fun x hx => by simp [Zof, hx]
      have hdis := disjoint_univMergeSet S gates hS hvw _ hz
      refine Nat.le_zero.mp ((Finset.inf'_le _ (mem_zeroPts.mpr fun x hx =>
        hz x (Finset.mem_union_left _ hx))).trans (Nat.le_zero.mpr ?_))
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxM, hxK⟩ := Finset.mem_inter.mp hx
      have hxK' : x = g ∨ x = g' := by
        rcases Finset.mem_insert.mp hxK with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      exact Finset.disjoint_left.mp hdis hxM (huniv x hxK')
    rw [Finset.sum_eq_single w (fun v _ hv => hzero v hv) (by simp)]
    exact minHit_le_two gates S w g g'
  · -- case B: every `m_w ≤ 1`; at most two sets have `m_w = 1`
    push Not at hA
    have hcard : (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card ≤ 2 := by
      by_contra hc
      obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp
        (show 2 < (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card by omega)
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      obtain ⟨b, hb, hC⟩ := hCall i j k hij hik hjk
      exact twoGate_triple gates p hp hg hU hN S hS hij hik hjk b hb hC g g' fun l hl z hz => by
        rcases hl with rfl | rfl | rfl
        · exact one_le_minHit gates hi' z hz
        · exact one_le_minHit gates hj' z hz
        · exact one_le_minHit gates hk' z hz
    calc ∑ w, minHit gates S w g g'
        ≤ ∑ w, (if 1 ≤ minHit gates S w g g' then 1 else 0) := Finset.sum_le_sum fun w _ => by
          have := hA w
          split_ifs with h <;> omega
      _ = (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card := by
          rw [Finset.sum_boole]; simp
      _ ≤ 2 := hcard

end TwoGate

end PEqualNP.Outside.L_meta_951_aux
