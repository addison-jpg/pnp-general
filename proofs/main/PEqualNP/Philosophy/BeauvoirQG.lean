import PEqualNP.Philosophy.Beauvoir

/-!
# Beauvoir routed at quantum gravity's discrete structures: sets, nodes, edges (seat BQG)

HONESTY. Every theorem below is a statement of finite-dimensional linear algebra, of finite sums
over a weighted graph, or of order theory. Each is proved from Mathlib plus two repo files (`Beauvoir`, `Fisher`). The names taken from
Beauvoir, Hegel and Barrès are READINGS attached to the definitions: they are our modelling
choices and are not proved, and nothing here claims what Beauvoir meant. Nothing here is a
statement about physical spacetime, and nothing is about circuits. `research/philosophy/BEAUVOIR_QG.md`
separates what is checked, what is interpretation, and what failed.

Philosophy sources (in copyright; cited, not quoted beyond one line; none re-read for this file).
* Simone de Beauvoir, *L'Invitée* (1943; *She Came to Stay*): the triad Françoise / Pierre /
  Xavière; epigraph from Hegel, given in the scholarship as "Chaque conscience poursuit la mort
  de l'autre".
* Simone de Beauvoir, *Pour une morale de l'ambiguïté* (1947): ambiguity; one's freedom and the
  freedom of others.
* Hegel, *Phenomenology of Spirit* (1807), "Lordship and Bondage": mutual recognition.
* Barrès's "barbarians" as taken over in Beauvoir's 1926 diary: see `Beauvoir.lean` and
  research/LITERATURE.md §M5 for what is and is not confirmed.

Physics sources (all cited from memory in this session; see research/LITERATURE.md §M6 for read status).
* Schmidt decomposition and reduced states: Nielsen and Chuang, *Quantum Computation and Quantum
  Information* (2000), §2.5.
* Purity and the 2×2 minors of the amplitude matrix (I-concurrence): Rungta, Bužek, Caves,
  Hillery and Milburn, Phys. Rev. A 64 (2001) 042315; for two qubits, Wootters, Phys. Rev.
  Lett. 80 (1998) 2245.
* Monogamy: Coffman, Kundu and Wootters, Phys. Rev. A 61 (2000) 052306. The CKW inequality itself
  is NOT proved here; the extreme case and a GHZ check are.
* Ryu and Takayanagi, Phys. Rev. Lett. 96 (2006) 181602; Pastawski, Yoshida, Harlow and Preskill,
  JHEP 06 (2015) 149 (HaPPY: entropy of a boundary region as a minimal cut of the network).
* Strong subadditivity from minimal surfaces: Headrick and Takayanagi, Phys. Rev. D 76 (2007)
  106013. Monogamy of mutual information: Hayden, Headrick and Maloney, Phys. Rev. D 87 (2013)
  046003. Graph models: Bao, Nezami, Ooguri, Stoica, Sully and Walter, JHEP 09 (2015) 130.
* Causal sets: Bombelli, Lee, Meyer and Sorkin, Phys. Rev. Lett. 59 (1987) 521.
-/

set_option linter.unusedSectionVars false

namespace PEqualNP.Philosophy.BeauvoirQG

open Matrix Finset Polynomial
open scoped BigOperators ComplexConjugate Kronecker ComplexOrder

/-! ## 1. Self and other as the two reductions of one pure state -/

section Entanglement

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The self's reduced state. A pure state of a self (basis `a`) and an other (basis `b`) is its
amplitude matrix `M`, with `M i j` the amplitude of `|i⟩|j⟩` (not assumed normalised). Tracing out
the other leaves `M Mᴴ`. Physics: Nielsen and Chuang §2.5. Reading: the self taken apart from the
other. -/
def selfState (M : Matrix a b ℂ) : Matrix a a ℂ := M * Mᴴ

/-- The other's reduced state, up to transpose: tracing out the self leaves `(Mᴴ M)ᵀ`, and
transposing changes neither trace, rank, powers' traces nor spectrum. Reading: the other taken
apart from the self. -/
def otherState (M : Matrix a b ℂ) : Matrix b b ℂ := Mᴴ * M

theorem mul_pow_succ_eq {R : Type*} [CommRing R] (A : Matrix a b R) (B : Matrix b a R) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

/-- **Every moment of the self's state equals the same moment of the other's.** `tr ρ_A^k =
tr ρ_B^k` for `k ≥ 1`, so normalisation, purity and all Rényi entropies of integer order agree.
Reading: self and other are mixed to the same degree (mutual constitution). -/
theorem moments_symm (M : Matrix a b ℂ) (k : ℕ) :
    ((selfState M) ^ (k + 1)).trace = ((otherState M) ^ (k + 1)).trace := by
  unfold selfState otherState
  rw [mul_pow_succ_eq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

/-- **The Schmidt rank is the same from both sides.** -/
theorem schmidt_rank_symm (M : Matrix a b ℂ) : (selfState M).rank = (otherState M).rank := by
  unfold selfState otherState
  rw [rank_self_mul_conjTranspose, rank_conjTranspose_mul_self]

theorem selfState_isHermitian (M : Matrix a b ℂ) : (selfState M).IsHermitian := by
  rw [selfState, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

theorem otherState_isHermitian (M : Matrix a b ℂ) : (otherState M).IsHermitian := by
  rw [otherState, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Von Neumann entropy of a Hermitian matrix: `∑ -λ log λ` over its eigenvalues (with
multiplicity). For a density matrix this is the entanglement entropy. -/
noncomputable def entropy {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : ℝ := ∑ i, Real.negMulLog (hA.eigenvalues i)

theorem entropy_eq_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    entropy hA = (A.charpoly.roots.map fun z : ℂ => Real.negMulLog z.re).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, entropy, Finset.sum]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => ?_)
  simp

/-- **`S(A) = S(B)` for a pure state.** In any pure state of two parties, of any finite
dimensions, the von Neumann entropy of the self's reduced state equals that of the other's.
Physics: the standard corollary of the Schmidt decomposition; proved here from
`Matrix.charpoly_mul_comm'` (`M Mᴴ` and `Mᴴ M` have the same nonzero eigenvalues) with no Schmidt
decomposition. Reading (ours): mutual recognition. The theorem holds for every pure state, so it
cannot tell recognition from domination; see BEAUVOIR_QG.md part 3. -/
theorem entropy_symm (M : Matrix a b ℂ) :
    entropy (selfState_isHermitian M) = entropy (otherState_isHermitian M) := by
  rw [entropy_eq_roots, entropy_eq_roots]
  unfold selfState otherState
  have key : ∀ (n : ℕ) (p : ℂ[X]), p ≠ 0 →
      ((X ^ n * p).roots.map fun z : ℂ => Real.negMulLog z.re).sum =
        (p.roots.map fun z : ℂ => Real.negMulLog z.re).sum := by
    intro n p hp
    rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp), roots_pow, roots_X]
    simp [Multiset.map_nsmul, Multiset.sum_nsmul]
  rw [← key (Fintype.card b) _ (charpoly_monic _).ne_zero, charpoly_mul_comm' M Mᴴ,
    key _ _ (charpoly_monic _).ne_zero]

/-- A 2×2 minor of the amplitude matrix. Physics: the squared moduli of these minors sum to the
squared I-concurrence (Rungta et al. 2001); for two qubits the single minor is the determinant and
`2 |det M|` is Wootters' concurrence. -/
def minor (M : Matrix a b ℂ) (i i' : a) (j j' : b) : ℂ := M i j * M i' j' - M i j' * M i' j

/-- **Mixedness is exactly the weight of the minors.** `∑ |minor|² = 2 ((tr ρ)² - tr ρ²)` for
`ρ = M Mᴴ`: the Lagrange identity. For a normalised state the right side is `2 (1 - tr ρ²)`, twice
the linear entropy. -/
theorem sum_minor_sq (M : Matrix a b ℂ) :
    ∑ i, ∑ i', ∑ j, ∑ j', minor M i i' j j' * conj (minor M i i' j j') =
      2 * ((selfState M).trace ^ 2 - (selfState M * selfState M).trace) := by
  have hρ : ∀ i i', selfState M i i' = ∑ j, M i j * conj (M i' j) := by
    intro i i'; simp [selfState, Matrix.mul_apply, conjTranspose_apply]
  have inner : ∀ i i', ∑ j, ∑ j', minor M i i' j j' * conj (minor M i i' j j') =
      2 * (selfState M i i * selfState M i' i' - selfState M i i' * selfState M i' i) := by
    intro i i'
    have h1 : ∑ j, ∑ j', (M i j * M i' j') * conj (M i j * M i' j') =
        selfState M i i * selfState M i' i' := by
      rw [hρ, hρ, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
        simp only [map_mul]; ring
    have h2 : ∑ j, ∑ j', (M i j' * M i' j) * conj (M i j' * M i' j) =
        selfState M i i * selfState M i' i' := by
      rw [Finset.sum_comm]; exact h1
    have h3 : ∑ j, ∑ j', (M i j * M i' j') * conj (M i j' * M i' j) =
        selfState M i i' * selfState M i' i := by
      rw [hρ, hρ, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
        simp only [map_mul]; ring
    have h4 : ∑ j, ∑ j', (M i j' * M i' j) * conj (M i j * M i' j') =
        selfState M i i' * selfState M i' i := by
      rw [Finset.sum_comm]; exact h3
    have hm : ∀ j j', minor M i i' j j' * conj (minor M i i' j j') =
        (M i j * M i' j') * conj (M i j * M i' j') + (M i j' * M i' j) * conj (M i j' * M i' j)
          - (M i j * M i' j') * conj (M i j' * M i' j)
          - (M i j' * M i' j) * conj (M i j * M i' j') := by
      intro j j'; simp only [minor, map_sub]; ring
    simp only [hm, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
    ring
  have ht : (selfState M).trace ^ 2 = ∑ i, ∑ i', selfState M i i * selfState M i' i' := by
    rw [sq, Matrix.trace, Finset.sum_mul_sum]; rfl
  have ht2 : (selfState M * selfState M).trace =
      ∑ i, ∑ i', selfState M i i' * selfState M i' i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [ht, ht2]
  simp only [inner, ← Finset.mul_sum, Finset.sum_sub_distrib]

theorem minor_eq_zero_of_pure {M : Matrix a b ℂ}
    (h : (selfState M).trace ^ 2 = (selfState M * selfState M).trace) (i i' : a) (j j' : b) :
    minor M i i' j j' = 0 := by
  have hs := sum_minor_sq M
  rw [h, sub_self, mul_zero] at hs
  simp only [Complex.mul_conj, ← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hs
  have nn := fun (z : ℂ) => Complex.normSq_nonneg z
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun i' _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ => nn _).1 hs i (mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i' _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ => nn _).1 h1 i' (mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    Finset.sum_nonneg fun j' _ => nn _).1 h2 j (mem_univ _)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j' _ => nn _).1 h3 j' (mem_univ _)
  exact Complex.normSq_eq_zero.1 h4

/-- **Reduced state pure iff product state.** For a pure state of
two parties of any finite dimensions: `tr ρ_A² = (tr ρ_A)²` (the self's reduced state is pure)
if and only if the joint state is a product `u ⊗ v`. Contrapositive: any entanglement with the
other makes the self, taken alone, a mixture. Reading: Beauvoir's ambiguity, the self that is not
a self-sufficient thing once it stands in relation (our reading). -/
theorem pure_iff_product (M : Matrix a b ℂ) :
    (selfState M).trace ^ 2 = (selfState M * selfState M).trace ↔
      ∃ (u : a → ℂ) (v : b → ℂ), M = vecMulVec u v := by
  constructor
  · intro h
    by_cases h0 : M = 0
    · exact ⟨0, 0, by ext i j; simp [h0, vecMulVec_apply]⟩
    · obtain ⟨i0, j0, hij⟩ : ∃ i0 j0, M i0 j0 ≠ 0 := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact h0 (by ext i j; simpa using hc i j)
      refine ⟨fun i => M i j0, fun j => M i0 j / M i0 j0, ?_⟩
      ext i j
      have hm := minor_eq_zero_of_pure h i i0 j j0
      simp only [minor] at hm
      rw [vecMulVec_apply]
      field_simp
      linear_combination hm
  · rintro ⟨u, v, rfl⟩
    have hs := sum_minor_sq (vecMulVec u v)
    have hz : ∀ i i' j j', minor (vecMulVec u v) i i' j j' = 0 := by
      intro i i' j j'; simp only [minor, vecMulVec_apply]; ring
    simp only [hz, zero_mul, Finset.sum_const_zero] at hs
    have := mul_eq_zero.1 hs.symm
    rcases this with h | h
    · exact absurd h two_ne_zero
    · exact sub_eq_zero.1 h

/-! ### The triad of *She Came to Stay* -/

/-- The joint reduced state of the first and third parties of a pure three-party state, the
middle one traced out. The state is written `ψ (x, y) z`: the amplitude matrix of the cut
"(first, second) against third". Reading (ours): first = Françoise, second = Pierre, third =
Xavière. -/
def reduceAC (ψ : Matrix (a × b) c ℂ) : Matrix (a × c) (a × c) ℂ :=
  fun p q => ∑ y, ψ (p.1, y) p.2 * conj (ψ (q.1, y) q.2)

/-- **`S(AB) = S(C)`.** For a pure three-party state, the pair
(first, second) and the third have the same entropy. An instance of `entropy_symm`. -/
theorem couple_entropy_eq_third (ψ : Matrix (a × b) c ℂ) :
    entropy (selfState_isHermitian ψ) = entropy (otherState_isHermitian ψ) := entropy_symm ψ

/-- **A pure pair decouples from the third (decoupling, NOT monogamy).** If the pair (first,
second) is in a pure state of its own, the whole state is a product `(12) ⊗ 3`, so the third is
uncorrelated with the first: their joint state is a product `σ ⊗ τ`. This is immediate from
`pure_iff_product`; it has no entanglement-measure content and does not use maximal
entanglement. It is the textbook extreme case behind Coffman-Kundu-Wootters monogamy, but the
CKW inequality itself is NOT proved here. Reading (ours): a couple that is one closed whole
leaves nothing for the third. -/
theorem pure_pair_decouples (ψ : Matrix (a × b) c ℂ)
    (h : (selfState ψ).trace ^ 2 = (selfState ψ * selfState ψ).trace) :
    ∃ (σ : Matrix a a ℂ) (τ : Matrix c c ℂ), reduceAC ψ = σ ⊗ₖ τ := by
  obtain ⟨u, v, rfl⟩ := (pure_iff_product ψ).1 h
  refine ⟨fun x x' => ∑ y, u (x, y) * conj (u (x', y)), fun z z' => v z * conj (v z'), ?_⟩
  ext ⟨x, z⟩ ⟨x', z'⟩
  change ∑ y, vecMulVec u v (x, y) z * conj (vecMulVec u v (x', y) z') =
    (∑ y, u (x, y) * conj (u (x', y))) * (v z * conj (v z'))
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by simp only [vecMulVec_apply, map_mul]; ring

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩` of three qubits. Physics: Greenberger, Horne
and Zeilinger (1989). -/
def ghz : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := fun p z => if p.1 = p.2 ∧ p.2 = z then 1 else 0

/-- **GHZ: the two-party reduced state is separable.** The joint state of
the first and third parties is `|00⟩⟨00| + |11⟩⟨11|`, a mixture of two product states: classical
correlation only. Reading (ours): the presence of the third is the death of the entanglement of
the other two (rhetoric: the correct statement is that the two are classically correlated, not
entangled); a statement about one state, not a law. -/
theorem ghz_pair_separable :
    reduceAC ghz = ∑ s : Fin 2, (Matrix.single s s (1 : ℂ)) ⊗ₖ (Matrix.single s s (1 : ℂ)) := by
  ext ⟨x, z⟩ ⟨x', z'⟩
  fin_cases x <;> fin_cases z <;> fin_cases x' <;> fin_cases z' <;>
    simp [reduceAC, ghz, Fin.sum_univ_two, Matrix.single, Matrix.sum_apply, kroneckerMap_apply]

/-- In the GHZ triad the pair (first, second) is nevertheless mixed: its state is not pure, so
the pair 12 (and by symmetry the others, not proved here) is entangled with the remaining
party. -/
theorem ghz_couple_mixed :
    (selfState ghz).trace ^ 2 ≠ (selfState ghz * selfState ghz).trace := by
  intro h
  have := minor_eq_zero_of_pure h (0, 0) (1, 1) 0 1
  simp [minor, ghz] at this

end Entanglement

/-! ## 2. Nodes and edges: minimal cuts -/

section Cut

variable {V : Type*} [Fintype V]

/-- The weight of the cut `S` of a network with edge weights `w`: the total weight of ordered
pairs of nodes that `S` separates. For symmetric `w` this is twice the usual cut weight; every
statement below is homogeneous, so the factor does not matter. Physics: the area of a bulk
surface in a tensor network (HaPPY), with `w` the log bond dimension. -/
def cut (w : V → V → ℕ) (S : V → Bool) : ℕ := ∑ x, ∑ y, if S x ≠ S y then w x y else 0

/-- A bulk region `S` is anchored on the boundary region `A`: on boundary nodes it agrees with
`A`. Physics: the homology condition of Ryu-Takayanagi in graph form (Bao et al. 2015). -/
def Anchored (bdy A S : V → Bool) : Prop := ∀ v, bdy v = true → S v = A v

open Classical in
/-- The graph analogue of the Ryu-Takayanagi value (a min-cut over node labellings anchored on
boundary nodes; real RT is a bulk minimal surface, and in real tensor networks the boundary is
dangling legs, so the name is an analogy). The value of a boundary region: the least cut among bulk regions anchored on
it. Physics: for HaPPY states, on regions where the greedy-cut argument applies, this equals the
entanglement entropy (Pastawski et al. 2015, cited, NOT proved here). Reading: how much of the network a set
of selves shares with everyone else. -/
noncomputable def rt (w : V → V → ℕ) (bdy A : V → Bool) : ℕ :=
  (univ.filter (Anchored bdy A)).inf' ⟨A, by simp [Anchored]⟩ (cut w)

theorem rt_le {w : V → V → ℕ} {bdy A S : V → Bool} (h : Anchored bdy A S) :
    rt w bdy A ≤ cut w S := by
  classical
  exact Finset.inf'_le _ (by simp [h])

theorem exists_min (w : V → V → ℕ) (bdy A : V → Bool) :
    ∃ S, Anchored bdy A S ∧ cut w S = rt w bdy A := by
  classical
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_inf' (s := univ.filter (Anchored bdy A))
    ⟨A, by simp [Anchored]⟩ (cut w)
  exact ⟨S, by simpa using hS, h.symm⟩

theorem edge_compl (p q : Bool) (n : ℕ) :
    (if (!p) ≠ (!q) then n else 0) = if p ≠ q then n else 0 := by
  cases p <;> cases q <;> simp

theorem edge_submodular (s s' t t' : Bool) (n : ℕ) :
    ((if (s || t) ≠ (s' || t') then n else 0) + if (s && t) ≠ (s' && t') then n else 0) ≤
      (if s ≠ s' then n else 0) + if t ≠ t' then n else 0 := by
  cases s <;> cases s' <;> cases t <;> cases t' <;> simp

/-- The edge-by-edge inequality behind monogamy of mutual information: the map from three cuts
to four is a contraction on every edge. -/
theorem edge_monogamy (p p' q q' r r' : Bool) (n : ℕ) :
    ((((if (p && r && !q) ≠ (p' && r' && !q') then n else 0) +
        if (p && q && !r) ≠ (p' && q' && !r') then n else 0) +
        if (q && r && !p) ≠ (q' && r' && !p') then n else 0) +
        if (p || q || r) ≠ (p' || q' || r') then n else 0) ≤
      ((if p ≠ p' then n else 0) + if q ≠ q' then n else 0) + if r ≠ r' then n else 0 := by
  cases p <;> cases p' <;> cases q <;> cases q' <;> cases r <;> cases r' <;> simp

theorem anchor_first (x y z : Bool) (hxy : ¬ (x = true ∧ y = true))
    (hyz : ¬ (y = true ∧ z = true)) (hxz : ¬ (x = true ∧ z = true)) :
    ((x || y) && (x || z) && !(y || z)) = x := by
  cases x <;> cases y <;> cases z <;> simp_all

theorem cut_compl (w : V → V → ℕ) (S : V → Bool) : cut w (fun v => !S v) = cut w S := by
  unfold cut
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => edge_compl _ _ _

/-- **A region and its complement have the same minimal cut.** A boundary region and its complement have the same
Ryu-Takayanagi value: the same cut serves both. Graph analogue of `S(A) = S(Aᶜ)` for a pure global state;
no state is involved. -/
theorem rt_compl (w : V → V → ℕ) (bdy A : V → Bool) :
    rt w bdy (fun v => !A v) = rt w bdy A := by
  apply le_antisymm
  · obtain ⟨S, hS, hc⟩ := exists_min w bdy A
    rw [← hc, ← cut_compl]
    exact rt_le fun v hv => by simp [hS v hv]
  · obtain ⟨S, hS, hc⟩ := exists_min w bdy (fun v => !A v)
    rw [← hc, ← cut_compl]
    exact rt_le fun v hv => by simp [hS v hv]

/-- **Strong subadditivity for minimal cuts** (submodularity). Physics: Headrick and Takayanagi
(2007), in graph form. -/
theorem rt_submodular (w : V → V → ℕ) (bdy A B : V → Bool) :
    rt w bdy (fun v => A v || B v) + rt w bdy (fun v => A v && B v) ≤
      rt w bdy A + rt w bdy B := by
  obtain ⟨S, hS, hcS⟩ := exists_min w bdy A
  obtain ⟨T, hT, hcT⟩ := exists_min w bdy B
  have h1 : rt w bdy (fun v => A v || B v) ≤ cut w (fun v => S v || T v) :=
    rt_le fun v hv => by simp [hS v hv, hT v hv]
  have h2 : rt w bdy (fun v => A v && B v) ≤ cut w (fun v => S v && T v) :=
    rt_le fun v hv => by simp [hS v hv, hT v hv]
  have h3 : cut w (fun v => S v || T v) + cut w (fun v => S v && T v) ≤ cut w S + cut w T := by
    unfold cut
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => edge_submodular _ _ _ _ _
  omega

/-- **Monogamy of mutual information (MMI) for minimal cuts.** This is NOT the CKW monogamy of
entanglement; they are different notions, and MMI is violated by general quantum states. For three pairwise disjoint boundary
regions, `S(A) + S(B) + S(C) + S(ABC) ≤ S(AB) + S(BC) + S(AC)`, that is
`I(A:B) + I(A:C) ≤ I(A:BC)`. Physics: Hayden, Headrick and Maloney (2013) for Ryu-Takayanagi
surfaces; the graph form is in Bao et al. (2015). General quantum states do not obey it.
Reading (ours): on a network, what the first shares with the second and with the third
separately never exceeds what it shares with the two together; correlation on nodes and edges is
monogamous (in the MMI sense). -/
theorem rt_mmi (w : V → V → ℕ) (bdy A B C : V → Bool)
    (hAB : ∀ v, ¬ (A v = true ∧ B v = true)) (hBC : ∀ v, ¬ (B v = true ∧ C v = true))
    (hAC : ∀ v, ¬ (A v = true ∧ C v = true)) :
    rt w bdy A + rt w bdy B + rt w bdy C + rt w bdy (fun v => A v || B v || C v) ≤
      rt w bdy (fun v => A v || B v) + rt w bdy (fun v => B v || C v) +
        rt w bdy (fun v => A v || C v) := by
  obtain ⟨P, hP, hcP⟩ := exists_min w bdy (fun v => A v || B v)
  obtain ⟨Q, hQ, hcQ⟩ := exists_min w bdy (fun v => B v || C v)
  obtain ⟨R, hR, hcR⟩ := exists_min w bdy (fun v => A v || C v)
  have hA : rt w bdy A ≤ cut w (fun v => P v && R v && !Q v) := rt_le fun v hv => by
    simp only [hP v hv, hQ v hv, hR v hv]
    exact anchor_first _ _ _ (hAB v) (hBC v) (hAC v)
  have hB : rt w bdy B ≤ cut w (fun v => P v && Q v && !R v) := rt_le fun v hv => by
    simp only [hP v hv, hQ v hv, hR v hv]
    rw [Bool.or_comm (A v) (B v)]
    exact anchor_first _ _ _ (fun h => hAB v ⟨h.2, h.1⟩) (hAC v) (hBC v)
  have hC : rt w bdy C ≤ cut w (fun v => Q v && R v && !P v) := rt_le fun v hv => by
    simp only [hP v hv, hQ v hv, hR v hv]
    rw [Bool.or_comm (B v) (C v), Bool.or_comm (A v) (C v), Bool.or_comm (A v) (B v)]
    exact anchor_first _ _ _ (fun h => hBC v ⟨h.2, h.1⟩) (fun h => hAB v ⟨h.2, h.1⟩)
      (fun h => hAC v ⟨h.2, h.1⟩)
  have hABC : rt w bdy (fun v => A v || B v || C v) ≤ cut w (fun v => P v || Q v || R v) :=
    rt_le fun v hv => by
      simp only [hP v hv, hQ v hv, hR v hv]
      generalize A v = x; generalize B v = y; generalize C v = z
      cases x <;> cases y <;> cases z <;> rfl
  have key : cut w (fun v => P v && R v && !Q v) + cut w (fun v => P v && Q v && !R v) +
      cut w (fun v => Q v && R v && !P v) + cut w (fun v => P v || Q v || R v) ≤
        cut w P + cut w Q + cut w R := by
    unfold cut
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => edge_monogamy _ _ _ _ _ _ _
  omega

/-- **The four-party GHZ pattern is on no network.** (The three-party GHZ pattern, six values
`k` and `S(ABC) = 0`, does satisfy the inequality, and a star graph with three weight-`k` edges
to a centre node realises it; this theorem does not touch it.) In the four-party GHZ state every nonempty
proper subset of parties has the same entropy. No weighted graph, with any boundary and any
three disjoint boundary regions, gives seven equal nonzero Ryu-Takayanagi values. Physics: GHZ
entropies violate monogamy of mutual information (Hayden et al. 2013). -/
theorem no_network_has_ghz_entropies (w : V → V → ℕ) (bdy A B C : V → Bool) (k : ℕ)
    (hAB : ∀ v, ¬ (A v = true ∧ B v = true)) (hBC : ∀ v, ¬ (B v = true ∧ C v = true))
    (hAC : ∀ v, ¬ (A v = true ∧ C v = true))
    (h1 : rt w bdy A = k) (h2 : rt w bdy B = k) (h3 : rt w bdy C = k)
    (h4 : rt w bdy (fun v => A v || B v) = k) (h5 : rt w bdy (fun v => B v || C v) = k)
    (h6 : rt w bdy (fun v => A v || C v) = k)
    (h7 : rt w bdy (fun v => A v || B v || C v) = k) : k = 0 := by
  have := rt_mmi w bdy A B C hAB hBC hAC
  omega

/-- **An edge bounds the entanglement that crosses it.** If the amplitude matrix factors through
a bond space `k` (`M = L R`, as it does when a tensor network is cut along bonds whose joint index
set is `k`), then the Schmidt rank is at most the dimension of the bond. Physics: the upper-bound
half of "entropy ≤ minimal cut" for tensor network states. The contraction of a general network
into this form is NOT formalised here. -/
theorem schmidt_rank_le_bond {a b k : Type*} [Fintype a] [Fintype b] [Fintype k] [DecidableEq a]
    (L : Matrix a k ℂ) (R : Matrix k b ℂ) : (selfState (L * R)).rank ≤ Fintype.card k := by
  unfold selfState
  rw [rank_self_mul_conjTranspose]
  exact (rank_mul_le_left L R).trans (rank_le_card_width L)

/-- The same bound when the bond index is a function `E → Fin D` on an index type `E`: Schmidt
rank at most `D ^ |E|`. `E` is only an index type; nothing relates it to a graph cut or to `rt`.
The step "so entropy at most `|E| log D`" (entropy ≤ log rank) is NOT proved in this file. -/
theorem schmidt_rank_le_bond_pow {a b E : Type*} [Fintype a] [Fintype b] [Fintype E] [DecidableEq a]
    [DecidableEq E] (D : ℕ) (L : Matrix a (E → Fin D) ℂ) (R : Matrix (E → Fin D) b ℂ) :
    (selfState (L * R)).rank ≤ D ^ Fintype.card E := by
  simpa using schmidt_rank_le_bond L R

/-- True by definition, nearly: the identity matrix has full rank `card k`, so it attains the
bound. Reading (ours, not proved): after normalisation it is the amplitude matrix of one Bell
pair per bond index. -/
theorem bell_bond_saturates {k : Type*} [Fintype k] [DecidableEq k] :
    (selfState (1 : Matrix k k ℂ)).rank = Fintype.card k := by
  simp [selfState]

end Cut

/-! ## 3. Causal sets: the barbarian is beyond the horizon -/

section Causal

open PEqualNP.Philosophy.Fisher

variable {P : Type*} [PartialOrder P]

/-- Spacelike separation: neither precedes the other. Physics: unrelated elements of a causal
set (Bombelli, Lee, Meyer and Sorkin 1987). The same relation is `Hegel.Other` and
`Beauvoir.Barbarian` on a Fisher frame. -/
def Spacelike (m x : P) : Prop := ¬ m ≤ x ∧ ¬ x ≤ m

/-- Beyond the horizon: no event has both in its past. Physics: two worldlines' events with no
common causal future (as across a cosmological horizon). Reading (ours): the barbarian. -/
def Beyond (m x : P) : Prop := ¬ ∃ h, m ≤ h ∧ x ≤ h

theorem spacelike_symm {m x : P} (h : Spacelike m x) : Spacelike x m := ⟨h.2, h.1⟩

theorem beyond_symm {m x : P} (h : Beyond m x) : Beyond x m :=
  fun ⟨w, hx, hm⟩ => h ⟨w, hm, hx⟩

theorem spacelike_of_beyond {m x : P} (h : Beyond m x) : Spacelike m x :=
  ⟨fun hmx => h ⟨x, hmx, le_rfl⟩, fun hxm => h ⟨m, le_rfl, hxm⟩⟩

/-- **No common future is inherited upward.** If two events have no common future, no later events of theirs
have one. This is the permanence that `Fisher.lost_mono` gets from linear past, here with no
assumption on the order (compare `Unify.permanence_iff_no_reconciliation`). -/
theorem beyond_mono {m x m' x' : P} (h : Beyond m x) (hm : m ≤ m') (hx : x ≤ x') :
    Beyond m' x' := fun ⟨w, h1, h2⟩ => h ⟨w, hm.trans h1, hx.trans h2⟩

/-- On a Fisher frame (a tree: linear past) spacelike and beyond-the-horizon coincide. -/
theorem frame_beyond_iff_spacelike {M : Type*} [Frame M] {m x : M} :
    Beyond m x ↔ Spacelike m x :=
  ⟨spacelike_of_beyond, fun h ⟨w, h1, h2⟩ =>
    (Frame.linear_past m x w h1 h2).elim h.1 h.2⟩

/-- DEFINITIONAL ALIAS of `Beauvoir.barbarian_iff_no_common_future` (`Beyond` is defined as
exactly its right side), not a new result. On a Fisher frame, `Beauvoir.Barbarian` (an incomparable
moment) is exactly `Beyond`, and `Beauvoir.Recognise` is exactly its negation. -/
theorem barbarian_iff_beyond {M : Type*} [Frame M] {m x : M} :
    Beauvoir.Barbarian m x ↔ Beyond m x := Beauvoir.barbarian_iff_no_common_future

/-- Alias: `not_not.symm` after the previous alias; true by definition. -/
theorem recognise_iff_not_beyond {M : Type*} [Frame M] {m x : M} :
    Beauvoir.Recognise m x ↔ ¬ Beyond m x := not_not.symm

/-- **In a causal set with a diamond they come apart.** In the lattice `ℕ × ℕ` (the light-cone
lattice of 1+1 dimensions, product order) the events `(1,0)` and `(0,1)` are spacelike and meet
at `(1,1)`. -/
theorem lightcone_spacelike_meet :
    Spacelike ((1, 0) : ℕ × ℕ) (0, 1) ∧ ¬ Beyond ((1, 0) : ℕ × ℕ) (0, 1) := by
  refine ⟨⟨by simp [Prod.le_def], by simp [Prod.le_def]⟩, fun h => h ⟨(1, 1), ?_, ?_⟩⟩ <;>
    simp [Prod.le_def]

/-- So the light-cone lattice is not a Fisher frame: its past is not linear. -/
theorem lightcone_not_frame :
    ¬ ∀ a b c : ℕ × ℕ, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a := fun h => by
  have := h (1, 0) (0, 1) (1, 1) (by simp [Prod.le_def]) (by simp [Prod.le_def])
  simp [Prod.le_def] at this

/-- In a directed order (any two events have a common future, as in Minkowski space) nobody is
beyond the horizon. -/
theorem directed_no_beyond [IsDirected P (· ≤ ·)] (m x : P) : ¬ Beyond m x :=
  fun h => h (directed_of (· ≤ ·) m x)

/-- **A directed Fisher frame is a chain.** A Fisher frame in which any two
moments have a common future is a single line. -/
theorem frame_directed_total {M : Type*} [Frame M] [IsDirected M (· ≤ ·)] (a b : M) :
    a ≤ b ∨ b ≤ a := by
  obtain ⟨w, h1, h2⟩ := directed_of (· ≤ ·) a b
  exact Frame.linear_past a b w h1 h2

/-- **Order from nodes and edges.** RENAME of Mathlib's `lt_iff_transGen_covBy`, not a result of
ours. In a locally finite order (a causal set) the causal relation
is the transitive closure of its links (covering pairs). Mathlib's `lt_iff_transGen_covBy`.
Physics: a causal set is determined by its Hasse diagram. -/
theorem causal_order_from_links [LocallyFiniteOrder P] {x y : P} :
    x < y ↔ Relation.TransGen (· ⋖ ·) x y := lt_iff_transGen_covBy

end Causal

end PEqualNP.Philosophy.BeauvoirQG
