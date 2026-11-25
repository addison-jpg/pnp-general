import PEqualNP.Lateral.Lawvere
import PEqualNP.Philosophy.BeauvoirQG
import PEqualNP.Library.L010

/-!
# Cross-program joins that are theorems (seat: cross-program unification)

HONESTY. Every theorem below is elementary: finite sets, natural numbers, functions. The file
records which of the candidate joins between the programs of this repository (circuits, quantum
gravity, logic and language, philosophy) are theorems, in the weakest form that is true. The
names of the programs appear only in comments; no theorem here is about circuits of any size,
about unitaries, about spacetime, or about P versus NP. `worlds/UNIFY_ALL.md` says what each
theorem is an instance of, and lists the analogies and the failed rhymes that are NOT here.

* Part A (counting and payment): the truncation `trunc c f`, the largest potential below `f`
  that grows by at most `c` per element. `trunc_eq_iff` is the Edmonds / Nash-Williams
  inequality in its bare form; `unsplit_of_partition` is the necessity half of the payment Hall
  condition for arbitrary rank-like functions; `trunc_eq_of_lip` is the counting case.
* Part B (diagonal and counting): the diagonal names the missed function with one evaluation per
  device and needs one private point per device; halving names it with one count per point and
  reaches the full counting range.
* Part C (views): equivalence relations (views) against families of properties (classes).
  Views embed in families, not conversely; two families that contain every singleton induce the
  same view.
* Part D (payment and entanglement): the rank of three parallel payers is monotone, submodular
  and unit-increment, violates monogamy of mutual information, and is not a min-cut function.
-/

namespace PEqualNP.Worlds.Unify

open Finset

/-! ## Part A. One potential for counting and for payment -/

section Trunc

variable {E : Type*} [DecidableEq E]

/-- `g` grows by at most `c` per added element. -/
def Lip (c : ℕ) (g : Finset E → ℕ) : Prop :=
  ∀ ⦃B A : Finset E⦄, B ⊆ A → g A ≤ g B + c * (A \ B).card

/-- The truncation of the potential `f` at rate `c`: pay `f` on a part `B` and `c` for each
element outside it, at the cheapest `B`. With `c = 1` and `f` a sum of matroid ranks this is the
Edmonds / Nash-Williams formula for the rank of the matroid union (cited, not proved here). -/
def trunc (c : ℕ) (f : Finset E → ℕ) (A : Finset E) : ℕ :=
  A.powerset.inf' ⟨A, mem_powerset_self A⟩ (fun B => f B + c * (A \ B).card)

theorem trunc_le_of_subset (c : ℕ) (f : Finset E → ℕ) {A B : Finset E} (h : B ⊆ A) :
    trunc c f A ≤ f B + c * (A \ B).card :=
  Finset.inf'_le _ (mem_powerset.mpr h)

theorem exists_trunc (c : ℕ) (f : Finset E → ℕ) (A : Finset E) :
    ∃ B, B ⊆ A ∧ trunc c f A = f B + c * (A \ B).card := by
  obtain ⟨B, hB, h⟩ := Finset.exists_mem_eq_inf' (s := A.powerset) ⟨A, mem_powerset_self A⟩
    (fun B => f B + c * (A \ B).card)
  exact ⟨B, mem_powerset.mp hB, h⟩

theorem trunc_le (c : ℕ) (f : Finset E → ℕ) (A : Finset E) : trunc c f A ≤ f A := by
  simpa using trunc_le_of_subset c f (Subset.refl A)

theorem card_sdiff_split {B' B A : Finset E} (h1 : B' ⊆ B) (h2 : B ⊆ A) :
    (A \ B').card = (B \ B').card + (A \ B).card := by
  have h : A \ B' = (B \ B') ∪ (A \ B) := by
    ext x; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hA, hB'⟩
      by_cases hx : x ∈ B
      · exact Or.inl ⟨hx, hB'⟩
      · exact Or.inr ⟨hA, hx⟩
    · rintro (⟨hB, hB'⟩ | ⟨hA, hB⟩)
      · exact ⟨h2 hB, hB'⟩
      · exact ⟨hA, fun hx => hB (h1 hx)⟩
  rw [h, card_union_of_disjoint]
  rw [disjoint_left]
  intro x hx hy
  exact (mem_sdiff.mp hy).2 (mem_sdiff.mp hx).1

/-- The truncation grows by at most `c` per element. -/
theorem trunc_lip (c : ℕ) (f : Finset E → ℕ) : Lip c (trunc c f) := by
  intro B A hBA
  obtain ⟨B', hB', h⟩ := exists_trunc c f B
  have h1 := trunc_le_of_subset c f (hB'.trans hBA)
  rw [card_sdiff_split hB' hBA] at h1
  rw [h]; linarith [Nat.mul_add c (B \ B').card (A \ B).card]

/-- **The truncation is the largest potential below `f` with increments at most `c`.** -/
theorem le_trunc {c : ℕ} {f g : Finset E → ℕ} (hg : Lip c g) (hgf : ∀ A, g A ≤ f A)
    (A : Finset E) : g A ≤ trunc c f A := by
  refine (Finset.le_inf'_iff _ _).mpr fun B hB => ?_
  exact (hg (mem_powerset.mp hB)).trans (Nat.add_le_add_right (hgf B) _)

/-- For a monotone potential the truncation is monotone. -/
theorem trunc_mono {c : ℕ} {f : Finset E → ℕ} (hf : Monotone f) : Monotone (trunc c f) := by
  intro B A hBA
  obtain ⟨A', hA', h⟩ := exists_trunc c f A
  have h1 := trunc_le_of_subset c f (inter_subset_right : A' ∩ B ⊆ B)
  have h2 : f (A' ∩ B) ≤ f A' := hf inter_subset_left
  have h3 : (B \ (A' ∩ B)).card ≤ (A \ A').card := by
    apply card_le_card
    intro x hx
    simp only [mem_sdiff, mem_inter] at hx ⊢
    exact ⟨hBA hx.1, fun hxA => hx.2 ⟨hxA, hx.1⟩⟩
  show trunc c f B ≤ trunc c f A
  rw [h]
  exact h1.trans (Nat.add_le_add h2 (Nat.mul_le_mul_left c h3))

/-- **The bounded-increment count.** A potential with increments at most `c` is at most its
empty value plus `c` per element. Instances by reading (UNIFY_ALL part 1): `c = 1`, one set of a
Boolean sum, `g` = number of merges (the base bound for one set); `c = 15` or `9`, `g` = number
of real parameters of a product of two-qubit gates (the shape of L119); `g` = log of a count
(Shannon, Knill). -/
theorem lip_count {c : ℕ} {g : Finset E → ℕ} (hg : Lip c g) (A : Finset E) :
    g A ≤ g ∅ + c * A.card := by
  simpa using hg (empty_subset A)

/-- The count for the truncation: whatever `f` is, `trunc c f` is a lower bound of this shape. -/
theorem trunc_count (c : ℕ) (f : Finset E → ℕ) (A : Finset E) :
    trunc c f A ≤ f ∅ + c * A.card := by
  simpa using trunc_le_of_subset c f (empty_subset A)

/-- **The split condition.** The truncation loses nothing at `A` exactly when the
Edmonds / Nash-Williams inequality holds at `A`. With `c = 1` and `f = Σ_w r_w` this is the
equivalent form of the payment Hall condition in U1 section 1; with
`f J = Σ_w (|K_w| − c_w(J))` it is F1's Lemma D. -/
theorem trunc_eq_iff (c : ℕ) (f : Finset E → ℕ) (A : Finset E) :
    trunc c f A = f A ↔ ∀ B, B ⊆ A → f A ≤ f B + c * (A \ B).card := by
  constructor
  · intro h B hB
    rw [← h]; exact trunc_le_of_subset c f hB
  · intro h
    refine le_antisymm (trunc_le c f A) ?_
    exact (Finset.le_inf'_iff _ _).mpr fun B hB => h B (mem_powerset.mp hB)

/-- **The counting case: additivity is automatic.** If `f` itself has increments at most `c`
(a dimension, a log-count), truncation changes nothing and the split condition holds
everywhere. -/
theorem trunc_eq_of_lip {c : ℕ} {f : Finset E → ℕ} (hf : Lip c f) : trunc c f = f := by
  funext A
  exact (trunc_eq_iff c f A).mpr fun B hB => hf hB

/-- If the split condition holds at `A` and nothing is free, the count `f A ≤ c |A|` follows
(U1 section 2.2: PHC@0 implies the point lemma, `B = ∅`). -/
theorem count_of_unsplit {c : ℕ} {f : Finset E → ℕ} {A : Finset E}
    (h : trunc c f A = f A) (h0 : f ∅ = 0) : f A ≤ c * A.card := by
  have := trunc_count c f A
  omega

/-- **Where additivity is lost.** A sum of `W` potentials with unit increments has increments
at most `W`, not `1`: one element can serve every summand. -/
theorem lip_sum {ι : Type*} (W : Finset ι) (r : ι → Finset E → ℕ) (hr : ∀ w ∈ W, Lip 1 (r w)) :
    Lip W.card (fun A => ∑ w ∈ W, r w A) := by
  intro B A hBA
  have : ∑ w ∈ W, r w A ≤ ∑ w ∈ W, (r w B + (A \ B).card) :=
    Finset.sum_le_sum fun w hw => by simpa using hr w hw hBA
  simpa [Finset.sum_add_distrib] using this

/-- **Necessity of the payment Hall condition, for arbitrary rank-like functions.** Let each
`r w` be monotone with unit increments. If the sets get pairwise disjoint parts `P w ⊆ A`, each
of full value (`r w (P w) = r w A`), then the split condition holds at `A` for `f = Σ_w r_w`:
the unit truncation loses nothing. No matroid axiom is used. The converse is Edmonds' matroid
partition theorem and needs the `r w` to be matroid ranks (cited, not proved here). -/
theorem unsplit_of_partition {ι : Type*} [DecidableEq ι] (W : Finset ι) (r : ι → Finset E → ℕ)
    (hmono : ∀ w ∈ W, Monotone (r w)) (hlip : ∀ w ∈ W, Lip 1 (r w)) (A : Finset E)
    (P : ι → Finset E) (hPA : ∀ w ∈ W, P w ⊆ A)
    (hdis : ∀ w ∈ W, ∀ v ∈ W, w ≠ v → Disjoint (P w) (P v))
    (hfull : ∀ w ∈ W, r w (P w) = r w A) :
    trunc 1 (fun J => ∑ w ∈ W, r w J) A = ∑ w ∈ W, r w A := by
  refine (trunc_eq_iff 1 _ A).mpr fun B hB => ?_
  have h1 : ∀ w ∈ W, r w A ≤ r w B + (P w \ B).card := by
    intro w hw
    have h := hlip w hw (inter_subset_left : P w ∩ B ⊆ P w)
    have h' : r w (P w ∩ B) ≤ r w B := hmono w hw inter_subset_right
    have h'' : P w \ (P w ∩ B) = P w \ B := by
      ext x; simp only [mem_sdiff, mem_inter]; tauto
    rw [h''] at h
    rw [← hfull w hw]; omega
  have h2 : ∑ w ∈ W, (P w \ B).card = (W.biUnion fun w => P w \ B).card := by
    rw [card_biUnion]
    intro w hw v hv hne
    exact (hdis w hw v hv hne).mono sdiff_subset sdiff_subset
  have h3 : (W.biUnion fun w => P w \ B).card ≤ (A \ B).card := by
    apply card_le_card
    intro x hx
    obtain ⟨w, hw, hx⟩ := mem_biUnion.mp hx
    exact mem_sdiff.mpr ⟨hPA w hw (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  calc ∑ w ∈ W, r w A ≤ ∑ w ∈ W, (r w B + (P w \ B).card) := Finset.sum_le_sum h1
    _ = ∑ w ∈ W, r w B + ∑ w ∈ W, (P w \ B).card := Finset.sum_add_distrib
    _ ≤ ∑ w ∈ W, r w B + 1 * (A \ B).card := by omega

/-- The count from a partition: disjoint full parts force `Σ_w r_w(A) ≤ |A|` when the ranks
vanish on the empty set. -/
theorem count_of_partition {ι : Type*} [DecidableEq ι] (W : Finset ι) (r : ι → Finset E → ℕ)
    (hmono : ∀ w ∈ W, Monotone (r w)) (hlip : ∀ w ∈ W, Lip 1 (r w)) (A : Finset E)
    (P : ι → Finset E) (hPA : ∀ w ∈ W, P w ⊆ A)
    (hdis : ∀ w ∈ W, ∀ v ∈ W, w ≠ v → Disjoint (P w) (P v))
    (hfull : ∀ w ∈ W, r w (P w) = r w A) (h0 : ∀ w ∈ W, r w ∅ = 0) :
    ∑ w ∈ W, r w A ≤ A.card := by
  have h := unsplit_of_partition W r hmono hlip A P hPA hdis hfull
  have := count_of_unsplit (c := 1) (f := fun J => ∑ w ∈ W, r w J) h
    (Finset.sum_eq_zero h0)
  simpa using this

end Trunc

/-! ## Part B. Diagonal and counting -/

section Engines

/-- **Diagonal, explicit.** Whatever the table `e`, the flipped diagonal is not a row. The
missed function is named, and naming it at the point `a` costs one evaluation of device `a`.
This is `Lateral.no_row_of_fixed_point_free` with `g = not`. -/
theorem diag_explicit {A : Type*} (e : A → A → Bool) : (fun a => !(e a a)) ∉ Set.range e := by
  rintro ⟨a, ha⟩
  exact Lateral.no_row_of_fixed_point_free e (fun b => !b) Lateral.bnot_ne_self ⟨a, ha⟩

/-- **Counting, existence.** Fewer devices than functions: some function is no device. The
proof is the pigeonhole principle and names nothing. -/
theorem count_exists {D A : Type*} [Fintype D] [Fintype A] [DecidableEq A]
    (h : Fintype.card D < 2 ^ Fintype.card A) (e : D → A → Bool) : ∃ g, g ∉ Set.range e := by
  by_contra hc
  push Not at hc
  have hs : Function.Surjective e := hc
  have := Fintype.card_le_of_surjective e hs
  simp at this
  omega

/-- The diagonal with private points: if each device `d` has its own point `p d`, a function
that differs from every device at its point exists, and is given by a formula. -/
theorem diag_of_private {D A : Type*} (p : D → A) (hp : Function.Injective p)
    (e : D → A → Bool) : ∃ g : A → Bool, ∀ d, g (p d) ≠ e d (p d) := by
  classical
  refine ⟨fun a => if h : ∃ d, p d = a then !(e h.choose a) else false, fun d => ?_⟩
  have h : ∃ d', p d' = p d := ⟨d, rfl⟩
  have hd : h.choose = d := hp h.choose_spec
  simp only [h, dite_true, hd]
  cases e d (p d) <;> simp

/-- **The reach of private points.** One private point per device needs at most as many devices
as points. Counting (`count_exists`) reaches `2 ^ (number of points) − 1` devices. -/
theorem private_reach {D A : Type*} [Fintype D] [Fintype A] (p : D → A)
    (hp : Function.Injective p) : Fintype.card D ≤ Fintype.card A :=
  Fintype.card_le_of_injective p hp

/-- Halving: fix the value at point `0` to the one fewer devices take, keep the devices that
still agree, and continue on the remaining points. Each step is a count over the devices. -/
def halve : (m : ℕ) → Finset (Fin m → Bool) → (Fin m → Bool)
  | 0, _ => fun i => i.elim0
  | m + 1, S =>
    let b : Bool := decide (2 * (S.filter fun f => f 0 = true).card ≤ S.card)
    Fin.cons b (halve m ((S.filter fun f => f 0 = b).image Fin.tail))

/-- **Halving names the missed function over the whole counting range.** If there are fewer
than `2 ^ m` devices on `m` points, `halve m S` is none of them. The witness is explicit; the
price is that each of its `m` values is decided by counting devices, where the diagonal
evaluates one. -/
theorem halve_not_mem : ∀ (m : ℕ) (S : Finset (Fin m → Bool)), S.card < 2 ^ m → halve m S ∉ S
  | 0, S, h => by
    have : S = ∅ := by simpa using h
    simp [this]
  | m + 1, S, h => by
    intro hmem
    set b : Bool := decide (2 * (S.filter fun f => f 0 = true).card ≤ S.card) with hb
    have hsplit : (S.filter fun f => f 0 = true).card + (S.filter fun f => f 0 = false).card
        = S.card := by
      have := Finset.card_filter_add_card_filter_not (s := S) (fun f => f 0 = true)
      simpa using this
    have hhalf : 2 * (S.filter fun f => f 0 = b).card ≤ S.card := by
      by_cases hc : 2 * (S.filter fun f => f 0 = true).card ≤ S.card
      · have : b = true := by simp [hb, hc]
        rw [this]; exact hc
      · have : b = false := by simp [hb, hc]
        rw [this]; omega
    have hsmall : ((S.filter fun f => f 0 = b).image Fin.tail).card < 2 ^ m := by
      have := Finset.card_image_le (s := S.filter fun f => f 0 = b)
        (f := (Fin.tail : (Fin (m + 1) → Bool) → Fin m → Bool))
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have hrec := halve_not_mem m _ hsmall
    apply hrec
    have hval : halve (m + 1) S
        = Fin.cons b (halve m ((S.filter fun f => f 0 = b).image Fin.tail)) := rfl
    refine Finset.mem_image.mpr ⟨halve (m + 1) S, Finset.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
    · rw [hval]; simp
    · rw [hval]; simp

end Engines

/-! ## Part C. Views and families -/

section Views

variable {X : Type*}

/-- The view induced by a family of properties: two points are identified when no property in
the family separates them. -/
def viewOf (F : Set (Set X)) : Setoid X where
  r x y := ∀ S ∈ F, (x ∈ S ↔ y ∈ S)
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h S hS => (h S hS).symm,
    fun h1 h2 S hS => (h1 S hS).trans (h2 S hS)⟩

/-- The family of a view: the properties that do not separate identified points. -/
def famOf (r : Setoid X) : Set (Set X) := {S | ∀ x y, r x y → (x ∈ S ↔ y ∈ S)}

/-- The two maps form a Galois connection (order-reversing on both sides). -/
theorem view_family_galois (r : Setoid X) (F : Set (Set X)) : r ≤ viewOf F ↔ F ⊆ famOf r :=
  ⟨fun h S hS x y hxy => h hxy S hS, fun h x y hxy S hS => h hS x y hxy⟩

/-- **Views embed in families.** A view is recovered from its family. So every projection
(finite level to polynomial level, slack table to Φ, a state to its marginal) is faithfully a
family of properties. -/
theorem viewOf_famOf (r : Setoid X) : viewOf (famOf r) = r := by
  ext x y
  constructor
  · intro h
    have := (h {z | r x z} (fun a b hab => ⟨fun ha => r.trans ha hab,
      fun hb => r.trans hb (r.symm hab)⟩)).mp (r.refl x)
    exact this
  · intro h S hS
    exact hS x y h

/-- More properties, finer view. -/
theorem viewOf_anti {F G : Set (Set X)} (h : F ⊆ G) : viewOf G ≤ viewOf F :=
  fun _ _ hxy S hS => hxy S (h hS)

/-- **A family that contains every singleton sees every point.** Its view is equality. -/
theorem viewOf_eq_bot (F : Set (Set X)) (h : ∀ x, ({x} : Set X) ∈ F) : viewOf F = ⊥ := by
  ext x y
  constructor
  · intro hxy
    have := (hxy {x} (h x)).mp rfl
    exact (Set.mem_singleton_iff.mp this).symm
  · intro hxy
    have : x = y := hxy
    subst this
    exact (viewOf F).refl x

/-- **Families do not embed in views.** Any two families that contain every singleton induce
the same view, however different they are. A statement of the form "these two classes of
properties are equal" is therefore not a statement about views. -/
theorem same_view_of_singletons (F G : Set (Set X)) (hF : ∀ x, ({x} : Set X) ∈ F)
    (hG : ∀ x, ({x} : Set X) ∈ G) : viewOf F = viewOf G := by
  rw [viewOf_eq_bot F hF, viewOf_eq_bot G hG]

/-- A concrete pair: on `Bool`, the singletons alone and all four subsets are different
families with the same view. -/
theorem family_not_determined :
    ∃ F G : Set (Set Bool), F ≠ G ∧ viewOf F = viewOf G := by
  refine ⟨{S | ∃ b, S = {b}}, Set.univ, ?_, ?_⟩
  · intro h
    have : (∅ : Set Bool) ∈ {S : Set Bool | ∃ b, S = {b}} := by rw [h]; trivial
    obtain ⟨b, hb⟩ := this
    exact Set.singleton_ne_empty b hb.symm
  · exact same_view_of_singletons _ _ (fun x => ⟨x, rfl⟩) (fun _ => trivial)

/-- The instance for this repository's `P` and `NP`: if every one-string language is in `P`
(true and standard; a hypothesis here, not proved in this file), then `P` and `NP` induce the
same view of binary strings, namely equality, whether or not `P = NP`. -/
theorem p_np_same_view (h : ∀ x : List Bool, ({x} : Set (List Bool)) ∈ P)
    (hsub : P ⊆ NP) : viewOf (X := List Bool) P = viewOf (X := List Bool) NP :=
  same_view_of_singletons _ _ h (fun x => hsub (h x))

end Views

/-! ## Part D. Payment and entanglement -/

section Payment

/-- The rank of three parallel payers (three gates that can each make the same single merge):
`0` on the empty set, `1` otherwise. It is the rank function of the matroid `U(1,3)`, and also
the entropy function of three copies of one fair bit. -/
def par (A : Finset (Fin 3)) : ℕ := min A.card 1

theorem par_mono : ∀ A B : Finset (Fin 3), A ⊆ B → par A ≤ par B := by decide

theorem par_submodular : ∀ A B : Finset (Fin 3), par (A ∪ B) + par (A ∩ B) ≤ par A + par B := by
  decide

theorem par_unit : ∀ A B : Finset (Fin 3), B ⊆ A → par A ≤ par B + 1 * (A \ B).card := by
  decide

/-- **The payment rank is not monogamous.** Monogamy of mutual information,
`r(a) + r(b) + r(c) + r(abc) ≤ r(ab) + r(bc) + r(ac)`, fails for three parallel payers
(`4 ≤ 3`). Min-cut values satisfy it (`BeauvoirQG.rt_mmi`). -/
theorem par_not_mmi :
    ¬ (par {0} + par {1} + par {2} + par {0, 1, 2} ≤ par {0, 1} + par {1, 2} + par {0, 2}) := by
  decide

/-- **Three parallel payers are on no network.** No weighted graph, boundary and three disjoint
boundary regions have min-cut values equal to the payment rank of three parallel payers. This
is `BeauvoirQG.no_network_has_ghz_entropies` at `k = 1`: the same seven numbers are the
four-party GHZ entropies. -/
theorem parallel_payers_not_cut {V : Type*} [Fintype V] (w : V → V → ℕ) (bdy A B C : V → Bool)
    (hAB : ∀ v, ¬ (A v = true ∧ B v = true)) (hBC : ∀ v, ¬ (B v = true ∧ C v = true))
    (hAC : ∀ v, ¬ (A v = true ∧ C v = true)) :
    ¬ (Philosophy.BeauvoirQG.rt w bdy A = par {0} ∧ Philosophy.BeauvoirQG.rt w bdy B = par {1} ∧
      Philosophy.BeauvoirQG.rt w bdy C = par {2} ∧
      Philosophy.BeauvoirQG.rt w bdy (fun v => A v || B v) = par {0, 1} ∧
      Philosophy.BeauvoirQG.rt w bdy (fun v => B v || C v) = par {1, 2} ∧
      Philosophy.BeauvoirQG.rt w bdy (fun v => A v || C v) = par {0, 2} ∧
      Philosophy.BeauvoirQG.rt w bdy (fun v => A v || B v || C v) = par {0, 1, 2}) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hp : par {0} = 1 ∧ par {1} = 1 ∧ par {2} = 1 ∧ par {0, 1} = 1 ∧ par {1, 2} = 1 ∧
      par {0, 2} = 1 ∧ par {0, 1, 2} = 1 := by decide
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  have := Philosophy.BeauvoirQG.no_network_has_ghz_entropies w bdy A B C 1 hAB hBC hAC
    (h1.trans p1) (h2.trans p2) (h3.trans p3) (h4.trans p4) (h5.trans p5) (h6.trans p6)
    (h7.trans p7)
  exact one_ne_zero this

end Payment

end PEqualNP.Worlds.Unify
