import PEqualNP.Defs.Base
import PEqualNP.Library.L010

/-!
# Descriptive complexity: P versus NP as a question about logical languages

Task `language unification` (BOARD.md, TEAM). Prose and the honest map: `research/worlds/LANGUAGE.md`.

**Prior art, not ours.** Fagin 1974 (NP = existential second-order logic) and Immerman 1982/86,
Vardi 1982 (on ordered finite structures, P = first-order logic with least fixed points) are
textbook theorems. A Lean 4 library for descriptive complexity exists (P. Senellart,
`descriptive-complexity`, on Mathlib's `ModelTheory`); this file does not use it, because adding a
dependency needs `lake update`, which this repository forbids. This file is a small restatement
against this repository's own `P` and `NP` (`Defs/Base.lean`, Mathlib's `Turing.FinTM2`).

What is in this file:

* definitions: finite ordered structures over a vocabulary, the syntax and semantics of FO,
  FO(LFP) and ∃SO, and the classes of properties they define;
* `Fagin`, `ImmermanVardi`: the two capture theorems as `Prop`s. NOT proved here;
* `p_eq_np_iff_lfp_eq_eso` (checked): `Fagin → ImmermanVardi → (P = NP ↔ LogicsCoincide)`. The
  adapter between strings and structures is the word structure, whose encoding is the string
  itself (`enc_wordStruc`), so no machine is needed;
* `eso_subset_np` (checked): the easy half of Fagin, ∃SO ⊆ NP, from ONE unproved premise,
  `FOModelCheckingInP`. The guessed relations are the witness; their tables have polynomial
  length. The premise (a first-order sentence can be evaluated in polynomial time) is true and
  standard but needs an evaluator built on `Turing.FinTM2`; that machine is not built here;
* `lfp_isLeast` and friends (checked): for a body positive in the bound relation variable, the
  semantics of the `lfp` constructor is a least fixed point (Knaster–Tarski);
* `single_instance` (checked): a claim about one fixed structure defines at most one string.

Conventions. The universe of a structure of size `n` is `{0, …, n-1}` with the order of `ℕ`;
`lt` is an atomic formula, so every structure is ordered. Relations are untyped
(`ℕ → List ℕ → Bool`); a vocabulary `σ : List ℕ` (arities) says which values count (`Agree`).
Free variables are read as `0`. Atoms are guarded so that no formula reads outside the universe.
-/

namespace PEqualNP.Worlds.Descriptive

open PEqualNP.Library

/-- A relational vocabulary: the list of the arities of its relation symbols. -/
abbrev Vocab := List ℕ

/-- A finite ordered structure: universe `{0, …, n-1}` with the order of `ℕ`, and relation
number `i` given by its truth table on lists of elements. -/
structure Struc where
  n : ℕ
  rel : ℕ → List ℕ → Bool

/-- Two structures agree on the vocabulary `σ`: same size, and the same value of every relation
of `σ` on every tuple of the right arity inside the universe. -/
def Agree (σ : Vocab) (A B : Struc) : Prop :=
  A.n = B.n ∧ ∀ i ts, σ[i]? = some ts.length → (∀ t ∈ ts, t < A.n) → A.rel i ts = B.rel i ts

theorem Agree.refl (σ : Vocab) (A : Struc) : Agree σ A A := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem Agree.symm {σ : Vocab} {A B : Struc} (h : Agree σ A B) : Agree σ B A :=
  ⟨h.1.symm, fun i ts hi ht => (h.2 i ts hi (fun t m => h.1 ▸ ht t m)).symm⟩

/-- A property of structures that only depends on the `σ` part. -/
def Invariant (σ : Vocab) (Q : Set Struc) : Prop :=
  ∀ A B, Agree σ A B → (A ∈ Q ↔ B ∈ Q)

/-! ## Syntax -/

/-- Formulas. First-order variables and relation variables are numbered. `rel i ts` is relation
`i` of the vocabulary; `var X ts` is a relation variable, bound by `lfp`.
`lfp X xs φ ts` is `[lfp_{X, xs} φ](ts)`. -/
inductive Fml where
  | fls : Fml
  | eq : ℕ → ℕ → Fml
  | lt : ℕ → ℕ → Fml
  | rel : ℕ → List ℕ → Fml
  | var : ℕ → List ℕ → Fml
  | neg : Fml → Fml
  | or : Fml → Fml → Fml
  | and : Fml → Fml → Fml
  | ex : ℕ → Fml → Fml
  | all : ℕ → Fml → Fml
  | lfp : ℕ → List ℕ → Fml → List ℕ → Fml

/-- First-order: no fixed point and no relation variable. -/
def Fml.IsFO : Fml → Prop
  | .var _ _ => False
  | .lfp _ _ _ _ => False
  | .neg φ => φ.IsFO
  | .or φ ψ => φ.IsFO ∧ ψ.IsFO
  | .and φ ψ => φ.IsFO ∧ ψ.IsFO
  | .ex _ φ => φ.IsFO
  | .all _ φ => φ.IsFO
  | _ => True

/-- `PosIn X true φ`: every free occurrence of the relation variable `X` in `φ` is under an even
number of negations. `PosIn X false φ`: under an odd number. -/
def Fml.PosIn (X : ℕ) : Bool → Fml → Prop
  | pol, .var Y _ => pol = true ∨ Y ≠ X
  | pol, .neg φ => Fml.PosIn X (!pol) φ
  | pol, .or φ ψ => Fml.PosIn X pol φ ∧ Fml.PosIn X pol ψ
  | pol, .and φ ψ => Fml.PosIn X pol φ ∧ Fml.PosIn X pol ψ
  | pol, .ex _ φ => Fml.PosIn X pol φ
  | pol, .all _ φ => Fml.PosIn X pol φ
  | pol, .lfp Y _ φ _ => Y = X ∨ Fml.PosIn X pol φ
  | _, _ => True

/-- Well formed over `σ`: relation atoms name a relation of `σ` with the right number of
arguments, and every `lfp` body is positive in its bound variable. -/
def Fml.WF (σ : Vocab) : Fml → Prop
  | .rel i ts => σ[i]? = some ts.length
  | .neg φ => φ.WF σ
  | .or φ ψ => φ.WF σ ∧ ψ.WF σ
  | .and φ ψ => φ.WF σ ∧ ψ.WF σ
  | .ex _ φ => φ.WF σ
  | .all _ φ => φ.WF σ
  | .lfp X _ φ _ => φ.WF σ ∧ φ.PosIn X true
  | _ => True

/-! ## Semantics -/

/-- Values of the relation variables. -/
abbrev RelEnv := ℕ → List ℕ → Prop

/-- Bind the variables `xs` to the values `as`, left to right. -/
def bind (v : ℕ → ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | x :: xs, a :: as => bind (Function.update v x a) xs as
  | _, _ => v

/-- Satisfaction. Quantifiers range over the universe `{0, …, n-1}`. The `lfp` case is the
intersection of all sets closed under the body (for a positive body: the least fixed point,
`lfp_isLeast`). -/
def Holds (A : Struc) : Fml → RelEnv → (ℕ → ℕ) → Prop
  | .fls, _, _ => False
  | .eq x y, _, v => v x = v y
  | .lt x y, _, v => v x < v y
  | .rel i ts, _, v => (∀ t ∈ ts, v t < A.n) ∧ A.rel i (ts.map v) = true
  | .var X ts, ρ, v => ρ X (ts.map v)
  | .neg φ, ρ, v => ¬ Holds A φ ρ v
  | .or φ ψ, ρ, v => Holds A φ ρ v ∨ Holds A ψ ρ v
  | .and φ ψ, ρ, v => Holds A φ ρ v ∧ Holds A ψ ρ v
  | .ex x φ, ρ, v => ∃ a, a < A.n ∧ Holds A φ ρ (Function.update v x a)
  | .all x φ, ρ, v => ∀ a, a < A.n → Holds A φ ρ (Function.update v x a)
  | .lfp X xs φ ts, ρ, v =>
      ∀ S : List ℕ → Prop,
        (∀ as : List ℕ, as.length = xs.length → (∀ a ∈ as, a < A.n) →
          Holds A φ (Function.update ρ X S) (bind v xs as) → S as) →
        S (ts.map v)

/-- The structures that satisfy `φ` (free variables read as `0`, relation variables empty). -/
def Mod (φ : Fml) : Set Struc :=
  {A | Holds A φ (fun _ _ => False) (fun _ => 0)}

/-- Definable in first-order logic with order. -/
def FODef (σ : Vocab) (Q : Set Struc) : Prop :=
  ∃ φ : Fml, φ.IsFO ∧ φ.WF σ ∧ Q = Mod φ

/-- Definable in first-order logic with order and least fixed points, FO(LFP). -/
def LFPDef (σ : Vocab) (Q : Set Struc) : Prop :=
  ∃ φ : Fml, φ.WF σ ∧ Q = Mod φ

/-- Definable in existential second-order logic, ∃SO: some expansion by relations of arities `τ`
satisfies a first-order formula over `σ ++ τ`. -/
def ESODef (σ : Vocab) (Q : Set Struc) : Prop :=
  ∃ (τ : Vocab) (φ : Fml), φ.IsFO ∧ φ.WF (σ ++ τ) ∧ Q = {A | ∃ B, Agree σ A B ∧ B ∈ Mod φ}

theorem FODef.lfpDef {σ : Vocab} {Q : Set Struc} (h : FODef σ Q) : LFPDef σ Q := by
  obtain ⟨φ, -, hw, hQ⟩ := h
  exact ⟨φ, hw, hQ⟩

/-! ## Encoding structures as binary strings -/

/-- All tuples of length `a` over `{0, …, n-1}`, in lexicographic order. -/
def tuples (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | a + 1 => (List.range n).flatMap fun x => (tuples n a).map (x :: ·)

/-- The truth tables of the relations `k, k+1, …` with the arities in `σ`, one after another. -/
def tablesFrom (A : Struc) : ℕ → Vocab → List Bool
  | _, [] => []
  | k, a :: σ => (tuples A.n a).map (A.rel k) ++ tablesFrom A (k + 1) σ

/-- The binary encoding of the `σ` part of a structure: its truth tables. -/
def enc (σ : Vocab) (A : Struc) : List Bool := tablesFrom A 0 σ

/-- The language of the encodings of the members of `Q`. -/
def encLang (σ : Vocab) (Q : Set Struc) : Language Bool :=
  {x | ∃ A ∈ Q, enc σ A = x}

/-- Some relation has positive arity. Then the length of the encoding fixes the size. -/
def Pos (σ : Vocab) : Prop := ∃ a ∈ σ, 0 < a

theorem mem_tuples {n a : ℕ} {ts : List ℕ} :
    ts ∈ tuples n a ↔ ts.length = a ∧ ∀ t ∈ ts, t < n := by
  induction a generalizing ts with
  | zero =>
    simp only [tuples, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | succ a ih =>
    simp only [tuples, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨x, hx, us, hus, rfl⟩
      obtain ⟨h1, h2⟩ := ih.mp hus
      refine ⟨by simp [h1], ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hx
      · exact h2 t ht
    · rintro ⟨hl, hr⟩
      cases ts with
      | nil => simp at hl
      | cons x us =>
        refine ⟨x, hr x (by simp), us, ih.mpr ⟨by simpa using hl, fun t ht => hr t (by simp [ht])⟩,
          rfl⟩

theorem length_tuples (n a : ℕ) : (tuples n a).length = n ^ a := by
  induction a with
  | zero => simp [tuples]
  | succ a ih =>
    simp only [tuples, List.length_flatMap, List.length_map, ih]
    simp [pow_succ, mul_comm]

theorem length_tablesFrom (A : Struc) (k : ℕ) (σ : Vocab) :
    (tablesFrom A k σ).length = (σ.map (A.n ^ ·)).sum := by
  induction σ generalizing k with
  | nil => rfl
  | cons a σ ih => simp [tablesFrom, length_tuples, ih]

theorem tablesFrom_append (A : Struc) (k : ℕ) (σ τ : Vocab) :
    tablesFrom A k (σ ++ τ) = tablesFrom A k σ ++ tablesFrom A (k + σ.length) τ := by
  induction σ generalizing k with
  | nil => simp [tablesFrom]
  | cons a σ ih =>
    simp only [List.cons_append, tablesFrom, ih, List.append_assoc, List.length_cons]
    rw [show k + 1 + σ.length = k + (σ.length + 1) by omega]

theorem tablesFrom_congr {A B : Struc} (hn : A.n = B.n) (σ : Vocab) (k : ℕ)
    (h : ∀ j ts, σ[j]? = some ts.length → (∀ t ∈ ts, t < A.n) →
      A.rel (k + j) ts = B.rel (k + j) ts) :
    tablesFrom A k σ = tablesFrom B k σ := by
  induction σ generalizing k with
  | nil => rfl
  | cons a σ ih =>
    simp only [tablesFrom]
    congr 1
    · rw [← hn]
      refine List.map_congr_left fun ts hts => ?_
      obtain ⟨h1, h2⟩ := mem_tuples.mp hts
      exact h 0 ts (by simp [h1]) h2
    · refine ih (k + 1) fun j ts hj ht => ?_
      have := h (j + 1) ts (by simpa using hj) ht
      rwa [show k + (j + 1) = k + 1 + j by omega] at this

theorem enc_congr {σ : Vocab} {A B : Struc} (h : Agree σ A B) : enc σ A = enc σ B :=
  tablesFrom_congr h.1 σ 0 fun j ts hj ht => by simpa using h.2 j ts hj ht

/-- With a relation of positive arity, the encoding is at least as long as the universe. -/
theorem size_le_length_enc {σ : Vocab} (hσ : Pos σ) (A : Struc) : A.n ≤ (enc σ A).length := by
  obtain ⟨a, ha, hpos⟩ := hσ
  rw [enc, length_tablesFrom]
  calc A.n = A.n ^ 1 := (pow_one _).symm
    _ ≤ A.n ^ a := by
        rcases Nat.eq_zero_or_pos A.n with h0 | h0
        · rw [h0]; simp [Nat.pos_iff_ne_zero.mp hpos]
        · exact Nat.pow_le_pow_right h0 hpos
    _ ≤ (σ.map (A.n ^ ·)).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-! ## The two capture theorems, as statements (not proved here) -/

/-- Fagin 1974: a property of finite structures is definable in ∃SO exactly when the language of
its encodings is in NP. -/
def Fagin : Prop :=
  ∀ σ : Vocab, Pos σ → ∀ Q : Set Struc, Invariant σ Q → (ESODef σ Q ↔ encLang σ Q ∈ NP)

/-- Immerman 1982/86, Vardi 1982: a property of finite ordered structures is definable in
FO(LFP) exactly when the language of its encodings is in P. -/
def ImmermanVardi : Prop :=
  ∀ σ : Vocab, Pos σ → ∀ Q : Set Struc, Invariant σ Q → (LFPDef σ Q ↔ encLang σ Q ∈ P)

/-- FO(LFP) and ∃SO define the same properties of finite ordered structures. -/
def LogicsCoincide : Prop :=
  ∀ σ : Vocab, Pos σ → ∀ Q : Set Struc, Invariant σ Q → (LFPDef σ Q ↔ ESODef σ Q)

/-! ## The adapter: a binary string is a structure with one unary relation -/

/-- The word structure of a string: positions `0 … |x|-1`, one unary relation "bit is 1". -/
def wordStruc (x : List Bool) : Struc where
  n := x.length
  rel := fun _ ts => x.getD (ts.headD 0) false

theorem tuples_one (n : ℕ) : tuples n 1 = (List.range n).map fun i => [i] := by
  simp only [tuples, List.map_cons, List.map_nil]
  induction List.range n with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The encoding of the word structure of `x` is `x`. -/
theorem enc_wordStruc (x : List Bool) : enc [1] (wordStruc x) = x := by
  simp only [enc, tablesFrom, List.append_nil, tuples_one, List.map_map]
  apply List.ext_getElem
  · simp [wordStruc]
  · intro i h1 h2
    simp [wordStruc, List.getD_eq_getElem?_getD, h2]

/-- The property of structures over one unary relation that a language defines. -/
def wordProp (L : Language Bool) : Set Struc := {A | enc [1] A ∈ L}

theorem wordProp_invariant (L : Language Bool) : Invariant [1] (wordProp L) := by
  intro A B h
  simp only [wordProp, Set.mem_ofPred_eq, enc_congr h]

theorem encLang_wordProp (L : Language Bool) : encLang [1] (wordProp L) = L := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact hA
  · intro hx
    exact ⟨wordStruc x, by simpa [wordProp, enc_wordStruc] using hx, enc_wordStruc x⟩

theorem pos_one : Pos [1] := ⟨1, by simp, Nat.one_pos⟩

/-! ## The formal equivalence -/

/-- **P versus NP in terms of logical languages.** Granted the two capture theorems (hypotheses
here), this repository's `P = NP` holds exactly when FO(LFP) and ∃SO define the same properties
of finite ordered structures. A restatement: it moves nothing. -/
theorem p_eq_np_iff_lfp_eq_eso (hF : Fagin) (hIV : ImmermanVardi) :
    P = NP ↔ LogicsCoincide := by
  constructor
  · intro h σ hσ Q hQ
    rw [hIV σ hσ Q hQ, hF σ hσ Q hQ, h]
  · intro h
    ext L
    have h1 := hIV [1] pos_one _ (wordProp_invariant L)
    have h2 := hF [1] pos_one _ (wordProp_invariant L)
    have h3 := h [1] pos_one _ (wordProp_invariant L)
    rw [encLang_wordProp] at h1 h2
    rw [← h1, ← h2, h3]

/-- Granted the two capture theorems, every FO(LFP) property is an ∃SO property; this is
`P ⊆ NP` (L-lib-010) read in logic. -/
theorem lfpDef_esoDef (hF : Fagin) (hIV : ImmermanVardi) {σ : Vocab} (hσ : Pos σ)
    {Q : Set Struc} (hQ : Invariant σ Q) (h : LFPDef σ Q) : ESODef σ Q :=
  (hF σ hσ Q hQ).mpr (PEqualNP.Library.L010 ((hIV σ hσ Q hQ).mp h))

/-! ## One cheap direction: ∃SO ⊆ NP, from first-order model checking -/

/-- The unproved premise: a first-order sentence over `σ ++ τ` can be evaluated in polynomial
time, the structure being handed over in two pieces (the tables of `σ`, the tables of `τ`).
True and standard; it needs an evaluator machine on `Turing.FinTM2`, not built here. -/
def FOModelCheckingInP : Prop :=
  ∀ (σ τ : Vocab) (φ : Fml), φ.IsFO → φ.WF (σ ++ τ) →
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | ∃ B ∈ Mod φ, enc σ B = p.1 ∧ tablesFrom B σ.length τ = p.2}

/-- The polynomial `Σ_b X^b` over the arities `b` of `τ`: the length of the guessed tables. -/
noncomputable def tablePoly (τ : Vocab) : Polynomial ℕ :=
  (τ.map fun b => (Polynomial.X : Polynomial ℕ) ^ b).sum

theorem eval_tablePoly (τ : Vocab) (m : ℕ) :
    (tablePoly τ).eval m = (τ.map (m ^ ·)).sum := by
  induction τ with
  | nil => simp [tablePoly]
  | cons b τ ih =>
    simp only [tablePoly, List.map_cons, List.sum_cons, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X] at ih ⊢
    rw [ih]

theorem sum_pow_mono (τ : Vocab) {n m : ℕ} (h : n ≤ m) :
    (τ.map (n ^ ·)).sum ≤ (τ.map (m ^ ·)).sum := by
  induction τ with
  | nil => simp
  | cons b τ ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (Nat.pow_le_pow_left h b) ih

/-- **∃SO ⊆ NP**, granted first-order model checking in polynomial time. The witness is the
truth tables of the guessed relations; the verifier is the first-order evaluator. -/
theorem eso_subset_np (hFO : FOModelCheckingInP) {σ : Vocab} (hσ : Pos σ) {Q : Set Struc}
    (h : ESODef σ Q) : encLang σ Q ∈ NP := by
  obtain ⟨τ, φ, hfo, hwf, rfl⟩ := h
  refine ⟨_, tablePoly τ, hFO σ τ φ hfo hwf, fun x => ?_⟩
  constructor
  · rintro ⟨A, ⟨B, hAB, hB⟩, rfl⟩
    refine ⟨tablesFrom B σ.length τ, ?_, B, hB, (enc_congr hAB).symm, rfl⟩
    rw [length_tablesFrom, eval_tablePoly, ← hAB.1]
    exact sum_pow_mono τ (size_le_length_enc hσ A)
  · rintro ⟨w, -, B, hB, hx, -⟩
    exact ⟨B, ⟨B, Agree.refl σ B, hB⟩, hx⟩

/-- So the hard half of Fagin (NP ⊆ ∃SO) and the evaluator are all that `Fagin` asks beyond
`eso_subset_np`. -/
theorem fagin_of_halves (hFO : FOModelCheckingInP)
    (hard : ∀ σ : Vocab, Pos σ → ∀ Q : Set Struc, Invariant σ Q → encLang σ Q ∈ NP → ESODef σ Q) :
    Fagin :=
  fun σ hσ Q hQ => ⟨eso_subset_np hFO hσ, hard σ hσ Q hQ⟩

/-! ## The `lfp` constructor is a least fixed point -/

/-- Monotonicity in a relation variable, by polarity. -/
theorem holds_mono (A : Struc) (X : ℕ) {S T : List ℕ → Prop} (hST : ∀ as, S as → T as) :
    ∀ (φ : Fml) (pol : Bool) (ρ : RelEnv) (v : ℕ → ℕ), φ.PosIn X pol →
      (pol = true → Holds A φ (Function.update ρ X S) v → Holds A φ (Function.update ρ X T) v) ∧
      (pol = false → Holds A φ (Function.update ρ X T) v → Holds A φ (Function.update ρ X S) v)
  | .fls, _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .eq _ _, _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .lt _ _, _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .rel _ _, _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .var Y ts, pol, ρ, v, hp => by
    simp only [Holds, Function.update_apply]
    by_cases hY : Y = X
    · simp only [hY, ite_true]
      refine ⟨fun _ h => hST _ h, fun hpol => ?_⟩
      rcases hp with hp | hp
      · rw [hp] at hpol; cases hpol
      · exact absurd hY hp
    · simp only [hY, ite_false]
      exact ⟨fun _ h => h, fun _ h => h⟩
  | .neg φ, pol, ρ, v, hp => by
    have ih := holds_mono A X hST φ (!pol) ρ v hp
    simp only [Holds]
    refine ⟨fun hpol h h' => h (ih.2 (by simp [hpol]) h'), fun hpol h h' => h (ih.1 (by simp [hpol]) h')⟩
  | .or φ ψ, pol, ρ, v, hp => by
    have i1 := holds_mono A X hST φ pol ρ v hp.1
    have i2 := holds_mono A X hST ψ pol ρ v hp.2
    simp only [Holds]
    exact ⟨fun hpol h => h.imp (i1.1 hpol) (i2.1 hpol), fun hpol h => h.imp (i1.2 hpol) (i2.2 hpol)⟩
  | .and φ ψ, pol, ρ, v, hp => by
    have i1 := holds_mono A X hST φ pol ρ v hp.1
    have i2 := holds_mono A X hST ψ pol ρ v hp.2
    simp only [Holds]
    exact ⟨fun hpol h => h.imp (i1.1 hpol) (i2.1 hpol), fun hpol h => h.imp (i1.2 hpol) (i2.2 hpol)⟩
  | .ex x φ, pol, ρ, v, hp => by
    simp only [Holds]
    refine ⟨fun hpol ⟨a, ha, h⟩ => ⟨a, ha, (holds_mono A X hST φ pol ρ _ hp).1 hpol h⟩,
      fun hpol ⟨a, ha, h⟩ => ⟨a, ha, (holds_mono A X hST φ pol ρ _ hp).2 hpol h⟩⟩
  | .all x φ, pol, ρ, v, hp => by
    simp only [Holds]
    refine ⟨fun hpol h a ha => (holds_mono A X hST φ pol ρ _ hp).1 hpol (h a ha),
      fun hpol h a ha => (holds_mono A X hST φ pol ρ _ hp).2 hpol (h a ha)⟩
  | .lfp Y xs φ ts, pol, ρ, v, hp => by
    simp only [Holds]
    by_cases hY : Y = X
    · subst hY
      simp only [Function.update_idem]
      exact ⟨fun _ h => h, fun _ h => h⟩
    · have hne : X ≠ Y := fun h => hY h.symm
      have hp' : φ.PosIn X pol := hp.resolve_left hY
      refine ⟨fun hpol h S' hS' => h S' fun as h1 h2 hb => hS' as h1 h2 ?_,
        fun hpol h S' hS' => h S' fun as h1 h2 hb => hS' as h1 h2 ?_⟩
      · rw [Function.update_comm hne] at hb ⊢
        exact (holds_mono A X hST φ pol _ _ hp').1 hpol hb
      · rw [Function.update_comm hne] at hb ⊢
        exact (holds_mono A X hST φ pol _ _ hp').2 hpol hb

/-- The relation a fixed point formula defines: the intersection of all closed sets. -/
def lfpSet (A : Struc) (X : ℕ) (xs : List ℕ) (φ : Fml) (ρ : RelEnv) (v : ℕ → ℕ) :
    List ℕ → Prop :=
  fun bs => ∀ S : List ℕ → Prop,
    (∀ as : List ℕ, as.length = xs.length → (∀ a ∈ as, a < A.n) →
      Holds A φ (Function.update ρ X S) (bind v xs as) → S as) → S bs

/-- One application of the body, as an operator on relations. -/
def lfpStep (A : Struc) (X : ℕ) (xs : List ℕ) (φ : Fml) (ρ : RelEnv) (v : ℕ → ℕ)
    (S : List ℕ → Prop) : List ℕ → Prop :=
  fun as => as.length = xs.length ∧ (∀ a ∈ as, a < A.n) ∧
    Holds A φ (Function.update ρ X S) (bind v xs as)

theorem holds_lfp_iff (A : Struc) (X : ℕ) (xs : List ℕ) (φ : Fml) (ts : List ℕ) (ρ : RelEnv)
    (v : ℕ → ℕ) : Holds A (.lfp X xs φ ts) ρ v ↔ lfpSet A X xs φ ρ v (ts.map v) := Iff.rfl

/-- The defined relation is below every set closed under the body. -/
theorem lfpSet_le (A : Struc) (X : ℕ) (xs : List ℕ) (φ : Fml) (ρ : RelEnv) (v : ℕ → ℕ)
    (S : List ℕ → Prop) (hS : ∀ as, lfpStep A X xs φ ρ v S as → S as) :
    ∀ bs, lfpSet A X xs φ ρ v bs → S bs :=
  fun _ h => h S fun as h1 h2 h3 => hS as ⟨h1, h2, h3⟩

/-- **Least fixed point.** For a body positive in `X`, the defined relation is a fixed point of
the body; by `lfpSet_le` it is the least one. -/
theorem lfp_isLeast (A : Struc) (X : ℕ) (xs : List ℕ) (φ : Fml) (ρ : RelEnv) (v : ℕ → ℕ)
    (hp : φ.PosIn X true) (bs : List ℕ) :
    lfpSet A X xs φ ρ v bs ↔ lfpStep A X xs φ ρ v (lfpSet A X xs φ ρ v) bs := by
  have mono : ∀ {S T : List ℕ → Prop}, (∀ as, S as → T as) →
      ∀ as, lfpStep A X xs φ ρ v S as → lfpStep A X xs φ ρ v T as :=
    fun hST as ⟨h1, h2, h3⟩ => ⟨h1, h2, (holds_mono A X hST φ true ρ _ hp).1 rfl h3⟩
  have closed : ∀ as, lfpStep A X xs φ ρ v (lfpSet A X xs φ ρ v) as → lfpSet A X xs φ ρ v as := by
    intro as h S hS
    have hle : ∀ cs, lfpSet A X xs φ ρ v cs → S cs := fun cs hcs => hcs S hS
    obtain ⟨h1, h2, h3⟩ := mono hle as h
    exact hS as h1 h2 h3
  refine ⟨fun h => ?_, closed bs⟩
  exact lfpSet_le A X xs φ ρ v _ (fun as has => mono closed as has) bs h

/-! ## asteroid on this map: one instance, not a language -/

/-- A claim about ONE fixed structure `A` (as every `.ath` claim is about fixed circuits): the
property "is `A`, and `Q` holds" has at most one encoding. Such a claim has a truth value and a
checking cost, but no growth rate, so it has no place among P, NP or the logics above. -/
theorem single_instance (σ : Vocab) (A : Struc) (Q : Set Struc) :
    ∀ x ∈ encLang σ {B | Agree σ A B ∧ B ∈ Q}, x = enc σ A := by
  rintro x ⟨B, ⟨hAB, -⟩, rfl⟩
  exact (enc_congr hAB).symm

/-- `forall cubes` in a `.ath` claim ranges over the subsets of `n` points: `2 ^ n` cases. -/
theorem cube_count (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp

/-- `forall states` ranges over the pairs of disjoint sets (each point: in Q, in R, or free):
`3 ^ n` cases. -/
theorem state_count (n : ℕ) : Fintype.card (Fin n → Fin 3) = 3 ^ n := by simp

end PEqualNP.Worlds.Descriptive
