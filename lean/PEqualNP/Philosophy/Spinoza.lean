import Mathlib

/-!
# Spinoza, *Ethica* Pars III: the affects as passages of a power of acting (emotion seat)

HONESTY. This file models one reading of *Ethica ordine geometrico demonstrata* (1677), Pars III.
Every theorem is a fact about sums and orders. The Latin is placed next to each definition; the
gloss after it is ours. Latin read status: quoted from memory and checked against an OCR scan of a
nineteenth-century Latin edition where the scan is legible (III Def. 3, P6, P12, P13, P17, P24, P44,
Aff. Def. 1, 2, 3 with the explicatio, 6, 7); the others (P4, P7, P11 schol., P13 cor. and schol.,
P18 schol. 2, P21 to P23, P51, P59, Aff. Def. 13 expl.) are from memory only. See `LITERATURE.md`.

THE HYPOTHESES THAT DO THE WORK (ours, not Spinoza's):

* **H1, a state function.** "Perfectio" / "agendi potentia" is a function `P` of the state with
  values in an ordered group. Spinoza gives no such function. Section 1 follows from H1 alone.
* **H2, additivity.** The power of a mind that imagines a set `A` of things is `∑ i ∈ A, w i`.
  Spinoza has no such sum.
* **H3, conatus as maximality.** "Quantum potest ... conatur" is read as: the mind holds a set of
  images of greatest power among the feasible ones (`Endeavours`). Spinoza derives P12 and P13
  from P6, P7, P9, P11 and II P17; here P6 is not derived, it is the definition `Endeavours`.
* **H4, love as dependence.** In section 3, "I love x" is read as: my power is a strictly
  increasing function of the power of x. Spinoza proves P19 to P24 from P12 and P13.
* **H5, a doubt weight.** In section 4 doubt is a number `q` between 0 and 1. Spinoza has
  "dubitamus" and "inconstans", no number.

What fails is recorded too: under H2 one scalar per image makes P17 (animi fluctuatio) impossible
for an object with one image (`fluctuates_two_images`).

Deleuze's reading (*Spinoza. Philosophie pratique*, 1981, ch. 3 and 4; cited, not opened): affectus
is the passage, the lived variation of the power of acting, as against affectio, the state. H1 with
`affect` is that reading in its barest form. `Deleuze.lean` in this directory models the virtual and
the actual and has no affect in it; nothing here depends on it.
-/

namespace PEqualNP.Philosophy.Spinoza

set_option linter.unusedSectionVars false

/-! ### 1. Affect as passage (III Def. 3; P11 schol.; Aff. Def. 2, 3) -/

section Passage

variable {S G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- "Per Affectum intelligo Corporis affectiones, quibus ipsius Corporis agendi potentia augetur vel
minuitur, juvatur vel coercetur, et simul harum affectionum ideas." (III Def. 3: by affect I
understand the affections of the body by which its power of acting is increased or lessened, helped
or checked, together with the ideas of these affections.) Model, under H1: the change of `P` in a
passage from state `s` to state `t`. The "ideas" half of the definition is not modelled. -/
def affect (P : S → G) (s t : S) : G := P t - P s

/-- "Laetitia est hominis transitio a minore ad majorem perfectionem." (Aff. Def. 2: joy is a
man's passage from a lesser to a greater perfection.) -/
def Joy (P : S → G) (s t : S) : Prop := 0 < affect P s t

/-- "Tristitia est hominis transitio a majore ad minorem perfectionem." (Aff. Def. 3.) -/
def Sadness (P : S → G) (s t : S) : Prop := affect P s t < 0

theorem joy_iff (P : S → G) (s t : S) : Joy P s t ↔ P s < P t := sub_pos

theorem sadness_iff (P : S → G) (s t : S) : Sadness P s t ↔ P t < P s := sub_neg

/-- Affects add along consecutive passages. This is H1 and nothing else. -/
theorem affect_trans (P : S → G) (s t u : S) : affect P s t + affect P t u = affect P s u := by
  simp [affect]

/-- The return passage of a joy is a sadness of the same size. -/
theorem joy_iff_sadness_back (P : S → G) (s t : S) : Joy P s t ↔ Sadness P t s := by
  rw [joy_iff, sadness_iff]

/-- The affects along a walk `σ 0, σ 1, …, σ n` sum to the affect of the whole passage. -/
theorem sum_affect (P : S → G) (σ : ℕ → S) (n : ℕ) :
    ∑ i ∈ Finset.range n, affect P (σ i) (σ (i + 1)) = affect P (σ 0) (σ n) := by
  simpa [affect] using Finset.sum_range_sub (fun i => P (σ i)) n

/-- **A round trip has as much sadness as joy.** If a walk returns to its starting state and one
step of it is a joy, another step is a sadness. A consequence of H1 that Spinoza does not state;
it is the price of reading perfection as a function of the state. -/
theorem sadness_of_round_trip (P : S → G) (σ : ℕ → S) (n : ℕ) (hclosed : σ n = σ 0)
    {i : ℕ} (hi : i < n) (hjoy : Joy P (σ i) (σ (i + 1))) :
    ∃ j < n, Sadness P (σ j) (σ (j + 1)) := by
  by_contra hno
  have hnn : ∀ j ∈ Finset.range n, 0 ≤ affect P (σ j) (σ (j + 1)) := by
    intro j hj
    by_contra hneg
    exact hno ⟨j, Finset.mem_range.mp hj, not_le.mp hneg⟩
  have hsum : ∑ j ∈ Finset.range n, affect P (σ j) (σ (j + 1)) = 0 := by
    rw [sum_affect, hclosed]; simp [affect]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_range.mpr hi)
  exact absurd hjoy (by simp [Joy, this])

/-- "Dico transitionem. Nam Laetitia non est ipsa perfectio." (Aff. Def. 3, explicatio: I say
passage, for joy is not perfection itself.) In the model: no property of the state arrived at
decides whether the passage was a joy. Shown on `S = ℤ` with `P` the identity. -/
theorem joy_is_not_a_state : ¬ ∃ J : ℤ → Prop, ∀ s t : ℤ, Joy (fun x : ℤ => x) s t ↔ J t := by
  rintro ⟨J, hJ⟩
  have h1 : Joy (fun x : ℤ => x) 0 1 := by simp [Joy, affect]
  have h2 : ¬ Joy (fun x : ℤ => x) 2 1 := by simp [Joy, affect]
  exact h2 ((hJ 2 1).mpr ((hJ 0 1).mp h1))

/-- "Odium, quod Amore plane vincitur, in Amorem transit; et Amor propterea major est, quam si
Odium non praecessisset." (III P44: hate that is wholly overcome by love passes into love, and
the love is greater than if hate had not come before.) In the model: `h` the state of hating,
`n` the state without either, `l` the state of loving. If hating is below `n`, the passage
`h → l` is a greater joy than `n → l`, by exactly the sadness removed. Spinoza's demonstration
adds the same two joys; under H1 it is `affect_trans`. -/
theorem love_after_hate (P : S → G) (h n l : S) (hhate : Sadness P n h) :
    affect P n l < affect P h l ∧ affect P h l = affect P h n + affect P n l := by
  refine ⟨?_, (affect_trans P h n l).symm⟩
  have := (sadness_iff P n h).mp hhate
  simpa [affect] using this

end Passage

/-! ### 2. Conatus as maximality: P12, P13, the scholium on love and hate, P59 -/

section Conatus

variable {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- H2. The power of a mind that imagines the set `A`: each image `i` adds `w i`. The weight is
positive for what "augent vel juvant" (increase or help) and negative for what "minuunt vel
coercent" (lessen or check) the power of acting. -/
def power (w : ι → G) (A : Finset ι) : G := ∑ i ∈ A, w i

/-- H3. "Unaquaeque res, quantum in se est, in suo esse perseverare conatur." (III P6: each thing,
as far as it lies in itself, endeavours to persist in its being.) Read as maximality: among the
feasible sets of images `F` (what "quantum potest" allows), the mind holds one of greatest power.
This is a definition here, not a theorem; Spinoza proves P6 from P4 and P5. -/
def Endeavours (w : ι → G) (F : Set (Finset ι)) (A : Finset ι) : Prop :=
  A ∈ F ∧ ∀ B ∈ F, power w B ≤ power w A

/-- "Amor nihil aliud est, quam Laetitia concomitante idea causae externae." (III P13 schol.;
Aff. Def. 6: love is joy with the accompanying idea of an external cause.) Model: the image of
the thing raises power. The "idea of a cause" is reduced to the index `i`. -/
def Loves (w : ι → G) (i : ι) : Prop := 0 < w i

/-- "Odium nihil aliud [est], quam Tristitia concomitante idea causae externae." (III P13 schol.;
Aff. Def. 7.) -/
def Hates (w : ι → G) (i : ι) : Prop := w i < 0

/-- "Mens, quantum potest, ea imaginari conatur, quae Corporis agendi potentiam augent vel
juvant." (III P12: the mind, as far as it can, endeavours to imagine what increases or helps the
body's power of acting.) Under H2 and H3: if adding the image `i` is feasible and `i` helps, an
endeavouring mind already holds it. With `Loves`, this is also the first half of the scholium to
P13: "qui amat, necessario conatur rem, quam amat, praesentem habere et conservare". -/
theorem imagines_what_helps {w : ι → G} {F : Set (Finset ι)} {A : Finset ι} {i : ι}
    (hA : Endeavours w F A) (hi : Loves w i) (hF : insert i A ∈ F) : i ∈ A := by
  by_contra hni
  have h := hA.2 _ hF
  rw [power, Finset.sum_insert hni] at h
  have : power w A < w i + power w A := lt_add_of_pos_left _ hi
  exact absurd h (not_le.mpr this)

/-- "Hinc sequitur, quod Mens ea imaginari aversatur, quae ipsius et Corporis potentiam minuunt
vel coercent." (III P13 cor.: the mind is averse to imagining what lessens its power.) Under H2
and H3: if dropping the image `i` is feasible and `i` harms, an endeavouring mind does not hold
it. With `Hates`: "qui odit, rem, quam odio habet, amovere et destruere conatur". -/
theorem averse_to_what_harms {w : ι → G} {F : Set (Finset ι)} {A : Finset ι} {i : ι}
    (hA : Endeavours w F A) (hi : Hates w i) (hF : A.erase i ∈ F) : i ∉ A := by
  intro hmem
  have h := hA.2 _ hF
  have hsplit : w i + power w (A.erase i) = power w A := Finset.add_sum_erase A w hmem
  have : power w A < power w (A.erase i) := by
    rw [← hsplit]; exact add_lt_of_neg_left _ hi
  exact absurd h (not_le.mpr this)

/-- "Cum Mens ea imaginatur, quae Corporis agendi potentiam minuunt vel coercent, conatur,
quantum potest, rerum recordari, quae horum existentiam secludunt." (III P13: when the mind
imagines what lessens the body's power, it endeavours, as far as it can, to recall things that
exclude their existence.)

Model. The harmful image `i` cannot simply be dropped (its cause is present). Recalling `j`
"excludes" `i`: the feasible move is to replace `i` by `j` (II P17: the mind regards a thing as
present until it is affected by an idea that excludes its presence; that proposition is built into
the shape of the move, not proved). Then an endeavouring mind has no better excluder left unused.
The hypothesis is only `w i < w j`, so a lesser harm is recalled to exclude a greater one; Spinoza
states the case where `i` harms. -/
theorem recalls_what_excludes {w : ι → G} {F : Set (Finset ι)} {A : Finset ι} {i j : ι}
    (hA : Endeavours w F A) (hi : i ∈ A) (hj : j ∉ A) (hw : w i < w j) :
    insert j (A.erase i) ∉ F := by
  intro hF
  have h := hA.2 _ hF
  have hj' : j ∉ A.erase i := fun hmem => hj (Finset.mem_of_mem_erase hmem)
  rw [power, Finset.sum_insert hj'] at h
  have hsplit : w i + ∑ x ∈ A.erase i, w x = power w A := Finset.add_sum_erase A w hi
  have : power w A < w j + ∑ x ∈ A.erase i, w x := by
    rw [← hsplit]; gcongr
  exact absurd h (not_le.mpr this)

/-- "Inter omnes affectus, qui ad Mentem, quatenus agit, referuntur, nulli alii sunt, quam qui ad
Laetitiam vel Cupiditatem referuntur." (III P59: among the affects that belong to the mind in so
far as it acts, there are none but those of joy or desire.) Together with "Nulla res, nisi a causa
externa, potest destrui" (III P4).

Under H3: if an endeavouring mind passes to lesser power, the set it held is no longer feasible.
Something outside took an option away. Reading "quatenus agit" as "the feasible family did not
lose the held set" is ours. -/
theorem sadness_needs_external {w : ι → G} {F' : Set (Finset ι)} {A B : Finset ι}
    (hB : Endeavours w F' B) (h : power w B < power w A) : A ∉ F' :=
  fun hmem => absurd (hB.2 A hmem) (not_le.mpr h)

/-- The same statement in the positive: while no option is removed, there is no sadness. -/
theorem no_sadness_while_options_stay {w : ι → G} {F F' : Set (Finset ι)} {A B : Finset ι}
    (hA : Endeavours w F A) (hB : Endeavours w F' B) (hsub : F ⊆ F') : power w A ≤ power w B :=
  hB.2 A (hsub hA.1)

/-! #### What fails: animi fluctuatio (P17) -/

/-- One image cannot be loved and hated at once. Immediate from the two definitions. -/
theorem not_loves_and_hates (w : ι → G) (i : ι) : ¬ (Loves w i ∧ Hates w i) :=
  fun h => lt_asymm h.1 h.2

/-- "Si rem, quae nos Tristitiae affectu afficere solet, aliquid habere imaginamur simile alteri,
quae nos aeque magno Laetitiae affectu solet afficere, eandem odio habebimus et simul amabimus."
(III P17: we shall hate it and love it at once.) "Haec Mentis constitutio ... animi vocatur
fluctuatio." An object is given here by the set `I` of its images. -/
def Fluctuates (w : ι → G) (I : Finset ι) : Prop := (∃ i ∈ I, Loves w i) ∧ ∃ i ∈ I, Hates w i

/-- **The scalar model cannot hold P17.** An object that is loved and hated at once has at least
two images. So with one number per object (`I` a singleton) vacillation is contradictory, though
Spinoza asserts it; the model needs the object split into aspects ("aliquid ... simile"). -/
theorem fluctuates_two_images {w : ι → G} {I : Finset ι} (h : Fluctuates w I) : 1 < I.card := by
  obtain ⟨⟨i, hi, hli⟩, j, hj, hhj⟩ := h
  refine Finset.one_lt_card.mpr ⟨i, hi, j, hj, ?_⟩
  rintro rfl
  exact not_loves_and_hates w i ⟨hli, hhj⟩

/-- With two images vacillation is consistent. -/
theorem fluctuation_exists : ∃ w : Bool → ℤ, Fluctuates w Finset.univ :=
  ⟨fun b => if b then 1 else -1, ⟨true, by simp, by simp [Loves]⟩, false, by simp, by simp [Hates]⟩

end Conatus

/-! ### 3. The sign rule: P21 to P24 (thin; H4 does the work) -/

section SignRule

variable {G : Type*} [Preorder G]

/-- H4. `f` gives my power as a function of the power of another thing. Love, read as strictly
increasing dependence. Not Spinoza's definition; he derives P19 to P24 from P12 and P13. -/
def LovesThrough (f : G → G) : Prop := StrictMono f

/-- Hate, read as strictly decreasing dependence (H4). -/
def HatesThrough (f : G → G) : Prop := StrictAnti f

/-- "Qui id, quod amat, Laetitia vel Tristitia affectum imaginatur, Laetitia etiam vel Tristitia
afficietur" (P21) and "Qui id, quod odio habet, Tristitia affectum imaginatur, laetabitur; si
contra idem Laetitia affectum esse imaginetur, contristabitur" (P23). Under H4 these unfold the
definitions; there is no content beyond H4. -/
theorem share_or_invert {f : G → G} {p p' : G} (hpp : p < p') :
    (LovesThrough f → f p < f p') ∧ (HatesThrough f → f p' < f p) :=
  ⟨fun h => h hpp, fun h => h hpp⟩

/-- "Si aliquem imaginamur Laetitia afficere rem, quam amamus, Amore erga eum afficiemur. Si
contra eundem imaginamur Tristitia eandem afficere, e contra Odio etiam contra ipsum afficiemur."
(P22.) "Si aliquem imaginamur Laetitia afficere rem, quam odio habemus, Odio etiam erga eum
afficiemur. Si contra eundem imaginamur Tristitia eandem rem afficere, Amore erga ipsum
afficiemur." (P24.)

`f`: my dependence on `x`. `g`: the dependence of `x` on a third. The four cases are the sign
rule: love of love and hate of hate give love, the mixed cases give hate. Composition of
monotone maps; the reading is H4. -/
theorem sign_rule (f g : G → G) :
    (LovesThrough f → LovesThrough g → LovesThrough (f ∘ g)) ∧
    (LovesThrough f → HatesThrough g → HatesThrough (f ∘ g)) ∧
    (HatesThrough f → LovesThrough g → HatesThrough (f ∘ g)) ∧
    (HatesThrough f → HatesThrough g → LovesThrough (f ∘ g)) :=
  ⟨fun hf hg => hf.comp hg, fun hf hg => hf.comp_strictAnti hg,
   fun hf hg => hf.comp_strictMono hg, fun hf hg => hf.comp hg⟩

end SignRule

/-! ### 4. Hope and fear with a doubt weight (P18 schol. 2; Aff. Def. 12, 13; H5 is ours) -/

section HopeFear

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- H5. The power lent by the image of a future thing worth `v`, held with confidence `q`
(`q = 0`: despair, `q = 1`: confidence). Spinoza has no number for doubt. -/
def prospect (v q : K) : K := q * v

/-- "Spes namque nihil aliud est, quam inconstans Laetitia orta ex imagine rei futurae vel
praeteritae, de cujus eventu dubitamus." (P18 schol. 2: hope is an inconstant joy arisen from the
image of a future or past thing whose outcome we doubt.) Model: the joy of the passage from
despair to confidence `q`. -/
def hope (v q : K) : K := affect (prospect v) 0 q

/-- "Metus contra inconstans Tristitia ex rei dubiae imagine etiam orta." (P18 schol. 2.) Model:
the sadness of the passage from full confidence down to `q`. -/
def fear (v q : K) : K := affect (prospect v) 1 q

/-- "Ex his definitionibus sequitur, non dari Spem sine Metu, neque Metum sine Spe." (Aff. Def.
13, explicatio: there is no hope without fear and no fear without hope.) Under H5: for a thing
of positive worth, hope and fear are both present exactly when there is doubt, `0 < q < 1`. -/
theorem hope_and_fear_iff_doubt {v : K} (hv : 0 < v) (q : K) :
    (0 < hope v q ∧ fear v q < 0) ↔ (0 < q ∧ q < 1) := by
  have h1 : hope v q = q * v := by simp [hope, affect, prospect]
  have h2 : fear v q = -((1 - q) * v) := by simp [fear, affect, prospect]; ring
  rw [h1, h2, neg_neg_iff_pos, mul_pos_iff_of_pos_right hv, mul_pos_iff_of_pos_right hv, sub_pos]

/-- Hope and fear share out the worth of the thing: what is not hoped is feared. -/
theorem hope_sub_fear (v q : K) : hope v q - fear v q = v := by
  simp [hope, fear, affect, prospect]

/-- "Si horum affectuum dubitatio tollatur, ex Spe fit Securitas, et ex Metu Desperatio." (P18
schol. 2: if doubt is taken away, hope becomes confidence and fear despair.) Under H5: the joy
of the passage to confidence is exactly the fear removed, and the sadness of the passage to
despair is exactly the hope lost. -/
theorem doubt_removed (v q : K) :
    affect (prospect v) q 1 = -fear v q ∧ affect (prospect v) q 0 = -hope v q := by
  constructor <;> simp [hope, fear, affect, prospect]

end HopeFear

end PEqualNP.Philosophy.Spinoza
