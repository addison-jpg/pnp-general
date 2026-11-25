import PEqualNP.W951.LiftHelpers
import PEqualNP.W951.F2Desc
import PEqualNP.W951.Cone
import PEqualNP.W951.Count
import PEqualNP.W951.CanonClass
import PEqualNP.W951.Open.MixedSlack

/-!
# F2Transfer: where the single NOT gate enters the F2 count at a mixed state (seat A4)

Board `open-one-not`, seat A4. Note: `one-not/research/open/A4_f2_transfer.md`.

The NOT gate reads a wire `h` (`hval`) computed by AND/OR gates, so `h` is monotone. Every failure of
monotonicity of the real circuit is a sign pattern of `h`:

* `sign_of_drop`: `x ≤ z`, a wire `1` at `x` and `0` at `z` ⇒ `h x = 0` and `h z = 1`.
* `unit_le_top`: at a mixed state `(Q, D)`, the unit atom `Q + e_u` lies below the top zero point
  `Zof (R ∪ D)` of a set `R` when `u ∉ R ∪ D` and `Q` avoids `R ∪ D`.
* `unit_overlap`: a wire that is `0` at the top zero point of `B` and `1` at the atoms of two distinct
  points of `A` (`|A ∩ B| ≤ 1`) has a point `t ∈ A \ (B ∪ D)` with `h (Q + e_t) = 0` and
  `h (Zof (B ∪ D)) = 1`: the merge sets of the unit-form count overlap only at the DD sign pattern.
* `goodT_of_noDD`: the unit-form test system of a set is `GoodT` (the NOT gate adds no free merge) as
  soon as `h z = 0` or `h = 1` at every atom.
* `unit_count_of_noDD`: hence, for a set that is not DD in this sense, `|R| - 1` counted wires.
* `DDAt`: the DD sign pattern of a set at `(Q, D)`: `h (Zof (S w ∪ D)) = 1` and `h (Q + e_t) = 0` for
  some `t ∈ S w \ D`.
* `F2WitMix_of_unit_noDD`: a wire `0` at `Zof (S w ∪ D)` and `1` at the unit atoms of two distinct
  points of `S w \ D` has a mixed F2 witness for `w` at `(Q, D)` when `w` is not DD there.
* `overlap_needs_DD`: such a wire for two sets `a ≠ b` (`|S a ∩ S b| ≤ 1`) forces BOTH to be DD.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Mono

variable {n : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)

theorem le_imp {x z : Fin n → Bool} (hxz : x ≤ z) : ∀ c, x c = true → z c = true :=
  fun c hc => le_antisymm (Bool.le_true _) (hc ▸ hxz c)

include hg in
theorem C0_mono' {x z : Fin n → Bool} (hxz : x ≤ z) (i : ℕ) (hx : val (C0 gates) x i = true) :
    val (C0 gates) z i = true :=
  mono_val (C0 gates) (fun g hm => (constNot_mono GateOp.or (Or.inr rfl) gates hg g hm).1) x z
    (le_imp hxz) i hx

include hg in
theorem C1_mono' {x z : Fin n → Bool} (hxz : x ≤ z) (i : ℕ) (hx : val (C1 gates) x i = true) :
    val (C1 gates) z i = true :=
  mono_val (C1 gates) (fun g hm => (constNot_mono GateOp.and (Or.inl rfl) gates hg g hm).1) x z
    (le_imp hxz) i hx

end Mono

section Sign

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN

/-- **The sign lemma.** With one NOT gate, a wire can drop from `1` to `0` along `x ≤ z` only if the
NOT input `h` rises from `0` at `x` to `1` at `z`. -/
theorem sign_of_drop {x z : Fin n → Bool} (hxz : x ≤ z) (i : ℕ)
    (hx : val gates x i = true) (hz : val gates z i = false) :
    hval gates p x = false ∧ hval gates p z = true := by
  have hx0 : hval gates p x = false := by
    cases h : hval gates p x
    · rfl
    · exfalso
      have hz' := hval_mono gates p hp hg hU hN hxz h
      have e1 := val_wld_false_of_hval gates p hp hU hN x h i
      have e2 := val_wld_false_of_hval gates p hp hU hN z hz' i
      simp only [wld, Bool.false_eq_true, ite_false] at e1 e2
      have := C0_mono' gates hg hxz i (e1 ▸ hx)
      rw [e2, hz] at this
      exact absurd this (by simp)
  refine ⟨hx0, ?_⟩
  cases h : hval gates p z
  · exfalso
    have e1 := val_wld_true_of_hval gates p hp hU hN x hx0 i
    have e2 := val_wld_true_of_hval gates p hp hU hN z h i
    simp only [wld, ite_true] at e1 e2
    have := C1_mono' gates hg hxz i (e1 ▸ hx)
    rw [e2, hz] at this
    exact absurd this (by simp)
  · rfl

/-- **Unit-form overlap.** Atoms `P u` (`u ∈ A`) below the zero point `zB` whenever `u ∉ B`, with
`|A ∩ B| ≤ 1`. A wire `0` at `zB` and `1` at the atoms of two distinct points of `A` forces a point
`t ∈ A \ B` with `h (P t) = 0` and `h zB = 1`. -/
theorem unit_overlap (A B : Finset (Fin n)) (hAB : (A ∩ B).card ≤ 1)
    (P : Fin n → Fin n → Bool) (zB : Fin n → Bool) (hPz : ∀ u ∈ A, u ∉ B → P u ≤ zB)
    (i : ℕ) (hzB : val gates zB i = false) {u u' : Fin n} (hu : u ∈ A) (hu' : u' ∈ A)
    (huu : u ≠ u') (h1 : val gates (P u) i = true) (h2 : val gates (P u') i = true) :
    ∃ t ∈ A, t ∉ B ∧ hval gates p (P t) = false ∧ hval gates p zB = true := by
  by_cases huB : u ∈ B
  · by_cases hu'B : u' ∈ B
    · exfalso
      have : 2 ≤ (A ∩ B).card :=
        Finset.one_lt_card.mpr ⟨u, mem_inter.mpr ⟨hu, huB⟩, u', mem_inter.mpr ⟨hu', hu'B⟩, huu⟩
      omega
    · exact ⟨u', hu', hu'B, sign_of_drop gates p hp hg hU hN (hPz u' hu' hu'B) i h2 hzB⟩
  · exact ⟨u, hu, huB, sign_of_drop gates p hp hg hU hN (hPz u hu huB) i h1 hzB⟩

/-- **The NOT gate adds no free merge** in the test system `(z, P, R)` when it is not DD there:
`h z = 0` (the NOT gate is `1` at the zero point) or `h = 1` at every atom. -/
theorem goodT_of_noDD (z : Fin n → Bool) (P : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (hnd : hval gates p z = false ∨ ∀ u ∈ R, hval gates p (P u) = true) :
    GoodT z P R gates := by
  intro pre g rest h
  have hmem : g ∈ gates := by rw [h]; simp
  rcases (hg g hmem).1 with h1 | h1 | h1
  · exact Or.inl ⟨Or.inl h1, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr h1, (hg g hmem).2⟩
  · right
    have hp' : gates = gates.take p ++ (gates[p]'hp) :: gates.drop (p + 1) := by
      simp
    have hlen : pre.length = (gates.take p).length :=
      not_index hU pre rest _ _ g _ h hp' h1 hN
    have hpl : pre.length = p := by rw [hlen]; simp; omega
    have hpre : gates.take p = pre := by rw [h, ← hpl]; simp
    have hgp : gates[p]'hp = g := by
      have : gates[pre.length]? = some g := by rw [h]; simp
      rw [hpl] at this
      exact (List.getElem?_eq_some_iff.mp this).2
    have key : ∀ x : Fin n → Bool,
        g.op.eval (g.inputs.map fun j => val pre x j) = !hval gates p x := by
      intro x
      have e := val_gate gates x p hp
      rw [hgp, hpre] at e
      rw [← e]
      exact val_not_hval gates p hp hN x
    rcases hnd with hz | hall
    · left
      rw [key, hz]; rfl
    · right
      intro u hu v _ hpu _
      rw [key, hall u hu] at hpu
      exact absurd hpu (by simp)

/-- **Unit-form count for a set that is not DD.** A test system `(z, P, R)` (the only common one of an
atom and the zero point is the atom's own point), a wire `0` at `z` and `1` at every atom: at least
`|R| - 1` counted wires. -/
theorem unit_count_of_noDD (z : Fin n → Bool) (P : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (hT : ∀ u ∈ R, ∀ c : Fin n, P u c = true → z c = false → c = u)
    (hnd : hval gates p z = false ∨ ∀ u ∈ R, hval gates p (P u) = true)
    (o : ℕ) (hz : val gates z o = false) (hu : ∀ u ∈ R, val gates (P u) o = true) :
    R.card - 1 ≤ (DT z P R gates).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ :=
    main_invT z P R hT gates (goodT_of_noDD gates p hp hg hU hN z P R hnd)
  have h1 : (R.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hb
    exact hinv o u v hz (hu u hu') (hu v hv') hu' hv'
  omega

end Sign

section Points

variable {n : ℕ}

/-- The unit atom `Q + e_u` lies below the top zero point `Zof (R ∪ D)` when `u ∉ R ∪ D` and `Q`
avoids `R ∪ D`. -/
theorem unit_le_top {Q R D : Finset (Fin n)} (hQ : Disjoint Q (R ∪ D)) {u : Fin n}
    (hu : u ∉ R ∪ D) : upPt (canonPt Q) u ≤ Zof (R ∪ D) := by
  intro c
  by_cases hc : c = u
  · subst hc
    simp [upPt, Zof, hu]
  · simp only [upPt, Function.update_of_ne hc, canonPt, Zof]
    by_cases hcQ : c ∈ Q
    · have : c ∉ R ∪ D := Finset.disjoint_left.mp hQ hcQ
      simp [hcQ, this]
    · simp [hcQ]

/-- The unit atoms and the top zero point of `R ∪ D` form a test system for `R \ D`. -/
theorem unit_testSystem {Q R D : Finset (Fin n)} (hQ : Disjoint Q (R ∪ D)) :
    ∀ u ∈ R \ D, ∀ c : Fin n, upPt (canonPt Q) u c = true → Zof (R ∪ D) c = false → c = u := by
  intro u _ c h1 h2
  by_contra hc
  simp only [upPt, Function.update_of_ne hc, canonPt_eq_true] at h1
  simp only [Zof, decide_eq_false_iff_not, not_not] at h2
  exact Finset.disjoint_left.mp hQ h1 h2

end Points

section Mixed

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN

/-- **Overlap at a mixed state needs the DD sign pattern.** At `(Q, D)` with `Q` avoiding `S b ∪ D`:
a wire `0` at `Zof (S b ∪ D)` and `1` at the unit atoms of two distinct points of `S a \ D`
(`|S a ∩ S b| ≤ 1`) gives a point `t ∈ S a \ (S b ∪ D)` with `h (Q + e_t) = 0` and
`h (Zof (S b ∪ D)) = 1`. -/
theorem mixed_overlap (S : Fin m → Finset (Fin n)) (a b : Fin m) (hab : (S a ∩ S b).card ≤ 1)
    (Q D : Finset (Fin n)) (hQ : Disjoint Q (S b ∪ D)) (i : ℕ)
    (hz : val gates (Zof (S b ∪ D)) i = false) {u u' : Fin n} (hu : u ∈ S a \ D)
    (hu' : u' ∈ S a \ D) (huu : u ≠ u') (h1 : val gates (upPt (canonPt Q) u) i = true)
    (h2 : val gates (upPt (canonPt Q) u') i = true) :
    ∃ t ∈ S a \ D, t ∉ S b ∧ hval gates p (upPt (canonPt Q) t) = false ∧
      hval gates p (Zof (S b ∪ D)) = true := by
  have hAB : (S a \ D ∩ S b).card ≤ 1 :=
    le_trans (Finset.card_le_card (Finset.inter_subset_inter_right (Finset.sdiff_subset))) hab
  refine unit_overlap gates p hp hg hU hN (S a \ D) (S b) hAB (fun t => upPt (canonPt Q) t)
    (Zof (S b ∪ D)) ?_ i hz hu hu' huu h1 h2
  intro t ht htb
  have htD : t ∉ D := (Finset.mem_sdiff.mp ht).2
  exact unit_le_top hQ (by simp [htb, htD])

/-- The DD sign pattern of the set `w` at the mixed state `(Q, D)`. -/
def DDAt (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) : Prop :=
  hval gates p (Zof (S w ∪ D)) = true ∧ ∃ t ∈ S w \ D, hval gates p (upPt (canonPt Q) t) = false

omit hg hU hN in
theorem canonPt_le_top {Q R D : Finset (Fin n)} (hQ : Disjoint Q (R ∪ D)) :
    canonPt Q ≤ Zof (R ∪ D) := by
  intro c
  by_cases hcQ : c ∈ Q
  · have : c ∉ R ∪ D := Finset.disjoint_left.mp hQ hcQ
    simp [canonPt, Zof, hcQ, this]
  · simp [canonPt, hcQ]

omit hg hU hN in
theorem upPt_le_upPt {x z : Fin n → Bool} (h : x ≤ z) (u : Fin n) : upPt x u ≤ upPt z u := by
  intro c
  by_cases hc : c = u
  · subst hc; simp [upPt]
  · simp only [upPt, Function.update_of_ne hc]; exact h c

/-- **Unit merges of a non-DD set are mixed F2 witnesses.** -/
theorem F2WitMix_of_unit_noDD (S : Fin m → Finset (Fin n)) (w : Fin m) (Q D : Finset (Fin n))
    (hQ : Disjoint Q (S w ∪ D)) (hnd : ¬ DDAt gates p S Q D w) (i : ℕ)
    (hz : val gates (Zof (S w ∪ D)) i = false) {u u' : Fin n} (hu : u ∈ S w \ D)
    (hu' : u' ∈ S w \ D) (huu : u ≠ u') (h1 : val gates (upPt (canonPt Q) u) i = true)
    (h2 : val gates (upPt (canonPt Q) u') i = true) :
    MixedSlack.F2WitMix gates (S w) Q D i := by
  have hzero : ∀ {Z : Fin n → Bool}, Z ≤ Zof (S w ∪ D) → ∀ x ∈ S w ∪ D, Z x = false := by
    intro Z hZ x hx
    have := hZ x
    simp only [Zof, hx, not_true_eq_false, decide_false] at this
    cases h : Z x
    · rfl
    · rw [h] at this; exact absurd this (by simp)
  cases hzw : hval gates p (Zof (S w ∪ D))
  · -- the NOT gate is 1 at the top zero point: witness at the bottom point `Q`
    have hle := canonPt_le_top hQ
    have h0 : val gates (canonPt Q) i = false := by
      cases h : val gates (canonPt Q) i
      · rfl
      · have := (sign_of_drop gates p hp hg hU hN hle i h hz).2
        rw [hzw] at this; exact absurd this (by simp)
    exact ⟨canonPt Q, u, u', hu, hu', huu, hzero hle, fun x hx => canonPt_eq_true.mpr hx, h0, h1, h2⟩
  · -- heavy set, not DD: `h = 1` at every atom; witness at the top zero point
    have hall : ∀ t ∈ S w \ D, hval gates p (upPt (canonPt Q) t) = true := by
      intro t ht
      by_contra hne
      exact hnd ⟨hzw, t, ht, by simpa using hne⟩
    have hup : ∀ t ∈ S w \ D, val gates (upPt (canonPt Q) t) i = true →
        val gates (Function.update (Zof (S w ∪ D)) t true) i = true := by
      intro t ht h
      cases h' : val gates (Function.update (Zof (S w ∪ D)) t true) i
      · have := (sign_of_drop gates p hp hg hU hN (upPt_le_upPt (canonPt_le_top hQ) t) i h h').1
        rw [hall t ht] at this; exact absurd this (by simp)
      · rfl
    refine ⟨Zof (S w ∪ D), u, u', hu, hu', huu, hzero le_rfl, fun x hx => ?_, hz, hup u hu h1,
      hup u' hu' h2⟩
    have : x ∉ S w ∪ D := Finset.disjoint_left.mp hQ hx
    simp [Zof, this]

/-- **Unit merge sets overlap only between two DD sets.** -/
theorem overlap_needs_DD (S : Fin m → Finset (Fin n)) (a b : Fin m)
    (hab : (S a ∩ S b).card ≤ 1) (Q D : Finset (Fin n)) (hQa : Disjoint Q (S a ∪ D))
    (hQb : Disjoint Q (S b ∪ D)) (i : ℕ)
    (hza : val gates (Zof (S a ∪ D)) i = false) (hzb : val gates (Zof (S b ∪ D)) i = false)
    {u u' : Fin n} (hu : u ∈ S a \ D) (hu' : u' ∈ S a \ D) (huu : u ≠ u')
    (h1 : val gates (upPt (canonPt Q) u) i = true) (h2 : val gates (upPt (canonPt Q) u') i = true)
    {v v' : Fin n} (hv : v ∈ S b \ D) (hv' : v' ∈ S b \ D) (hvv : v ≠ v')
    (h3 : val gates (upPt (canonPt Q) v) i = true) (h4 : val gates (upPt (canonPt Q) v') i = true) :
    DDAt gates p S Q D a ∧ DDAt gates p S Q D b := by
  have hba : (S b ∩ S a).card ≤ 1 := by rwa [Finset.inter_comm]
  obtain ⟨t, ht, -, hPt, hZb⟩ :=
    mixed_overlap gates p hp hg hU hN S a b hab Q D hQb i hzb hu hu' huu h1 h2
  obtain ⟨s, hs, -, hPs, hZa⟩ :=
    mixed_overlap gates p hp hg hU hN S b a hba Q D hQa i hza hv hv' hvv h3 h4
  exact ⟨⟨hZa, t, ht, hPt⟩, ⟨hZb, s, hs, hPs⟩⟩

end Mixed

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
