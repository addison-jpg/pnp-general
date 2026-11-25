import Mathlib
import PEqualNP.W951.AsteroidMixed
/-!
# AsteroidCheapMixed: the mixed slack on the diagonal `r = 0` (task `asteroid-cheap-proofs`)

With no point fixed to 0 the mixed state `(q, 0)` is the cube `q`.

* `baseMixed_zero`: `baseMixed C q 0 = baseAt C q`.
* `hasWitnessMixedNaive_zero`: the naive mixed witness test at `(q, 0)` is `hasWitnessAt` at `q`.
* `mslackVal_zero`: if the kernel check `naiveAgrees C` succeeds (the bit-parallel mixed witness test agrees
  with the naive one at every state), then `mslackVal C q 0 = orWitnessAt C q − baseAt C q` at every cube
  `q < 2^n`; `mslackGe_zero`: the Boolean form `mslackGe C q 0 k = slackGe C q k`.

What is NOT here: the bit-parallel `hasWitnessMixed` is not proved equal to the naive test in general; that
equality is taken per circuit from the kernel check `naiveAgrees`.
-/
namespace SearchCheck

theorem foldl_filter_ge_two (p : List Nat → Bool) (l : List (List Nat)) (acc : Nat) :
    ((l.filter fun S => p S && decide (S.length ≥ 2)).foldl (fun acc S => acc + (S.length - 1)) acc)
      = (l.filter p).foldl (fun acc S => acc + (S.length - 1)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons S l ih =>
    by_cases hp : p S = true
    · by_cases h2 : S.length ≥ 2
      · simp [hp, h2, ih]
      · have h0 : S.length - 1 = 0 := by omega
        simp [hp, h2, ih, h0]
    · simp [hp, ih]

/-- **The mixed base on the diagonal** is the base of the cube. -/
theorem baseMixed_zero (C : Circ) (q : Nat) : baseMixed C q 0 = baseAt C q := by
  unfold baseMixed baseAt
  have h : (fun S : List Nat => aliveMixed S q 0)
      = fun S => (S.all fun s => !q.testBit s) && decide (S.length ≥ 2) := by
    funext S; simp [aliveMixed]
  have hf : ∀ S : List Nat, (S.filter fun s => !Nat.testBit 0 s) = S := by intro S; simp
  simp only [hf]
  rw [h]
  exact foldl_filter_ge_two _ _ _

/-- **The naive mixed witness test on the diagonal** is the witness test of the cube. -/
theorem hasWitnessMixedNaive_zero (n : Nat) (sets : List (List Nat)) (q t : Nat) :
    hasWitnessMixedNaive n sets q 0 t = hasWitnessAt n sets q t := by
  unfold hasWitnessMixedNaive hasWitnessAt
  congr 1
  funext S
  rw [Bool.eq_iff_iff]
  simp only [aliveMixed, Nat.zero_testBit, Bool.not_false, List.filter_true, Bool.and_eq_true,
    List.any_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨hall, -⟩, r, hr, ⟨⟨⟨a, -⟩, b⟩, c⟩, d⟩
    exact ⟨hall, r, hr, ⟨⟨a, b⟩, c⟩, d⟩
  · rintro ⟨hall, r, hr, ⟨⟨a, b⟩, c⟩, d⟩
    exact ⟨⟨hall, le_trans d (List.length_filter_le _ _)⟩, r, hr, ⟨⟨⟨a, (Nat.zero_and r :)⟩, b⟩, c⟩, d⟩

/-- **Mixed slack on the diagonal.** If the kernel check `naiveAgrees C` succeeds, the mixed slack at the
state `(q, 0)` is the ordinary slack `orWitnessAt − baseAt` at the cube `q`. -/
theorem mslackVal_zero (C : Circ) (h : naiveAgrees C = true) {q : Nat} (hq : q < 2 ^ C.n) :
    mslackVal C q 0 = (orWitnessAt C q : Int) - (baseAt C q : Int) := by
  unfold naiveAgrees allStates at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 := h 0 (Nat.pos_of_ne_zero (by positivity)) q hq
  have e : Nat.land q 0 = 0 := Nat.and_zero q
  simp only [e, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h1
  have e2 : hasWitnessMixedNaive C.n C.sets q 0 = hasWitnessAt C.n C.sets q :=
    funext (hasWitnessMixedNaive_zero C.n C.sets q)
  unfold mslackVal mslackValWith orWitnessAt orWitnessAtWith
  rw [← h1, baseMixed_zero, e2]

/-- the Boolean form: on the diagonal `mslack(c) >= k` is `slack(c) >= k` -/
theorem mslackGe_zero (C : Circ) (h : naiveAgrees C = true) {q : Nat} (hq : q < 2 ^ C.n) (k : Int) :
    mslackGe C q 0 k = slackGe C q k := by
  unfold mslackGe slackGe
  rw [mslackVal_zero C h hq]

end SearchCheck

#print axioms SearchCheck.baseMixed_zero
#print axioms SearchCheck.hasWitnessMixedNaive_zero
#print axioms SearchCheck.mslackVal_zero
#print axioms SearchCheck.mslackGe_zero
