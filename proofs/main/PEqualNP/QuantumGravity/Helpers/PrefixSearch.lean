import PEqualNP.Defs.QuantumGravity
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.MetaComplexity.Helpers.Machines.StrEq

/-!
Helpers for L-qg-103: if P = NP, a polynomial-time, length-preserving `f` is inverted in
polynomial time by prefix search.

* The prefix language of `f`: the strings `pairB y p` such that some `w` completes the prefix
  `p` to a preimage of `y`, `f (p ++ w) = y`. The witness `w` is no longer than the input, so
  the language is in NP (`prefixLang_mem_NP`): the verifier decodes the pair, runs `f` on
  `p ++ w` and compares the result with `y`.
* Under P = NP a polynomial-time `d` decides the prefix language. One round of the search
  (`prefixStep`) turns the state `pairB y p` into `pairB y (p ++ [b])`, with `b = false` when `d`
  accepts `pairB y (p ++ [false])` and `b = true` otherwise. The inverter (`prefixInv`) runs `|y|`
  rounds from `pairB y []` and returns the prefix.
* Each round lengthens the state by at most two symbols, so the bounded iteration theorem of
  the library makes the inverter polynomial-time (`cpt_prefixInv`).
* On `y = f x` the state stays in the prefix language (`prefixStep_iter`); after `|y|` rounds the
  prefix has length `|y|`, `f` preserves length, so the completing `w` is empty and `f p = y`
  (`invertible_of_P_eq_NP`).

The pairing `pairB`, the bounded iteration `cpt_iterGrow`, the selection `cpt_sel` and the
string equality machine `strEq_polyTime` come from the library; nothing here builds a new
machine.
-/

namespace PEqualNP.QuantumGravity.Helpers.PrefixSearch

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- Rewriting the function of a polynomial-time computation along a pointwise equality. -/
theorem cpt_rw {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f f' : α → β}
    (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The prefix language is in NP -/

/-- The prefix language of `f`: `pairB y p` is in it when some `w`, no longer than the input,
has `f (p ++ w) = y`. -/
def prefixLang (f : List Bool → List Bool) : Language Bool :=
  {s | ∃ w : List Bool, w.length ≤ s.length ∧ f ((unpairB s).2 ++ w) = (unpairB s).1}

/-- The verifier of the prefix language: the input `s` and the witness `w`. -/
def prefixRel (f : List Bool → List Bool) : Set (List Bool × List Bool) :=
  {q | f ((unpairB q.1).2 ++ q.2) = (unpairB q.1).1}

theorem mem_prefixLang (f : List Bool → List Bool) (s : List Bool) :
    s ∈ prefixLang f ↔
      ∃ w : List Bool, w.length ≤ s.length ∧ f ((unpairB s).2 ++ w) = (unpairB s).1 :=
  Iff.rfl

theorem mem_prefixLang_pairB (f : List Bool → List Bool) (y p : List Bool) :
    pairB y p ∈ prefixLang f ↔
      ∃ w : List Bool, w.length ≤ (pairB y p).length ∧ f (p ++ w) = y := by
  simp only [mem_prefixLang, unpairB_pairB]

/-- The verifier is decided in polynomial time: pair the input and the witness, decode, run `f`
on the prefix followed by the witness, and compare with the target. -/
theorem prefixRel_decidable {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    DecidableInPolyTime encodePair (prefixRel f) := by
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => f ((unpairB (unpairB s).1).2 ++ (unpairB s).2)) :=
    cpt_comp (cpt_app2 (cpt_unpairB2_1 cpt_unpairB1) cpt_unpairB2) hf
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).1).1) :=
    cpt_unpairB1_1 cpt_unpairB1
  have hEq : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  refine ⟨fun q => decide (f ((unpairB q.1).2 ++ q.2) = (unpairB q.1).1), ?_, ?_⟩
  · intro q
    simp only [prefixRel, Set.mem_ofPred_eq, decide_eq_true_eq]
  · refine cpt_rw (cpt_comp cpt_pairB (cpt_comp (cpt_pair hA hB) hEq)) ?_
    intro q
    simp only [unpairB_pairB]

/-- The prefix language of a polynomial-time `f` is in NP, with witnesses no longer than the
input. -/
theorem prefixLang_mem_NP {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    prefixLang f ∈ NP := by
  refine ⟨prefixRel f, Polynomial.X, prefixRel_decidable hf, fun s => ?_⟩
  simp only [mem_prefixLang, prefixRel, Set.mem_ofPred_eq, Polynomial.eval_X]

/-! ### The search -/

/-- One round of the search, for a flag function `fl` (empty for no, nonempty for yes): extend
the prefix by `false` when the flag of the prefix extended by `false` is up, by `true`
otherwise. -/
def prefixStep (fl : List Bool → List Bool) (s : List Bool) : List Bool :=
  pairB (unpairB s).1
    ((unpairB s).2 ++ sel (fl (pairB (unpairB s).1 ((unpairB s).2 ++ [false]))) [true] [false])

theorem prefixStep_pairB (fl : List Bool → List Bool) (y p : List Bool) :
    prefixStep fl (pairB y p) =
      pairB y (p ++ sel (fl (pairB y (p ++ [false]))) [true] [false]) := by
  simp only [prefixStep, unpairB_pairB]

theorem cpt_prefixStep {fl : List Bool → List Bool}
    (hfl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) fl) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (prefixStep fl) := by
  have hy : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hq := cpt_comp (cpt_pairB2 hy (cpt_app2 hp (cpt_const [false]))) hfl
  exact cpt_rw
    (cpt_pairB2 hy (cpt_app2 hp (cpt_sel hq (cpt_const [true]) (cpt_const [false]))))
    (fun _ => rfl)

theorem sel_true_false_length (F : List Bool) : (sel F [true] [false]).length = 1 := by
  unfold sel
  split <;> rfl

/-- One round lengthens the state by at most two symbols. -/
theorem prefixStep_length (fl : List Bool → List Bool) (s : List Bool) :
    (prefixStep fl s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  simp only [prefixStep, pairB_length, List.length_append, sel_true_false_length]
  omega

/-- The inverter: `|y|` rounds from the empty prefix, then the prefix. -/
def prefixInv (fl : List Bool → List Bool) (y : List Bool) : List Bool :=
  (unpairB ((prefixStep fl)^[y.length] (pairB y []))).2

theorem cpt_prefixInv {fl : List Bool → List Bool}
    (hfl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) fl) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (prefixInv fl) :=
  cpt_rw (cpt_unpairB2_1 (cpt_iterGrow (cpt_prefixStep hfl) 2 (prefixStep_length fl) cpt_id
    (cpt_pairB2 cpt_id (cpt_const [])))) (fun _ => rfl)

/-! ### Correctness -/

/-- On `y = f x`, after `k ≤ |y|` rounds the state is `pairB y p` with `|p| = k` and the state
in the prefix language. -/
theorem prefixStep_iter (f : List Bool → List Bool) (hlen : ∀ x, (f x).length = x.length)
    (d : List Bool → Bool) (hd : ∀ a, a ∈ prefixLang f ↔ d a = true) (x : List Bool) :
    ∀ k ≤ (f x).length, ∃ p : List Bool, p.length = k ∧ pairB (f x) p ∈ prefixLang f ∧
      (prefixStep (fun a => if d a then [true] else []))^[k] (pairB (f x) []) = pairB (f x) p := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], rfl, (mem_prefixLang_pairB f _ _).mpr ⟨x, ?_, rfl⟩, rfl⟩
    rw [pairB_length, hlen]
    omega
  | succ k ih =>
    intro hk
    obtain ⟨p, hpl, hmem, hst⟩ := ih (by omega)
    obtain ⟨w, -, hw⟩ := (mem_prefixLang_pairB f _ _).mp hmem
    have hwl : p.length + w.length = (f x).length := by
      have h := congrArg List.length hw
      rw [hlen, List.length_append] at h
      exact h
    rw [Function.iterate_succ_apply', hst, prefixStep_pairB]
    cases hdq : d (pairB (f x) (p ++ [false]))
    · -- the prefix extended by `false` has no completion: the completion starts with `true`
      refine ⟨p ++ [true], by simp [hpl], ?_, by simp⟩
      obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
        cases w with
        | nil => simp at hwl; omega
        | cons b w' => exact ⟨b, w', rfl⟩
      cases b
      · exfalso
        have hm : pairB (f x) (p ++ [false]) ∈ prefixLang f := by
          refine (mem_prefixLang_pairB f _ _).mpr ⟨w', ?_, ?_⟩
          · rw [pairB_length]
            simp only [List.length_cons] at hwl
            omega
          · simpa using hw
        rw [(hd _).mp hm] at hdq
        exact Bool.noConfusion hdq
      · refine (mem_prefixLang_pairB f _ _).mpr ⟨w', ?_, ?_⟩
        · rw [pairB_length]
          simp only [List.length_cons] at hwl
          omega
        · simpa using hw
    · -- the prefix extended by `false` has a completion
      exact ⟨p ++ [false], by simp [hpl], (hd _).mpr hdq, by simp⟩

/-- If P = NP, every polynomial-time, length-preserving `f` is inverted in polynomial time. -/
theorem invertible_of_P_eq_NP (hP : P = NP) (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (hlen : ∀ x, (f x).length = x.length) : PEqualNP.QuantumGravity.InvertibleInPolyTime f := by
  have hNP := prefixLang_mem_NP hf
  rw [← hP] at hNP
  obtain ⟨d, hd, hc⟩ := hNP
  refine ⟨prefixInv (fun a => if d a then [true] else []), cpt_prefixInv (cpt_bitFlag hc),
    fun x => ?_⟩
  obtain ⟨p, hpl, hmem, hst⟩ := prefixStep_iter f hlen d hd x (f x).length le_rfl
  have hinv : prefixInv (fun a => if d a then [true] else []) (f x) = p := by
    simp only [prefixInv, hst, unpairB_pairB]
  rw [hinv]
  obtain ⟨w, -, hw⟩ := (mem_prefixLang_pairB f _ _).mp hmem
  have hwl : w.length = 0 := by
    have h := congrArg List.length hw
    rw [hlen, List.length_append] at h
    omega
  rw [List.eq_nil_of_length_eq_zero hwl, List.append_nil] at hw
  exact hw

end PEqualNP.QuantumGravity.Helpers.PrefixSearch
