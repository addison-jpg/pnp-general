import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Core

/-!
# Minimal counterexamples to L-meta-951

`IsCE S gates out` : the problem hypotheses of 951 together with `hlt` (fewer gates than
`∑ (|S w| - 1)`).  `MinCE S gates out` : `IsCE` and no `IsCE` instance (over all `n', m'`) is smaller
in the lexicographic order on `(gates.length, ∑ |S w|)`.

THE ONLY OPEN STATEMENT of the 951 development is `no_minCE`: there is no minimal counterexample.
Everything else (`hard_case_core`, `L_meta_951`, ...) is derived from it in this file and Final.lean.

Every proved reduction is one lemma per minimality fact (`MinCE.clean`, `.live`, `.essential`, `.h0`,
`.noThmX`, `.twoHardN`, `.DD`, `.has4`, `.core`), each concluding exactly the corresponding hypothesis of
`HardCaseCore`; more minimality facts live in MinCEFacts, MinCEN3, Bottom, EasySets, PairLemma, Peel, RuleS,
Heredity. (The old HardCase chain in Main/Core was removed; `HardCase*` now reach `L_meta_951` only through
the bridges `no_minCE_of_hardCase*` below.) Equivalent targets: `no_minCE_of_liftedBound` (LiftBound) and
`no_minCE_of_liftClassFrac` (LiftFrac).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- A counterexample to 951: the problem hypotheses (exact shapes of `HardCaseCore`) and `hlt`. -/
structure IsCE {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop where
  h2 : ∀ i : Fin m, 2 ≤ (S i).card
  hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1
  hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
  hU : AtMostOneNot gates
  hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)
  hlt : gates.length < ∑ i : Fin m, ((S i).card - 1)

/-- The size of an instance: total set size (second component of the minimality order). -/
def ceSize {n m : ℕ} (S : Fin m → Finset (Fin n)) : ℕ := ∑ w : Fin m, (S w).card

/-- Lexicographic order on `(gates.length, ceSize S)` (= `Prod.Lex (· < ·) (· < ·)`). -/
def CELt (L' s' L s : ℕ) : Prop := L' < L ∨ (L' = L ∧ s' < s)

/-- A minimal counterexample: `IsCE`, and no counterexample (any `n', m'`) is lexicographically
smaller in `(gates.length, ∑ |S w|)`. -/
structure MinCE {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop where
  ce : IsCE S gates out
  min : ∀ (n' m' : ℕ) (S' : Fin m' → Finset (Fin n')) (gates' : List Gate) (out' : Fin m' → ℕ),
    IsCE S' gates' out' → ¬ CELt gates'.length (ceSize S') gates.length (ceSize S)

/-- A counterexample exists ⇒ a minimal one exists. -/
theorem exists_minCE {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (h : IsCE S gates out) :
    ∃ (n' m' : ℕ) (S' : Fin m' → Finset (Fin n')) (gates' : List Gate) (out' : Fin m' → ℕ),
      MinCE S' gates' out' := by
  by_contra hno
  push Not at hno
  have key : ∀ L s : ℕ, ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate)
      (out : Fin m → ℕ), gates.length = L → ceSize S = s → ¬ IsCE S gates out := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ihL =>
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
    intro n m S gates out hL hs hce
    apply hno n m S gates out
    refine ⟨hce, fun n' m' S' gates' out' hce' hlt' => ?_⟩
    rcases hlt' with h | ⟨h, h'⟩
    · exact ihL _ (hL ▸ h) _ n' m' S' gates' out' rfl rfl hce'
    · exact ihs _ (hs ▸ h') n' m' S' gates' out' (h.trans hL) rfl hce'
  exact key _ _ n m S gates out rfl rfl h

/-- THE ONLY OPEN STATEMENT: there is no minimal counterexample to 951. -/
theorem no_minCE : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
    ¬ MinCE S gates out := by sorry

/-- The 951 bound (with `AtMostOneNot`), from `no_minCE`. -/
theorem bound_of_noMinCE {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n', m', S', gates', out', hM⟩ := exists_minCE S gates out ⟨h2, hS, hg, hU, hev, hlt⟩
  exact no_minCE S' gates' out' hM

/-- L-meta-951 (same statement as `PEqualNP.Outside.L_meta_951`) from `no_minCE`. -/
theorem L_meta_951_of_minCE : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact bound_of_noMinCE S h2 hS gates out hg (hU_of_ι hι) hev

/-- `HardCaseCore` from `no_minCE`: its `hlt` contradicts the bound. -/
theorem hardCaseCore_of_minCE : HardCaseCore := by
  intro n m S h2 hS gates out hg hU hev _ _ _ _ _ _ _ _ _ hlt
  have := bound_of_noMinCE S h2 hS gates out hg hU hev
  omega

/-! ## Minimality facts, one per reduction (no sorry) -/

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- Every strictly shorter instance (any `m'`, any `n'`) satisfies the 951 bound. -/
theorem bound_lt (M : MinCE S gates out) : ∀ (n' m' : ℕ) (S' : Fin m' → Finset (Fin n'))
    (gates' : List Gate) (out' : Fin m' → ℕ), gates'.length < gates.length →
    (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
    (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) → AtMostOneNot gates' →
    (∀ (w : Fin m') (x : Fin n' → Bool), val gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
    ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length := by
  intro n' m' S' gates' out' hlen h2 hS hg hU hev
  by_contra hlt
  push Not at hlt
  exact M.min n' m' S' gates' out' ⟨h2, hS, hg, hU, hev, hlt⟩ (Or.inl hlen)

/-- hlive: every gate is read or is an output (dead-gate reduction). -/
theorem live (M : MinCE S gates out) :
    ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs := by
  intro k hk
  by_contra hne
  push Not at hne
  obtain ⟨hout, hno⟩ := hne
  have C := M.ce
  have hlen := dropGate_length gates k 0 n hk
  have hg' := dropGate_hg gates k 0 n C.hg
  have hU' := dropGate_hU gates k 0 n hk C.hU
  have hev' : ∀ (w : Fin m) (x : Fin n → Bool),
      val (dropGate gates k 0 n) x (redir (n + k) 0 (out w)) =
        decide (∃ v ∈ S w, x v = true) := by
    intro w x
    rw [val_dropDead gates k 0 hk hno x (out w) (hout w)]
    exact C.hev w x
  have := M.bound_lt n m S (dropGate gates k 0 n) (fun w => redir (n + k) 0 (out w)) (by omega)
    C.h2 C.hS hg' hU' hev'
  have := C.hlt
  omega

/-- hclean: no gate computes the same function as an earlier wire (copy-gate reduction). -/
theorem clean (M : MinCE S gates out) :
    ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j := by
  intro k j hk hj hcopy
  have C := M.ce
  have hlen := dropGate_length gates k j n hk
  have hg' := dropGate_hg gates k j n C.hg
  have hU' := dropGate_hU gates k j n hk C.hU
  have hev' : ∀ (w : Fin m) (x : Fin n → Bool),
      val (dropGate gates k j n) x (redir (n + k) j (out w)) =
        decide (∃ v ∈ S w, x v = true) := by
    intro w x
    rw [val_dropGate gates k j hk hj hcopy x (out w)]
    exact C.hev w x
  have := M.bound_lt n m S (dropGate gates k j n) (fun w => redir (n + k) j (out w)) (by omega)
    C.h2 C.hS hg' hU' hev'
  have := C.hlt
  omega

/-- hC0 ∧ hC1: the NOT gate is essential (removable-NOT reduction, `bound_const`). -/
theorem essential (M : MinCE S gates out) :
    (¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true)) ∧
    (¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true)) := by
  have C := M.ce
  have := C.hlt
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := bound_const S gates out GateOp.or (Or.inr rfl) C.hS C.hg h; omega
  · have := bound_const S gates out GateOp.and (Or.inl rfl) C.hS C.hg h; omega

/-- hz: the NOT gate is not dead (`good_all_of_dead`). -/
theorem h0 (M : MinCE S gates out) : NotQuiet (Finset.univ : Finset (Fin n)) gates := by
  have C := M.ce
  by_contra hz
  have := L951_core_c S gates out C.hev (chargeOKc_of S gates out
    (charge_of_good S gates out C.hS C.hev fun w => good_all_of_dead gates C.hg C.hU hz (S w)))
  have := C.hlt
  omega

/-- hC: no Theorem X family (`charge_of_pair_c`). -/
theorem noThmX (M : MinCE S gates out) :
    ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1 := by
  rintro ⟨Q, hSQ, hG, hP⟩
  have C := M.ce
  have := L951_core_c S gates out C.hev (charge_of_pair_c S Q (fun w => coneOf n gates (out w))
    gates out hSQ (fun w => coneOf_closed n gates (out w)) (fun w => coneOf_out n gates (out w))
    hG hP)
  have := C.hlt
  omega

/-- hhard, h1, h1N: at least two hard sets, at least two hard N-sets (all-easy / one-hard /
Theorem X with the universal family). -/
theorem twoHardN (M : MinCE S gates out) :
    (¬ ∀ w, NotQuiet (S w) gates) ∧
    (¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates) ∧
    (¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates) := by
  have C := M.ce
  have hlt := C.hlt
  have hz := M.h0
  have hS := C.hS
  have hg := C.hg
  refine ⟨fun hq => ?_, fun ⟨w0, he⟩ => ?_, fun h1N => ?_⟩
  · have := L951_core_c S gates out C.hev (chargeOKc_of S gates out
      (charge_of_good S gates out hS C.hev fun w => good_of_quiet _ _ hg (hq w)))
    omega
  · have := L951_core_c S gates out C.hev
      (chargeOKc_of S gates out (charge_one_hard S gates hS hg w0 he hz))
    omega
  · apply M.noThmX
    classical
    obtain ⟨w0, hw0⟩ := h1N
    refine ⟨fun w => if w = w0 then Finset.univ else S w, ?_, ?_, ?_⟩
    · intro w; by_cases h : w = w0 <;> simp [h]
    · intro w
      by_cases h : w = w0
      · simp only [h, ite_true]
        exact good_mask_of_good _ _ _ (coneOf_closed n gates (out w0))
          (good_of_quiet _ _ hg hz)
      · simp only [h, ite_false]
        rcases hw0 w h with hno | hq'
        · exact good_mask_noNot _ _ hg hno _
        · exact good_mask_of_good _ _ _ (coneOf_closed n gates (out w))
            (good_of_quiet _ _ hg hq')
    · intro a b hab
      by_cases hb : b = w0
      · right
        have ha : a ≠ w0 := fun h => hab (h.trans hb.symm)
        simp only [ha, ite_false]
        exact hS b a (fun h => hab h.symm)
      · left
        simp only [hb, ite_false]
        exact hS a b hab

/-- hDD: some DD set (Two-World, `bound_of_noDD`). -/
theorem DD (M : MinCE S gates out) :
    ∃ w, val (C1 gates) (Zof (S w)) (out w) = true ∧
      ∃ u ∈ S w, val (C0 gates) (eof u) (out w) = false := by
  have C := M.ce
  by_contra hd
  have hno : ∀ w, val (C1 gates) (Zof (S w)) (out w) = false ∨
      ∀ u ∈ S w, val (C0 gates) (eof u) (out w) = true := by
    intro w
    cases hA : val (C1 gates) (Zof (S w)) (out w)
    · exact Or.inl rfl
    · refine Or.inr fun u hu => ?_
      cases hB : val (C0 gates) (eof u) (out w)
      · exact absurd ⟨w, hA, u, hu, hB⟩ hd
      · rfl
  have := bound_of_noDD S C.hS gates out C.hg C.hev hno
  have := C.hlt
  omega

/-- h4: some set has at least 4 elements (T1, `small3_bound`). -/
theorem has4 (M : MinCE S gates out) : ∃ w, 4 ≤ (S w).card := by
  have C := M.ce
  by_contra h4
  push Not at h4
  have := small3_bound S C.h2 C.hS gates out C.hg C.hU C.hev M.clean
    (fun w => by have := h4 w; omega)
  have := C.hlt
  omega

/-- hcore: every point lying in a set lies in at least two sets of size `≥ 3` (R0', `r0_step`). -/
theorem core (M : MinCE S gates out) : ∀ v : Fin n, (∃ w, v ∈ S w) →
    2 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w ∧ 3 ≤ (S w).card).card := by
  intro v hvw
  by_contra hlt2
  have C := M.ce
  have := r0_step S C.h2 C.hS gates out C.hg C.hU C.hev
    (fun m' S' gates' out' hlen => M.bound_lt n m' S' gates' out' hlen) v hvw (by omega)
  have := C.hlt
  omega

/-- A minimal counterexample satisfies every hypothesis of `HardCaseCore`; hence
`HardCaseCore → no_minCE` (the converse of `hardCaseCore_of_minCE`). -/
theorem false_of_hardCaseCore (H : HardCaseCore) (M : MinCE S gates out) : False := by
  have C := M.ce
  obtain ⟨hhard, h1, h1N⟩ := M.twoHardN
  exact H S C.h2 C.hS gates out C.hg C.hU C.hev hhard M.h0 h1 M.clean M.essential.1 M.essential.2
    M.live M.noThmX h1N C.hlt M.DD M.has4 M.core

end MinCE

/-! ## The hard-case statements imply `no_minCE` (no sorry)

`HardCase`, `HardCaseDD`, `HardCaseDD4`, `HardCaseCore` each add hypotheses to the previous one, and a
minimal counterexample satisfies all of them (`MinCE.false_of_hardCaseCore`). With
`bound_of_forall_not_minCE`, each of them gives the 951 bound without `no_minCE` (Final.lean). -/

/-- The 951 bound (with `AtMostOneNot`) when there is no minimal counterexample, taken as a
hypothesis (`bound_of_noMinCE` is the case `no_minCE`). -/
theorem bound_of_forall_not_minCE
    (hN : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out)
    {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n', m', S', gates', out', hM⟩ := exists_minCE S gates out ⟨h2, hS, hg, hU, hev, hlt⟩
  exact hN S' gates' out' hM

/-- `HardCaseCore → no_minCE` (`MinCE.false_of_hardCaseCore`, stated like `no_minCE`). -/
theorem no_minCE_of_hardCaseCore (H : HardCaseCore) : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ), ¬ MinCE S gates out :=
  fun _ _ _ M => MinCE.false_of_hardCaseCore H M

/-- `HardCaseDD4 → no_minCE` (`HardCaseCore` adds the hypothesis `hcore`). -/
theorem no_minCE_of_hardCaseDD4 (H : HardCaseDD4) : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ), ¬ MinCE S gates out :=
  no_minCE_of_hardCaseCore (by
    intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD h4 _
    exact H S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD h4)

/-- `HardCaseDD → no_minCE` (`HardCaseDD4` adds the hypothesis `h4`). -/
theorem no_minCE_of_hardCaseDD (H : HardCaseDD) : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ), ¬ MinCE S gates out :=
  no_minCE_of_hardCaseDD4 (by
    intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD _
    exact H S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt hDD)

/-- `HardCase → no_minCE` (`HardCaseDD` adds the hypothesis `hDD`). -/
theorem no_minCE_of_hardCase (H : HardCase) : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ), ¬ MinCE S gates out :=
  no_minCE_of_hardCaseDD (by
    intro n m S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt _
    exact H S h2 hS gates out hg hU hev hhard hz h1 hclean hC0 hC1 hlive hC h1N hlt)

end PEqualNP.Outside.L_meta_951_aux
