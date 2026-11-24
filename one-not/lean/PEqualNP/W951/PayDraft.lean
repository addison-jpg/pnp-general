import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Pay

/-! DRAFT (imported by nothing): Theorem P (payment lemma, scaffold notes
`work/notes951/payment_lemma.md`) split into small lemmas. Definitions and proved lemmas are in
`Pay.lean`; lemmas still carrying `sorry` live here and move to `Pay.lean` once proved. The
assembly (`pay_theoremP`, `pay_final`) below is sorry-free modulo the lemmas. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

namespace PaySetting

variable {n m : ℕ} (P : PaySetting n m)

/-! ## Facts F1-F3 (front) -/















/-! ## Lemmas 1-6 -/

/-- Lemma 5 (i), generic: rewiring gate `k` to `OR(α, α)` changes nothing at a point where
gate `k` already equals `α`. -/
theorem pay_rewire_agree (k α : ℕ) (hk : k < P.gates.length) (hα : α < n + k)
    (y : Fin n → Bool) (hy : val P.gates y (n + k) = val P.gates y α) :
    ∀ i, val (P.rewire k α) y i = val P.gates y i := sorry

/-- Lemma 5 (ii), generic: at a point in `L` (`h = 0`), rewiring an OR gate to one of its
inputs only lowers wires. -/
theorem pay_rewire_le (k α : ℕ) (hk : k < P.gates.length) (hα : α < n + k)
    (hin : α ∈ (P.gates[k]'hk).inputs) (hor : (P.gates[k]'hk).op = GateOp.or)
    (y : Fin n → Bool) (hy : val P.gates y P.hw = false) :
    ∀ i, val (P.rewire k α) y i = true → val P.gates y i = true := sorry

/-- Lemma 5 (ii), reach part: every changed wire is reached from `n + k` by a `y`-live path. -/
theorem pay_rewire_reach (k α : ℕ) (hk : k < P.gates.length) (hα : α < n + k)
    (hin : α ∈ (P.gates[k]'hk).inputs) (hor : (P.gates[k]'hk).op = GateOp.or)
    (y : Fin n → Bool) (hy : val P.gates y P.hw = false) :
    ∀ i, val (P.rewire k α) y i ≠ val P.gates y i →
      ∃ L, P.IsPath L (n + k) i ∧ P.LiveAt y L := sorry

/-- Lemma 4, Claim 1: in the live case a payer exists. -/
theorem pay_lemma4_exists (g : ℕ) (T : Fin m) (c kbar : Fin n) (hs : P.SideOK g T c kbar)
    (hlive : ∃ L, P.IsPath L g (P.out T) ∧ P.LiveAt (eof c) L) : ∃ p, P.LivePayer g p := sorry

/-- Lemma 4, Claim 1: live payers are AND gates. -/
theorem pay_live_and (g p : ℕ) (h : P.LivePayer g p) : p ∈ P.ands := sorry

/-- Lemma 4, Claim 2: live payers are distinct. -/
theorem pay_lemma4_inj (g g' p : ℕ) (h : P.LivePayer g p) (h' : P.LivePayer g' p) :
    g = g' := sorry

/-- Lemma 6: in the bypass case a payer (an uncharged OR in `D_T`) exists. -/
theorem pay_lemma6 (g : ℕ) (T : Fin m) (c kbar : Fin n) (hs : P.SideOK g T c kbar)
    (hno : ¬ ∃ L, P.IsPath L g (P.out T) ∧ P.LiveAt (eof c) L) :
    ∃ p, P.BypassPayer g p := sorry

/-- Injectivity, bypass vs bypass. -/
theorem pay_bypass_inj (g g' p : ℕ) (h : P.BypassPayer g p) (h' : P.BypassPayer g' p) :
    g = g' := sorry

/-! ## Counting -/







/-! ## Assembly (no sorry below this line) -/

theorem pay_exists (hH : P.HStar) (g : ℕ) (hg : P.Coll g) :
    ∃ p, P.Payer g p ∧ p ∈ P.ands ∪ P.unch := by
  obtain ⟨T, c, kbar, hs⟩ := P.pay_side hH g hg
  by_cases hl : ∃ L, P.IsPath L g (P.out T) ∧ P.LiveAt (eof c) L
  · obtain ⟨p, hp⟩ := P.pay_lemma4_exists g T c kbar hs hl
    exact ⟨p, Or.inl hp, Finset.mem_union_left _ (P.pay_live_and g p hp)⟩
  · obtain ⟨p, hp⟩ := P.pay_lemma6 g T c kbar hs hl
    obtain ⟨-, -, -, -, -, -, hu⟩ := id hp
    exact ⟨p, Or.inr hp, Finset.mem_union_right _ hu⟩



theorem pay_inj (g g' p : ℕ) (h : P.Payer g p) (h' : P.Payer g' p) : g = g' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact P.pay_lemma4_inj g g' p h h'
  · exfalso
    obtain ⟨-, -, -, -, -, -, hu⟩ := h'
    exact Finset.disjoint_left.mp P.pay_ands_unch_disj (P.pay_live_and g p h) hu
  · exfalso
    obtain ⟨-, -, -, -, -, -, hu⟩ := h
    exact Finset.disjoint_left.mp P.pay_ands_unch_disj (P.pay_live_and g' p h') hu
  · exact P.pay_bypass_inj g g' p h h'

/-- Theorem P: an injection from collision gates into AND gates ∪ uncharged OR gates. -/
theorem pay_theoremP (hH : P.HStar) :
    ∃ pay : ℕ → ℕ, Set.InjOn pay P.coll ∧ ∀ g ∈ P.coll, pay g ∈ P.ands ∪ P.unch := by
  classical
  have hex : ∀ g, ∃ p, P.Coll g → P.Payer g p ∧ p ∈ P.ands ∪ P.unch := by
    intro g
    by_cases hg : P.Coll g
    · obtain ⟨p, hp⟩ := P.pay_exists hH g hg
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose pay hpay using hex
  have hc : ∀ g ∈ P.coll, P.Coll g := by
    intro g hg
    simp only [coll, Finset.mem_filter] at hg
    exact hg.2
  refine ⟨pay, ?_, fun g hg => (hpay g (hc g hg)).2⟩
  intro g hg g' hg' he
  have h1 := (hpay g (hc g hg)).1
  have h2 := (hpay g' (hc g' hg')).1
  rw [he] at h1
  exact P.pay_inj g g' (pay g') h1 h2

theorem pay_coll_card (hH : P.HStar) : P.coll.card ≤ P.ands.card + P.unch.card := by
  obtain ⟨pay, hinj, hmap⟩ := P.pay_theoremP hH
  calc P.coll.card ≤ (P.ands ∪ P.unch).card := Finset.card_le_card_of_injOn pay hmap hinj
    _ ≤ P.ands.card + P.unch.card := Finset.card_union_le _ _

/-- The final statement: `s ≥ base + 1`. -/
theorem pay_final (hH : P.HStar) : P.base + 1 ≤ P.gates.length := by
  have h1 := P.pay_coll_card hH
  have h2 := P.pay_count_step
  have h3 := P.pay_sum_M
  have h4 := P.pay_union_coll
  omega

end PaySetting

end PEqualNP.Outside.L_meta_951_aux
