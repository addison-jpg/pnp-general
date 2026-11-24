import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.TUCert
import PEqualNP.W951.CertDHeavy
import PEqualNP.W951.Pay
import PEqualNP.Base.Matching.Simple
import PEqualNP.W951.MatchBase
import PEqualNP.W951.F2Light
import PEqualNP.W951.CrossWorld
import PEqualNP.W951.Final

section CertStair

/-!
# CertStair: CERT-3c from (D) at a heavy point with SEE and (S) by the real Theorem U

Composition of qg-d2's (D) (`certD_of_heavy_see`, CertDHeavy.lean: a heavy `v`, every cone merge of the
star `1` at `Q + e_v`) with cTAHG's (S) (`certS_of_tu`, `certS_stair`, TUCert.lean).

* `cert3c_of_heavy_tu`: heavy `v`, zero points `z_w ⊇ Q` off `S_w`, SEE for their cone merges and
  pairwise `TUPair` in one direction ⇒ CERT-3c at `v`.
* `cert3c_of_heavy_stair`: the same at the staircase points (`h = 0` there).
* `no_minCE_of_heavy_tu_or_local`: every `Q` with positive base is `CubeLocal`, satisfies LW1, or has a
  heavy `v ∉ Q` with such zero points ⇒ no minimal counterexample.
* `cert3c_of_see0_tu`, `no_minCE_of_see0_tu_or_local`: the same at ANY `v` with qg-d2's SEE0 (cone merges
  `1` at `Q + e_v` in the real circuit and in `C_0`, `certD_of_see0`): qg-d2's PROVED coverage 16,970 /
  17,045 non-local all-read instances.

Data (tools/kill_tests/tu_cert.py, flags `hsee_tu`, `hsee_stair`): heavy SEE + TU zero points exist at
101 / 155 local non-local instances with a heavy point (staircase: 92). MATCH-C (board
fable-f2-nonlocal.md) refutes the F2 step itself at non-local cubes under R1-R5' and R+, so these
conditions can hold in a minimal counterexample only through `gates < base`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CertStair

variable {n m : ℕ}

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **CERT-3c at a heavy point**: heavy `v`, zero points `z_w ⊇ Q` off `S_w` whose cone merges are all
`1` at `Q + e_v` (SEE) and which are pairwise TU-compatible in one direction. -/
theorem cert3c_of_heavy_tu (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n) (z : Fin m → Fin n → Bool)
    (hzS : ∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false)
    (hzQ : ∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hsee : ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
      val gates (canonPt (insert v Q)) i = true)
    (htu : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
      TUPair gates p (S w) (z w) (z w') ∨ TUPair gates p (S w') (z w') (z w)) :
    Cert3c gates S out Q v :=
  ⟨z, hzS, hzQ, certD_of_heavy_see gates p hp hg hU hN S out Q v z hv hsee,
    certS_of_tu gates p hp hg hU hN S out Q v z htu⟩

include hp hg hU hN in
/-- **CERT-3c at a heavy point on the staircase** (`h = 0` at the staircase points, SEE there). -/
theorem cert3c_of_heavy_stair (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (rank : Fin m → ℕ)
    (hrank : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, rank w = rank w' → w = w')
    (hnot : ∀ w ∈ starSets S Q v, val gates (stairPt S Q v rank w) (n + p) = true)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hsee : ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (stairPt S Q v rank w),
      val gates (canonPt (insert v Q)) i = true) :
    Cert3c gates S out Q v :=
  cert3c_of_stair gates p hp hg hU hN S out Q v hS rank hrank hnot
    (certD_of_heavy_see gates p hp hg hU hN S out Q v _ hv hsee)

include hp hg hU hN in
/-- **CERT-3c at any point** (qg-d2's SEE0, `certD_of_see0`): zero points `z_w ⊇ Q` off `S_w` whose cone
merges are `1` at `Q + e_v` in the real circuit and in `C_0`, pairwise TU-compatible in one direction. -/
theorem cert3c_of_see0_tu (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n) (z : Fin m → Fin n → Bool)
    (hzS : ∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false)
    (hzQ : ∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true)
    (hsee : ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
      val gates (canonPt (insert v Q)) i = true ∧
        val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true)
    (htu : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
      TUPair gates p (S w) (z w) (z w') ∨ TUPair gates p (S w') (z w') (z w)) :
    Cert3c gates S out Q v :=
  ⟨z, hzS, hzQ, certD_of_see0 gates p hp hg hU hN S out Q v z hsee,
    certS_of_tu gates p hp hg hU hN S out Q v z htu⟩

end CertStair

/-- **951 from heavy SEE + TU zero points with the local closures.** -/
theorem no_minCE_of_heavy_tu_or_local
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q → CubeLocal gates p Q ∨ LW1 gates p S Q ∨
          ∃ v, v ∉ Q ∧ val gates (canonPt (insert v Q)) (n + p) = false ∧
            ∃ z : Fin m → Fin n → Bool, (∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false) ∧
              (∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true) ∧
              (∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
                val gates (canonPt (insert v Q)) i = true) ∧
              ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
                TUPair gates p (S w) (z w) (z w') ∨ TUPair gates p (S w') (z w') (z w)) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_cert_or_local fun n m S gates out M => by
    obtain ⟨p, hp, hN, hQ⟩ := H n m S gates out M
    refine ⟨p, hp, hN, fun Q hpos => ?_⟩
    rcases hQ Q hpos with h | h | ⟨v, hvQ, hv, z, hzS, hzQ, hsee, htu⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨v, hvQ, cert3c_of_heavy_tu gates p hp M.ce.hg M.ce.hU hN S out Q v z
        hzS hzQ hv hsee htu⟩)

/-- **951 from SEE0 + TU zero points with the local closures** (the PROVED-coverage certificate of
qg-d2's proved_cover.py, flag proved0). -/
theorem no_minCE_of_see0_tu_or_local
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q → CubeLocal gates p Q ∨ LW1 gates p S Q ∨
          ∃ v, v ∉ Q ∧ ∃ z : Fin m → Fin n → Bool, (∀ w ∈ starSets S Q v, ∀ u ∈ S w, z w u = false) ∧
            (∀ w ∈ starSets S Q v, ∀ q ∈ Q, z w q = true) ∧
            (∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
              val gates (canonPt (insert v Q)) i = true ∧
                val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true) ∧
            ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
              TUPair gates p (S w) (z w) (z w') ∨ TUPair gates p (S w') (z w') (z w)) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_cert_or_local fun n m S gates out M => by
    obtain ⟨p, hp, hN, hQ⟩ := H n m S gates out M
    refine ⟨p, hp, hN, fun Q hpos => ?_⟩
    rcases hQ Q hpos with h | h | ⟨v, hvQ, z, hzS, hzQ, hsee, htu⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨v, hvQ, cert3c_of_see0_tu gates p hp M.ce.hg M.ce.hU hN S out Q v z
        hzS hzQ hsee htu⟩)

end PEqualNP.Outside.L_meta_951_aux

end CertStair

section PayDraft

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

end PayDraft

section MatchBase2

/-! W951's two-world matching (`MatchG2`) on the circuit-free base.

* `matchG2_iff_simpleBMatching`, `matchG2_iff_simpleHall`, `matchG2_iff_exists_simpleHall`:
  for fixed test systems, the `MatchG2` injection is a simple b-matching of the vertices
  `(w, c) : Fin m × Fin 2` (demand `|S w| - 1`) into gate wires of capacity two, hence equivalent
  to the simple Hall inequality.
* `fracMatch_of_matchG'`, `fracMatch_of_matchG2'`: aliases of the two `FracMatch` lemmas, which
  `FracMatch.lean` proves from `image_props_of_injective_one` / `image_props_of_injective_sigmaProd`
  (capacity `1`, `2`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- For fixed test systems, the `MatchG2` injection is a simple b-matching with capacity two. -/
theorem matchG2_iff_simpleBMatching {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    {out : Fin m → ℕ} (σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w)) :
    (∃ f : (Σ w : Fin m, Fin 2 × Fin ((S w).card - 1)) → ℕ × Fin 2, Function.Injective f ∧
        (∀ x, (f x).1 ∈ (σ x.1 x.2.1).cnt) ∧
        ∀ w c, Function.Injective fun k : Fin ((S w).card - 1) => (f ⟨w, (c, k)⟩).1) ↔
      HasSimpleBMatching (fun i : Fin m × Fin 2 => (σ i.1 i.2).cnt)
        (fun i => (S i.1).card - 1) (fun _ => 2) := by
  exact (hasSimpleBMatching_sigmaProd_iff (fun w c => (σ w c).cnt) _ 2).symm

/-- For fixed test systems, the `MatchG2` injection exists exactly when the simple Hall
inequality (gate capacity two) holds over the vertices `(w, c)`. -/
theorem matchG2_iff_simpleHall {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    {out : Fin m → ℕ} (σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w)) :
    (∃ f : (Σ w : Fin m, Fin 2 × Fin ((S w).card - 1)) → ℕ × Fin 2, Function.Injective f ∧
        (∀ x, (f x).1 ∈ (σ x.1 x.2.1).cnt) ∧
        ∀ w c, Function.Injective fun k : Fin ((S w).card - 1) => (f ⟨w, (c, k)⟩).1) ↔
      ∀ s : Finset (Fin m × Fin 2), ∑ i ∈ s, ((S i.1).card - 1) ≤
        ∑ g ∈ s.biUnion (fun i => (σ i.1 i.2).cnt),
          min 2 (s.filter fun i => g ∈ (σ i.1 i.2).cnt).card :=
  exists_simple_injective_sigmaProd_iff_hall (fun w c => (σ w c).cnt) _ 2

/-- `MatchG2` is the simple Hall condition (capacity two) for some choice of test systems. -/
theorem matchG2_iff_exists_simpleHall {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) :
    MatchG2 S gates out ↔ ∃ σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w),
      ∀ s : Finset (Fin m × Fin 2), ∑ i ∈ s, ((S i.1).card - 1) ≤
        ∑ g ∈ s.biUnion (fun i => (σ i.1 i.2).cnt),
          min 2 (s.filter fun i => g ∈ (σ i.1 i.2).cnt).card :=
  exists_congr fun σ => matchG2_iff_simpleHall S σ

/-- `fracMatch_of_matchG` (proved from the base in `FracMatch.lean`). -/
alias fracMatch_of_matchG' := fracMatch_of_matchG

/-- `fracMatch_of_matchG2` (proved from the base in `FracMatch.lean`). -/
alias fracMatch_of_matchG2' := fracMatch_of_matchG2

end PEqualNP.Outside.L_meta_951_aux

end MatchBase2

section F2FirstJoin

/-!
# F2FirstJoin: first-joining gates (dwV8p, `PROOF_PLAN_SUGGESTIONS.md` §6 Step 2', PROVED there)

`P` = the points of the star sets of `v` at `Q` (`starPts`), zero point `Q`, the real block of a wire
`i`: the points `x ∈ P` with `i` true at `Q + e_x`. For `u ∈ P \ {v}`, `firstJoin gates Q v u` is the
first wire that is `0` at `Q` and true at `Q + e_v` and `Q + e_u` (`JoinsAt`).

* `exists_joinsAt`: it exists (the output of a star set through `u` and `v`).
* `firstJoin_isOr`: it is an OR gate (an input joins at most one point; the NOT gate, if `0` at `Q`,
  is `0` above `Q`; an AND gate that joins has an earlier joining input).
* `firstJoin_mem_F2`, `firstJoin_mem_SEE`: `f(u) ∈ F2(Q) ∩ SEE(v)` (witness `Z = Q` with the star set
  through `u` and `v`).
* `firstJoinSet` (`F(v)`), `firstJoinSet_subset_SEE`, `card_firstJoinSet_le` (`|F(v)| ≤ cost(v)`; the difference is `deficit(v)`).
* `gainF2_of_firstJoin`: `f` injective on `P \ {v}` (deficit `0`) and no `f`-gate in `SURV(v)` ⇒ the F2 step
  (the immediate case: 19,613 / 19,620 random instances). For heavy `v` `SURV = ∅` (`gainF2_of_firstJoin_heavy`).
* `Absorb` (OPEN, dwV8p's ABSORB: `deficit(v) + |F(v) ∩ SURV(v)| ≤ |gain(v) \ F(v)|`) ⇒ the F2 step
  (`gainF2_of_absorb`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section FirstJoin

variable {n m : ℕ} (gates : List Gate)

theorem upPt_canonPt (Q : Finset (Fin n)) (v : Fin n) :
    upPt (canonPt Q) v = canonPt (insert v Q) := by
  funext c
  by_cases hc : c = v
  · subst hc
    simp [upPt, canonPt]
  · rw [upPt, Function.update_of_ne hc]
    simp [canonPt, hc]

/-- Wire `i` is `0` at `Q` and `1` at `Q + e_v` and `Q + e_u` (its block contains `v` and `u`). -/
def JoinsAt (Q : Finset (Fin n)) (v u : Fin n) (i : ℕ) : Prop :=
  val gates (canonPt Q) i = false ∧ val gates (upPt (canonPt Q) v) i = true ∧
    val gates (upPt (canonPt Q) u) i = true

open Classical in
/-- **The first-joining gate** `f(u)`: the first wire joining `v` and `u` at `Q`. -/
noncomputable def firstJoin (Q : Finset (Fin n)) (v u : Fin n) : ℕ :=
  if h : ∃ i, JoinsAt gates Q v u i then Nat.find h else 0

theorem firstJoin_spec {Q : Finset (Fin n)} {v u : Fin n} (h : ∃ i, JoinsAt gates Q v u i) :
    JoinsAt gates Q v u (firstJoin gates Q v u) ∧
      ∀ j < firstJoin gates Q v u, ¬ JoinsAt gates Q v u j := by
  classical
  rw [firstJoin, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- **Existence**: the output of a star set through `u` and `v` joins them. -/
theorem exists_joinsAt (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ starPts S Q v) :
    ∃ i, JoinsAt gates Q v u i := by
  obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨hwa, hvw⟩ := Finset.mem_filter.mp hw
  refine ⟨out w, ?_, ?_, ?_⟩
  · rw [hev]
    simpa using fun y hy => canonPt_zero_of_alive hwa y hy
  · rw [hev]
    exact decide_eq_true ⟨v, hvw, by simp [upPt]⟩
  · rw [hev]
    exact decide_eq_true ⟨u, huw, by simp [upPt]⟩

/-- `F(v)`: the first-joining gates of the points of `P \ {v}`. -/
noncomputable def firstJoinSet (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Finset ℕ :=
  ((starPts S Q v).erase v).image (firstJoin gates Q v)

variable (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **The first joining wire is an OR gate.** -/
theorem firstJoin_isOr (Q : Finset (Fin n)) {v u : Fin n} (huv : u ≠ v)
    (h : ∃ i, JoinsAt gates Q v u i) :
    ∃ k, firstJoin gates Q v u = n + k ∧ IsOrAt gates k := by
  obtain ⟨⟨h0, h1, h2⟩, hmin⟩ := firstJoin_spec gates h
  set i := firstJoin gates Q v u
  set Z := canonPt Q
  by_cases hin : i < n
  · rw [val_input gates Z i hin] at h0
    rw [val_input gates _ i hin] at h1 h2
    have e1 : (⟨i, hin⟩ : Fin n) = v := by
      by_contra hc
      rw [upPt, Function.update_of_ne hc, h0] at h1
      exact absurd h1 (by decide)
    have e2 : (⟨i, hin⟩ : Fin n) = u := by
      by_contra hc
      rw [upPt, Function.update_of_ne hc, h0] at h2
      exact absurd h2 (by decide)
    exact absurd (e2.symm.trans e1) huv
  by_cases hil : n + gates.length ≤ i
  · rw [mr_val_ge gates _ i hil] at h1
    exact absurd h1 (by decide)
  obtain ⟨k, hik⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
  have hk : k < gates.length := by omega
  rw [hik] at h0 h1 h2
  refine ⟨k, hik, ?_⟩
  rcases (hg _ (List.getElem_mem hk)).1 with hop | hop | hop
  · exfalso
    rw [mr_val_gate gates Z k hk, hop] at h0
    rw [mr_val_gate gates _ k hk, hop] at h1 h2
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id] at h0 h1 h2
    obtain ⟨a, ha, haz⟩ := h0
    have hva := h1 a ha
    have hua := h2 a ha
    have ha' : a < n + k := by
      by_contra hc
      rw [mr_val_ge (gates.take k) _ a (by simp; omega)] at hva
      exact absurd hva (by simp)
    rw [← mr_val_take gates _ k a ha'] at hva hua
    have haz' : val gates Z a = false := by
      rw [mr_val_take gates _ k a ha']
      simpa using haz
    exact hmin a (by omega) ⟨haz', hva, hua⟩
  · exact ⟨gates[k], List.getElem?_eq_getElem hk, hop⟩
  · exfalso
    have hkp : k = p := hU k p hk hp hop hN
    rw [hkp] at h0 h1
    have := not_false_of_le gates p hp hg hU hN (le_upPt Z v) h0
    rw [this] at h1
    exact absurd h1 (by decide)

include hg hU hN in
/-- **`f(u) ∈ F2(Q)`** (witness `Z = Q` with the star set through `u` and `v`). -/
theorem firstJoin_mem_F2 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ (starPts S Q v).erase v) :
    firstJoin gates Q v u ∈ F2 gates S Q := by
  obtain ⟨huv, huP⟩ := Finset.mem_erase.mp hu
  have hex := exists_joinsAt gates S out hev Q v huP
  obtain ⟨⟨h0, h1, h2⟩, -⟩ := firstJoin_spec gates hex
  obtain ⟨k, hk, hor⟩ := firstJoin_isOr gates p hp hg hU hN Q huv hex
  obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp huP
  obtain ⟨hwa, hvw⟩ := Finset.mem_filter.mp hw
  refine mem_F2.mpr ⟨⟨k, hk, hor⟩, w, hwa, canonPt Q, v, u, hvw, huw, Ne.symm huv,
    canonPt_zero_of_alive hwa, fun x hx => canonPt_eq_true.mpr hx, h0, h1, h2⟩

include hg hU hN in
/-- **`f(u) ∈ SEE(v)`**. -/
theorem firstJoin_mem_SEE (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ (starPts S Q v).erase v) :
    firstJoin gates Q v u ∈ SEE gates S Q v := by
  classical
  have hex := exists_joinsAt gates S out hev Q v (Finset.mem_erase.mp hu).2
  obtain ⟨⟨-, h1, -⟩, -⟩ := firstJoin_spec gates hex
  refine Finset.mem_filter.mpr ⟨firstJoin_mem_F2 gates p hp hg hU hN S out hev Q v hu, ?_⟩
  rwa [← upPt_canonPt]

include hg hU hN in
theorem firstJoinSet_subset_SEE (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) : firstJoinSet gates S Q v ⊆ SEE gates S Q v := by
  intro i hi
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
  exact firstJoin_mem_SEE gates p hp hg hU hN S out hev Q v hu

/-- `|F(v)| ≤ cost(v)` (the star sets meeting pairwise in at most one point); the difference is the
deficit. -/
theorem card_firstJoinSet_le (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1) :
    (firstJoinSet gates S Q v).card ≤ ∑ w ∈ starSets S Q v, ((S w).card - 1) := by
  classical
  rcases (starSets S Q v).eq_empty_or_nonempty with h0 | hne
  · have : starPts S Q v = ∅ := by simp [starPts, h0]
    simp [firstJoinSet, this]
  have hc := card_starPts S Q v hne hinter
  have hvP : v ∈ starPts S Q v := by
    obtain ⟨w, hw⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Finset.mem_filter.mp hw).2⟩
  have h1 := Finset.card_image_le (s := (starPts S Q v).erase v) (f := firstJoin gates Q v)
  rw [Finset.card_erase_of_mem hvP] at h1
  unfold firstJoinSet
  omega

include hg hU hN in
/-- **The immediate case**: `f` injective on `P \ {v}` (deficit `0`) and no `f`-gate survives ⇒ the F2
step. -/
theorem gainF2_of_firstJoin (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hinj : Set.InjOn (firstJoin gates Q v) ((starPts S Q v).erase v : Set (Fin n)))
    (hsurv : Disjoint (firstJoinSet gates S Q v) (SURV gates S Q v)) : GainF2 gates S Q v := by
  classical
  rcases (starSets S Q v).eq_empty_or_nonempty with h0 | hne
  · unfold GainF2
    rw [h0, Finset.sum_empty]
    exact Nat.zero_le _
  have hc := card_starPts S Q v hne hinter
  have hvP : v ∈ starPts S Q v := by
    obtain ⟨w, hw⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Finset.mem_filter.mp hw).2⟩
  have hcard : (firstJoinSet gates S Q v).card = ∑ w ∈ starSets S Q v, ((S w).card - 1) := by
    rw [firstJoinSet, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hvP]
    omega
  have hsub : firstJoinSet gates S Q v ⊆ (SEE gates S Q v \ SURV gates S Q v) ∪ K3 gates S Q v := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨firstJoinSet_subset_SEE gates p hp hg hU hN S out hev Q v hi, Finset.disjoint_left.mp hsurv hi⟩)
  exact gainF2_of_seeK3 gates S Q v (hcard.symm.le.trans (Finset.card_le_card hsub))

include hg hU hN in
/-- **The immediate case for heavy `v`**: `SURV = ∅`, so deficit `0` suffices. -/
theorem gainF2_of_firstJoin_heavy (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hinj : Set.InjOn (firstJoin gates Q v) ((starPts S Q v).erase v : Set (Fin n))) :
    GainF2 gates S Q v := by
  refine gainF2_of_firstJoin gates p hp hg hU hN S out hev Q v hinter hinj ?_
  rw [surv_eq_empty_of_heavy gates S Q v p hp hg hU hN hv]
  exact Finset.disjoint_empty_right _

/-- **ABSORB(v)** (dwV8p, OPEN): the deficit and the surviving `f`-gates are covered by dying gates
outside `F(v)`. -/
def Absorb (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  (∑ w ∈ starSets S Q v, ((S w).card - 1) - (firstJoinSet gates S Q v).card) +
      (firstJoinSet gates S Q v ∩ SURV gates S Q v).card ≤
    ((F2 gates S Q \ F2 gates S (insert v Q)) \ firstJoinSet gates S Q v).card

include hg hU hN in
/-- **ABSORB ⇒ the F2 step.** -/
theorem gainF2_of_absorb (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (H : Absorb gates S Q v) : GainF2 gates S Q v := by
  classical
  have hle := card_firstJoinSet_le gates S Q v hinter
  have hFS : firstJoinSet gates S Q v \ SURV gates S Q v ⊆
      (F2 gates S Q \ F2 gates S (insert v Q)) ∩ firstJoinSet gates S Q v := by
    intro i hi
    obtain ⟨hiF, hiS⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_inter.mpr ⟨seeK3_subset_gain gates S Q v (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨firstJoinSet_subset_SEE gates p hp hg hU hN S out hev Q v hiF, hiS⟩)), hiF⟩
  have h1 := Finset.card_le_card hFS
  have h2 := Finset.card_sdiff_add_card_inter (firstJoinSet gates S Q v) (SURV gates S Q v)
  have h3 := Finset.card_sdiff_add_card_inter (F2 gates S Q \ F2 gates S (insert v Q)) (firstJoinSet gates S Q v)
  unfold Absorb at H
  unfold GainF2
  omega

end FirstJoin

end PEqualNP.Outside.L_meta_951_aux

end F2FirstJoin

section CrossWorldCex

/-! CrossWorldCex: hypothesis (ii) of `CrossWorldAt.ndep` cannot be dropped even for circuits with
every minimality property of a MinCE that is a property of the circuit alone (tractability's
question, 09:08).

The question was whether, at a MinCE, a cross-world gate under hypothesis (i) alone is N-dependent
(`MinCE.crossWorld_ndep`), via hypothesis (ii) `C0(g)(Zof (S a)) = 0` for every merge gate `g` of `a`
at a world-0 zero point. On the corpus (34,064 one-NOT circuits: front's allcirc + chist + cxrb +
scaffold's data-corpora; script and results: see the board entry) both fail:
* (ii) fails for some merge gate at a world-0 point in 1,476 circuits, 155 of them live (every gate
  read or an output), essential and clean;
* a cross-world gate under (i) is N-INDEPENDENT in 174 circuits, 60 of them live, essential, clean.
No failure among the essential clean circuits with `s - base ≤ 4` (842 circuits): every failure
of the live essential clean kind has `s - base ≥ 5`.

`cx3_counterexample` is the smallest live essential clean failure (scaffold corpus
`ess/ess_k4e_clean.jsonl:627`), checked here by `decide`: `n = 4`, sets the edges `{0,1}, {0,2},
{0,3}, {1,2}, {1,3}` of `K4` minus `{2,3}`, 10 gates (one NOT, reading `h = x0 ∨ x2`), all outputs
correct, every gate read or an output, no gate a copy of an earlier wire (`MinCE.clean`), and the NOT
gate essential (`MinCE.essential`). Wire `6 = x0 ∨ x1 ∨ x3` is the merge of `{0,1}` at the world-0
point `e2` and of `{1,3}` at the world-1 point `0`, `0` vanishes on `{0,1}` (hypothesis (i)), `C0`
of wire `6` is `1` at `Zof {0,1}` (hypothesis (ii) fails), and wire `6` is N-independent.
So `MinCE.crossWorld_ndep` needs a property of a MinCE beyond `clean`, `live` and `essential`
(near-optimality: the data has no failure with `s - base ≤ 4`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- `cx3`: wires `0-3` inputs; `4 = x0 ∨ x3`, `5 = x0 ∨ x2`, `6 = x1 ∨ 4`, `7 = x3 ∧ 5`,
`8 = ¬ 5`, `9 = x0 ∨ x1`, `10 = x1 ∨ 7`, `11 = 8 ∨ 10`, `12 = x1 ∨ x2`, `13 = 6 ∧ 11`. -/
def cx3Gates : List Gate :=
  [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [6, 11]⟩]

/-- The sets of `cx3`: `{0,1}, {0,2}, {0,3}, {1,2}, {1,3}`. -/
def cx3S : Fin 5 → Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}]

/-- The outputs of `cx3`. -/
def cx3Out : Fin 5 → ℕ := ![9, 5, 4, 12, 13]

/-- The point `e2`. -/
def cx3E2 : Fin 4 → Bool := fun i => decide (i = 2)

set_option maxRecDepth 10000 in
theorem cx3_hyps : ProblemHyps cx3S cx3Gates cx3Out := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · intro g hg
    simp only [cx3Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i1 i2 h1 h2 e1 e2
    simp only [cx3Gates, List.length_cons, List.length_nil] at h1 h2
    interval_cases i1 <;> interval_cases i2 <;> simp_all [cx3Gates]

set_option maxRecDepth 10000 in
/-- **(ii) is necessary even for live, essential, clean circuits.** -/
theorem cx3_counterexample :
    ProblemHyps cx3S cx3Gates cx3Out ∧
      -- live: every gate is read by a gate or is an output
      (∀ k < cx3Gates.length, (∃ w, cx3Out w = 4 + k) ∨
        ∃ j < cx3Gates.length, 4 + k ∈ (cx3Gates.getD j ⟨GateOp.or, []⟩).inputs) ∧
      -- clean (`MinCE.clean`): no gate computes the same function as an earlier wire
      (∀ k j : ℕ, k < cx3Gates.length → j < 4 + k →
        ¬ ∀ x : Fin 4 → Bool, val cx3Gates x (4 + k) = val cx3Gates x j) ∧
      -- essential (`MinCE.essential`): both constant-NOT circuits are wrong
      (¬ ∀ (w : Fin 5) (x : Fin 4 → Bool),
        val (cx3Gates.map (constNot GateOp.or)) x (cx3Out w) = decide (∃ v ∈ cx3S w, x v = true)) ∧
      (¬ ∀ (w : Fin 5) (x : Fin 4 → Bool),
        val (cx3Gates.map (constNot GateOp.and)) x (cx3Out w) = decide (∃ v ∈ cx3S w, x v = true)) ∧
      -- the cross-world gate, hypothesis (i), the failure of (ii), N-independence
      CrossWorldAt cx3S cx3Gates 6 0 4 cx3E2 (fun _ => false) ∧
      (∀ v ∈ cx3S 0, (fun _ : Fin 4 => false) v = false) ∧
      val (C0 cx3Gates) (Zof (cx3S 0)) 6 = true ∧ ¬ NDep 4 cx3Gates 6 := by
  refine ⟨cx3_hyps, by decide, ?_, by decide, by decide,
    ⟨by decide, ⟨by decide, ?_, by decide⟩, ⟨by decide, ?_, by decide⟩⟩, by decide, by decide, ?_⟩
  · intro k j hk hj
    simp only [cx3Gates, List.length_cons, List.length_nil] at hk
    interval_cases k <;> interval_cases j <;> decide
  · intro p hp hn
    simp only [cx3Gates, List.length_cons, List.length_nil] at hp
    interval_cases p <;> first | decide | simp [cx3Gates] at hn
  · intro u hu p hp hn
    simp only [cx3Gates, List.length_cons, List.length_nil] at hp
    have hu' : u = 1 ∨ u = 3 := by simpa [cx3S] using hu
    rcases hu' with rfl | rfl <;> interval_cases p <;> first | decide | simp [cx3Gates] at hn
  · rintro ⟨x, hx⟩
    revert x
    decide

end PEqualNP.Outside.L_meta_951_aux

end CrossWorldCex

section Plane

-- Extension of the 951 base: the line-ORs of a projective plane of order q (step L-meta-952)
-- are a special case of 951 (lines meet in exactly one point, each line has q + 1 >= 3 points,
-- and the sum of (|line| - 1) over the m lines is m * q). So 952 holds as soon as 951 does:
-- this file adds no new sorry of its own.

namespace PEqualNP.Outside.L_meta_951_aux

theorem sum_const_sub {m q : ℕ} (S : Fin m → Finset (Fin m))
    (hcard : ∀ i : Fin m, (S i).card = q + 1) :
    ∑ i : Fin m, ((S i).card - 1) = m * q := by
  simp [hcard]

end PEqualNP.Outside.L_meta_951_aux

open PEqualNP.Outside.L_meta_951_aux in
theorem PEqualNP.Outside.L_meta_952 : ∀ (q m : ℕ) (S : Fin m → Finset (Fin m)), 2 ≤ q → m = q * q + q + 1 → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → (∀ p : Fin m, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card = q + 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin m → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → m * q ≤ gates.length := by
  intro q m S hq hm hcard hint _ gates out hg hι hev
  have h := PEqualNP.Outside.L_meta_951 m m S
    (fun i => by rw [hcard i]; omega) (fun i j hij => (hint i j hij).le) gates out hg hι hev
  rw [sum_const_sub S hcard] at h
  exact h

end Plane
