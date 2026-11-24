import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.TUCert
import PEqualNP.W951.CertDHeavy

/-!
# CertStair: CERT-3c from (D) at a heavy point with SEE and (S) by the real Theorem U

Composition of qg-d2's (D) (`certD_of_heavy_see`, CertDHeavy.lean: a heavy `v`, every cone merge of the
star `1` at `Q + e_v`) with cTAHG's (S) (`certS_of_tu`, `certS_stair`, TUCert.lean).

* `cert3c_of_heavy_tu`: heavy `v`, zero points `z_w ⊇ Q` off `S_w`, SEE for their cone merges and
  pairwise `TUPair` in one direction ⇒ CERT-3c at `v`.
* `cert3c_of_heavy_stair`: the same at the staircase points (`h = 0` there).
* `no_minCE_of_heavy_tu_or_local`: every `Q` with positive base is `CubeLocal`, satisfies LW1, or has a
  heavy `v ∉ Q` with such zero points ⇒ no minimal counterexample.

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

end PEqualNP.Outside.L_meta_951_aux
