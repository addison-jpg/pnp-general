import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.ConeCert
import PEqualNP.W951.F2SeeK3

/-!
# CertDHeavy: lemma (D) of qg-d2's certificate at a heavy point (qg-d2, 2026-11-24)

qg-d2's certificate CERT-1c / CERT-3c (`ConeCert.lean`, board `951/board/agents/qg-d2-ucert.md`) needs,
at a chosen `v`, (D): no cone merge of a set through `v` lies in `F2(Q ∪ {v})`, and (S): the cone merge
sets of the sets through `v` are pairwise disjoint (cTAHG).

This file proves (D) at a HEAVY `v` (the NOT gate is `0` at `Q + e_v`, i.e. `h(Q + e_v) = 1`) under the
condition SEE: every cone merge of a set through `v` is `1` at `Q + e_v`. The proof is F1
(`F1_real_zero`): at a heavy `v`, every gate with an F2 witness at `Q ∪ {v}` is `0` at `Q + e_v`.
`certD_of_see0` proves (D) at ANY `v`, heavy or light, under SEE0: every such cone merge is `1` at
`Q + e_v` in the real circuit and in `C_0` (the circuit with the NOT gate forced to `0`). The proof is
F1* (`F1star_mem`): a gate of `F2(Q ∪ {v})` that is `1` at `Q + e_v` has `C_0 = 0` there.

Coverage (`951/tools/kill_tests/proved_cover.py`): with cTAHG's `certS_of_tu` for (S), SEE0 + TU zero points
cover 16,970 / 17,045 non-local every-gate-read instances (light 4,170 / 4,192, heavy 12,800 / 12,853).

Data (`951/tools/kill_tests/certd.py`, 17,045 every-gate-read instances whose NOT gate is not a literal or
constant on the cube): heavy `v` with SEE at `z = Q` gives (D) at 25,081 / 25,081 pairs (as it must);
such a `v` exists in 12,620 of the 12,853 instances that have a heavy point. Survivors of (D) at `z = Q`
are almost all merges between two points of `S_w` other than `v` (not `1` at `Q + e_v`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CertDHeavy

variable {n m : ℕ}

/-- **(D) at a heavy `v` with SEE.** If the NOT gate is `0` at `Q + e_v` and every cone merge (at any
zero points `z w`) of a set through `v` is `1` at `Q + e_v`, then no such merge lies in `F2(Q ∪ {v})`. -/
theorem certD_of_heavy_see (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (z : Fin m → Fin n → Bool)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hsee : ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
      val gates (canonPt (insert v Q)) i = true) :
    CertD gates S out Q v z := by
  intro w hw i hi hiF
  obtain ⟨-, w', -, hwit⟩ := mem_F2.mp hiF
  have h0 := F1_real_zero gates p hp hg hU hN (S w') Q v hv hwit
  rw [hsee w hw i hi] at h0
  exact absurd h0 (by decide)

/-- **(D) at any `v` with SEE0.** If every cone merge (at any zero points `z w`) of a set through `v` is
`1` at `Q + e_v` both in the real circuit and in `C_0`, then no such merge lies in `F2(Q ∪ {v})`. -/
theorem certD_of_see0 (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (z : Fin m → Fin n → Bool)
    (hsee : ∀ w ∈ starSets S Q v, ∀ i ∈ coneMerge gates (S w) (out w) (z w),
      val gates (canonPt (insert v Q)) i = true ∧
        val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true) :
    CertD gates S out Q v z := by
  intro w hw i hi hiF
  obtain ⟨h1, h0⟩ := hsee w hw i hi
  have h2 := (F1star_mem gates p hp hg hU hN S Q v hiF h1).2.1
  rw [h0] at h2
  exact absurd h2 (by decide)

end CertDHeavy

end PEqualNP.Outside.L_meta_951_aux
