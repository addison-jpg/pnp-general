# Note 2: quantum gravity models of computation and the three barriers

pequalnp.com, 2026-11-24. An assessment, not a claim. No statement here bears on whether P equals NP.

**Question assessed.** Can unified gravity, or quantum gravity more generally, be mapped onto the
relativization barrier, and through it onto the algebrization and natural proofs barriers, in a way
that this project's checker can use?

**Short answer.** Yes as a map, no as a route. Each of the three barriers has an exact counterpart in
how physics enters complexity theory, and every counterpart lands on the side of the barrier, never
past it. The relativization and algebrization parts are corollaries of checked rows (section 6).
Unified gravity itself adds nothing that the map can use.

## 0. The word "relativization"

"Relativization" means "holds relative to every oracle". The name comes from "relative to an
oracle", not from special or general relativity. There is no link through the word. The only link
between physics and these barriers is the model of computation, and the rest of this note uses
only that link.

## 1. How a physical theory enters

P versus NP is a statement about Turing machines (`Defs/Base.lean`). No physical theory changes
its truth value. A physical theory T changes only which machines count as physically efficient. It
can do that in two ways:

1. **A black-box resource.** T supplies a device D, and an algorithm uses D only through its
   input-output behaviour. That behaviour is a language A_D, and a machine with D is an oracle
   machine relative to A_D (`Defs/Oracle.lean`). Then P_T = P^{A_D} and NP_T = NP^{A_D}.
2. **A new machine model.** T changes the step rule itself: quantum mechanics gives BQP; Deutsch's
   closed timelike curves give P_CTC.

Two checked rows fix the baseline. With no added resource (the empty oracle), P^∅ = P (L-lib-084)
and NP^∅ = NP (L-lib-085). An added resource only enlarges P: P ⊆ P^A for every A (L-lib-057).

## 2. Relativization: physics as an oracle

**Checked rows.** Baker, Gill and Solovay (1975): some oracle A has P^A = NP^A (L-lib-061), and
some oracle B has P^B ≠ NP^B (L-lib-062). Corollary (section 6): neither equation nor inequation
holds for every oracle.

**Map.** An argument that uses a physical resource only as a black box proves its conclusion
relative to every oracle the resource could be. By the corollary, no such argument decides
P versus NP. Physics realizes both sides of the barrier:

| Barrier side | Checked row | Physics counterpart |
|---|---|---|
| collapse, P^A = NP^A | L-lib-061 (padded oracle; the textbook proof uses a PSPACE-complete oracle) | Closed timelike curves in Deutsch's model: P_CTC = BQP_CTC = PSPACE (Aaronson and Watrous 2009). That is the world of a PSPACE-complete oracle, where NP ⊆ PSPACE = P_CTC. |
| separation, P^B ≠ NP^B | L-lib-062 | Quantum mechanics as a black box: relative to a random oracle, with probability 1, NP is not solved by a quantum machine in time o(2^{n/2}) (Bennett, Bernstein, Brassard and Vazirani 1997). That is the quantum version of the separation side. |

Special-relativistic time dilation does not give a third case: the speedup needs energy that grows
exponentially as the computer approaches the speed of light (Aaronson 2005, "NP-complete problems
and physical reality").

**Consequence.** A quantum gravity theory moves the question only if it adds a resource such as
closed timelike curves. It then picks an oracle world, the PSPACE-complete one above. The
relativization barrier says that picking a world does not decide the unrelativized question
(the empty oracle, section 1).

## 3. Unified gravity

Partanen and Tulkki (Rep. Prog. Phys. 88, 057802, 2025) derive gravity as a gauge theory of four
one-dimensional unitary (U(1)) gauge symmetries, in the framework of the Standard Model. The
authors have shown renormalizability at first order; higher orders are open.

For this map, the theory is a quantum field theory. It does not posit closed timelike curves or
any other non-unitary resource, so it supplies no oracle of either side of section 2. If its
dynamics can be simulated by quantum circuits with polynomial overhead, it is inside BQP and adds
nothing beyond case 2 of section 1. Such a simulation is shown for some quantum field theories
(scalar φ⁴ theory: Jordan, Lee and Preskill 2012). No simulation result for unified gravity is
known to this note. **Verdict: unified gravity gives no relativization handle, no algebrization
handle and no natural proofs handle.** Its open renormalizability question does not change that.

## 4. Algebrization: amplitudes as low-degree extensions

**Checked rows.** Aaronson and Wigderson (2009): for every injective naming of field elements,
there are an oracle A and a multiquadratic extension E of A with NP^A ⊄ P^E (L-lib-065), and an
oracle A and a multiquadratic extension E of A with NP^E ⊆ P^A (L-lib-076). The extension oracle
is `extOracle` in `Defs/Algebraic.lean`. Corollary (section 6): neither inclusion holds for every
oracle and every multiquadratic extension.

**Map.** After T queries, the acceptance probability of a quantum query algorithm is a real
multilinear polynomial of degree at most 2T in the oracle bits (Beals, Buhrman, Cleve, Mosca and
de Wolf 2001). That is the same object as an extension oracle: a low-degree polynomial that agrees
with the oracle on the Boolean cube. Aaronson and Wigderson (section 5 of their paper) also give
oracles A, Ã with NP^A ⊄ BQP^Ã: a quantum machine that reads the algebraic extension still does not
get NP. So quantum mechanics as an arithmetized black box is blocked by algebrization exactly as
the classical machines of L-lib-065 are.

**Gap in this repository.** `Defs` has no quantum machine, so the BQP form of the Aaronson and
Wigderson separation cannot be stated here yet.

## 5. Natural proofs: holographic complexity as a natural property

**Checked rows.** Razborov and Rudich (1997), with fan-in-two distinguishers: an exponentially
secure pseudorandom function in P rules out natural proofs against P/poly (L-lib-086, from
L-lib-087 and the circuit simulation L-lib-073). Use L-lib-086, not L-lib-035: the hypothesis of
L-lib-035 holds for no function (L-lib-093), because its distinguishers may use a MOD 2 gate.

**Map.** The complexity-equals-volume proposal (Stanford and Susskind 2014) equates the volume of a
wormhole with the circuit complexity of the dual boundary state. Bouland, Fefferman and Vazirani
(ITCS 2020) give evidence for computationally pseudorandom states in the boundary theory and
conclude that either the AdS/CFT dictionary is exponentially complex or the quantum extended
Church-Turing thesis fails in quantum gravity. The argument has the shape of Razborov and Rudich:

| Razborov and Rudich | Holographic complexity |
|---|---|
| natural property: large and constructive (decidable in time polynomial in the truth table) | wormhole volume: large on typical states, and efficiently computable in the bulk |
| usefulness: holds on no function of small circuit size | volume growth: holds on no state of small circuit complexity |
| a pseudorandom function defeats every constructive test | a pseudorandom state family defeats every efficient boundary test |

Aaronson (2016, "The complexity of quantum states and transformations") shows that hardness of
states of this kind follows from PSPACE ⊄ PP/poly. An unconditional proof would be a superpolynomial
lower bound of the kind these three barriers constrain.

## 6. Corollaries, in Lean

These three statements follow from the checked rows named in them. They were compiled with
`lake env lean` against the pinned toolchain and the pinned Mathlib, and `#print axioms` shows
only `propext`, `Classical.choice` and `Quot.sound`. They have not been through the project's
checker, so they are not rows; they are candidates for gaps.

```lean
import PEqualNP.Library.L057
import PEqualNP.Library.L061
import PEqualNP.Library.L062
import PEqualNP.Library.L065
import PEqualNP.Library.L076
import PEqualNP.Library.L084
import PEqualNP.Library.L085

open PEqualNP.Library

theorem relativization_map :
    ¬ (∀ A : Language Bool, OracleP A = OracleNP A) ∧
    ¬ (∀ A : Language Bool, OracleP A ≠ OracleNP A) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨B, hB⟩ := PEqualNP.Library.L062
    exact hB (h B)
  · obtain ⟨A, hA⟩ := PEqualNP.Library.L061
    exact h A hA

theorem algebrization_map (codes : FieldCodes) (hc : FieldCodes.Injective codes) :
    ¬ (∀ (A : Language Bool) (E : AlgExtension), IsMultiquadraticExtension A E →
        OracleNP A ⊆ OracleP (extOracle codes E)) ∧
    ¬ (∀ (A : Language Bool) (E : AlgExtension), IsMultiquadraticExtension A E →
        ¬ OracleNP (extOracle codes E) ⊆ OracleP A) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨A, E, hE, hA⟩ := PEqualNP.Library.L065 codes hc
    exact hA (h A E hE)
  · obtain ⟨A, E, hE, hA⟩ := PEqualNP.Library.L076 codes hc
    exact h A E hE hA

theorem empty_oracle_map :
    OracleP (∅ : Set (List Bool)) = P ∧ OracleNP (∅ : Set (List Bool)) = NP ∧
    ∀ A : Language Bool, P ⊆ OracleP A :=
  ⟨PEqualNP.Library.L084, PEqualNP.Library.L085, PEqualNP.Library.L057⟩
```

## 7. What would be new work

1. A quantum machine in `Defs` (BQP). That is the prerequisite for stating the Bennett, Bernstein,
   Brassard and Vazirani separation and the BQP form of the Aaronson and Wigderson separation.
2. A closed-timelike-curve machine in `Defs` (Deutsch fixed points), to state P_CTC = PSPACE.
   This needs PSPACE in `Defs` as well.
3. Neither item gives a route to P versus NP. Both would make the physics side of the map in
   sections 2 and 4 checkable instead of cited.

## 8. Sources

- T. Baker, J. Gill, R. Solovay. Relativizations of the P =? NP question. SIAM J. Comput. 4(4), 1975.
- S. Aaronson, J. Watrous. Closed timelike curves make quantum and classical computing equivalent.
  Proc. R. Soc. A 465(2102), 631-647, 2009. arXiv:0808.2669.
- C. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum
  computing. SIAM J. Comput. 26(5), 1997.
- S. Aaronson. NP-complete problems and physical reality. SIGACT News 36(1), 2005.
- M. Partanen, J. Tulkki. Gravity generated by four one-dimensional unitary gauge symmetries and
  the Standard Model. Rep. Prog. Phys. 88, 057802, 2025.
- S. Jordan, K. Lee, J. Preskill. Quantum algorithms for quantum field theories. Science 336, 2012.
- S. Aaronson, A. Wigderson. Algebrization: a new barrier in complexity theory. ACM Trans. Comput.
  Theory 1(1), 2009.
- R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials.
  J. ACM 48(4), 2001.
- A. Razborov, S. Rudich. Natural proofs. J. Comput. Syst. Sci. 55, 1997.
- D. Stanford, L. Susskind. Complexity and shock wave geometries. Phys. Rev. D 90, 126007, 2014.
- A. Bouland, B. Fefferman, U. Vazirani. Computational pseudorandomness, the wormhole growth
  paradox, and constraints on the AdS/CFT duality. ITCS 2020. arXiv:1910.14646.
- S. Aaronson. The complexity of quantum states and transformations: from quantum money to black
  holes. arXiv:1607.05256, 2016.
