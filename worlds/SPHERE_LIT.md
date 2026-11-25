# SPHERE_LIT: literature map of the hairy ball theorem and its extensions

Seat S3 (Sonnet, retrieval), 2026-11-25. Task: BOARD.md "SPHERE OF FIELDS". Theory first, Lean last.
Originals are cited in their own language. **Read status** as in LITERATURE.md: TXT / ABS / TLDR / MEM / CITED.
Honest note: this seat could not open any original (all 1885-1962 papers are paywalled or scanned). Every
statement below is **MEM** (standard, from memory) unless a row says otherwise; bibliographic details
(volume, pages) are also MEM and must be checked before they are quoted in print. Only three items were
touched on the web this session: the Milnor 1978 citation (CITED, via a course page), the PPAD hairy ball
paper (ABS, arXiv 1902.07657) and the Nash PPAD chain (CITED, via ECCC and SICOMP listings).

Mathlib check: grep of `/home/user/pequalnp-proofs/lean/.lake/packages/mathlib/Mathlib` (the repo has no
`.lake` of its own). Names searched: Brouwer, hairy, EulerCharacteristic, Sphere, fixedPoint, Borsuk,
Sperner, Lefschetz, Hopf, Hurwitz, parallelizable, PPAD, Tucker, Octonion, Quaternion.

## 1. Statements, sources, status, Mathlib

| # | Item and exact statement | Original source (language), year | Read | Mathlib |
|---|---|---|---|---|
| 1 | **Hairy ball.** Every continuous tangent vector field on S^{2m} (m >= 1) has a zero; S^n carries a nowhere-zero continuous tangent field iff n is odd. S² case first (via index sum 2). | Poincaré, "Sur les courbes définies par les équations différentielles (III)", J. Math. Pures Appl. (4) 1 (1885) 167-244 (French), the S² case through the index of singular points. Brouwer, "Über Abbildung von Mannigfaltigkeiten", Math. Ann. 71 (1912) 97-115 (German), all even spheres, by degree. | MEM | **Absent.** No `hairy`; only a CategoryTheory grading file matches the string. The sphere is there as a manifold (`Geometry/Manifold/Instances/Sphere.lean`: `stereographic`, `EuclideanSpace.instChartedSpaceSphere`), but no tangent-field zero theorem. |
| 2 | **Poincaré-Hopf.** M compact smooth manifold (boundary empty), v a smooth vector field with isolated zeros; then the sum of the indices of the zeros = χ(M). On S² this gives 2, which is hairy ball with a count. | Poincaré 1885 (surfaces, same paper, French); Hopf, "Vektorfelder in n-dimensionalen Mannigfaltigkeiten", Math. Ann. 96 (1926) 225-250 (German), general dimension. Modern text: Milnor, *Topology from the Differentiable Viewpoint* (1965), §6. | MEM | **Absent.** `EulerCharacteristic.lean` is only the alternating sum of ranks of a chain complex (algebra), no manifold χ, no vector-field index. |
| 3 | **Milnor's analytic proof.** Hairy ball on S^{2m}, and Brouwer in the ball, by calculus: if v is a nowhere-zero field, normalise to unit, form the homotopy f_t(x) = cos t x + sin t v(x), show the volume of the image of the sphere of radius r is a polynomial in t, contradicting that f_π = antipode reverses orientation when n is even. Brouwer follows by a retraction argument. | Milnor, "Analytic proofs of the 'Hairy Ball Theorem' and the Brouwer Fixed Point Theorem", Amer. Math. Monthly 85 (1978) 521-524 (English). Companion: Eisenberg and Guy, Monthly 86 (1979), a proof by the same device. | CITED (citation confirmed on a course page; text not opened) | Needs: Stokes or change of variables on spheres, polynomiality of volume. Mathlib has change-of-variables (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) but not the sphere surface measure with tangent homotopy. Not present. |
| 4 | **Adams 1962 and Radon-Hurwitz.** Write n = (odd)·2^{c+4d}, 0 <= c <= 3, and ρ(n) = 2^c + 8d. Then S^{n-1} has exactly ρ(n) - 1 linearly independent continuous tangent fields. Values: ρ(2)=2, ρ(4)=4, ρ(8)=8, ρ(16)=9, odd n: ρ=1 (no field: hairy ball). Existence: Clifford-module / orthogonal multiplication (Radon, Hurwitz). Non-existence: Adams, by K-theory with Adams operations ψ^k. S¹, S³, S⁷ have ρ(n) - 1 = n - 1 fields, i.e. a full frame, so they are parallelizable; this is exactly n = 2, 4, 8 = dim ℂ, ℍ, 𝕆 (the only S^{n-1} with ρ(n) = n). | Radon, "Lineare Scharen orthogonaler Matrizen", Abh. Math. Sem. Hamburg 1 (1922) 1-14; Hurwitz, "Über die Komposition der quadratischen Formen", Math. Ann. 88 (1923) 1-25 (both German); Hurwitz's theorem on composition algebras only in dim 1, 2, 4, 8, Nachr. Ges. Wiss. Göttingen (1898) 309-316 ("Über die Composition der quadratischen Formen von beliebig vielen Variabeln"); Eckmann, Comment. Math. Helv. 15 (1943), group-theoretic Hurwitz-Radon; Adams, "Vector fields on spheres", Ann. of Math. 75 (1962) 603-632 (English). | MEM | **Quaternions yes** (`Algebra/Quaternion.lean`, `QuaternionBasis.lean`, `DualQuaternion.lean`); **octonions no** (grep empty). **No ρ(n), no Adams, no Clifford-module count, no parallelizability.** The circle is a Lie group (`LieGroup (𝓡 1) ω Circle` in the sphere file), the only sphere with a manifold group structure proved. |
| 5 | **Hopf invariant one.** A map S^{2n-1} -> S^n has a Hopf invariant H in ℤ; H = ±1 occurs only for n = 1, 2, 4, 8. Equivalent: R^n is a (non-associative) division algebra only for n = 1, 2, 4, 8; equivalent: S^n is an H-space only for n = 0, 1, 3, 7. Bott-Milnor and Kervaire (1958) got the division-algebra form by other means. | Adams, "On the non-existence of elements of Hopf invariant one", Ann. of Math. 72 (1960) 20-104 (English), via secondary cohomology operations; Adams-Atiyah, "K-theory and the Hopf invariant", Quart. J. Math. 17 (1966) 31-38, the short K-theory proof. Hopf's invariant: Hopf 1931 (row 6). | MEM | **Absent.** No Hopf invariant, no H-space classification of spheres, no Steenrod or Adams operations. |
| 6 | **Hopf fibration.** S¹ -> S³ -> S² (z1, z2) |-> [z1 : z2]; also S³ -> S⁷ -> S⁴ (ℍ) and S⁷ -> S¹⁵ -> S⁸ (𝕆). First essential map S³ -> S², Hopf invariant 1, so π₃(S²) = ℤ. Bloch sphere: the pure qubit states, ℂP¹ = S²; the unit vector in ℂ² (S³ = SU(2)) maps to the state up to phase. | Hopf, "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche", Math. Ann. 104 (1931) 637-665 (German); Hopf 1935 for the other two (Fund. Math. 25, "Über die Abbildungen von Sphären auf Sphären niedrigerer Dimension"). | MEM | **Not as a named bundle.** Pieces exist: `Complex.circle`, `Circle`, the projective space `Projectivization` (algebra), `unitary`, SU(2) as `Matrix.specialUnitaryGroup`; no fibre-bundle statement, no π₃(S²). |
| 7 | **Lefschetz fixed point.** M compact triangulable (or compact ENR), f: M -> M continuous, L(f) = Σ (-1)^k tr(f_* on H_k(M; ℚ)). If L(f) ≠ 0 then f has a fixed point. L(id) = χ(M). Hopf-Lefschetz: a vector field's index sum is χ, and the fixed-point form of Poincaré-Hopf. Sphere: L(f) = 1 + (-1)^n deg f, so on S^{2m} a fixed-point-free map has degree -1, which gives hairy ball (v gives a homotopy of the identity to the antipode only if deg = 1 = -1, absurd). | Lefschetz, "Intersections and transformations of complexes and manifolds", Trans. Amer. Math. Soc. 28 (1926) 1-49 (English); Hopf, "Über die algebraische Anzahl von Fixpunkten", Math. Z. 29 (1929) 493-524 (German), general form. | MEM | **Absent.** The word hits (`AxGrothendieck.lean`) are the algebraic Lefschetz principle (model theory), not topology. `EilenbergSteenrod.lean` and `SingularHomology` exist as scaffolding. |
| 8 | **Brouwer fixed point.** Every continuous f: D^n -> D^n has a fixed point. n = 1 is the intermediate value theorem. Equivalent to: no retraction D^n -> S^{n-1}; to hairy ball (no wait, hairy ball implies Brouwer for even n via Milnor; both follow from degree). | Brouwer, "Über Abbildung von Mannigfaltigkeiten", Math. Ann. 71 (1912) 97-115 (German); Hadamard, in Tannery's *Introduction à la théorie des fonctions* (1910), appendix (French), and Brouwer's 1911 "Beweis der Invarianz des n-dimensionalen Gebiets", Math. Ann. 71 (1911) 305-313; Bohl 1904 for n = 3. Knaster-Kuratowski-Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe", Fund. Math. 14 (1929) 132-137 (German), the KKM lemma, a Sperner consequence. | MEM | **Absent.** Names in grep for `Brouwer` are Brouwerian lattices (Heyting), unrelated. Nearby: Banach (`ContractingWith.fixedPoint`, `Topology/MetricSpace/Contracting.lean`), Knaster-Tarski (`OrderHom.lfp`, `Order/FixedPoints.lean`), intermediate value theorem (`Topology/Order/IntermediateValue.lean`, = Brouwer n = 1). |
| 9 | **Borsuk-Ulam.** Every continuous f: S^n -> R^n has x with f(x) = f(-x). Equivalent: no odd (antipodal-equivariant) map S^n -> S^{n-1}; the n = 2 case: some two antipodal points of the Earth have equal temperature and pressure. Implies Brouwer (n = 2 via ham sandwich as well). Lusternik-Schnirelmann-Borsuk covering form. | Borsuk, "Drei Sätze über die n-dimensionale euklidische Sphäre", Fund. Math. 20 (1933) 177-190 (German); the conjecture is Ulam's. Matoušek, *Using the Borsuk-Ulam Theorem* (2003), the modern text. | MEM | **Absent.** The grep hit for Borsuk is Borsuk-Mazurkiewicz in `Topology/Homotopy/LocallyContractible.lean` (a counterexample citation), not the theorem. |
| 10 | **Sperner's lemma.** Triangulate an n-simplex, colour vertices with n+1 colours so that a vertex on a face uses only that face's colours; then the number of fully-coloured cells is odd. (Parity, hence existence; a counting argument along a door-to-door path.) Gives Brouwer and KKM by limit. | Sperner, "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes", Abh. Math. Sem. Univ. Hamburg 6 (1928) 265-272 (German). Hairy ball by Sperner: Jarvis and Tanton, Amer. Math. Monthly 111 (2004) (only noted as cited in the Wikipedia hairy-ball article). | MEM | **Name collision.** Mathlib's `Sperner` is *Sperner's theorem* on antichains in the Boolean lattice (`Combinatorics/SetFamily/LYM.lean`), a different Sperner. The simplicial lemma is absent. `AlgebraicTopology/SimplicialComplex` is scaffolding. |
| 11 | **Tucker's lemma.** Triangulate B^n, antipodally symmetric on the boundary, with labels in {±1, ..., ±n} that are antipodally odd on the boundary; then some edge has complementary labels (i, -i). Combinatorial Borsuk-Ulam. | Tucker, "Some topological properties of disk and sphere", Proc. First Canadian Math. Congress, Montreal (1945) 285-309 (English). Constructive proof: Freund and Todd, J. Combin. Theory A 30 (1981) 321-325. | MEM | **Absent.** (`Tucker` grep hits are unrelated Lipschitz files.) |
| 12 | **PPAD.** Total search problems with a polynomial-time checkable "directed graph, in-degree and out-degree at most 1, given a source, find another end" (END OF LINE). PPAD ⊆ TFNP; it captures parity-style existence proofs that are directed. | Papadimitriou, "On the complexity of the parity argument and other inefficient proofs of existence", J. Comput. System Sci. 48 (1994) 498-532 (English). | MEM | **Absent** (the grep for `PPAD` is just substrings of `MvPolynomial`; no TFNP, no search-problem classes). Mathlib has `Computability`, `Turing` machines, `Polynomial` time via `Computability/TMComputable`. |
| 13 | **Sperner and Brouwer are PPAD-complete.** SPERNER (given the colouring by a Boolean circuit on a grid triangulation, find a fully coloured cell) and 2D/3D BROUWER (find an approximate fixed point of a Lipschitz map given by a circuit) are PPAD-complete. Papadimitriou 1994 puts Sperner in PPAD and proves PPAD-completeness of 3-D (a Sperner) problem; hardness in 2D by Chen and Deng. Hairy ball: finding the zero of a tangent field on S² (given by a circuit) is PPAD-complete. | Papadimitriou 1994 (row 12); Chen and Deng, "On the complexity of 2D discrete fixed point problem", Theoret. Comput. Sci. 410 (2009) 4448-4456 (English, 2D Sperner; ICALP 2006 version); Daskalakis, Goldberg, Papadimitriou, below. Goldberg and Hollender, "The Hairy Ball Problem is PPAD-Complete", ICALP 2019, arXiv:1902.07657 (J. Comput. System Sci. 2021). | CITED (PPAD hairy ball: **ABS** from the search listing only; rest MEM) | Absent. |
| 14 | **Nash is PPAD-complete.** Finding a Nash equilibrium of a game is PPAD-complete: 4 players (Daskalakis, Goldberg, Papadimitriou, STOC 2006; SIAM J. Comput. 39 (2009) 195-259, "The Complexity of Computing a Nash Equilibrium"), 3 players (Chen and Deng, and independently Daskalakis and Papadimitriou 2005), 2 players (Chen and Deng, "Settling the complexity of two-player Nash equilibrium", FOCS 2006, 261-272; Chen, Deng, Teng, J. ACM 56(3) (2009), "Settling the complexity of computing two-player Nash equilibria"). The route: Nash ⇒ Brouwer for the best-response map (Nash 1950 via Kakutani 1941, then Brouwer 1951 proof), and Brouwer-in-circuit-form ⇒ Nash by gadgets. | as stated, all English | CITED (listings seen on the web; the proofs not read) | Absent. |

## 2. How the pieces hang together (all MEM, for the theory seats)

- Degree route (Brouwer 1912): deg of antipode on S^n is (-1)^{n+1}; a nowhere-zero field on S^n is a
  homotopy from id to antipode; so n even has none. Poincaré-Hopf makes this a count (index sum = χ).
- Lefschetz generalises Brouwer (D^n has L = 1) and gives the sphere statement through L(id) = χ = 2 on S^{2m}.
- Brouwer, Sperner, KKM, Tucker, Borsuk-Ulam are one cluster: each implies the next in the sense of
  "equivalent by short deductions", and the two combinatorial ones are the parity lemmas that PPAD
  abstracts. Tucker is to Borsuk-Ulam as Sperner is to Brouwer.
- Adams is the quantitative form of hairy ball: n even gives ρ(n) >= 2 only when n is even, n odd gives 1.
  The parallelizable spheres S¹, S³, S⁷ are the ρ(n) = n cases, and the same list 1, 2, 4, 8 is Hopf
  invariant one and Hurwitz's composition theorem (row 4, 5). The three results (Hurwitz 1898/1923,
  Adams 1960, Adams 1962) say the same thing: the algebras ℝ, ℂ, ℍ, 𝕆 are the whole story.

## 3. Ranking: extension, repository program, reachability in Lean

Ranked by (join with the repository, then Lean reach). Lean is last by rule; "reach" means how far Mathlib already
is, not a promise to formalise.

1. **Hopf fibration / Bloch sphere (row 6)** to **quantum gravity and qubits** (S² = pure qubit states;
   S³ = SU(2) = unit ℍ, the KAK and qubit layer). Strongest join and nearest Lean: Mathlib has `Quaternion`,
   `Circle`, `Matrix.specialUnitaryGroup`, the sphere as a chart-carrying manifold. Missing: the quotient
   map statement. First formalisable: the map (z1, z2) |-> (|z1|²-|z2|², 2 z1 conj z2) lands in S² and its fibres
   are circles (an algebraic identity, no topology).
2. **Radon-Hurwitz / Adams (rows 4, 5)** to **the hypercomplex layer** (ℝ, ℂ, ℍ, 𝕆 are the only
   normed division algebras). Reach: quaternion norm multiplicative is in Mathlib; octonions are not,
   so the Hurwitz statement (composition algebras only in dimension 1, 2, 4, 8) would need a
   Cayley-Dickson construction first. Adams' non-existence is out of reach (K-theory operations).
   The *existence* half (ρ(n) fields via Clifford-module matrices) is finite linear algebra and reachable.
3. **PPAD, Sperner, Brouwer (rows 12, 13, 14)** to **complexity** (the repository's P vs NP programs).
   A real extra: hairy ball itself is PPAD-complete (Goldberg-Hollender, row 13), which makes the sphere
   statement a total search problem sitting in the same class as Nash. Lean reach: low for the
   class; moderate for *Sperner's lemma on a triangulated simplex* (a finite parity argument; but the Mathlib name
   `Sperner` is the antichain theorem, do not confuse them), and the 1-D case of Brouwer (IVT) is already in
   Mathlib. A Lean statement of END OF LINE as a total search problem is a definition, not a theorem,
   so it can be written first.
4. **Poincaré-Hopf / hairy ball (rows 1, 2)** to **Deleuze.lean, zeros of fields** (a problem = a vector
   field, the actual = its zeros; existence on S² by topology alone). Theory join is the best of all, but Lean reach is
   the worst of the top four: no manifold Euler characteristic, no vector-field index, no degree. The cheapest
   checkable form is the combinatorial one: a discrete vector field on a triangulated sphere has a zero with
   index sum 2 (Forman-style, a finite count), which needs only `SimplicialComplex` scaffolding.
5. **Lefschetz, Borsuk-Ulam, Tucker (rows 7, 9, 11)** are the strongest generalisations but join the
   repository only through the above; reach is nil for Lefschetz (needs homology traces), low for Borsuk-Ulam
   (n = 1 is checkable: f: S¹ -> ℝ has f(x) = f(-x) by IVT, a good first lemma), moderate for Tucker in a fixed
   small dimension.
6. **Milnor's analytic proof (row 3)** is the best *paper* route and the worst Lean route (volume of the
   image under a one-parameter family of maps, needs surface measure on spheres). Theory seat S2 owns it.

Cheapest Lean statements in order: the IVT form of Brouwer (n = 1) and Borsuk-Ulam (n = 1); the Hopf map
algebra identity; Sperner's lemma in dimension 1 and 2 as a finite parity count; the existence half of Radon-Hurwitz
for n = 2, 4, 8.

## 4. Not done

No original opened (see the note at the top). The Lefschetz sphere sentence in row 7 and the "equivalent"
clause in row 8 are rough and need a paper check; row 13's attribution of 2D hardness is MEM. Items to
re-read first: Poincaré 1885 (Gallica), Brouwer 1912 (GDZ), Hopf 1926 and 1931 (GDZ), Adams 1962 (JSTOR),
Milnor 1978 (JSTOR).
