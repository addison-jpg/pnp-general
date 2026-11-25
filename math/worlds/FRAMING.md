# Is the framing of P vs NP wrong?

Seat FR1 (Opus), 2026-11-25. Asked by Addison: "we have to seriously consider that the entire framing of pnp is nonsense ... it seems built on old math, with infinite bounds that are just not properly infitely ocntinious." This note gives the case against the framing at full strength, then the replies, then the continuous formulations and what is proved about them, then where this repository sits, then a verdict. Nothing here says P vs NP is proved, near, or meaningless.

Read status as in [`LITERATURE.md`](../LITERATURE.md) (TXT, ABS, TLDR, MEM, CITED); new rows are in section P. Network: arXiv opened; scottaaronson.com, scottaaronson.blog and users.cs.duke.edu did not resolve in this session, so Aaronson's independence survey was **not** read (search summary only). One paper was read in its text: Aaronson, "Why philosophers should care about computational complexity" (arXiv 1108.1791; §3, §5.2, §12.1 read, TXT).

## 0. What the question is

"P ≠ NP" is an arithmetic sentence of the form ∀∃: for every machine M and exponent c there is an input on which M, run for n^c steps, errs on SAT. Its only infinity is "for every n", as in Goldbach; it needs no reals, limits or continuum. So "the bounds are not continuous" is true but does not bear on meaning. Whether it is the *right* question is where the serious critique lives.

## 1. The case against the framing (steel-manned)

**1a. Polynomial is the wrong line (Cobham–Edmonds is a choice).** Cobham (1965) and Edmonds (1965) proposed "polynomial time = feasible". Nothing forces it. An n^10000 algorithm is useless; a 1.00000001^n algorithm is fast for every n anyone will meet (Aaronson states this objection himself, 1108.1791 §3, TXT). Galactic algorithms are real, not hypothetical (the term is Lipton and Regan's; MEM):
- Robertson–Seymour give a cubic-time test for any fixed minor, with constants beyond astronomy.
- Via the Graph Minor Theorem, every minor-closed property is in P, often with no algorithm known. Membership in P can be proved non-constructively (Fellows–Langston; MEM).
- Harvey and van der Hoeven multiply integers in O(n log n), but the bound only bites for inputs larger than any computer can store (MEM).

Conversely, for linear programming the worst-case-exponential simplex method (Klee–Minty 1972) beat the polynomial ellipsoid method (Khachiyan 1979) in practice (MEM). So P neither implies nor is implied by "practical". A resolution of P vs NP in either direction could leave practice unchanged: a proof of P = NP with an n^1000 algorithm, or a proof of P ≠ NP with the hard instances at n = 10^9.

**1b. Asymptotics against concrete complexity.** Any statement for "all large n" is consistent with any behaviour for every n below 10^100. Aaronson lists this as criticism (1) of complexity theory: asymptotic statements "need not have any implications whatsoever for the finite values of n ... that humans care actually about, nor can any finite amount of experimental data confirm or refute an asymptotic claim" (1108.1791 §12.1, TXT). Gödel's 1956 letter to von Neumann asked a *concrete* question: whether proofs of length n can be found in about k·n or k·n² steps (MEM). The asymptotic class was a later choice.

**1c. Worst case against typical case.**
P vs NP is about the worst input of each length. SAT solvers settle industrial instances with millions of variables (MEM); smoothed analysis makes the simplex method polynomial under slight perturbation (Spielman–Teng, JACM 2004, MEM). In Impagliazzo's "Heuristica" (1995; `math/worlds/README.md`) P ≠ NP and NP is still easy on every samplable distribution; the worst-case answer underdetermines what matters.

**1d. Independence.** P vs NP may be independent of ZFC or of weaker theories.
- Razborov (1995) proved that superpolynomial circuit lower bounds are unprovable in certain fragments of bounded arithmetic, under a cryptographic assumption (MEM).
- Ben-David and Halevi (1991–92) showed that if independence were proved by the usual techniques, NP would have algorithms very close to polynomial (search summary). Even an "unprovable" answer would then be practically P = NP.
- Aaronson's survey ("Is P versus NP formally independent?", BEATCS 81, 2003) treats the possibility seriously (search summary; not read).

**1e. Uniform against non-uniform.** P uses one machine for all n; P/poly allows a different circuit per n. P/poly contains undecidable unary languages, so neither is clearly "the" model of feasibility. In the physical world we build one chip per input size, which favours circuits. P vs NP and NP ⊄ P/poly are different conjectures, linked only by Karp–Lipton (`math/worlds/README.md`).

**1f. "Polynomial" is historical.** The class has an algebraic justification (closure under composition, Cobham's axioms) but no physical one. Ultrafinitists sharpen the point:
- Parikh (1971) showed that a theory can consistently treat "feasible numbers" as closed under addition and multiplication yet bounded far below 2^1000 (MEM).
- Sazonov (1995) worked in the same direction (MEM).

On this view, "for every n" is itself an idealisation, and the asymptotic quantifier smuggles in an infinity that no machine instantiates. This is the most rigorous version of Addison's worry.

**1g. Physicists and philosophers.**
- Siegelmann (Science 1995): analog networks with real weights compute beyond Turing machines (MEM). If nature computes with reals, bits are the wrong idealisation.
- Factoring is in BQP (Shor 1994) and not known in P, so the classical machine is a physical bet, not a mathematical necessity.
- Dean's SEP entry "Computational complexity theory" (2016) treats Cobham–Edmonds as a philosophical thesis with largely inductive support (MEM, not opened).

## 2. The strongest replies

**2a. P is robust across models.** Turing machines (one or many tapes), log-cost RAMs, cellular automata and uniform circuits simulate each other with polynomial overhead, so P is the same in all of them. NP has machine-free characterisations: existential second-order logic (Fagin 1974; here as `p_eq_np_iff_lfp_eq_eso`, `math/worlds/LANGUAGE.md`), PCP (1992–98, MEM), and thousands of natural complete problems (Garey–Johnson 1979, MEM). The one known way to break robustness is unbounded precision. Hartmanis and Simon (1974) show that unit-cost RAMs with multiplication decide PSPACE in polynomial time (TLDR). The lesson is that a model which charges one step for an arbitrarily long number is not a reasonable model. A line that every reasonable model draws in the same place is not arbitrary in the way a convention is.

**2b. The extended Church–Turing thesis.** The thesis says every physically reasonable model is polynomially simulable by a probabilistic Turing machine. It is a physical hypothesis. Quantum mechanics may refute it, and the refutation is itself stated in the same framework (BPP against BQP). The framing absorbed its strongest physical challenge instead of breaking. Infinite-precision analog models (Siegelmann) are excluded for the same reason as Hartmanis–Simon RAMs: noise of any fixed size collapses them (MEM).

**2c. Why asymptotics are the right invariant.** For a fixed n every problem is easy in the trivial sense: any function on n bits has a circuit of size O(2^n/n) (Shannon, Lupanov; MEM). So "how hard is SAT at n = 1000?" is a question about one constant, and that constant depends on the machine, the encoding and the gate basis. The growth class is the coarsest quantity that is invariant under all of these.

Concrete complexity is a legitimate, finite question, and this repository works on it (exact gate counts). It is a *different* question, and it is model-dependent. Aaronson's reply to the asymptotic objection: galactic constants are possible in principle, "however, experience has shown that ... that happens rarely enough that one can usually take asymptotic behavior as 'having explanatory force until proven otherwise'" (1108.1791 §5.2, TXT). He also lists understanding *why* n^10000 algorithms are rare as an open philosophical question (§12.2, TXT). That is the honest state of the matter.

**2d. Independence does not mean meaningless.** A ∀∃ sentence about the integers has a truth value in the standard model whether or not ZFC proves it. Aaronson draws exactly this contrast with the Continuum Hypothesis (1108.1791, footnote 73, TXT). Independence would be a fact about our axioms, not about the question.

**2e. Average case and non-uniformity are refinements, not replacements.**
Impagliazzo's worlds are defined relative to P vs NP, and cryptography's average-case hardness implies P ≠ NP. Worst-case P ≠ NP is the weakest of a family of hardness statements, so the first to settle.

**2f. The essay's general reply.** Aaronson grants all four standard criticisms some merit. He then argues that "if we reject the conclusions of the best approximate theory in some area, then the burden is on us to explain why" (1108.1791 §12.1, TXT). A critic must commit to an alternative: a galactic P = NP, practical heuristics, or a physical model that escapes the extended Church–Turing thesis. Each of these is itself a statement in the framework.

## 3. Continuous formulations, and what links them to the discrete question

Two ways: **algebraic** (exact real or complex operations at unit cost: BSS, Valiant, GCT) and the **bit model** (reals given by approximations, cost in bits: Ko, Braverman–Cook).

**3a. Blum–Shub–Smale.** BSS (Bull. AMS 1989; book with Cucker, *Complexity and Real Computation*, 1998; MEM) define P_ℝ, NP_ℝ, P_ℂ, NP_ℂ.
- **Complete problems.** Hilbert's Nullstellensatz (does a complex system have a common zero?) is NP_ℂ-complete; feasibility of one real degree-4 polynomial is NP_ℝ-complete (MEM).
- **Proved links:**
  - transfer: P = NP has one answer over all algebraically closed fields of characteristic 0 (BCSS, search summary);
  - P_ℂ = NP_ℂ implies NP ⊆ BPP (Shub–Smale; BCSS; search summary), so the classical NP ⊄ BPP implies P_ℂ ≠ NP_ℂ;
  - *under GRH*, the Nullstellensatz for integer systems is in AM ⊆ Π₂ (Koiran, J. Complexity 1996; hypothesis weakened by Rojas 2003; ABS / search);
  - over ℝ with algebraic constants, BSS polynomial time with Boolean output is P^PosSLP, inside the counting hierarchy (Allender–Bürgisser–Kjeldgaard-Pedersen–Miltersen, SICOMP 2009; ABS; one lemma questioned in a later thesis);
  - P_ℂ ≠ NP_ℂ implies VP⁰ ≠ VNP⁰, uniform and constant-free (Bürgisser, arXiv 2606.25121, 2026; ABS fetched; converse conjectured);
  - separations hold in restricted variants such as Koiran's weak model (Cucker–Shub–Smale 1994; MEM).
- **Open:** P_ℝ vs NP_ℝ; P_ℂ vs NP_ℂ; whether either implies or is implied by P vs NP.

**3b. Valiant's VP vs VNP** (Valiant 1979, MEM). This is the algebraic form of the question: can the permanent be written as a polynomial-size projection of a determinant? The determinant is efficiently computable; the permanent is VNP-complete (characteristic ≠ 2).
- **Proved:** if VP = VNP over a finite field, or over characteristic 0 *under GRH*, then nonuniform NC, P, NP, PH coincide (Bürgisser, TCS 2000; search summary); so under GRH, discrete hypotheses of the form #P ⊄ P/poly imply VP ≠ VNP. Derandomising identity testing gives NEXP ⊄ P/poly or a permanent lower bound (Kabanets–Impagliazzo 2004, MEM). Best bound: determinantal complexity of perm_n ≥ n²/2 (Mignon–Ressayre 2004, MEM).
- **Open:** VP ≠ VNP itself. It is believed easier than P ≠ NP, and no implication from it to P ≠ NP is known.

**3c. Geometric complexity theory.** Mulmuley–Sohoni (SICOMP 2001, 2008; MEM) recast VP vs VNP as a question about orbit closures: is the padded permanent in the orbit closure of det_m for m polynomial in n? Separation would come from representation-theoretic *obstructions*.
- **No-go (2016):** rectangular Kronecker coefficients cannot work (Ikenmeyer–Panova, Adv. Math. 2017, arXiv 1512.03798; search summary); *occurrence* obstructions cannot separate det from padded perm (Bürgisser–Ikenmeyer–Panova, JAMS 2019, arXiv 1604.06431; ABS fetched).
- **Open:** multiplicity obstructions. Mulmuley's "P ≠ NC without bit operations" (SICOMP 1999, MEM) is a proved separation, but in an algebraic PRAM model.

**3d. Smale's 17th problem (solved).** Can an approximate zero of n complex polynomial equations in n unknowns be found in polynomial time on average? Smale posed it in 1998 (MEM).
Beltrán–Pardo (JAMS 2009, MEM): randomized, yes. Bürgisser–Cucker (Annals 2011, MEM): deterministic N^{O(log log N)}, polynomial smoothed. Lairez (FoCM 2017; arXiv 1507.05485; search summary): deterministic average polynomial time (BSS with square roots), derandomising Beltrán–Pardo "using the randomness contained in the input itself".

No relation to the discrete question is proved. Its lesson is the one in 1c: under an *average* (and smoothed) measure, a problem whose decision version is NP_ℂ-complete has a tractable search version for generic square systems.

**3e. Complexity of real computation (bit model).** Ko (*Complexity Theory of Real Functions*, 1991; MEM) and Braverman–Cook (Notices AMS 2006; arXiv cs/0509042; ABS) represent a real number by a machine that returns approximations, and count cost in bits. Braverman and Cook argue this is "the most accurate abstraction of how computers are used to solve problems over the reals" (ABS).
- **Proved:** the continuous problems here *are* the discrete ones. There is an infinitely differentiable polynomial-time computable f on [0,1] whose running maximum is polynomial-time computable **iff P = NP**; integration corresponds to FP = #P (Ko–Friedman 1982, Friedman 1984; search summary via Konečný–Neumann). Lipschitz ODE solving is PSPACE-complete (Kawamura, CCC 2010, MEM).

So in the bit model, "making it continuous" returns P vs NP unchanged.

**Summary of 3.** The unit-cost continuous worlds have their own open P vs NP analogues. Each is linked to the discrete one only one way, often only under GRH, and none is known to settle it. The bit-model continuous world is provably the discrete question in another form.

## 4. Where this repository's continuous attempts sit

None of them is a continuous *model of computation*. All three are continuous *proof devices* for finite, restricted circuit statements on the circuit axis (`math/worlds/README.md`, last section).

- **Φ** (`one-not/lean/PEqualNP/W951/ContinuousAttach.lean`, `Continuous.lean`, board [`continuous-mapping`](../boards/tasks/continuous-mapping.md)). Φ(p) = E_{μ_p}[slack] is the multilinear (Bernstein) extension of a finite table at fixed n. In kind it is Fourier analysis or Russo–Margulis, not BSS. The board's verdict was that the gradient at the corner is the vector of one-point steps, so every continuous route "is the count again or refuted". That is a small-scale case of the Ko–Friedman pattern in 3e: a continuous extension of a finite object carries exactly the finite difficulty.
- **The limit level and flag algebras** (BOARD.md "THREE LEVELS"; LITERATURE.md §L). Taking n → ∞ gives pattern densities, and the hope is inequalities proved by semidefinite certificates. This is extremal combinatorics (Razborov 2007), not complexity over ℝ. At best it gives gates ≥ (1 − o(1))·base for a restricted model, a linear bound for functions in P. Exactness needs a stability step. Hatami–Norine show that density inequalities are undecidable in general.
- **The descriptive restatement** (`math/worlds/LANGUAGE.md`) is evidence for 2a, not a route around it.

No object here is a BSS machine, an arithmetic circuit for perm/det, or an orbit closure; nothing bears on VP vs VNP, P_ℂ vs NP_ℂ or GCT. The repository's core work (exact gate counts in fixed restricted models) is *concrete complexity*, the alternative 1b asks for.

## 5. Verdict

**Arbitrary (modelling choices):** the line at *polynomial* (justified by closure and robustness, not practicality; galactic algorithms diverge from practice both ways); *worst case*; *uniform* rather than non-uniform; the *classical* machine (grounded in an extended Church–Turing thesis that quantum computing doubts); *bits* rather than exact reals (unit-cost ℝ and ℂ give different, open questions).

**Forced (robust across models):** the class P (same in every reasonable discrete model; only unbounded unit-cost precision changes it); the class NP (machine-free definitions, thousands of complete problems); its meaning (a ∀∃ sentence about integers, true or false whether or not ZFC decides it); its persistence (the bit-model continuous version is provably the same question, Ko–Friedman; algebraic siblings are, where anything is known, implied by discrete conjectures, not the reverse); growth classes themselves (forced once you ask about a problem rather than one size, since every fixed size is a finite table).

**Is "the framing is nonsense" defensible?** Not as stated. The question is precise, robust and meaningful, and its "infinite bounds" are the ordinary ∀n of arithmetic, not a defective continuum. A weaker claim is defensible and held by serious people:

> P vs NP may not be the question whose answer tells us what we can compute in practice. Either answer could be practically uninformative (galactic P = NP; P ≠ NP with hardness only at absurd n or only on rare inputs). The polynomial line and the worst-case quantifier are conventions chosen for mathematical robustness.

That is a critique of *relevance*, not of *sense*. The convincing argument against the strong claim is that every attempt to replace the framing by a more natural one has either reproduced it (other discrete models, logic, the bit model of the reals) or produced a sibling whose known relation to it runs one way and is itself open.
