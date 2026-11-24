# Gate elimination / complexity measures: verbatim extracts

All quotes are from pdftotext of the open-access full texts, fetched this session. Quotes are exact except for pdftotext artifacts (ligatures, line breaks, minus signs). Where I paraphrase, it is marked "NOTE".
PDF/text copies are in /tmp/claude-0/-home-user/8c137ad4-29bc-5711-be93-e44232612946/scratchpad/charging/pdf/ (fghk, gk, dk, li, limits, hjkp, cdj, cs .pdf/.txt).

Read in full text: papers 1-7 (all). NOT obtainable: paper 8 (Lachish-Raz, Iwama-Morizumi, Zwick); see section 8 for what second-hand statements exist in the papers I did read.

---------------------------------------------------------------------
## 1. Find, Golovnev, Hirsch, Kulikov. "A better-than-3n lower bound for the circuit complexity of an explicit function"
URL read: https://eccc.weizmann.ac.il/report/2015/166/download (ECCC TR15-166, latest revision; the ECCC page shows the title "Improving $3n$ Circuit Complexity Lower Bounds", Revision #2, Aug 2022. The PDF text I read is headed "Report No. 166 (2015)", dated October 17, 2015, and is the (3+1/86)n version.)

### Measure (Sec. 3.4, "Circuit complexity measure")
"For a circuit C and a straight-line program R defining an rdq-source, we define the following circuit complexity measure:
   µ(C, R) = g + αQ · q + αT · t + αI · i ,
where g is the number of internal gates in C, q is the number of quadratic substitutions in R, t is the number of troubled gates in C, and i is the number of influential input gates in C. We say that an input is influential if it feeds at least one gate or is protected (recall that a variable is protected if it occurs in the right-hand side of a quadratic substitution in R). The constants αQ, αT, αI > 0 will be chosen later."

Troubled gate (Sec. 3.2.2): "We say that an internal gate G is troubled if it satisfies the following three criteria:
 • G is an and-type gate of fanout 1,
 • the gates feeding G are input gates,
 • both input gates feeding G have fanout 2."

rdq-source (Sec. 3.3, Def. 1; Definition 3): a system with free variables F, quadratic substitutions x_j = (x_i ⊕ c_i)(x_k ⊕ c_k) ⊕ c_j for j in Q ("the variables from the right-hand side of all the quadratic substitutions are pairwise disjoint"), and affine substitutions for j in L. "Definition 3. An rdq-disperser for dimension d(n) is a family of functions f_n : F_2^n → F_2 such that for all sufficiently large n, for every rdq-source R of dimension at least d(n), f_n|R is non-constant." Prop. 4: "Let R be an rdq-source of F_2^n of dimension d. Then R contains an affine subspace of dimension at least d/2." Corollary 2: "An affine disperser for sublinear dimension is also an rdq-disperser for sublinear dimension."

Constants (Sec. 3.4 / proof of Cor. 3 and Sec. 3.5.2): "αT = 1/43, αQ = 1 + 22αT = 65/43, αI = 6 + 2αT = 6 + 2/43, β = 1 − 4αT = 39/43, δ = 9 + 3αT = 9 + 3/43." "This gives a (3 + 1/86)n − o(n) lower bound for an affine disperser for sublinear dimension." (β is the guaranteed measure drop per normalization-removed gate.)

### Main theorem (Sec. 3.4, Theorem 1; Corollary 3)
"Theorem 1. Let f : F_2^n → F_2 be an rdq-disperser for dimension d and C be a fair semicircuit computing f. Let αQ, αT, αI ≥ 0 be some constants, and αT ≤ 1/4. Then µ(C, ∅) ≥ δ(n−d−2) where
   δ := αI + min{ nαI/2 [sic; pdftotext of "αI/2"], 4β, 3 + αT, 2β + αQ, 5β − αQ, 2.5β + αQ/2 },   (1)
and β = 1 − 4αT."
"Corollary 3. Let δ, β, αQ, αT, αI be constants as above, then the circuit size of an affine disperser for sublinear dimension is at least (δ − αT/2 − αI) n − o(n)."
Proof of Cor. 3 uses "q = 0, i ≤ n, t < n/2 + 5d/2 (see Lemma 3)".
"Lemma 3. Let C be a circuit computing an affine disperser f : F_2^n → F_2 for dimension d, then the number of troubled gates in C is less than n/2 + 5d/2." (proof: each variable feeding a troubled gate has outdegree 2; double-counting gives 2t = v1 + 2v2; if t ≥ n/2+5d/2 then v2 ≥ 5d and one builds X, Y with |X|=d and consistent equations making C independent of X ∪ Y, contradicting the disperser.)
The LP used: "maximize δ − αT/2 − αI subject to β + 4αT = 1, αT, αQ, αI, β ≥ 0, δ ≤ αI + min{...}".

### Elimination step (Sec. 3.5, Theorem 2)
"Theorem 2. Let f : F_2^n → F_2 be an rdq-disperser for dimension d, let R be an rdq-source of dimension s ≥ d + 2, and let C be an optimal (i.e., C with the smallest µ(C, R)) fair semicircuit computing the function f|R. Then there exist an rdq-source R′ of dimension s′ < s and a fair semicircuit C′ computing the function f|R′ such that µ(C′, R′) ≤ µ(C, R) − δ(s − s′)."
"Proof of Theorem 1. We prove that for optimal C computing f|R, µ(C, R) ≥ δ(s − d − 2). We do it by induction on s, the dimension of R."
Normalization (Prop. 3): "Each of the Rules 1–5 removes one internal gate, introduces at most four new troubled gates." So "during normalization if we eliminate a gate then we introduce at most four new troubled gates, this means that we decrease the measure by at least 1 − 4αT = 39/43. Therefore, normalization never increases the measure."
Substitution types in the full proof (Sec. 3.5.2), "by ∆µ we denote the decrease of the measure after subsequent normalization":
 1. two consecutive affine substitutions reducing influential inputs by ≥ 3: "∆µ ≥ 1.5αI" per substitution.
 2. one affine substitution reducing influential inputs by ≥ 2: ∆µ ≥ 2αI.
 3. one affine substitution killing four internal gates: ∆µ ≥ 4β + αI.
 4. one constant substitution eliminating three internal gates including a troubled gate with no new troubled gate: ∆µ ≥ αI + 3 + αT.
 5. one quadratic substitution killing five internal gates: ∆µ ≥ 5β − αQ + αI.
 6. two affine substitutions killing ≥5 gates and replacing a quadratic substitution by an affine one: 5β + αQ + 2αI (per substitution 2.5β + αQ/2 + αI).
 7. one affine substitution killing two gates and replacing one quadratic substitution by an affine one: ∆µ ≥ 2β + αQ + αI.
Sketch of the central case (Sec. 3.5.1): A = topologically minimal and-type gate with inputs I1, I2. Case 5(b)i: "we eliminate a variable, three gates and decrease the number of troubled gates by one. Thus, we decrease the measure by αI + 3 + αT = 9 3/43 = δ." Case 5(b)ii (troubled gate whose elimination would create a new troubled gate): "we make a different substitution: z = (x ⊕ c1)(y ⊕ c2) ⊕ c3 ... we eliminate one variable, five gates, but we introduce a new quadratic substitution, and decrease the measure by at least αI + 5β − αQ = 9 3/43 = δ."
Cyclic circuits (Sec. 2.1, Lemma 2, "xor-reconstruction"): affine substitution x = ⊕x_i ⊕ c is implemented by rewiring the xor part, which may create cycles ("fair" cyclic xor-circuit: linear system has full rank); semicircuit = cyclic xor-circuit composed with ordinary circuit. "In what follows we abuse the notation by using the word 'circuit' to mean a fair semicircuit."

### Amortization / memory
- The measure is µ(C, R): a function of the CURRENT semicircuit C and the CURRENT source R only. t and i are recomputed from the current graph (t = number of troubled gates currently present; i = currently influential inputs). The only history-dependent term is q = number of quadratic substitutions currently pending in R (a "delayed affine substitution"; when later converted to an affine one, µ gets αQ back: cases 6 and 7 above).
- Amortization is via potential-like terms: αT·t is "an amortized analysis: we count not just the number of gates, we compute a linear combination of the number of gates and the number of bottlenecks" (Intro). Quote: "The second ingredient in our proof is a complexity measure that manages difficult situations (bottlenecks) by allowing to perform an amortized analysis".
- Initial value: µ(C, ∅) is bounded below via induction; final size recovered by subtracting αT·t + αI·i using Lemma 3 (needs the disperser property to bound t) and i ≤ n.
- Intro on lineage of such measures (verbatim): "Zwick [Zwi91] counted the number of (internal) gates minus the number of inputs of outdegree 1. The same measure was later used by Lachish and Raz [LR01] and by Iwama and Morizumi [IM02]. Kojevnikov and Kulikov [KK10] used a measure assigning different weights to linear and non-linear gates to show that Schnorr's 2n − O(1) lower bound [Sch76] can be strengthened to 7n/3 − O(1)."
- Open question quote: "A natural extension is to allow similarly sized varieties defined by quadratic polynomials. As shown by Golovnev and Kulikov [GK15], such dispersers with appropriate parameters must have circuit size at least 3.1n."

---------------------------------------------------------------------
## 2. Golovnev, Kulikov. "Weighted gate elimination: Boolean dispersers for quadratic varieties imply improved circuit lower bounds"
URL read: https://eccc.weizmann.ac.il/report/2015/170/download (ECCC TR15-170)

### Definitions
"Definition 1 (quadratic variety). A set S ⊆ F_2^n is called an (n, k)-quadratic variety if it can be defined as the set of common roots of t ≤ k polynomials of degree at most 2."
"Definition 2 (quadratic disperser). A Boolean function f ∈ B_n is called an (n, k, s)-quadratic disperser if f is non-constant on any (n, k)-quadratic variety S ⊆ F_2^n of size at least s."
xor-layered circuit: "a circuit whose inputs may be labeled not only by input variables but also by sums of variables."

### Measure
Sec. 3, before Lemma 3: "we use the following circuit complexity measure: µ(C) = G(C) + α · I(C) where 0 < α ≤ 1 is a constant to be determined later." (G(C) = number of non-input gates, I(C) = number of input gates.) Intro (3n warm-up): "Consider the following measure of an xor-layered circuit C: µ(C) = G(C) + I(C)" with the claim "for any affine subspace S ⊆ F_2^n of dimension D and any xor-layered circuit C computing f on S, µ(C) ≥ 4(D − d − 1)"; "It is also interesting to note that the inequality G(C) + I(C) ≥ 4(n − d − 1) is tight" (inner product function).

### Main theorem (Theorem 1)
"Theorem 1. Let 0 < α ≤ 1 and 0 < β be constants satisfying
   2^{−(2+α)/β} + 2^{−(4+2α)/β} ≤ 1,  (2)
   2^{−2/β} + 2^{−(5+2α)/β} ≤ 1,  (3)
   2^{−(3+3α)/β} + 2^{−(2+2α)/β} ≤ 1,  (4)
   2^{−3/β} + 2^{−(4+α)/β} ≤ 1,  (5)
and let f ∈ B_{n,1} be an (n, k, s)-quadratic disperser. Then C(f) ≥ min{βn − β log2 s − β, 2k} − αn."
"For example, for an (n, 1.83n, 2^{o(n)})-quadratic disperser Theorem 1 with α = 0.535 and β = 3.6513 implies a 3.1163n − o(n) > 3.116n lower bound. For an (n, 1.78n, 2^{0.03n})-quadratic disperser it implies a 3.006n lower bound." Abstract: "if a Boolean function f is a (n, 1.83n, 2^{g(n)})-quadratic disperser for any function g(n) = o(n) then the circuit size of f is at least 3.11n."

### Elimination step / weighted induction (Lemma 3 and Sec. 1.4)
"Lemma 3. Let f ∈ B_n be an (n, k, s)-quadratic disperser, S ⊆ F_2^n be an (n, t)-quadratic variety, 0 < α ≤ 1, 0 < β be constants satisfying inequalities (2), (3), (4), (5), C be an xor-layered circuit that computes f on S. Then µ(C) ≥ min{β(log2|S| − log2 s − 1), 2(k − t)}."
Induction is on |S| (size of the variety), not on number of variables. Pick a gate G computing a function g of degree ≤ 2; split S into S0 = {g=0}, S1 = {g=1}, |S_i| = p_i|S|, p0+p1 = 1. If µ(C) − µ(C_i) ≥ ∆_i then "µ(C) ≥ µ(C_i) + ∆_i ≥ min{β(log2|S| − log2 s − 1) + ∆_i − β log2(1/p_i), 2(k − t) + (∆_i − 2)}". The step goes through if for some i, ∆_i ≥ β log2(1/p_i) and ∆_i ≥ 2; "The inequality ∆_i ≥ β log2 1/p_i is true whenever p_i ≥ 2^{−∆_i/β}. ... for the induction step to go through it suffices to have 2^{−∆0/β} + 2^{−∆1/β} ≤ 1 and ∆0, ∆1 ≥ 2 . (8)" Case 1.1.1 example: "{∆0, ∆1} = {2 + 2α, 3 + 3α}. The required inequalities (8) follows from (4)."
Sec. 1.4 (verbatim): "We prove Theorem 1 by extending the gate elimination method. The proof goes by induction on the size of the current quadratic variety S. ... We then estimate how much the size of the circuit shrinks for each of these varieties and how much the size of the variety shrinks. Roughly, we show that in at least one of these cases the circuit shrinks a lot while the size of the variety does not shrink a lot. That is why we call this method weighted gate elimination."

### Amortization / memory
- µ(C) = G + α·I depends only on the current (xor-layered) circuit. The "memory" is the variety S (its log-size and the number t of quadratic equations used so far): the potential in the final bound is min{β(log2|S| − ...), 2(k − t)}, i.e. two counters of the current variety, not of circuit history. No troubled-gate counter is used here.
- The branching is two-sided (both S0 and S1 tracked), with weights 2^{−∆_i/β} (a Kraft-type inequality) instead of a fixed per-step drop.

---------------------------------------------------------------------
## 3. Demenkov, Kulikov. "An elementary proof of a 3n − o(n) lower bound on the circuit complexity of affine dispersers"
URL read: https://eccc.weizmann.ac.il/report/2011/026/download (ECCC TR11-026)

### Measure (Sec. 4)
"In this section we consider only circuits over B2. Let µ(C) = s(C) + N(C), where s(C) is the size (number of gates) of C and N(C) is the number of input variables of C with out-degree at least 1."

### Main theorem
"Theorem. Let f : F_2^n → F_2 be an affine disperser for sources of dimension d, let A be an affine subspace of F_2^n of dimension D, and let C be a circuit with n inputs such that ∀x ∈ A, C(x) = f(x). Then µ(C) ≥ 4(D − d)."
"Corollary. Any circuit over B2 computing an affine disperser for d = o(n) has at least 3n − o(n) gates. Proof. ... Then s(C) = µ(C) − N(C) ≥ 4(n − d) − n = 3n − d."

### Elimination step
"Lemma. Let P be a gate of a circuit C that is a ⊕-type gate that depends only on ⊕-type gates of out-degree 1 and variables. Then there is a variable x_j and a (possibly empty) subset of variables I ⊆ {1,...,n}\{j} such that for any constant c ∈ F_2, the substitution x_j = ⊕_{i∈I} x_i ⊕ c makes the gate P constant and reduces N(C) by at least 1."
Proof of Theorem: induction on D. "In the following we find a substitution of the form ⊕_{i∈I} x_i ⊕ c under which C is reduced to C′ such that µ(C) ≥ µ(C′) + 4 and C(x) = C′(x) for all x ∈ A′ = {x ∈ A : ⊕_{i∈I} x_i = c}. Since A′ has dimension at least D − 1, we conclude by induction that µ(C) ≥ 4(D − 1 − d) + 4 = 4(D − d)." Take P = first gate in topological order that is not a ⊕-type gate of out-degree 1. Cases: 1 (P ⊕-type, outdeg ≥ 2: make P constant; µ drops ≥ 4); 2.1 (an input of the ∧-type P is a gate Q: make Q constant, kills P, Q, successors of P; N reduced by ≥ 1, so µ ≥ 4); 2.2 (both inputs variables, one of outdegree ≥ 2: assign constant killing successors of x_i and of P; s drops ≥ 3, N ≥ 1); 2.3 (both inputs outdegree-1 variables: s drops ≥ 2 and N drops ≥ 2).

### Amortization / memory
- µ = s + N, a function of the current circuit only; no history. The "+N" term amortizes the case where a substitution removes an input without removing 4 gates (each of the cases above drops s by ≥ 3 and N by ≥ 1, or s by ≥ 2 and N by ≥ 2).
- Related-work quote (Sec. 3): "Zwick [16] proved a 4n−c lower bound for all MOD^n_{m,r} functions, m ≥ 3. He noticed that any optimal circuit for such a function can contain only a constant number of out-degree 1 variables. This allows to remove such variables from the consideration by using a circuit complexity measure equal to the number of gates minus the number of out-degree 1 variables." and "Iwama, Lachish, Morizumi, and Raz [10, 8, 7] used Zwick's circuit complexity measure to prove a lower bound 5n − o(n) on C_U2 for strongly two-dependent functions, i.e., functions satisfying the following property: for any two variables all the four sub-functions resulting by fixing the values of these variables are different." (They then describe the main bottleneck of Zwick's proof as a specific top-of-circuit configuration, and mention Amano-Tarui: a k-mixed function (k = o(n)) of circuit complexity 5n + o(n) shows k-mixedness is not enough for stronger than 5n.)

---------------------------------------------------------------------
## 4. Li, Yang. "3.1n − o(n) circuit lower bounds for explicit functions"
URL read: https://eccc.weizmann.ac.il/report/2021/023/download (ECCC TR21-023, 43 pp.)

### Main theorem
"Theorem 1.1 (Main theorem). Assume that C is a B2 circuit computing an affine disperser for sublinear dimension, then C has size at least 3.1n − o(n)."

### Measure (Sec. 3.1-3.2)
"Definition 3.1 (Troubled gate). A gate G is called troubled if it is an ∧-type 1-gate fed by two 2-variables (see Figure 8). Two troubled gates are called adjacent if they share at least one common input variable."
"Definition 3.2 (Troubled pair). A troubled pair (G, G′) is a pair of adjacent troubled gates. The input variables that feed both G and G′ are called inner variables, and the variables that feed one of G and G′ are called boundary variables." (compact pair: no boundary variable.)
"Definition 3.3 (Packing). Let C be a circuit and T be the set of all troubled pairs. A subset of disjoint troubled pairs P ⊆ T is called a packing of C, and each troubled pair (G, G′) ∈ P is called a pack. By disjoint, we mean that each gate can be contained in at most one pack."
"Definition 3.4 (Truly troubled gate). Let C be a circuit and P be a packing. A gate is said to be truly troubled if it is a troubled gate that does not contained in a pack."
"Definition 3.5 (Potential). ... We define the potential Φ(C, P) as the number of truly troubled gates plus |P|, or equivalent, as the number of troubled gates minus |P|."
"Definition 3.6 (Circuit complexity measure). Let C be a circuit, P be a packing and R be an rdq-source. The circuit complexity measure µ(C, P, R) is defined as
   µ(C, P, R) ≜ g + αI · i + αQ · q + αφ · Φ(C, P),
where g is the number of gates, i is the number of influential inputs and q is the number of quadratic equations. An input is called influential if it is either a 1+-variable or protected. Note that αI, αQ and αφ are positive constants that will be chosen later."
"Lemma 3.7 (Lemma 3 in [FGHK16]). Let C be a circuit computing an affine disperser for dimension d, then the number of troubled gates is at most n/2 + 5d/2." Cor. 3.8: Φ(C,P) ≤ n/2 + 5d/2 for every packing P.
"Theorem 3.9. Assume that computing a function f : F_2^n → F_2 requires complexity µ(C, P, ∅) ≥ µ0 for any circuit C and packing P, we must have |C| ≥ µ0 − αI · n − αφ (n/2 + d). Furthermore, if f is an affine disperser for sublinear dimension and µ0 = δn − o(n), we have |C| ≥ (δ − αI − αφ/2) n − o(n)."

### Normalization lemma (Lemma 3.11)
"Let β be the complexity measure decrement for each normalization rule. For Rule 1 we have β ≥ 1 − 2αφ, and for other rules we have β ≥ 1 − αφ. Moreover, ... the potential increment is caused only by direct introduction of troubled gates or packs, which are either I1 (or I2) or fed by them after the normalization." ("αφ will be chosen to be smaller than 1/2, so that β ≥ 0.") Compare FGHK: each removed gate may create 4 troubled gates (cost 4αT); Li-Yang improves to 2 (Rule 1) or 1 (other rules) via packing: "we may improve the 4k bound to 2k".

### Elimination steps
"Lemma 3.12 (Troubled pair elimination). Let C be a circuit computing f|R for function f and rdq-source R. Let P be a non-empty packing of C. Assume that f is not trivial under two substitutions. Then it is possible to perform substitutions such that complexity measure decrement per substitution is at least δp = min{ (3/2)αI, 3 − 3αφ + αI + αQ }."
"Theorem 4.1. Let C be a circuit computing an affine disperser f for dimension d. For all packing P of C, we have µ(C, P, ∅) ≥ δ(n − 2d − 2), where
   δ ≜ αI + min{ αI/3, 2 − 2αφ + αQ, 4 − 4αφ, 3 + αφ, 5 − αQ, (5 − 2αφ + αQ)/2 }."
Proof structure: "it is possible to perform 1 ≤ t ≤ 3 substitutions with complexity measure decrement ≥ δ per substitution, while the simplified circuit C′ remains to compute f restricting to the updated rdq-source."
Parameters (proof of Thm 1.1): LP "max δ − αφ/2 − αI s.t. δ ≤ αI + min{...}, αφ, αQ, αI ≥ 0, αφ ≤ 1/2. The optimal solution is αφ = 0.2, αI = 9.6, αQ = 1.8 and δ = 12.8, which gives |C| ≥ (δ − αφ/2 − αI) n − o(n) = 3.1n − o(n)."

### Amortization / memory
- µ(C, P, R) depends on the current circuit C, plus two pieces of auxiliary state: the rdq-source R (via q and "protected" in the influential-input count) and the packing P (a chosen maximal-or-not disjoint set of troubled pairs; "For all packing P of C" the bound holds, i.e., P is an adversarially/arbitrarily chosen function of the current circuit, not history). Φ counts currently present troubled gates minus packs.
- Quote on mechanism: "they argue that for each substitution, one may either eliminate k > 3 gates while introducing at most 4k troubled gates, or eliminate exactly 3 gates while destructing one troubled gate without forming any additional troubled gates. With this intuition they perform an amortized analysis to this gate elimination procedure, where the number of troubled gates is considered as the potential of the circuit." (Sec. 3, on FGHK.)
- "Recall that to perform an amortized analysis to the number of gates eliminated, we define the circuit complexity measure as a linear combination of the number of gates and bottlenecks." (Sec. 3.2)
- Per-step drop: up to three substitutions per induction step ("1 ≤ t ≤ 3"), decrement ≥ δ per substitution.

---------------------------------------------------------------------
## 5. Golovnev, Hirsch, Knop, Kulikov. "On the limits of gate elimination"
URL read: https://eccc.weizmann.ac.il/report/2016/119/download (ECCC TR16-119; journal JCSS 2018; MFCS 2016)

### What a "gate elimination argument" is (Sec. 3.1)
"A gate elimination argument uses a certain nonnegative complexity measure µ, a family of substitutions S, a family of functions F, a function gain : N → R, and a certain predicate stop, and includes proofs of the following statements:
 1. (Measure usefulness.) If µ(f) is large, then gates(f) is large.
 2. (Invariance.) For every f ∈ F and ρ ∈ S, either f|ρ ∈ F or stop(f|ρ).
 3. (Induction step.) For every f ∈ F with inputs(f) = n, there is a substitution ρ ∈ S such that µ(f|ρ) ≤ µ(f) − gain(n). (In known proofs, gain(n) is constant.)
The family must contain functions f such that stop(f|ρ1,...,ρs) is not reached for sufficiently many substitutions from S (for example, for s = 0.999 · inputs(f) substitutions)."
Definitions: a substitution ρ of R ⊆ X is a set of restrictions r_i = f_i(...) with f_i depending only on X \ R; "The size of a substitution is |R|. Substitutions of size m are called m-substitutions." µ(f) = min over circuits C computing f of µ(C). Measures used in known proofs: "the measure µ(f) = gates(f) + α · inputs(f)".
"A function µ : B_n → R is called a subadditive complexity measure, if for all functions f and g, µ(h) ≤ µ(f)+µ(g), where h(x̄, ȳ) = f(g(x̄), ..., g(x̄), ȳ)." "Clearly, the measures µ(f) = gates(f) and µ_α(f) = gates(f) + α · inputs(f) are subadditive."

### Limitation theorems
Abstract: "In this note we prove that this method cannot achieve linear bounds of cn beyond a certain constant c, where c depends only on the number of substitutions made at a single step of the induction."
"Lemma 1. For any m > 0, for any function h of n inputs, there exists a function f = h ∘ MAJ_{2m+1} of n(2m+1) variables, such that
 • Circuit complexity of f is close to that of h: gates(h) ≤ gates(f) ≤ gates(h) + 4.5(2m+1)n,
 • For any m-substitution ρ, gates(f) − gates(f|ρ) ≤ 4.5(2m+1)m."
"Definition 1 (weakly m-stable function). A function g(X) is weakly m-stable if, for every Y ⊆ X of size |Y| ≤ m, there exist two assignments τ0, τ1 : X \ Y → {0,1} ... such that g|τ0(Y) ≡ 0 and g|τ1(Y) ≡ 1."
"Theorem 1. Let µ be a subadditive measure, f be a Boolean function, g be a weakly m-stable function, and h = f ∘ g. Then for every m-substitution ρ, µ(h) − µ(h|ρ) ≤ m · µ(g)."
Conclusion drawn: "The results of the previous section prove that no subadditive complexity measure can prove a lower bound of more than nµ(g), where the gadget g depends only on m. For g = MAJ_{2m+1} and measure µ(g) = gates(g) Lemma 1 gives 4.5(2m+1)n as a specific linear bound barrier that gate elimination cannot overcome."
"Definition 2 (m-stable function). A function g(X) is m-stable if, for every Y ⊆ X of size |Y| ≤ m+1 and every y ∈ Y, there exists an assignment τ : X \ Y → {0,1} to the remaining variables such that g|τ(Y) ≡ y or g|τ(Y) ≡ ¬y."
"Theorem 2. Let f be a Boolean function, g be an m-stable function, and h = f ∘ g. Then for every m-substitution ρ, µ_α(h) − µ_α(h|ρ) ≤ m · (gates(g) + α)."
"Corollary 1. For any m > 0, there exists k > 0 and a function g of k inputs, such that for any function h of n inputs, the function f = h ∘ g of nk inputs satisfies: gates(h) ≤ gates(f) ≤ gates(h) + gates(g)·n; for any m-substitution ρ and real α > 0, µ_α(f) − µ_α(f|ρ) ≤ gates(g)·m + αm. Thus, for many functions gate elimination with m-substitutions and µ_α measures can prove only O(n) lower bounds."
"Corollary 2. For any m > 0, there exists a function g of k = O(m) inputs such that ... gates(f) ≤ gates(h) + O(m² n log m); for any m-substitution ρ and real α > 0, µ_α(f) − µ_α(f|ρ) ≤ O(m³ log m) + αm."
"Lemma 4. There exists a 1-stable function g1st : {0,1}^5 → {0,1} of circuit complexity at most 11." "This lemma implies that the basic gate elimination argument is unable to prove a lower bound of 11n using the measure µ_α and 1-substitutions. (Note that almost all known proofs use either 1- or 2-substitutions.)" Corollary 3: for f = h ∘ g1st, "For any 1-substitution ρ and real α > 0, µ_α(f) − µ_α(f|ρ) ≤ 11 + α."
Constants are independent of α ("which may depend on m but not on α").

### Scope of the limitation (verbatim caveats)
- Conclusion: "This puts a barrier on gate elimination proofs that do not use specific properties of the functions while analyzing how their circuits degrade after substitutions. Most proofs indeed do not use functions properties for the analysis (properties of the function are only used for estimating how many substitutions the function can withstand). However, there is one exception: in order to estimate the number of 'bad' local situations on the top of a circuit computing the function, [13] uses the fact that the function is an affine disperser."
- Open questions: "Show that interesting classes of functions contain functions resistant to gate elimination. For example, it would be interesting to show that the class of affine dispersers ... contains a series of functions resistant to gate elimination." "Another possible direction is to extend the result to other possible complexity measures, because some syntactic measures can lack subadditivity (for example, composition can in principle introduce more 'bad' local situations). One can imagine, for example, 'local' measures that count specific small patterns in a circuit. • Extend the result to local complexity measures or other large classes." "Allow induction to descend to arbitrary varieties instead of the varieties described by substitutions (for example, allow restrictions of the form xy = zt)."
- NOTE (my reading): the proven limitation covers subadditive measures (gates, gates+α·inputs) and m-substitutions of ANY type; it does NOT cover measures that count local patterns (troubled gates, packs, quadratic-source counters) because those are not shown subadditive; the paper explicitly lists that as open.
- Other limits listed in Sec. 2/4: "Vadhan and Williams [36] note that the inequality (1) [gates(C)+inputs(C) ≥ 4(n−o(n))] is tight for the inner product function. This implies that the approach from [9] described in Section 2 cannot yield stronger bounds." "Demenkov et al. [8] show that each symmetric function ... can be computed by a circuit of size 4.5n + o(n). This, in turn, implies that no gate elimination argument for a class of functions that contains a symmetric function can lead to a superlinear lower bound." Natural proofs: "If subexponentially strong one-way functions exist, then for any large class P of functions (fraction of elements of P is greater than 1/n), for any effective measure (computable in time 2^{O(n)}) and effective family of substitutions S ... gate elimination cannot prove lower bounds better than O(n)." U2: "The strongest known lower bound for circuits over the basis U2 is 5n − o(n). This bound is proved by Iwama and Morizumi [20] for (n − o(n))-mixed functions. Amano and Tarui [3] construct an (n − o(n))-mixed function whose circuit complexity over U2 is 5n + o(n)."
- Sec. 2 summary table: 2n [Schnorr, Q^n_{2,3}, gates, x_i←c]; 2.5n [Stockmeyer, symmetric, gates, {x_i←f, x_j←f⊕1}]; 3n [Blum, artificial, gates, arbitrary]; 3n [DK11, affine dispersers, gates+inputs, linear]; 3.01n [FGHK, affine dispersers, gates+α·inputs+..., quadratic]; 3.1n [GK, quadratic dispersers, gates+α·inputs, quadratic].
- Amortization statements (Sec. 1): "One can use amortized analysis of the number of eliminated gates. For example, one can show that at each step one can either find a substitution that eliminates 3 gates or a pair of consecutive substitutions, the first one eliminating 2 gates and the next one eliminating 4 gates." "In order to amortize for steps that eliminate too few gates, they also use more intricate complexity measures that combine the number of gates with the number of variables or other quantities." About FGHK: "use a carefully chosen circuit complexity measure which besides the number of gates and inputs also depends on the number of certain local bottleneck configurations and the number of quadratic substitutions."

---------------------------------------------------------------------
## 6. Hrubeš, Jukna, Kulikov, Pudlák. "On convex complexity measures"
URL read: https://eccc.weizmann.ac.il/report/2009/040/download (ECCC TR09-040). NOTE: this concerns formal complexity measures for De Morgan FORMULA size (rectangle measures), not circuit gate-elimination measures.

### Definitions (Sec. 2-3)
"A function m : F → R is called a formal complexity measure of boolean functions if it satisfies the following inequalities: (a) Normalization: the measure of each literal is at most 1; (b) Subadditivity: m(g ∨ h) ≤ m(g) + m(h) and m(g ∧ h) ≤ m(g) + m(h), for every g, h ∈ F." "It follows, by induction, that for every formal complexity measure m, we have that L(f) ≥ m(f)." (L = De Morgan formula size, number of literal occurrences.)
"A rectangle measure is a rectangle function µ : R → R satisfying the following two conditions: (i) Normalization: µ(M) ≤ 1 for every monochromatic rectangle M ∈ M. (ii) Subadditivity: µ(R) ≤ µ(R1) + µ(R2), for every rectangle R ∈ R and for every its partition into disjoint union of rectangles R1, R2 ∈ R."
Fractional partition: rectangles R_1..R_m with weights r_i ∈ [0,1] such that χ_R = Σ r_i χ_{R_i}.
"(iv) Convexity: A rectangle function µ is convex if, for every rectangle R and every fractional partition R = Σ_i r_i R_i, µ(R) ≤ Σ_{i=1}^m r_i · µ(R_i)." (2)
"D*(R) = min Σ_i r_i, such that R has a fractional partition with monochromatic rectangles M_1..M_m and weights r_1..r_m." "Proposition 3.1. D* is the largest convex measure, i.e., D* is convex and for every convex measure µ, µ(R) ≤ D*(R) for all rectangles R."

### Limitation theorems
"Theorem 3.2 ([6]). For every n-dimensional rectangle S, D*(S) ≤ 4n²." "Consequently every convex measure is bounded by 4n²." (KKN; the paper reproves with constant 9/8.)
"Theorem 3.5. If µ is a convex rectangle measure then, for every n-dimensional rectangle S, µ(S) ≤ 1.25(n² + n)." (Proof: parity rectangles P_{I,ε} form a fractional partition of S, each edge in exactly 2^{n−1} of them (Lemma 3.3), weight 2^{−(n−1)}; µ(P_{I,ε}) ≤ (9/8)|I|² (Lemma 3.4).)
Abstract: "We prove the negative result that convex measures are bounded by O(n²) and show that several measures considered for proving lower bounds on the formula size are convex. We also prove quadratic upper bounds on a class of measures that are not necessarily convex."
Intro: "The main message of this paper is that we must use non-convex measures in order to beat Khrapchenko's bound. Non-convexity, however, is only necessary but not sufficient property: we show that the measure based on matrix introduced by Razborov in [13] is not convex but still, as shown by Razborov in [14], cannot even yield super-linear lower bounds."
Corollary 4.3: µ(R) = s(R)·ϕ(w(R)/s(R)), ϕ convex, s additive & positive: "1. If w(R) is additive, then µ is convex. 2. If ϕ is nondecreasing and w(R) is subadditive then µ is subadditive." Polynomial measures of degree k: µ(R) = w(R)^k/|R|^{k−1}; "polynomial measures with convex w(R) can yield at most quadratic lower bounds."
"Theorem 5.2. Let µ be a rectangle measure of the form µ(R) = w(R)^k/|R|^{k−1}, where w(R) is a subadditive rectangle function. Then, for any n-dimensional rectangle S, we have 1. µ(S) ≤ n² if k = 2; 2. µ(S) = O(n) if k > 2."
"Proposition 6.1. For any even integer n there is a (0,1) matrix A such that the measure µ_A [rank-based, Razborov] is not convex." "Still, Razborov in [14] proved that these measures belong to the class of so-called submodular measures, and none of them can yield larger than O(n) lower bound."
Cited as a limitation by paper 5: "Hrubeš et al. [19] prove that convex measures (including the measure used by Khrapchenko) cannot lead to superquadratic bounds."
Relation to circuit gate elimination: none of these results applies directly to circuit-size measures; paper 5 only cites it as an analogue ("Paterson introduces the notion of formal complexity measures for proving De Morgan formula size lower bounds"). The measures here are required to be defined on (sub)functions/rectangles and subadditive, i.e., NOT dependent on the syntactic structure of any one circuit.

---------------------------------------------------------------------
## 7a. Carmosino, Dang, Jackman. "Convergent gate elimination and constructive circuit lower bounds"
URL read: https://arxiv.org/pdf/2602.17942 (arXiv 2602.17942v1, 20 Feb 2026; the PDF text is the full LIPIcs-format paper incl. appendices, ~1350 lines)

NOTE: this paper does NOT define a weighted measure or discuss troubled gates/amortization. It formalizes gate-elimination simplification as term graph rewriting and re-proves Schnorr's DeMorgan XOR bound constructively.
- Main formal results: "Theorem (Informal Statement of Theorem 13). Circuit simplification is convergent in the DeMorgan ({∧, ∨, ¬}) and {∧, ⊕, ¬} bases." "Observation (Informal Statement of Observation 16). U2 and B2 do not admit confluent circuit simplification systems." (Obs. 16: "Gate elimination is not confluent in the U2 or B2 bases, even when restricted to optimal circuits." Reason: superfluous negation gates (∗4, ∗6 of U2) can be pushed up or down, giving non-isomorphic results; passing rules must generate intermediate negation gates.)
- "Theorem 18 (Schnorr, [38]). XOR_n requires 3(n − 1) gates in the DeMorgan basis." "Theorem 19. Let C be a DeMorgan circuit on n inputs with size s < 3(n − 1) that claims to compute XOR_n. We can construct an input x ∈ {0,1}^n such that C(x) ≠ XOR_n(x) in polynomial time with respect to n."
- Measure: size = number of binary gates; "costly" gates = those labelled ∧ or ∨; ¬ gates free. Step: "find a substitution of an input hyperedge which results in at least 3 costly gate hyperedges ... to be removed during rewriting steps"; measure is the current number of costly gates; no memory (Algorithm 2 tracks "a partial restriction α and a list V of the variables still unrestricted").
- Quotes on state of the art / limits: "the best known lower bounds remain linear: about 5n for the DeMorgan and U2 bases [23, 18] and 3.1n for the B2 basis [26]." "Besides decades of limited progress and known limitations (see Related Works), provable barriers to using gate elimination to prove superlinear circuit bounds remain unknown." Research Direction 2: "Does there exist a barrier for the technique against proving circuit lower bounds?"
- Abstract: "Unlike other methods in complexity theory, there is only limited characterization of the obstacles to improving circuit lower bounds proved via gate elimination."
- Convergence statement relevant to "memory": "because every simplification sequence terminates in the same normal form, the structural properties of the simplified circuit are invariant under the choice of rewrites." (i.e., the normal form is a function of the current circuit only, in DeMorgan and {∧,⊕,¬}.)

## 7b. Carmosino, Dang, Jackman. "Constructive Separations from Gate Elimination"
URL read: https://arxiv.org/pdf/2604.23958 (arXiv 2604.23958v1, 27 Apr 2026)
- Theorem 5: "There is an affine refuter for dimension d against B2-size 3n − 4d(n)." Corollary 6: "Fix any explicit affine disperser f ∈ P of dimension o(n). There is a P^NP-constructive separation of f from circuits of size 3n − o(n)." Theorem 3: constructive separation of MUX from DeMorgan-size 2N + log N − 2. Theorem 7: constructive separation of XOR from DeMorgan-size 3(n−1); Theorem 8 (circuits of size exactly 3(n−1) that fail to compute XOR_n).
- Measure used (Sec. 4.2, re-presenting DK11): "Recall from [5] that µ(C) = σ(C) + η(C)", with "The size of a circuit C, denoted σ(C), is the number of binary gates in C. We denote by η(C) the number of input variables in C whose fanout is at least one." "Theorem 16 (from [5]). Let f : {0,1}^n → {0,1} be an affine disperser of dimension d and S be a affine space of dimension d′ > d. If C computes f on S then µ(C) ≥ 4(d′ − d)." Lemma 15: for any C with µ(C) < 4(d′ − d), Algorithm 2 outputs an affine subspace of dimension ≥ d on which C is constant.
- Statement about sophisticated measures: "This demonstrates that even gate elimination arguments which use (1) complex measures other than circuit size and (2) substitutions other than simple constant substitutions are constructive." (Here "complex measure" = µ = σ + η.) Future directions (verbatim): "what about state-of-the-art circuit lower bounds? Do the more sophisticated complexity measures impede refutation by efficient algorithms?"
- Statement about barriers: "Indeed, a certain formalization of gate elimination cannot prove lower bounds better than 5n [7]. However, the barrier does not cover every argument by gate elimination, including those that depend on the optimal structure of circuits computing f or rely on special properties of the hard function f to successful carry out induction." ([7] in its bibliography = Golovnev-Hirsch-Knop-Kulikov, "On the limits of gate elimination", i.e., paper 5.) NOTE: paper 5 as I read it states barriers of 4.5(2m+1)n (subadditive measures) and 11n for µ_α with 1-substitutions via g1st, with larger constants for larger m; I did not find the specific figure "5n" in the text of paper 5; the "5n" in 7b is their paraphrase. (The 5-input function g1st gives 5n inputs; the 11 is its circuit size.)
- Also: "While simplifying, gate elimination arguments track certain complexity measures; basic arguments simply track circuit size, ... More advanced gate elimination arguments, like [5], track additional quantities, such as η(C)." Gate elimination "contradiction ... or (2) shrink a complexity measure of C".

---------------------------------------------------------------------
## 8. U2 / De Morgan 4n-5n results (Zwick 1991, Lachish-Raz 2001, Iwama-Morizumi 2002)
STATUS: full texts NOT found on the permitted hosts. ECCC year listings 2000-2002 have no such report; arXiv search returned nothing; OpenAlex gives only DOI landing pages (doi 10.1145/380752.380832 for LR01, 10.1007/3-540-45687-2_29 for IM02), no OA PDF. DK11 cites an unpublished manuscript on Raz's webpage (not an allowed host). I therefore cannot quote how these papers charge/amortize eliminated gates. Only second-hand statements from the papers I read:

- Zwick measure (FGHK, Intro): "Zwick [Zwi91] counted the number of (internal) gates minus the number of inputs of outdegree 1. The same measure was later used by Lachish and Raz [LR01] and by Iwama and Morizumi [IM02]." (DK11, Sec. 3): "He noticed that any optimal circuit for such a function can contain only a constant number of out-degree 1 variables. This allows to remove such variables from the consideration by using a circuit complexity measure equal to the number of gates minus the number of out-degree 1 variables." So the measure is µ = gates − (#variables of outdegree 1) (current circuit only), in the U2 basis; the "constant number of outdegree-1 variables" follows from the function's property (strongly two-dependent: "for any two variables all the four sub-functions resulting by fixing the values of these variables are different").
- DK11: "Iwama, Lachish, Morizumi, and Raz [10, 8, 7] used Zwick's circuit complexity measure to prove a lower bound 5n − o(n) on C_U2 for strongly two-dependent functions ... [the property] guarantees that a top of a circuit cannot look like [two ⊕-type gates sharing structure]. This case is the main bottleneck in Zwick's proof. An explicit construction of a strongly two-dependent function was previously given by Savicky and Zak [12]. In fact, this function is even k-mixed, for k = n − o(n): for any subset of k variables, all the 2^k sub-functions w.r.t. these k variables are different. Recently, Amano and Tarui [1] showed that this property is not enough for proving stronger than 5n lower bounds on C_U2 by constructing a function of circuit complexity 5n + o(n) that is k-mixed, for k = o(n)." (Paper 5 states the Amano-Tarui function as (n − o(n))-mixed with U2 complexity 5n + o(n).)
- Li-Yang Sec. 1: "Even if the usage of linear gates (⊕, ≡) is banned in the circuit (which are called U2 circuits), significantly better lower bounds are still unknown. For this model, Schnorr [Sch76] first proved a 3n − O(1) lower bound for parity, which was later pushed up to 4n − O(1) by Zwick [Zwi91] on certain symmetric functions. Later, Lachish and Raz [LR01] gave a 4.5n − o(n) lower bound for strongly two-dependent functions, which was soon improved to 5n − o(n) by Iwama and Morizumi [IM02]."
- Whether LR01/IM02 amortize over several restriction steps: NOT stated in any paper I could read. Do not infer.

---------------------------------------------------------------------
## Summary table of measures (from the sources above)
| paper | measure | per-step drop | state beyond current circuit |
| DK11 | µ = s(C) + N(C) | ≥ 4 per affine substitution | none (affine subspace dimension D) |
| GK15 | µ = G + α I (xor-layered), induction on log|S| | ∆_i with 2^{−∆0/β}+2^{−∆1/β} ≤ 1, ∆_i ≥ 2 | quadratic variety S (size, # equations t) |
| FGHK15 | µ = g + αQ q + αT t + αI i | δ = 9 + 3/43 per substitution | rdq-source R (q, protected vars); t, i recomputed from C |
| LY22 | µ = g + αI i + αQ q + αφ Φ(C,P) | δ = 12.8 (per substitution, 1-3 substitutions per step) with αφ=0.2, αI=9.6, αQ=1.8 | rdq-source R and packing P |
| Zwick/LR/IM (second-hand) | gates − (# outdegree-1 variables) | not read | not read |
