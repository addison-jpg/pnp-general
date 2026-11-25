# research: templates for amortised / global charging (coord assignment 'lit' for no_minCE; target = MergeFrac / hload)

Status legend: READ (text read), CHECKED (computed), FROM MEMORY (standard result, not re-read). Code: workspace
research/tools/research951/charging/ (mzmatroid.py, worlds.py; inputs = the 26 shared instances of research/tools/w951/tests/instances).

## (d) NEW CHECK: are the merge-set families {M_z(w)}_z matroid basis families? (relevant to every LP/integrality route)
- Implemented front's Lemma M definition (union-find over S_w in circuit order at zero point z; OR gate 0 at z merges iff
  both children have nonempty S-sets in different classes). Lemma M REPRODUCED: |M_z(w)| = d_w for every z on all 26 instances.
- Basis exchange (∀ B1,B2 ∈ F_w, x ∈ B1\B2 ∃ y ∈ B2\B1: B1-x+y ∈ F_w): FAILS on 18 of 26 instances (CHECKED). Typical failure:
  two disjoint blocks, e.g. cx44_0 {16,17,18} vs {7,11,15}. So {M_z(w)} is NOT a matroid basis family; Edmonds' matroid-union
  integrality / greedy cannot be invoked directly (this weakens research-nominCE-lit.md item 1, which assumed a matroid).
- Split by world (world0: h(z) = 1, world1: h(z) = 0): exchange holds for 73/82 sets in world0 and 82/84 in world1, but only
  43/84 when both worlds are pooled; world0 and world1 merge sets share gates for 53/84 sets. Within-world failures remain
  (cfgI, cxT2, cxT4 world0; cxr world1; ce3). Reading: the family is NEAR-matroidal inside one world and breaks ACROSS worlds,
  exactly at the N-dependent gates the target names as the missing piece.
- Dual price form sanity: on 300 random prices per instance Σ_w min_z π(M_z(w)) - π(G) < 0 everywhere (consistent with
  front's MergeFrac checks; nothing new).
- Suggested use: a proof of the price form can treat each world as (almost) a matroid (greedy min over z inside a world), and
  must handle only the cross-world choice per set: a 2-choice (world0 block vs world1 block) packing problem with overlaps.
## (b) Charging lower-bound gates to gates that die under a restriction

B1. Weiß's BOTTLENECK argument (J. Weiß, 'An n^{3/2} lower bound on the monotone network complexity of the Boolean
    convolution', Inf. Control 59 (1983); exact text READ in Wegener, CoBF §6.7, Thm 7.1, pp.169-170).
    Setting: semi-disjoint bilinear forms (outputs' prime implicants x_i y_j pairwise distinct; each variable in at most
    one PI of each output). Thm 7.1: C_m(f) >= Σ_i r_i^{1/2}, r_i = #outputs depending essentially on x_i.
    Proof skeleton (verbatim structure): set x_1 := 0 (the subfunction is again a semi-disjoint form with r_2..r_n
    unchanged, so it suffices to ELIMINATE >= r_1^{1/2} gates). Let G* = the set of FIRST OR-gates on paths from x_1 to the
    affected outputs whose function has an implicant x_i y_j with i ≠ 1. (i) Every path from x_1 to such an output meets
    G* (else the output could be replaced by 0 when x_1 = 0, Thm 5.1 replacement rule), and every gate of G* loses an input
    when x_1 = 0, so all of G* is eliminated. (ii) BOTTLENECK SIZE by pigeonhole: pick x_{i(l)} y_{j(l)} ∈ I(g_l) for
    g_l ∈ G*; setting all these to 1 makes every G* gate 1, so each affected output becomes 1 and must have a PI
    x_{i(l)} y_{j(m)}; distinct outputs have distinct PIs, so p^2 >= r_1 - s_1, |G*| = p >= (r_1 - s_1)^{1/2}.
    For no_minCE: the same two-step shape fits 'the 3rd+ merges of a hard 4-set are charged to gates polluted by x_4 that die
    under x_4 := const' (scaffold f15/HARD4.md): define G*_4 = first gates on paths from x_4 to the hard outputs that are
    polluted by x_4; (i) they all die under the restriction (team's R0'/N2 dead-bound machinery already proves 'dies');
    (ii) a Weiß-style pigeonhole on the (1,1)-structure (pairwise |S_a ∩ S_b| <= 1 plays the role of semi-disjointness)
    lower-bounds |G*_4| by the number of merges the class gates cannot supply. Memory: none needed inside one restriction
    step; the charge is a CUT (bottleneck), i.e. a global object, not a per-gate rule.
B2. Gate elimination with amortised dead-gate counting is the standard route for exact small-constant bounds (Schnorr,
    Red'kin, Blum 3n); the De Morgan / U2 basis versions (Zwick SICOMP 1991 4n; Lachish-Raz STOC 2001 4.5n; Iwama-Morizumi
    MFCS 2002 5n) are the closest to 'AND/OR plus negations'. Exact charging statements: see section (a) (Sonnet extraction).
B3. Team-internal instances already proved: R0' (point deletion kills >= deg(v) gates), N2/N3 dead bounds (MinCEFacts,
    MinCEN3). These are the 'elimination' half; Weiß adds the 'bottleneck size by pigeonhole' half.

## (c) LP / fractional lower bounds with don't-care inputs

C1. Karchmer-Kushilevitz-Nisan, 'Fractional covers and communication complexity', SIAM J. Discrete Math. 8 (1995)
    (abstract READ): communication complexity as an integer program, relaxed to an LP; lower bounds by exhibiting dual
    solutions. For formula size (KW relation of f, which is defined only on f^{-1}(1) × f^{-1}(0), i.e. works for partial
    functions): 'one cannot use this method for proving superpolynomial lower bounds for formula size' (LP bound is
    polynomially bounded). Tree-like (formulas), not DAG circuits.
C2. Sokolov, ECCC TR16-202, Thm 3.2 (READ, see research-partial.md): monotone circuit size S <=> dag-like KW game of size S,
    exact for partial functions. The natural LP relaxation of the dag game is not studied there.
C3. Chistikov-Iván-Lubiw-Shallit, STACS 2017 (abstract READ): fractional rectangle coverings lower-bound OR (rectifier)
    circuits; front Fable 'chist' owns this one.
C4. Matroid-union form of the merge packing (research-nominCE-lit.md): its LP is integral; the dual is a 'blocking set' A of
    gates with Σ_w (r_w(G) - r_w(A)) > |G \ A|.

## (a) Weighted gate elimination with a potential / measure (exact statements READ in full text; Sonnet extraction,
##     key quotes re-checked by research; full extract: workspace research/tools/research951/charging/gate_elim_extract.md)
A1. Demenkov-Kulikov, MFCS 2011 (ECCC TR11-026): µ(C) = s(C) + N(C), N = #inputs of out-degree >= 1; µ(C) >= 4(D - d)
    => 3n - o(n) for affine dispersers. Measure = function of the CURRENT circuit only.
A2. Golovnev-Kulikov, ITCS 2016 (ECCC TR15-170): µ = G + α·I on xor-layered circuits; induction on the size of a quadratic
    variety S (not on #variables); Lemma 3: µ(C) >= min{β(log2|S| - log2 s - 1), 2(k - t)}; step condition
    2^{-Δ0/β} + 2^{-Δ1/β} <= 1 with Δ_i >= 2 (a branching/'splitting number' recurrence); α = 0.535, β = 3.6513 -> 3.1163n.
A3. Find-Golovnev-Hirsch-Kulikov, FOCS 2016 (ECCC TR15-166): µ(C, R) = g + α_Q·q + α_T·t + α_I·i (g gates, t TROUBLED gates
    = and-type, fan-out 1, fed by two fan-out-2 inputs; q = quadratic substitutions currently pending in the source R; i inputs);
    α_T = 1/43, α_Q = 65/43, α_I = 6 + 2/43, δ = 9 + 3/43; normalization drops µ by >= β = 1 - 4α_T; Thm: µ(C, ∅) >= δ(n - d - 2)
    => (3 + 1/86)n. State carried between steps: the pending-substitution source R.
A4. Li-Yang, STOC 2022 (ECCC TR21-023): µ(C, P, R) = g + α_I·i + α_Q·q + α_φ·Φ(C, P), where P is a PACKING of troubled pairs
    (disjoint pairs, Def 3.3) and Def 3.5: Φ(C, P) = #truly troubled gates + |P| = #troubled gates - |P|. Normalization drop
    >= 1 - 2α_φ (Rule 1), >= 1 - α_φ (others), vs FGHK's 1 - 4α_T; α_φ = 0.2, α_I = 9.6, α_Q = 1.8, δ = 12.8 -> 3.1n - o(n);
    Thm 4.1: µ(C, P, ∅) >= δ(n - 2d - 2). 'Unpacking' a pack is accounted explicitly (a truly troubled gate created by
    unpacking (G, G') leaves G' untroubled).
A5. Limits (Golovnev-Hirsch-Knop-Kulikov, ECCC TR16-119): for any SUBADDITIVE measure and m-substitutions, functions h∘g whose
    measure drops by <= m·µ(g) per step (e.g. gates drop <= 4.5(2m+1)m for MAJ_{2m+1}); covers gates + α·inputs; measures with
    local patterns (troubled gates) are explicitly OPEN; the barrier is for arguments that ignore properties of the function.
A6. Hrubeš-Jukna-Kulikov-Pudlák, TCS 2010 (ECCC TR09-040): FORMULA size; convex rectangle measures <= 1.25(n^2 + n) (Thm 3.5).
A7. Carmosino-Dang-Jackman (arXiv 2602.17942, 2604.23958): constructive / convergent gate elimination; no weighted measure.
A8. Zwick 1991 (4n, U2), Lachish-Raz 2001 (4.5n), Iwama-Morizumi 2002 (5n): not open access; second-hand (FGHK, DK): measure =
    gates minus #out-degree-1 variables; amortization details NOT verified.

## Verdict (for angle 2 = merge-tree charging, tractability; angle 3 = potential with memory)
- Angle 3: YES, a published template with memory exists: Li-Yang's measure µ(C, P, R) carries a prover-chosen PACKING P of
  troubled pairs across substitution steps, with potential Φ = #troubled - |P| and explicit accounting when a pack is
  'unpacked'; FGHK carries the pending-substitution source R. Transfer to no_minCE: let 'troubled' = an N-dependent gate that
  merges for one set in world 0 and another in world 1 (the target's missing piece); carry a packing P of such double merges
  paired with a zero-merge / dying gate that will repay it; measure = gates - (merges still owed) + α·(#unpaired troubled - |P|).
  The step to verify is the analogue of Li-Yang's normalization drop >= 1 - α_φ per rule.
- Angle 2: Weiß's bottleneck (B1): restriction x_v := const kills a CUT of first polluted gates, cut size by pigeonhole over
  the (1,1) structure; matches 'charge 3rd+ merges of a hard 4-set to gates polluted by x_4 that die under x_4 := const'.
- Limits to respect: A5 (subadditive measures that ignore the function's structure cannot go far; ours uses the (1,1)
  structure, so not blocked) and the weight barrier (research-fable-weight.md: zero tests must be join-closed).
- LP route: no integrality for free (section d): MergeFrac must be proved as an LP / price statement directly.
