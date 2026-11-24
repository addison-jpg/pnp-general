Serves README items L5, C2 (task continuous-mapping)

# Literature on mapping the continuous form back to the discrete corner (main's Sonnet D)

Rows with sources and read status: `LITERATURE.md`, section "Mapping the continuous form to the discrete count". Data below was computed with `core.slack` and `core.witness` on the 15 witness circuits with n <= 9 in `one-not/data/witnesses/` (twin trees excluded, n > 9). Basis: slack(Q) = W(Q) − base(Q); base(Q) = B0 − cov(Q) with cov a weighted coverage function (monotone submodular), so slack = W + cov − B0.

## The 5 most promising ideas

### 1. Monotone level means (variation diminishing in Bernstein form)
Idea. Φ(p) = Σ_i C(n,i) p^i (1−p)^(n−i) m_i with m_i the mean of slack over level i. Then Φ'(p) = n Σ_i (m_{i+1} − m_i) B_{i,n−1}(p). If m_0 >= m_1 >= ... >= m_n = 0 then Φ' <= 0 and Φ(0) >= Φ(1) = 0, with no one-point step. It is weaker than the one-point step (an average over a level) and need not need a pointwise path.
Property. slack's level means are nonincreasing: m_i >= m_{i+1} for every i (equivalently, Σ_{|Q|=i} slack(Q)/C(n,i) decreasing). DATA: true on all 15 circuits tested; level means all >= 0.
Test. `m=[mean(core.slack(c,Q) for Q with popcount i)]` and `all(m[i]>=m[i+1])`; run on the twin trees, the hunt output `one-not/data/`, and random minimal circuits; look for the first counterexample, then ask whether m_i − m_{i+1} = (n/ (n−i)) E[−step] has a double-counting proof (Σ over pairs Q ⊂ Q+v).
Source. Bernstein basis variation diminishing (MEM); Rossignol arXiv math/0511607 Lemma 2.2 (TXT) for the derivative; Harris arXiv 2309.10675 (TXT) for the weaker coefficient certificate.

### 2. Convexity of Φ with a tangent at p = 1 (slack cross-supermodular in expectation)
Idea. Φ'(1) = −Σ_v slack(N−v). If Φ is convex on [0,1] then Φ(0) >= Φ(1) − Φ'(1) = Σ_v slack(N−v) >= 0. Dughmi's survey: for submodular f, F is concave along nonnegative directions via ∂²F/∂x_i∂x_j = E[second difference]; the mirror image gives up-convexity for supermodular slack.
Property. E_{μ_p}[slack(Q+u+v) − slack(Q+u) − slack(Q+v) + slack(Q)] >= 0 for all u ≠ v and all p (F up-convex), or at least Φ'' >= 0. DATA: slack is supermodular on 2 of 12 circuits tested, neither sub- nor supermodular on 9, modular on 1; Φ is not convex on a 20-point grid on 5 of 12. So the plain version is FALSE; the open question is the weakest form that survives: Φ above its tangent at 1 only (that is the statement Φ(0) >= Σ slack(N−v), true on the data trivially since slack(N−v) = 0 everywhere).
Test. second differences over all Q, u, v (classify the set function as sub/super/neither; 15 lines of Python over `core.slack`); then `Φ''(p) >= 0` on a fine grid; then find which pairs (u,v) violate and whether they are the NOT-gate inputs.
Source. Dughmi arXiv 0912.0322 §3 (TXT); Murota (search result, NOT read) for the discrete-convex analogue.

### 3. Acyclic matching (discrete Morse) as a replacement for the monotone path
Idea. The one-point step is false at some Q, but the claim only needs the corner. Choose an acyclic matching M on the Boolean lattice (Forman/Chari); on matched pairs (Q, Q+v) require slack(Q+v) <= slack(Q); unmatched critical cells must have slack >= 0 by a cheaper argument (e.g. they have no witness, or base zero). Then follow the gradient paths from ∅ to a critical cell.
Property. There is an acyclic matching of 2^[n] (with ∅ matched upward or critical) such that every matched pair has slack(Q+v) <= slack(Q) and every critical cell has slack >= 0 and is reached.
Test. ILP/SAT over matched pairs; acyclicity by ordering variables. Start n <= 7 on each circuit: variables x_{Q,v} ∈ {0,1}, each Q in at most one pair, forbidden pairs where the step is positive. Feasibility only needs "each Q is either matched along a non-increasing edge or critical", plus acyclicity (a topological order variable). Alternatively check the simpler necessary condition: the directed graph of non-increasing steps has a path from ∅ to a vertex with slack = 0 (not just a local minimum).
Source. Forman Adv. Math. 134 (1998) and Chari 2000 (search result, NOT read); symmetric chain decompositions (de Bruijn et al.; Tomon arXiv 1509.07346, search result NOT read) for the averaged version.

### 4. Lovász extension / DC certificate g_L >= h_L
Idea. For normalized F the min of F over subsets equals the min of its Lovász extension over [0,1]^d (El Halabi et al. Prop. 2.3, TXT; no submodularity needed). Write slack = W − base' (DS decomposition; any set function has one, arXiv 2506.07952, search result). slack >= 0 iff g_L(x) >= h_L(x) for all x, a comparison of two convex functions. A sufficient certificate: a modular function m with g_L >= m >= h_L (separation), i.e. a point of the (sub)gradient set; equivalently a vector y with y(Q) <= W-part(Q) for all Q and y(Q) >= base-part(Q) (an LP over 2^n constraints, or the subdifferential at ∅).
Property. There is a modular m(Q) = Σ_{v ∈ Q} y_v + c with H(Q) <= m(Q) <= G(Q) for all Q where G, H are submodular with slack = G − H (a sandwich/Frank-type theorem: exists for submodular G and supermodular H' iff G − H' >= 0, Frank discrete sandwich, MEM).
Test. LP in numpy/scipy per circuit with G = W (check submodular first: classify W; DATA: W neither on 9 of 12, supermodular on 3, so choose G, H by LP to be submodular via Iyer-Bilmes style decomposition) or directly the LP: find modular m with H <= m <= G.
Source. El Halabi, Orfanides, Hoheisel ICML 2023 (TXT, §2); Iyer-Bilmes arXiv 1207.0560 (ABS); Frank's discrete sandwich theorem (MEM, not searched).

### 5. Möbius/dividend picture: signs of m(T) by size, and a Hart-Mas-Colell potential
Idea. slack(Q) = Σ_{T ⊆ Q} m(T) (Harsanyi dividends); Φ(p) = Σ_T m(T) p^{|T|}; Φ(0) = m(∅); Φ(1) = 0 forces Σ_{T ≠ ∅} m(T) = −m(∅). The potential P(S) = Σ_{T ⊆ S} m(T)/|T| (Hart-Mas-Colell) has marginals summing to slack(N) − ... the chain-sum identity under uniform random orders. The question becomes: which dividend patterns (e.g. m(T) <= 0 for all |T| >= 1, so slack(∅) = −Σ m(T) >= 0) hold?
Property. m(T) <= 0 for every nonempty T, or at least Σ_{|T| = k} m(T) <= 0 for each k >= 1 ("negative dividends": slack is a decreasing, totally "anti-monotone" game, every T only subtracts).
Test. Möbius inversion m(T) = Σ_{Q ⊆ T} (−1)^{|T∖Q|} slack(Q); print Σ_{|T|=k} m(T) for each k and the minimum single m(T); compare with the dual sign pattern in the variables 1−x_v.
Source. Hart and Mas-Colell Econometrica 57 (1989) (search result, NOT read); Harsanyi dividends (search result, NOT read).

## Searched, nothing useful
- "Russo-Margulis lemma sharp threshold non-monotone signed function" -> only the monotone-event versions (Friedgut-Kalai, Talagrand); the signed form is just Rossignol Lemma 2.2, a derivative identity.
- "difference of submodular multilinear extension nonnegativity certificate" -> algorithms only (Iyer-Bilmes, Narasimhan-Bilmes, El Halabi et al.), no sufficient conditions for min >= 0.
- "M-natural convex multilinear extension relation" -> only Lovász extension / L-natural and correlation-gap results (arXiv 2209.09896).
- "Bernstein coefficients level averages unimodal Boolean set function" -> not searched in that wording; only generic Bernstein positivity (Harris, arXiv 2309.10675; 1710.05735).
- "gate elimination real-valued measure potential" -> Golovnev et al. limits paper only (abstract level).
- Laplante-Lee-Szegedy formula-size adversary: not searched. Wikipedia pages (Russo-Margulis, Bernstein polynomial) and the Hart homepage were unreachable (host blocked).
- No source found that proves an inequality for a difference of two decreasing set functions from the behaviour of a continuous extension at interior points.
