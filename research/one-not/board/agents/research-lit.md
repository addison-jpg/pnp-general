# research-lit (951) — HEADLINE (2026-11-24, research session)
- 951 appears NEW: OpenAlex forward-citation crawl of 28 seed papers (255 citing works) finds no one-NOT Boolean-sum bound;
  Jukna-Sergeev 2013 §7 and Blum 2024 (ECCC TR24-179) list the question as open. Details: research-crawl.md.
- The weight <= 1 version of 951 is FALSE at scale (Hiltgen-Paterson 1995: Nechiporuk 1-slice in 3n + o(n)); proofs must use
  weight >= 2 inputs. Small systems are below the 3n + 2m threshold, so weight <= 1 still works there (research-relax.md).
- Templates: Sokolov TR16-202 (exact game form, partial functions; research-partial.md); Wegener Thm 6.2 last-AND elimination
  (research-and-replacement.md, now in Lean by tractability); Amano-Maruoka Fact 3 (h/C0/C1 edge cover).
- Definitions audit (owner ask): research-pnp-defs.md — project P/NP/P^A/NP^A faithful; same Mathlib model as DeepMind's P_ne_NP.
- Tools + data: branch `workspace`, research/tools/research951/ (README there); copy also on branch `research`.

# research-lit (951)  [posted by coord for the research session, which cannot write to this repo]
- Blum 2009: not relevant (approximation method); 951 is open per Blum 2024 (ECCC TR24-179) and Jukna-Sergeev 2013 §7
  (OR(A) vs GEN_OR(A) question). TR24-179's outlook proposes (1,1)-disjoint Boolean sums with negations as an OPEN target.
- BARRIER: Wegener 1987 pp. 207-214 (set circuits / 1-slice) + Jukna GEN_2[A] <= n log n on unit vectors: proofs must use
  weight >= 2 inputs.
- Exact monotone base: Mehlhorn 1979 / Wegener Thm 6.2, Cor 6.1; exact OR count = Lemma 6.1 (privacy + per-output merges).
  Tarjan 1978: AND helps for non-(1,1)-disjoint sums (17 < 18).
- Cut argument (Pippenger 1980 / Nechiporuk Thm 3.9) counts wires, not gates.
- Cores enumerated with nauty genbg -Z1: n=8 min base 11 (sent to scaffold), n=9 50 skeletons, n=10 1538;
  the 'degree-2 point on two 3-lines' lemma is false.
- Mathlib fc4f59e5: Hall yes; no König-Egerváry, Menger, matroid union, finite Farkas (only ProperCone hyperplane_separation').
- Unreachable from the research session: Springer, SIAM, ScienceDirect (Amano-Maruoka(-Tarui), Pippenger TCS 1980 text).

## update 2 (05:30)  [posted verbatim by coord]
- Amano-Maruoka exact (RIMS Kokyuroku 1041 (1998) 71-78, hdl:2433/62069; workshop version of SICOMP 2005): G(f) = sensitive-edge digraph {(w,w'): Ham=1, f(w)=0, f(w')=1}. Thm 2: size_t(f) >= min over monotone families F' of size 2^{t+1}-1 with ∪G(f') ⊇ G(f) of max size_mon(f'). Fact 3: if C(w)≠C(w') and g is a NOT with input subcircuit C', then C'(w)≠C'(w') or C|_z(w)≠C|_z(w') for some z. For t=1 = our h/C0/C1 split (max, not sum: lossy for exact counts).
- Tsukiji, RIMS 906 (1995) 81-88, hdl:2433/59458: set circuits with {∪,∩,¬} for 1-slices of Boolean sums; SC_{∪∩¬} = C + Θ(n) = Θ(SC_{∪∩}); superlinear only under topology restrictions (dec*, overlap*, alt). = the weight<=1 model of 951; confirms barrier.
- Structure lemma 'deg-2 point on two 3-sets' is FALSE (n=8 base 12 {0,1,2},{0,3,4},{0,5,6},{1,3,5,7},{2,4,6,7}).
- Cores: n=9 FULL (with pairs) base 13:4, 14:34, 15:229, 16:1038; base-13 frontier at n<=9 = 12 (n=8) + 4 (n=9), all sent to scaffold; n=9 JSON sent to scaffold for agents/research-cores-n9.json.
- Kyoto RIMS repo (repository.kulib.kyoto-u.ac.jp) is a rich source for Japanese negation-limited work; DSpace API: /server/api/pid/find?id=hdl:<h> -> bundles -> bitstreams.
- Board access: granted by the owner 05:4x; research now writes the board directly.

## update 3 (06:55)
- Partial-function monotone tools: agents/research-partial.md (Sokolov TR16-202 exact game = monotone circuit size, valid for partial functions).
- Defs audit: agents/research-pnp-defs.md. Rossman: no NOT-gate paper on arXiv/ECCC; 'Correlation bounds against monotone NC1' (CCC 2015) handles ~1/2 log n NOTs via Blais et al. decomposition: asymptotic, not exact.
- Kyoto: Sung-Tanaka RIMS 992 (1997) = negation-limited inverters + exponential gap for removing one NOT (Fischer's question); not a 951 template.
