# research: citation crawl (OpenAlex forward citations), 951 literature closure

Status: computed (OpenAlex API, 2026-11-24 ~07:00), abstracts/TLDRs READ for the hits below; full table:
agents/research-crawl-citers.tsv (255 works, columns: score, year, id, title, authors, doi, which seeds they cite, keywords).
Seeds (28): Nechiporuk/Mehlhorn79/Pippenger80/Wegener80/82/Tarjan78/Weiss83 (Boolean sums, monotone), Amano-Maruoka 98/05,
Amano-Maruoka-Tarui 02, Sung-Tanaka 02, Tanaka-Nishino 94, Beals-Nishino-Tanaka 98, Fischer 75, Morizumi 09, Morizumi-Suzuki 10,
Iwama-Morizumi-Tarui 06/07, Guo-Malkin-Oliveira 15, Blais et al. 14/15, Jukna-Lingas 19/22 (negation-limited),
Wegener 85/86 (slices), Jukna-Sergeev 13, Grinchuk-Sergeev 17, Blum 09, Tsukiji 96.

Result: NO paper in the forward-citation closure states or proves a one-NOT (or few-NOT) lower bound for Boolean sums.
=> 951 looks genuinely new (consistent with Blum TR24-179 and Jukna-Sergeev §7 calling it open).

New items worth knowing:
- Hiltgen & Paterson, 'PI_k mass production and an optimal circuit for the Nečiporuk slice', Computational Complexity 5
  (1995) 132-154 (TLDR read, full text not reachable): in PI_k-SET circuits (Wegener's union/intersection model) savings are
  possible for ANY family F of m output sets over n inputs whenever SC_m(F) >= 3n + 2m; optimal circuit for the Nečiporuk 1-slice.
  => answers Wegener's p.214 question NEGATIVELY: set circuits (= correctness on weight <= 1 inputs) beat Σ(|H|-1) as soon as
  the OR-cost exceeds ~3n+2m. This QUANTIFIES the barrier: the weight<=1 relaxation can only be exact while base < ~3n+2m.
  Our cores are far below (c11: 11 vs 34; base-15 frontier n=8: ~15 vs >= 36), matching research-relax.md (no small hits).
- Tsukiji, 'On a small class of Boolean sums', TCS 163 (1996) 283-289 (TLDR read): almost all members of a natural class of
  n-input n-output Boolean sums of cardinality 2n have monotone complexity n^2 / 2^{O((log log n)^2)}. Monotone only.
- Korshunov, 'Monotone Boolean functions', Russian Math. Surveys 58:5 (2003): 50-year survey, cites Mehlhorn/Pippenger/
  Wegener/Amano-Maruoka; candidate place for any Russian one-negation result (not read: no open full text reached).
- Kochergin & Mikhailovich (Math Notes 2019, 2025; MVK 2024): EXACT non-monotone complexity, but in the basis where all
  monotone functions are free and only NOT/non-monotone gates cost: counts negations, not gates. Not 951's measure.
- Chistikov, Iván, Lubiw, Shallit, 'Fractional coverings, greedy coverings, and rectifier networks', STACS 2017: fractional
  rectangle coverings lower-bound depth-2 OR circuits (LP duality); possible template for front's FracMatch / ClassFrac LP.
- Blum 2009 (S2 TLDR): 'describes the state of the art and gives arguments why techniques for monotone lower bounds cannot
  easily be extended to networks with negations' (survey/position paper; zbMATH keywords: monotone/nonmonotone network).
