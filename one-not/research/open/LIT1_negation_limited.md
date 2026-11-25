# LIT1: is "k NOTs need Sum(|S_w|-1) gates on (1,1)-disjoint Boolean sums" known, open or false?

Seat LIT1 (Sonnet), 2026-11-25. Target: Boolean sums f_w = OR of S_w with |S_a ∩ S_b| ≤ 1; every
circuit over AND/OR/NOT with at most k NOT gates has at least Σ(|S_w| − 1) gates. No P vs NP
implication is claimed.

## Verdict: OPEN (not known; no counterexample found)

Reasons. (1) No source read or found proves any gate lower bound for Boolean sums with even one NOT
gate beyond the trivial n−comp for a single OR; the project's earlier 255-paper citation crawl
(`research-crawl`, LITERATURE.md §J) found none. (2) Jukna and Sergeev 2013 §7 ask the
AND/OR/NOT question for Boolean sums as a problem (read, TXT, per LITERATURE.md §A); Jukna's errata
page lists Problems 7.4 and 7.7 as solved but gives no statements, so whether the negation problem
is among them is UNCHECKED (the page fetched today names no negation result). (3) Nothing found
contradicts the target for k = 1 or general k: no known example where a NOT saves gates on a
(1,1)-disjoint sum.

Strongest source for "open": Jukna and Sergeev, FnTTCS 9(1) 2013, §7 (asks it). Strongest
source for "not known": absence in the 255-work crawl. Neither is a proof of absence.

## Source by source

| Source | What it proves | Read | Effect on target (k = 1 / general k) |
|---|---|---|---|
| Markov 1958 | ⌈log2(d(f)+1)⌉ NOTs suffice and are needed for a function; says nothing about size | TXT via Jukna Thm 10.5 | none / none; it counts NOTs, not gates |
| Fischer 1975 | log-many NOTs cost only polynomial overhead | TXT via Jukna 10.18 | none; shows few NOTs are not size-free in general, no lower bound |
| Amano-Maruoka (RIMS 1998 = SICOMP 2005) | size_t(f) ≥ min over t-NOT covers of the sensitivity graph by 2^{t+1}−1 monotone functions; function-level, asymptotic | TXT (1998) | leaves open: gives no exact gate count for sums |
| Amano-Maruoka-Tarui, DAM 126 (2003) 3-8 | merging with r NOTs: size Θ(n log n / 2^r), tight | ABS via search snippet | not Boolean sums; shows NOTs can save a factor on non-sum functions, consistent with open |
| Morizumi-Tarui-Iwama 2007; Morizumi (parity, inverters) | parity with few NOTs; accounting loses 1 gate per NOT | TXT (RIMS 1554) | no Boolean-sum statement; leaves open |
| Sung-Tanaka 1997/2002 | NOT removal can cost exponentially; inverter depth | ABS | leaves open |
| Blais-Canonne-Oliveira-Servedio-Tan 1410.8420 | t NOTs ⇒ PARITY of O(2^t) monotone fns; influence bound | TXT | function level; no gate count |
| Jukna-Lingas 2022 (negation width) | size ≥ monotone size / K − 1, multiplicative loss | TXT | gives only a constant-factor-lossy bound, NOT Σ(|S|−1) exactly; leaves open |
| Rossman CCC 2015 | correlation bounds, ~½ log n NOTs vs monotone NC1; asymptotic | CITED | no exact sum bound; open |
| Guo-Malkin-Oliveira-Rosen (negation-limited and pseudorandomness) | pseudorandom functions with few NOTs; not about sums | NOT read (named only) | does not apply |
| Jukna, BFC 2012, ch. 10 (negation-limited) | Markov, Fischer, Tardos-Razborov context | partly read (MEM) | no Boolean-sum k-NOT bound recalled; unverified |
| Wegener 1987 §6.6; Mehlhorn 1979; Pippenger 1980 | monotone case: OR-only optimal, Σ(|S|−1) exact | TXT (Wegener, Pippenger); Mehlhorn CITED | covers k = 0 only; the target is exactly its extension |
| Jukna-Sergeev 2013 §7 | asks if AND/OR/NOT helps for Boolean sums | TXT | OPEN for all k |
| Blum 2024 TR24-179 | ECCC abstract (fetched today) does not mention Boolean sums with negations; the earlier LITERATURE row claim rests on TLDR | ABS | the "lists it as open" claim is UNVERIFIED; downgrade |
| Tardos 1988; Razborov 1985; Alon-Boppana | monotone functions in P (Tardos, matching-type) needing exponential monotone size, so unlimited NOTs save exponentially | search snippets only | exponential separations use many NOTs and non-sum functions; they do not give a 1-NOT saving on a (1,1)-disjoint sum and do not contradict the target |
| Cavalar-Goos-Sofronova-Sokolov 2025 (arXiv 2507.16105) | matching: exponential monotone vs general gap | ABS | same: asymptotic, many NOTs |

## Does a known example show one NOT saves gates on monotone functions?

Yes in general: merging with r NOTs beats monotone by factor 2^r (Amano-Maruoka-Tarui), and
Tardos/Razborov-type gaps are exponential. None is a Boolean sum with |S_a ∩ S_b| ≤ 1; for such
sums the monotone optimum is OR-only and equals the target value. Tarjan 1978's 17 < 18 saving is
for non-(1,1)-disjoint sums with AND, still monotone. So no source gives a counterexample.
Razborov's matching gap does not apply (it needs unbounded NOTs and non-sum functions).

## Caveats and next reads

Not opened: Mehlhorn 1979, Amano-Maruoka full text on sums, Jukna ch. 10 text, Guo et al.,
Rossman full text, Jukna errata items 7.4/7.7 statements (to be sure the negation question was
not solved in 2017). Search is US-only web; publisher full texts were unreachable. Verdict is
"open to the best of this search", enough to forbid "known" but not enough to assert novelty
without those reads.
