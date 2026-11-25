# Protein complexes: molecules join into machines, counted

What this is: the counting behind ring-shaped protein complexes and cell-surface identity codes, with every number checked by `check.py` (run: `python3 -I brain/complexes/check.py`). What this is not: a model of the mind, a clinical claim, or a statement about any person. **A combinatorial ceiling is not a count of what exists.** It is how many arrangements the parts allow; cells build far fewer. Labels: **fact** (literature, cited), **checked-finite** (exact, exhaustive over a stated finite set, rerunnable), **tested**, **join**, **analogy**, **open**.

## 1. Rings in a membrane are necklaces

A *subunit* is one protein chain. Many ion channels are rings of n subunits around a pore. A *necklace* is a ring of n beads in k colours, counted up to rotation. A *bracelet* is counted up to rotation and mirror flip. A membrane has an inside and an outside, so a flipped ring is a different complex: channels are necklaces, not bracelets.

Burnside's lemma: necklaces = (1/n) Σ_{i=0}^{n-1} k^gcd(i,n); for prime n this is (k^n + (n−1)k)/n.

| k | n=4 necklace / bracelet | n=5 | n=6 |
|---|---|---|---|
| 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| 2 | 6 / 6 | 8 / 8 | 14 / 13 |
| 3 | 24 / 21 | 51 / 39 | 130 / 92 |
| 4 | 70 / 55 | 208 / 136 | 700 / 430 |
| 5 | 165 / 120 | 629 / 377 | 2635 / 1505 |
| 6 | 336 / 231 | 1560 / 888 | 7826 / 4291 |
| 7 | 616 / 406 | 3367 / 1855 | 19684 / 10528 |

**Checked-finite**: every word of length n in {4,5,6} over k ≤ 7 colours was enumerated (218,504 words in all) and the classes counted; they match Burnside and the bracelet formula. The difference (necklaces minus bracelets) is the number of bracelets that split into two mirror-image necklaces.

## 2. Biological anchors (ceilings, then what exists)

| Complex | Ring size | Gene pool | Ceiling (necklaces) | What exists |
|---|---|---|---|---|
| GABA-A receptor | 5 | 19 subunits | 495,235 (bracelets 251,047) | Olsen & Sieghart 2008 list 26 native subtypes (identified, probable, tentative); "a few dozen" with reasonable certainty |
| Ionotropic glutamate receptor | 4 | 18 subunits (from memory) | 26,334 | far fewer; assembly is within families (AMPA, kainate, NMDA) |
| Connexon (half a gap junction) | 6 | 21 human connexins | 14,296,051 | far fewer |

- GABA-A: 19 subunit genes (α1–6, β1–3, γ1–3, δ, ε, θ, π, ρ1–3), mostly 2α:2β:1γ. **Fact.** The ceiling 495,235 = (19^5 + 4·19)/5 is **checked-finite** (formula; it matches the orchestrator's expectation).
- Potassium channels (Kv) are tetramers like glutamate receptors: same n = 4 necklace count. **Fact** (from memory).
- Gap junctions: two connexons, one from each cell, dock across the gap. This is cells joining. With homomeric connexons (all six alike): 21 homotypic + C(21,2) = 210 heterotypic = 231 pairings. With any hexamers: 14,296,051·14,296,052/2 = 102,188,544,245,326 unordered pairs. **Checked-finite** (arithmetic); the connexin count of 21 is **fact** but annotation-dependent (20 to 22 in different studies).

## 3. Dscam1: identity by sampling

Drosophila *Dscam1* has 12 × 48 × 33 × 2 = 38,016 splice isoforms (exons 4, 6, 9, 17; Schmucker et al. 2000). Exon 17 is the membrane anchor, so 12 × 48 × 33 = 19,008 distinct outer parts (ectodomains). **Fact; product checked.** A neuron's branches repel when they share an isoform (self-avoidance). If two neurons each show m isoforms chosen at random from N, the chance they share none is C(N−m, m)/C(N, m), checked against the product form as exact fractions.

| N | m=10 | m=20 | m=50 |
|---|---|---|---|
| 19,008 | 0.994750 | 0.979155 | 0.876457 |
| 38,016 | 0.997372 | 0.989528 | 0.936274 |

With small N it fails: N = 48, m = 4 gives 0.697662, so about 30% of neighbour pairs would wrongly look like self. **Checked-finite** (exact fractions, printed to 6 places). This matches in direction Hattori et al. 2009, who found thousands of isoforms are needed; the m values used here are illustrative, not theirs (open item 1).

## 4. Clustered protocadherins

Mouse: 14 α + 22 β + 22 γ variable exons = 58 (Wu et al. 2001). **Fact** (counts per cluster confirmed by search; sum checked). Each neuron picks a few, giving a combinatorial surface code like Dscam1. **Analogy** to section 3: same sampling calculation, different N and m.

## Joins

- **Join**: necklaces here are orbits of the cyclic group acting on words, the same Burnside counting as any rotation-class count in the repo; the matcher should compare `fingerprints.json` (OEIS A000031-family columns, from memory) with other levels.
- **Analogy**: Dscam1/protocadherin identity as random codes with few collisions (birthday problem).

## Limits and open items

1. Confirm the isoforms-per-neuron figures in Hattori et al. 2009 and use them in place of m = 10, 20, 50.
2. Glutamate subunit count 18 and Kv tetramers are from memory; cite a primary source.
3. Assembly rules (which neighbours are allowed) would cut the ceilings; not modelled.

## Sources

- Olsen & Sieghart, "GABA A receptors: subtypes provide diversity of function and pharmacology", Pharmacol Rev 60:243 (2008) — abstract only (search result).
- Schmucker et al., "Drosophila Dscam is an axon guidance receptor exhibiting extraordinary molecular diversity", Cell 101:671–684 (2000) — search result only.
- Hattori et al., "Robust discrimination between self and non-self neurites requires thousands of Dscam1 isoforms", Nature 461:644–648 (2009) — abstract only.
- Wu et al., "Comparative DNA sequence analysis of mouse and human protocadherin gene clusters", Genome Res 11:389 (2001) — search result only.
- Human connexin count 21 (with 20–22 by annotation) — search result only (review summaries).
