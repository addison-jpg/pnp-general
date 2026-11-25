# Mobius tube: the pipeline as a strip

Status: specification. The finite parts are checked in `workshop/mobius/checks/` (see `PROOF_STATUS.md`). The topological parts are stated, not proved.

## Terms

These words are used with one meaning each, every time.

| term | meaning |
|---|---|
| tube | the pipeline, taken as a continuous object |
| strip | the Mobius strip: the tube with a half twist |
| twist | the identification (x, 0) ~ (1 - x, 1) on [0,1] x [0,1] |
| hot dog | only this: a continuous smooth path through the tube with no break |
| coordinator | `baby.ath` at the front, which maps inputs onto the strip |
| bus | one of the spiraling buses in `workshop/bus/` |
| push | one bounded unit of work along a bus |

## Prior work in the repo

There is no earlier Mobius-strip mapping of the pipeline in this repository. This file is the first.

The word appears elsewhere only in other senses:
- `LITERATURE.md` line 267: Harsanyi dividends as a Mobius transform (Mobius inversion on subsets). That is combinatorial inversion, not the strip.
- `lean/PEqualNP/Gct/Helpers/InvisibleBlock.lean`, `lean/PEqualNP/Gct/L098.lean`, `lean/PEqualNP/Outside/L_gct_114.lean`: Moebius inversion statements. Also not the strip.
- `core/ontology/SOURCES.md` line 18 and `frames_sync.ath` line 31: ~ATH's "Mobius Double Reacharound" read as a catch-22. The Boolean catch-22 fact there is checked-finite. The link between ~ATH and the catch-22 is a reading, not checked.

`baby.ath` (the coordinator) does not exist in the repository today. Below it is specified, not cited.

## (a) The tube as a formal object

Let S = [0,1] x [0,1] with the product topology. Let ~ be the smallest equivalence relation with (x, 0) ~ (1 - x, 1) for every x in [0,1]. This is the twist.

The strip is M = S / ~ with the quotient topology. Write q : S -> M for the quotient map. q is continuous by the definition of the quotient topology.

On the two ends (y = 0 and y = 1) the twist acts as the map tau(x, 0) = (1 - x, 1), tau(x, 1) = (1 - x, 0). Then:
- tau(tau(p)) = p for every end point p. tau is an involution.
- tau swaps the ends, so no end point is its own partner.
- tau reverses x. The midline x = 1/2 is the only x with 1 - x = x.

Checked on finite grids: `checks/twist.ath`.

**The continuity claim, stated with care.** "A path that never leaves the tube is continuous" is not true as written: a map [0,1] -> M can stay inside M and still jump. The claim this spec makes is:

> C1. If gamma : [0, L] -> M is a finite concatenation of continuous pieces, and each piece ends where the next begins, then gamma is continuous.

This is the pasting lemma for a finite cover by closed intervals. A hot dog is such a gamma. C1 is a standard theorem of topology. It is not checked in this repository (see `PROOF_STATUS.md`).

## (b) The coordinator and the three buses as maps into the strip

Pipeline order (a design choice made here, not read from running code):

| stop | object | file |
|---|---|---|
| 0 | coordinator | `baby.ath` (not yet in the repo) |
| 1 | bus 1 | `workshop/bus/bus.ath` (layer order) |
| 2 | bus 2 | `workshop/bus/laws.ath` (laws L1, L2 and part of L4 on a slice: 12 true, 0 false; L3 and L4 open) |
| 3 | bus 3 | `workshop/bus/general.ath` (readings only, no claims) |

The maps:

- **Coordinator.** Let I be the finite set of inputs, numbered 0 .. N. The coordinator is c : I -> M, c(j) = q(j / N, 0). Every map from a finite discrete set is continuous. On the check grid N = 5, and c(j) is world j of `checks/twist.ath`.
- **Bus i, for i = 1, 2, 3.** For a start point x in [0,1], bus i is beta_i : [0, 1] -> M, beta_i(s) = q(x, (i - 1 + s) / 3). Each beta_i is q composed with a continuous map into S, so it is continuous.
- **Hand-offs.** beta_1(0) = c(j) when x = j / N. beta_i(1) = beta_(i+1)(0) for i = 1, 2, since both equal q(x, i / 3).
- **One lap.** beta_3(1) = q(x, 1) = q(1 - x, 0). One lap of the pipeline lands on the mirror input. A second lap lands on q(1 - (1 - x), 0) = q(x, 0). This is the involution of (a), checked as T3 and T8 in `checks/twist.ath`.

The bus order 0, 1, 2, 3 has no repeated stop, and each hand-off has one input stop and one output stop. Checked: `checks/pipeline.ath` (O1, O4, O6, O7) and `checks/pipeline_val.ath` (V1 to V4).

## (c) The front-to-main push as one continuous path

Split each bus into m pushes. Push k of bus i is the restriction of beta_i to [k / m, (k + 1) / m], for k = 0 .. m - 1.

- Each push has one input, its start point, and one output, its end point.
- The output of push k is the input of push k + 1, and the output of the last push of bus i is the input of the first push of bus i + 1. There is no gap: the end parameter of push k equals the start parameter of push k + 1.
- The whole front-to-main run is gamma : [0, 3] -> M, gamma(t) = beta_i(t - i + 1) on [i - 1, i]. By C1, gamma is continuous: it is a hot dog.

The no-gap bookkeeping on integer parameters (sum of squared gaps is 0; the pushes cover the full length) is checked in `checks/pipeline.ath` (O6, O7). The step from that bookkeeping to continuity is C1, which is not checked here.

Smoothness: each beta_i is smooth in s. At the hand-offs the velocity is (0, 1/3) on both sides, so gamma is smooth on [0, 3] in the chart of S, including across the twist when one lap is followed by the next. This is reasoning only.

## (d) Mapping table for the named fields

A row is "analogy" unless a file in the repository checks it. No row claims that a field maps to the strip as a fact.

| field | the object it contributes | label |
|---|---|---|
| philosophy | the catch-22: two loops, each ending only when the other ends (`frames_sync.ath` line 31 checks the Boolean fact, not any link to the strip) | analogy |
| ontology | ~ATH's "Mobius Double Reacharound" reading in `core/ontology/SOURCES.md`; the ~ATH link is a reading, not checked | analogy |
| psychology | a one-sided surface as an image of a view that returns mirrored after one pass; no file in the repo | analogy |
| quantum | a spin-1/2 state changes sign after one full turn and returns after two, as one lap of the strip returns mirrored and two laps return; no file in the repo | analogy |
| physics | the strip as a physical band (a single surface, one edge); no file in the repo | analogy |
| all of mathematics: finite combinatorics | the twist as an involution with no fixed end point, which reverses x, on finite grids | checked-finite (`checks/twist.ath`, T1 to T9) |
| all of mathematics: topology | the strip as the quotient S / ~, and C1 (pasting) for the hot dog | open (stated here; no Lean statement and no finite check) |
| all of mathematics: Mobius inversion | Harsanyi dividends (`LITERATURE.md` line 267); a different object that shares the name | analogy (name only) |

## Not claimed

- That any field "is" the strip.
- That the running pipeline has been measured to behave as a hot dog. The checks are about the model in this file.
- That bus order 0, 1, 2, 3 is the order code runs in. It is chosen here.
