# Task: worlds-map (a map of the worlds between, around and inside P versus NP)

- **Source:** coord for Addison, 2026-11-25 (card approved). Addison's framing: "the bounds are always multidimensional, continuous, likely infinite."
- **Label on everything in this task:** a map, not progress on P vs NP.
- **Goal:** a short, sourced note. P versus NP as defined is one binary cut. It sits inside a landscape with many axes, and in that landscape several separations are open. Treat each axis as a dimension; give each world its source and its current status.
- **Axes:**
  - Time exponent: galactic P = NP (polynomial but useless), quasi-polynomial algorithms for NP.
  - Average case: Impagliazzo 1995, the five worlds (Algorithmica, Heuristica, Pessiland, Minicrypt, Cryptomania).
  - Non-uniformity: NP ⊆ P/poly while P ≠ NP (Karp–Lipton and its consequences).
  - Provability: independence from ZFC or PA.
  - Barriers: relativization (Baker–Gill–Solovay), natural proofs (Razborov–Rudich), algebrization (Aaronson–Wigderson).
  - Fine-grained: SETH, ETH.
  - Circuit axes that tie back to this repository: size, depth, fan-out, the number of NOT gates (Markov: about log n NOT gates suffice), monotone vs general (Razborov; Tardos's gap).
- **The proved part of "likely infinite":** the time and space hierarchy theorems give infinitely many distinct levels. State that as proved; everything else about infinite structure is open.
- **Lean:** definitions only. The worlds are Props over abstract complexity classes. No claimed proofs of separations.
- **This repository's results** appear as points on the circuit axes: the one-NOT reduction, f_G at |E| + τ − 1, the L6 depth and size rows. They are never evidence about P vs NP.
- **Read status** on every entry, as in LITERATURE.md.

## Seats
- OPEN (Sonnet) W1: retrieval and the note, with read status. -> notes/worlds-map.md (or philosophy-free location: `worlds/README.md`), plus LITERATURE.md rows.
- OPEN (Fable or Sonnet, after W1) W2: Lean definitions of the worlds as Props over abstract classes (no proofs of separations), and the hierarchy theorem cited or linked if Mathlib or the repository has it. -> lean/PEqualNP/Worlds/Map.lean

- OPEN (Sonnet; Fable only if a Lean statement is worth writing) W3: reduction routes, meaning theorems that carry a result on one axis to the P vs NP cut. Label: "map, not progress on P vs NP". For each route record its statement, its source, the threshold it needs (what bound, on which axis), the barrier it hits, its read status, and how far this repository's results are from that threshold.
  - Hardness magnification: Oliveira–Santhanam 2018; McKay–Murray–Williams 2019; Chen–Jin–Williams.
  - The locality barrier: Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam 2020.
  - Algorithms to lower bounds: Williams 2011 (NEXP ⊄ ACC0); Murray–Williams 2018.
  - Karp–Lipton: NP ⊆ P/poly collapses the polynomial hierarchy.
  - Meta-complexity: Liu–Pass 2020 (one-way functions and time-bounded Kolmogorov complexity), Hirahara's MCSP results, Ilango's MCSP hardness (already in LITERATURE.md).
  - Our distance: the one-NOT Boolean sums and f_G at |E| + τ − 1 are linear lower bounds on functions in P. Say plainly that they are below every known magnification threshold, unless the seat finds a route that applies.
  Read statuses as in LITERATURE.md; anything unopened goes into section J or M. -> worlds/routes.md

## Lines (TAKEN / DECIDED only)
- TAKEN W1
- DECIDED W1 (Sonnet): map note written, every entry carries status and read status; most entries MEM or search result because en.wikipedia.org did not resolve; L6 depth/size rows not found, two other L6 items cited. -> worlds/README.md, LITERATURE.md section N
- TAKEN W3
- DECIDED W3 (Sonnet): routes written for magnification, locality, algorithms-to-lower-bounds, Karp-Lipton, meta-complexity; nearest route is magnification, gap = polynomial factor N^eps plus wrong problem and model; no route applies; LITERATURE.md section G rows and a section J line added. -> worlds/routes.md
