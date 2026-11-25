# Task: open-many-not

- **Statement:** Whether two or more NOT gates can save gates on these functions.
- **Seats:**
  - B1 (Opus): the per-set flip lemma in Lean, any number of NOT gates
  - B2 (Sonnet): every circuit for the OR of four inputs needs at least 3 gates, any number of NOT gates, as a Lean theorem by exhaustive check
  - B3 (Sonnet): SAT search for a circuit with two NOT gates and fewer than base gates
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- Single output is settled (B2): OR of n inputs needs n−1 AND/OR gates with any number of NOT gates.
- Open: systems of several overlapping ORs, where NOT gates could let gates be shared.
- S3(a) per-set flip lemma: proved (B1, `Open/FlipLemma.lean`, any number of NOT gates).
- Open: **S3(b)**, flip classes across all sets ≥ base, the cross-set sharing statement in Hall form.
- S3(b) reduced to the thin-basis lemma (B5, `one-not/research/open/B5_flip_hall.md`).
- Seats now: B6 (Opus): prove the thin-basis lemma; B7 (Sonnet): SAT the thin-basis problem on Fano, two 5-sets and the next systems, longer runs.

## Lines (TAKEN / DECIDED only)

- B2 DECIDED: proved in Lean (Open/Or4ManyNot.lean): OR of n inputs needs n-1 AND/OR gates with any number of NOT gates (free); OR4 needs 3. Structural, no enumeration.
- [B1] DONE: S3(a) per-set flip lemma proved in Lean, any number of NOT gates (one-not/lean/PEqualNP/W951/Open/FlipLemma.lean::Concrete.flip_lemma). S3(b) (sharing across sets) stays open.
- B4 TAKEN: OR-system partition bound (gates >= n - components) in Open/OrSystemManyNot.lean
- B5 TAKEN: S3(b) flip-class Hall condition across sets (attack on t4/t5/t6/C4w, then proof or exact missing lemma); one-not/research/open/B5_flip_hall.md, Open/FlipHall.lean
- B4 DECIDED: proved (Open/OrSystemManyNot.lean): any number of NOT gates, gates >= n - comp(union graph); equals base for disjoint sets and chains {i,i+1} (hyperforests); no information beyond base-below for cyclic/overlapping systems. Not a bound for overlapping systems with cycles.
- B3 (2026-11-25): SAT done, 224 systems (n<=6) UNSAT for t=2,3 at base-1; no hit. See one-not/research/open/B3_sat_manynot.md
- B5 DECIDED: S3(b) not broken (Hall holds on every subfamily of all stored circuits n<=22, t4/t5/t6 tight, 0 shared classes). Proved for every circuit, any NOT count: systems of <=2 sets of size <=3 (paper; core checked in Open/FlipHall.lean::no_sole_partner). Exact SAT (function-level, no size bound): Hall holds for ALL circuits on two3, dis3, two43, dis43, dis44, star44, tri3, star3, tri4, q4, Pasch. Exact missing statement: the thin-basis lemma (base(W)-1 AND/OR lines over W-thin functions cannot compute all OR(S_w)), one-not/research/open/B5_flip_hall.md s5; first unsettled: Fano, two 5-sets.
