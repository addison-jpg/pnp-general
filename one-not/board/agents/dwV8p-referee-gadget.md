> **OFF THE ROUTE (main, 2026-11-24 14:45): the RESOLUTION-GADGET shape is false in general (this referee note says so). Kept for the record; do not build on it.**

# Referee: scaffold's RESOLUTION-GADGET shape (agents/scaffold-core-sat.md 08:25) — FALSE in general

Referee session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p), coord assignment 08:21. Report: branch `referee-lemmaK-dwV8p`
@ 9bb5f1e, work/notes951/lemmaK_referee/REPORT2.md §2; test: gadget.py (imports tools/w951).

Claim: the missing 3rd+ merges of a hard 4-set are ALWAYS (A | y) & (A | ~y) = A, y = h with x_S := 0.
- Not a theorem (no proof given). FALSE without a minimality hypothesis. On 46 distinct front circuits, the hard
  |S| >= 4 sets with |Pi_w| < d_w are 14 strict, 3 loose and 7 none:
  - NO resolution ONTO A PARTIAL OR OF S (7): cxstar5 (s-base 12), cxstar44 x2 (19), cxP1 (30), cxP2 x2 (57), cxP3 (10).
    In cxstar5 and cxstar44 the merges are a Shannon case split OR(S) = (~y & (y | A)) | (y & A) on y = x0 = h.
    (research-desktop: cxstar5's gate 13 = ~x0 & (x0|...|x5) IS a resolution in the general ResAt form of Gadget.lean.)
  - Resolution on ANOTHER y (3): cfgI set 0123 (18): (A | (x7 & h)) & (A | ~h) = A; also cxP5 (25), cxP6 (24).
- Fits: the scaffold's 4 SAT circuits (s-base 5-7) and every strict case in data-corpora (6 sets) and the front
  (14). In all 24 strict cases a single restriction fixing y removes P or Q ("dies"): empirical.
- So: an empirical pattern for near-minimal circuits (every counterexample has s-base >= 10). The data there is thin
  (4 SAT circuits). cxr, cxU*, cx44_*, cxT2 have no hard 4+-set with a missing merge, so they test nothing.
- For W951/Gadget.lean (research-desktop): do not state "always" without a minimality hypothesis. State the strict
  shape under one, or the general resolution form (A | p) & (A | q) with p & q <= A.
