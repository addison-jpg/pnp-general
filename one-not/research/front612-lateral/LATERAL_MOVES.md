# Lateral moves for `no_minCE` (front612, 2026-11-24 evening)

Each move: what it is, why it is not on `../../DEAD_ENDS.md` (families A-G), which board item it serves, and the
first test. Labels as in `../../../SYNTHESIS.md`: checked / paper / tested n/N / premise. Nothing here is checked.

## M1. Induction by variable IDENTIFICATION (x_v := x_u), not by constants  [serves C2, C3; new restriction type]

Every dead induction in family E sets ONE input to a CONSTANT. Boolean sums admit a second restriction that
keeps the problem class: identify two inputs u, v of a common set S_w. Then OR(S_w) becomes OR(S_w - v), every
other output stays a Boolean sum, and by (1,1)-disjointness S_w is the ONLY set containing both points, so
base drops by EXACTLY 1. If the identified circuit also loses one gate, s < base is inherited:

- IDENT (lemma candidate): every correct one-NOT circuit (or every MinCE) has u, v in a common set such that
  (adm) the identified system is again (1,1)-disjoint with distinct sets, and (kill) some gate becomes constant,
  an input copy, a duplicate of an earlier gate, or dead on the face x_u = x_v.
  MinCE + IDENT => smaller counterexample, so `no_minCE` reduces to IDENT for MinCE.
- tested (ident.py, corpus = data-corpora + w9 + instances, n <= 14, 27,988 one-NOT circuits): whenever an
  admissible pair exists (9,089 circuits), a killing pair exists: 9,089 / 9,089. The kill is the rule, not the
  exception: the first merge gate of S_w that joins u and v is an obvious candidate.
- The gap is (adm): on 18,899 circuits (K4, fixh16, triple-heavy systems) EVERY identification makes two other sets
  equal or share 2 points. Fix tried: IDENT+ = identify, then delete the outputs of colliding sets D; needs
  (gates freed) >= 1 + sum_{t in D} d_t. Result: see the IDENT+ line below.
- Why it may beat family E: identification moves along the diagonal x_u = x_v, which is NOT a subcube, so the
  TWIN-TREE / MATCH-C mechanisms (junk x_y AND x_a at OR-tree leaves; gain < cost at every point of Q = ∅) are not
  automatically inherited; and the base drop is exactly 1, independent of degrees (constant restrictions drop
  base by deg(v), which is what makes cost large).
- Lean: identification is a substitution on inputs (`Circuit.subst` style); for MinCE one needs (adm) from the
  MinCE facts (no_dup, live, has4) and (kill) from a first-merge-gate argument. Paper first.

## M2. Proof mining from UNSAT cores  [serves C2, C4(t); turns SAT data into lemma candidates]

`kill_tests/c4t_sat.py` already proves s = base - 1 UNSAT on triangle, Pasch, star, tri4, q4, Fano minus 2 lines.
Ask cadical for minimal UNSAT cores (or DRAT proofs) and read off WHICH input points (truth-table rows) the
refutation uses. Prediction worth testing: the rows are exactly the atoms of a few cubes (points z + e_u), i.e. the
refutation IS a count at specific cubes. If the cores are uniform across the ladder (pg13, ag16), that is a
circuit-free certificate shape to prove (the count lives where the step dies: wall C2). Cheap: core extraction on
the existing encoder, 1 CPU-hour.

## M3. U-game modulo equal-size NOT rewiring  [serves C1, the lost certificate game]

`no_minCE_of_ugame` closes every circuit whose lift wins the U-game. R6 shows the NOT gate can often read another
wire without changing the outputs (MATCH-C: gate 41 can read wire 64 instead of h). A MinCE has no gate-SAVING
rewiring, but equal-size rewirings are allowed and change the lift. Lemma candidate: every correct one-NOT circuit
has an equal-size, output-preserving NOT rewiring whose lift wins the U-game. Test on the open list first: the
smallest lost game (sets {0,1,2},{0,3,4}, NOT input x1 OR x3) and cxT2: enumerate every wire the NOT may read
(correctness checked on all 2^n points), rerun the game for each. One win per circuit on the losing suite would make
'lost game' a property of the wiring, not of the function.

## M4. Gate-to-tree packing via matroid union  [serves C1; a relaxation that drops world consistency]

Each set's merge gates form a spanning tree on S_w (Lemma M). Drop the requirement that one zero point produces
the whole tree: let gate g offer to set w every edge it merges at SOME zero point. Then 's >= base' follows from a
packing of one spanning tree per set with distinct gates, and Edmonds' matroid union theorem gives the exact
condition: for every gate set K, |gates - K| >= sum_w (c_w(K) - 1) (c_w = components of S_w under the edges
offered by K). This is a statement about cuts only (front612's cut sandwich bounds the per-zero-point version), and
K = all gates is the trivial case. Test: compute the matroid-union rank (polynomial) on the 75k corpus and the
killers of families C and D (cxMU_dd, STAR4, selector path); if it never fails, the cut form is the new target; if it
fails, the failing K says which world consistency is essential.

## M5. Learned certificate rules  [serves the PureSDR / C1 lanes; method, not a theorem]

Label every gate of the corpus by 'lies in some disjoint choice' (pure classes, real merge sets) and fit a small
decision tree on local features (op, depth, reads h, below/above the NOT, number of sets whose cone contains it,
number of zero points where it merges). A short tree with high accuracy is a rule; feed it to kill_tests, then to
paper. The board found rules by hand and each was killed by one family; a learner trained on the killers too
(cxT2, cxe3, ADV3/4, cxMU_dd) proposes rules that already survive them. `tools/stat_search` has the naive Bayes
plumbing.

## M6. Port the technique to a harder function, not more NOT gates  [serves the ceiling note, wall C3 19:4x]

The ceiling: Boolean sums are in P and base <= O(n^{3/2}), so even C4(all t) is not P != NP. Moving up the NOT
ladder keeps that ceiling. Lateral: keep ONE NOT gate and change the function. The lifted-certificate / union-find
count is a size technique for monotone circuits with one NOT; test it on functions whose monotone complexity is
known and larger than linear (Boolean convolution, Boolean matrix product, Wegener's sums of products), asking
whether a one-NOT analogue of `no_minCE` is even true there (SAT on small instances), and whether the U-game
certificate reproves the known monotone bound. Premise only; it decides whether the 951 machinery is worth lifting.

## Order

M1 first (data in hand, one open condition), then M3 (cheap, targets the exact open list), then M2 and M4 (CPU,
both produce circuit-free statements), M5 as tooling, M6 as a strategy question for coord.
