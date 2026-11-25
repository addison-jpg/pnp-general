# research: literature for the no_minCE global step (owner 07:49: focus on no_minCE, 3rd+ merge gates of |S| >= 4)

Status: literature + framing (no new proof). Read: Schrijver-style statements from memory of standard texts, flagged below;
Lean facts READ in the repo.

1. Exact min-max for 'pack |S_w|-1 merges per set, each gate used once': MATROID UNION / PARTITION theorem
   (Edmonds 1965 'Minimum partition of a matroid into independent subsets'; Nash-Williams 1966; Schrijver, Combinatorial
   Optimization, ch. 42). For matroids M_w on the gate set G with rank functions r_w:
       max { |I_1 ∪ ... ∪ I_m| : I_w independent in M_w, pairwise disjoint } = min_{A ⊆ G} ( |G \ A| + Σ_w r_w(A) ).
   With r_w(G) = |S_w| - 1 (each output's merge structure spans S_w) this gives
       s >= base   <=   for every gate set A:  Σ_w ( r_w(G) - r_w(A) ) <= |G \ A|          (*)
   ('the merges each set loses when only A is kept are paid by gates outside A'). Honest caveats:
   - A = ∅ in (*) is exactly 951, so (*) is a STRENGTHENING; its value is that a minimal counterexample yields a concrete
     BLOCKING SET A* violating (*) (the argmin), an object to analyse instead of the whole circuit. A double merge g
     (merges for 2 sets) violates (*) at A = G - g; zero-merge gates are what must repay: (*) is S-repay / J-repay in
     matroid form (front w9/srepay_opus.md, j_cut_opus.md).
   - The merge structure of a set is a POLYMATROID (a gate's support can have >= 2 points: f(A) = |S_w| - #components of the
     support hypergraph of A), not a matroid. Use the matroid induced by it (Edmonds 1970 'Submodular functions, matroids
     and certain polyhedra'): independent iff |B| <= f(B) for all B ⊆ I; for supports this is the HYPERGRAPHIC matroid
     (Lorea 1975; Frank-Király-Kriesell, Discrete Appl. Math. 131 (2003) 373-383). Per-world supports (z-based, as in
     Kernel/Privacy) give one such matroid per (output, world).
   - The fractional (LP) version is the matroid-union polytope, which is integral (Edmonds): front's ClassFrac / MergeFrac
     LP with 0/1 extreme duals ('K-Rado form', s_fable.md) is consistent with this; a fractional packing of value base
     already implies an integral one if the constraints are of this matroid type.
2. Lean resources (READ):
   - Rado's theorem for LINEAR matroids is already PROVED in the repo: proofs/main/PEqualNP/Gct/Helpers/RadoLinear.lean,
     `rado_aux` (finite sets of vectors with Rado's rank condition `Good` have a linearly independent transversal),
     used by L-gct-171 / ThreeRowRado. Hypergraphic and graphic matroids are linear over GF(2)/Q, so a transversal-type
     step could reuse it.
   - Mathlib fc4f59e5: Matroid basics, ranks, minors, duals, direct Sum (Matroid/Sum.lean); NO matroid union /
     partition theorem, no Nash-Williams, no hypergraphic matroid. tractability's Hall b-matching + LP duality are in Lean.
3. No published exact charging / merge-tree double counting for Boolean sums beyond Wegener Lemma 6.1 (privacy + per-output
   union-find count) and Thm 6.2 (last-AND replacement); both are in Lean (Kernel/Privacy, Kernel/AndReplace). See
   research-crawl.md (255 citers of the Boolean-sum / negation literature, none with a one-NOT bound).
