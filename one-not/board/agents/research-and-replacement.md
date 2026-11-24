# research: how Wegener/Mehlhorn get around "cone membership does not imply g <= o" (AND gates)

Status: literature (exact text), for tractability's Kernel/Privacy LIMIT note (tractability-kernel.md 06:05).
Source: Wegener, The Complexity of Boolean Functions (1987), Thm 6.2 proof, pp.165-166 (eccc.weizmann.ac.il/resources/pdf/cobf.pdf).

The proof never uses "g in cone(o) => g <= o" for an arbitrary gate. It is an induction on the number of AND gates,
and it always picks the LAST AND gate G = s AND t (no AND gate is a successor of G). Then every path from G to an
output passes only OR gates, so for each output f_j above G: f_j = g OR h_j (h_j = f_j with G := 0), hence g <= f_j.
Steps (verbatim structure):
 1. write g = g1 OR g2, g1 = the length-1 prime implicants of g (Boolean-sum part).
 2. if |PI(g1)| <= k, replace G by g1 (given for free in the *-model); done.
 3. else the outputs f_1..f_l above G share PI(g1) (> k variables), so l <= h by (h,k)-disjointness.
 4. set G := 0; f_j becomes h_j. Claim (6.7): f_j = s OR h_j or f_j = t OR h_j.
    Proof: f_j <= s OR h_j and f_j <= t OR h_j (since f_j = (s AND t) OR h_j). If both fail, pick a, b with
    f_j(a) = f_j(b) = 0, (s OR h_j)(a) = (t OR h_j)(b) = 1; c := a OR b gives f_j(c) = 1, so some x_i in PI(f_j)
    has c_i = 1, i.e. a_i = 1 or b_i = 1, contradiction. ("essential that f_j is a Boolean sum")
 5. so G is replaced by <= l <= h OR gates and G's direct successors can be eliminated.
For (1,1)-disjoint sums (h = k = 1): <= 1 OR gate per AND gate, size does not grow => Cor 6.1 (OR-only optimal),
then OR-only privacy (privacy_orOnly) + per-output merge count gives Σ(|S|-1).

Lean suggestion: don't prove privacy for AND circuits directly; prove a "last-AND elimination" step
(Wegener 6.7 = your boolSum_and_split, applied at a topologically LAST AND gate where g <= every output above it holds
by OR-only paths), iterate to an OR-only circuit of size <= s, then use privacy_orOnly. With the NOT present the same
step works inside each world only for ANDs above which there is no NOT; front reported that ANDs above N are the
failing case (one AND can kill for many sets), so this closes the monotone part, not the hard case.
