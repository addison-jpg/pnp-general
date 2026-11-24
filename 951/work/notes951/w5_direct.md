# w5 direct route: NO PROOF found. Failing steps pinpointed (no Lean run, no code run).

Idea A (o' = C0 v (C1 & G)): per output w, correctness needs G=1 on P1={h=0,f_w=1,g0_w=0} (nonempty iff C0 wrong at w)
and G=0 on P0={h=1,f_w=0,g1_w=1} (nonempty iff C1 wrong at w). G must be a monotone function (a wire, or a monotone
surrogate for not-h). It exists iff no p in P1, q in P0 with p<=q. Since h is monotone with h(p)=0,h(q)=1, p<=q is
exactly the generic situation (e.g. p = z_{T} below the h-flip, q above it), so no monotone G is forced, and a free
existing wire is not available in general. Failing step: nothing forces P1,P0 to be incomparable. Also even when G
exists as a wire, the new circuit needs 1 extra AND and 1 extra OR per repaired output (cost 2 each) versus the
single NOT saved: net gate count goes up, not down.

Idea B (Wegener top-down elimination, elim_proof.md): last AND g=h1&h2 above N. Repair (A) and (B) fail only for
hard outputs j with the two relevant points on opposite sides of {h=0} (a in {h=0}, b in {h=1}, c=a|b). The
C0-wrong / C1-wrong witnesses (x with h=0, y with h=1) are single points; they certify that SOME output is bad
on each side but not that the bad output is the one downstream of g. In elim_proof.md's counterexample (n=5,
S1={0,1,2}, S2={3,4}, N=~x3, g=N&(x3|x0|x1|x2), gp=x3&(x0|x1|x2), o1=g|gp) both repairs of g err at 2 points
and gp->0 errs at 14 points; this circuit is C0-wrong (x with x3=0, x0=1... h(x)=0 gives f=1,g0=0) and C1-wrong?
(C1 here equals o1 = x0|x1|x2|... correct on x3=0, but at x3=1,x0..2=0: g1=1 vs f=0 -> wrong), so it satisfies
hypothesis 4 locally; it is not a counterexample to s>=base only because it is not clean/optimal (it has base+? gates),
i.e. the elimination step genuinely fails and a global (counting) argument is needed -- elimination cannot be done
gate-by-gate for free.

Idea C (3 free gates: NOT, h-gate(s), blocking AND): the gate computing h can be an input wire (h = x_v) or a shared
gate used by outputs, so it is not removable; the blocking AND g is used by hard output o1 above (g|gp), and gp
cannot be dropped. In the circuit above s = 7 gates... (N, qp:2, q, g, gp, o1, o2 = 9 incl. NOT ... base=3) so
slack is large, but removing the 3 gates leaves o1 = gp-only which is WRONG, so "monotone size of the remainder
>= base-1" is not witnessed by the remainder itself; one needs a modified remainder (replace g by an OR of V =
{x0,x1,x2}), which costs the same gates again. So C only works by exhibiting a repair, = Idea B.

Restriction route (set x_v=1 for v in a minimal R0 with h(1_R0)=1, R0 disjoint from a hard S0, so N=0 on the
subcube and C0 is correct there for sets disjoint from R0): gives NOT-free circuit for sets disjoint from R0 (monotone
bound: >= sum_{S cap R0 = empty}(|S|-1)). Missing: need the restriction to kill >= 1 + sum_{S cap R0 != empty}(|S|-1)
gates. Failing step: a set S with |S cap R0|=1 keeps its OR-tree gates alive if they are shared with surviving
outputs; sharing is limited (|S cap S'|<=1) only for gates with >=2 leaves in the OR-only case; with AND/NOT gates a
gate in the cone of o_S and o_S' need not have bounded leaf set. So this reduces to exactly the D-counting
(disjointness of D's), which tests show is false in general (context file) though the sum fits.

Conclusion: the gap remains the same: the hard-hard pair with each T_S containing the other. No free
repair exists in general; any proof must charge across two different test points per set (z_Q with Q via C1 and
e_u via C0) -- the hybrid atoms y_u idea, not a gate-elimination.
