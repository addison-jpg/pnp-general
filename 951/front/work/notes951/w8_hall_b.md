# w8_hall_b: Hall's condition, route B (non-union-find) log

## B1 (PROVED) privacy of pure gates. For Good unit systems, a gate g in cnt(w)∩cnt(w') has B_w(g) ⊆ S_w∩Q_w', B_w'(g) ⊆ S_w'∩Q_w
(comparability: e_u <= z_Q' if u ∉ Q', and N(e_u) <= N(z_Q') in every Good case). Hence g with unit-support inside S_w ("pure",
e.g. any g <= OR(S_w), in particular o_w) is counted by w only. Graph case (|S|=2) of Hall is trivial. (Same as R1 of w8_hall.md.)

## B2 (independently found; same mechanism as R2/R3 in w8_hall.md) canonical Hall is FALSE in general
n=9, S_w={0,1,2,3}, S_w'={4,5,6,7}, h=r=OR(x0..x7) built as ((x0|x4)|(x1|x5)) | ((x2|x6)|(x3|x7)), N=¬r,
s=N|x0|x1|x2|x3, s'=N|x4|..|x7, o_w=r&s, o_w'=r&s'. Q=Q'={0..7}; cnt(w)={t1,t2,r,o_w}, cnt(w')={t1,t2,r,o_w'}; union 5<6.
(Here C0 is correct; the other agent's R2/R3 give essential clean versions.) So Hall+canonical needs s<base, where it is vacuous.
Top-down view that produced it: a gate splitting claims for two sets needs a kill AND per set; the kill AND (o_w = r∧s) can serve
many double splits because s contains N and is 1 at the zero point, so the whole s-chain is uncounted.

## B3 (PROVED) uniform one-parameter menu Sigma(z)
For ANY z vanishing on S_w: sigma = (z; atoms p_u = z+e_u; K = all gates) is a Lean TestSys (hT: p_u∩Zero(z)={u}; Good: if h(z)=0
then N(z)=1; if h(z)=1 all atoms are >= z so N=0 on every atom, "<=1 atom with N=1" holds). cnt_z(w) = {g : g(z)=0, g(z+e_u)=1 for
>=2 u in S_w} = gates sensitive at z to >=2 variables of S_w. No reference to h, cones or hardness. z=0 gives the unit system Q=[n].

## B4 (PROVED) common-minterm separation
Hard sets a,b avoiding one common minterm M of h: systems (z_{S}; atoms e_u+1_M) have disjoint counted sets (any K).
Proof: all test points lie in U={h=1}, where the circuit is the monotone C0. g in both: g(1_M+e_u)=1 for two u in S_a, g(z_b)=0;
1_M+e_u <= z_b unless u in S_b; so two points in S_a∩S_b. Contradiction.

## B5 (DATA) rule R*: z_w = z_{S_w} for EVERY set (easy or hard), atoms z+e_u, K=all  (w8b/rstar.py)
Hall holds on cx1, cx2, cx3 (counted sets even disjoint) and on all 2437 circuits having a set of size 3
(chk/c.jsonl, w7/badT, w6B/tri_ess, w6C/cross5, cross5f): 0 Hall failures, 0 short sets, disjoint in 2360.

## B6 (COUNTEREXAMPLE, verified w8b/cxr.py, w8b/cxr.json) R* is FALSE with junk ("inner-product" design)
n=8, S_a={0,1,2,3}, S_b={4,5,6,7}, t = h = OR_i (x_i & x_{i+4}), N=¬t, k_a = OR_{u in S_a}(N & x_u), o_a = t | k_a (same for b). s=24.
Correct, clean. R*: cnt(a)={3 OR gates of t, o_a}, cnt(b)={same 3, o_b}: union 5 < 6. Reason: at z_a every x_v (v in S_b) is 1, so t is
sensitive to each u in S_a, while N&x_u is NOT sensitive (flipping x_u turns N off). Fixed by z=0 (unit atoms): k-chains counted, private.
183 of the 256 Sigma(z) pairs give a full matching. NOTE: here C1 is correct (removable NOT, no DD set); adding the independent
DD gadget of cx1 (set c on fresh variables) gives a DD set without touching a,b, so "a DD set exists" does not rescue R*.
So: canonical (Q transversal, units) dies on AND-cuts o=r&k with k(z)=1 [k ⊇ N]; R* (z in U) dies on OR-cuts o=t|k with k = N&(...)
insensitive at z. Each fixed (h-only or set-only) rule has a junk counterexample; a rule must read the gates.

## B7 top-down accounting (PROVED as stated; explains both cuts)
Fix systems. For w keep "claims" (wire i, A ⊆ B_w(i)), A's partition S_w, start (o_w,S_w); descend: OR zero at z -> split A along
B(a),B(b); AND zero at z -> move to an input that is zero at z. Splits happen only at counted OR gates, exactly |S_w|-1 per set.
Hence sum_w d_w = sum over counted ORs of mult(t), and Hall deficiency <= sum_t (mult(t)-1)^+ - #(counted gates that split for nobody).
A multiply-splitting gate is impure for each of its sets, so each such set has an AND on its claim chain (counted, never splits).
One such AND can serve arbitrarily many multiple splits (B2: 3 double splits, 2 ANDs) — the missing gates are in the AND's other
input k, which is 1 at z and therefore invisible to that system.

## STATUS (route B)
No choice rule proved. Exact open statement: for every correct one-NOT circuit there are z_w (vanishing on S_w) such that the sets
cnt_{z_w}(w) of B3 satisfy Hall. Unrefuted on cx1-3, cxr and all data; no proof; a single universal junk circuit defeating all z is
neither found nor excluded. DD hypothesis: used nowhere, helps nowhere so far.
