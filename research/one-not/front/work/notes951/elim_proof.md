# Elimination proof (monotone) and one-NOT status
See final report; example script: /tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/elim/ex.py

## Monotone theorem (Lemma M, weak spec)
Monotone circuit (leaves: variables, constant 0), outputs F_i with F_i(z_{S_i})=0 (i.e. F_i<=f_i) and F_i(e_v)=1 for v in S_i. Then #gates >= base.
Induction on #AND. g=h1&h2 last AND (later gates are ORs). Every descendant w satisfies w = g v w' (w' = value with g:=0, or with g:=g').
V={v: g(e_v)=1}, I={i: g<=f_i}. v in V, i in I => v in S_i, so |V|<=1 or |I|<=1.
 (B) |V|<=1: g' = OR of V (0 or a variable) <= g, same unit values; outputs stay <= f_i and keep units. -1 gate.
 (A) |I|<=1: outputs not in I are not descendants of g (a descendant is >= g and <= f_i). For the i0 in I:
     g(z_{S})=0 => h1(z_S)=0 or h2(z_S)=0 => h1<=f_i0 (or h2) by monotonicity (z_S is the top zero point).
     f_i0 = g v u = h1 v u (u<=f_i0, h1<=f_i0, g<=h1). Replace g by 0, new output u v h1 (one OR). Net 0, -1 AND.
OR-only end: L(w)=set of leaves; L(o_i)=S_i. U_i = gates of cone(o_i) with |L|>=2; U_i, U_j disjoint (L(w) in S_i cap S_j);
edge count in cone with {|L|<=1} wires as leaves: 2|U_i| >= |U_i|+|Leaf_i|-1, |Leaf_i|>=|S_i| => |U_i|>=|S_i|-1.

## One NOT
Proved: N last non-OR gate => N dead or const 0 => delete, monotone bound. No AND downstream of N => same.
Repair (iii) valid for output j when a,b,c=a|b stay on one side of {h=0}; always valid when S_j easy (h(z_{S_j})=0), since then a,b,c<=z_{S_j} lie in {h=0} (down-closed).
Fails only for hard S_j (h(z_{S_j})=1) with a in {h=0}, b in {h=1}.
Step (B) fails only for z in {h=1} with e_v in {h=0} (u_j(e_v)=1 but u_j(z)=0).
Counterexample (ex.py): n=5, S1={0,1,2}, S2={3,4}, N=~x3, qp=x0|x1|x2, q=x3|qp, g=N&q, gp=x3&qp, o1=g|gp, o2=x3|x4.
 g: V={0,1,2}, t=1, hard output; repairs N|gp and q|gp wrong at 2 points. gp: V empty, t=2, gp->0 wrong at 14 points.
