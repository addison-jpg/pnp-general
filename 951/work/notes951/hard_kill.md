# hard_kill: pay for double charges (paper only, no code run)

## Proved / usable
1. Cone restriction. In Theorem X, S may restrict union-find to gates in the cone of o_S. Invariant and collision argument unchanged (N=1 in C1 is never in A(S); AND step uses an input in A(S), which is again in the cone). So a double-charged OR gate g=a|b lies in cone(S) and cone(S'): a path g -> o_S' and a path g -> o_S exist.
2. h(e_p)=1 means {p} is a minterm, so p is in EVERY hitting set T. Such p are in T_S' for all S'. Double charges with such p,q are the D / C0 situation (use C0 atoms). For h(e_p)=0: true circuit = C1 at e_p.
3. For double charge (g;S,S'): p,q in S distinct, |S cap S'|<=1 so some p in S\S' (likewise p' in S'\S). o_S'(e_p)=0, g1(e_p)=1 (p in B(g)); if h(e_p)=0, every path g -> o_S' has a first gate with value 0 at e_p; it is an AND (OR with a 1-input is 1; N=1 const in C1). So a kill AND exists on each path, for each of S, S' side.
4. Easy family check (hand circuit, T_S=[n]): A=p|p', B=q|q', g=A|B, o_S=g&(p|q), o_S'=g&(p'|q'). g double charged (1 extra), 2 ANDs. Fine.

## Injection attempt and obstruction
Rule: g -> first AND on a path g -> o_S' killing e_p. Fails to be injective in general:
(i) Shared kill. kappa = g & y with y(e_u)=0 for all units u (y = AND of two disjointly supported junk gates). kappa feeds o_i = kappa | R_i for many i. kappa lies in all cones, is 0 at all unit points, so it is the first kill for every (g;S_i,S_j). One AND pays for c-1 extra charges. Hence no injection into AND gates alone can exist for such circuits.
 But in that circuit the gates o_i = kappa | R_i are UNCHARGED OR gates (B(kappa)=empty, no merge), m of them >= m-1 extra charges. So the deficit is paid by uncharged ORs.
(ii) Root-sharing: root=a|b with a=OR(p_1..p_m), b=OR(q_1..q_m), S_i={p_i,q_i}, T=[n]: root charged by all S_i (m-1 extra); trees a,b give 2m-2 uncharged ORs, outputs root&(p_i|q_i) give m ANDs. Paid by either.
So the correct statement is a Hall-type one: extra charges <= #AND + #uncharged ORs (and then s-1 >= #charged OR + #uncharged OR + #AND >= base). Both channels are needed; neither alone suffices.

## Exact obstruction
Need: for each double-charged g with charging sets S_1..S_c, c-1 distinct "payers" across all g, each payer an AND on a kill path or an uncharged OR. Kill gates can be shared only if they lie in several cones, hence are 0 at all but <=1 unit point of cones' intersection; showing such a gate then forces a nearby uncharged OR (as in (i)) is the missing lemma. Not proved; no counterexample found (none can exist by (i),(ii) for the examples). Not tested by computer (live951 never produces double charges; hand constructions above checked by reasoning only).
Alternative cure: pick T_S so the hypothesis holds (Theorem X), which fails in ~9% of n=4 pair-choice cases (c1_cases.md), so payment route or a stronger charging (two zero points for S) is still required there.
