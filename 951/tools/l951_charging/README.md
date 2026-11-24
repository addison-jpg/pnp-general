# L-meta-951 charging scaffold (helper tooling, not a proof)

Step: L-meta-951 (one NOT gate saves nothing on Boolean sums of sets meeting pairwise in at most one point).
Setting: set systems S_1..S_m on inputs 0..n-1, |S_i| >= 2, |S_i ∩ S_j| <= 1; circuits of fan-in-2 AND/OR plus at most one NOT;
outputs are OR(S_i). NOT graph edge functions.

Definitions (as checked in inj951.py `analyse`):
- h: the wire the NOT gate reads; minterms of h computed by brute force.
- easy set: no minterm of h is disjoint from S (h(Zof S) = 0). hard set: otherwise.
- T_S: for a hard S, a minimum set hitting every minterm disjoint from S, minus S; T_S = ∅ for easy S.
- zero point Z'_S: 0 on S ∪ T_S, 1 elsewhere (scaffold asserts h(Z'_S) = 0). Test points: unit vectors e_u.
- S-set of wire w: {u in S : w(e_u) = 1}, defined only when w(Z'_S) = 0 (scaffold asserts: then w(e_x) = 0 for all x outside S ∪ T_S).
- merge for S: an OR gate g = a ∨ b, processed in gate order with union-find on S, where g(Z'_S)=0, both a and b have nonempty S-sets,
  and their classes differ (then the classes are joined). Scaffold asserts every S gets >= |S|-1 merges.
- double merge: a gate that is a merge for >= 2 sets. excess = Σ_g (#sets g merges − 1)_+.
- zero-merge gate: a gate (any op, incl. the NOT) that is a merge for no set.
- crossing wire (charging rule): for a double merge g = a ∨ b, among the ancestors of a and of b (incl. themselves), the latest zero-merge gate;
  the rule charges g to it; a "conflict" is two double merges charged to the same gate.
Inequality tested: excess <= #zero-merge gates (951 needs this; data also shows excess <= #zero - 1).
Identity: size = Σ(|S|-1) − excess + #zero-merge gates.
