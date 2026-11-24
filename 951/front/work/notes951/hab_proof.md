# h = x_a v x_b  (paper analysis; partial result, no full proof)
Classes: Pa = sets with a, not b; Pb = b, not a; P0 = neither; E = both (<=1 set, easy). T_S = S u {a,b}.
## Proved
L1 (collision classification). Hypothesis of Theorem X fails for (S,S') iff S in Pa, S' in Pb (or reverse) and S n S' = {c}, c not in {a,b}.
 Proof: |S n T_S'| = |(S n S') u (S n A)|, same for S'. Both >= 2 with |S n S'| <= 1: I=∅ forces both easy (contradiction); I={c}, c in A forces b in both (|S n S'|=2); alpha=S n A must be a singleton != {c}, same for alpha'; alpha=alpha' gives {a,c} in S n S'. So alpha={a}, alpha'={b}, c not in A.
L2. In C1 with this T, a gate is charged by at most 2 sets (one in Pa, one in Pb), and a doubly charged gate has B(g) = {a,b,c}.
Cor A. If no Pa set meets a Pb set (in particular Pa or Pb empty), Theorem X applies: s >= base+1; N live => s >= base+2.
Cor A'. Charging only atoms S\A (collision-free, plain monotone argument in x_a=x_b=0, N=1) gives base - d(a) - d(b) distinct OR gates.
L3 (hybrid). Modes: Pa,P0,E in C1 (zero z_{S u A}, atoms e_u); Pb in C0 (zero z_S', atoms e_u+e_a; h=1 there so C0 exact; valid invariant since a not in S').
 - C1/C1 pairs in this class: no collision (L1). C0/C0 pairs (Pb,Pb): no collision (M={a} misses S').
 - C1/C0 on a gate not downstream of N (g0=g1): no collision (p,q would both lie in S n S').
 - Direct readers of N are never charged in either mode (OR(N,y)=1 in C1, B0(N)=∅ in C0; AND never charged).
 Hence s >= 1 + base - m_D, m_D = #gates downstream of N charged once by a C1 set and once by a C0 set. If N is dead, m_D=0 (cone restriction), s-1 >= base.
 A double D-charged gate g=u v v needs u,v not direct N-readers, so depth(N->g) >= 2.
## Why D gates resist
C1 point (z_T,1) has x_a=0 (T contains A) while the C0 atoms e_u+e_a have x_a=1 and y=0 for N: no ordering relation between the two kinds of points (only g0<=g1), so no contradiction. C0/C0 on Pa/Pb is unconstrained even for disjoint sets (M_S={b} meets S', M_S'={a} meets S).
Double charge in pure C1 (S in Pa, S' in Pb, S n S'={c}): g >= x_a v x_b v x_c as function, yet o_S(e_b)=0=o_S'(e_a); non-D case needs kill ANDs on paths to o_S and o_S' (hard_kill.md Hall-type issue, shared kill gates).
## Open
Need: m (double charges) - 1 distinct payers (AND kill gates / uncharged ORs / D-chain gates). Not proved. Also union-find order freedom (any topological order) not exploited.
