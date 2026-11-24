# Hybrid C0/C1 charging for mutually absorbing hard sets

Notation: D = gates downstream of N (N, its readers, and everything they reach); non-D gates have g0 = g1 = g.
C1: S charged with atoms e_u, zero z_T, T ⊇ S, h(z_T)=0 (Theorem X). C0: S charged with zero z_S (always valid, g0 <= f),
test points y_{S,u} = e_u + 1_{M_S}, M_S a minterm of h avoiding S (needs S hard), h(y)=1 so g0_S(y)=1.
Same union-find scheme in each monotone circuit (OR in A(S): both inputs in A(S), one merge; AND: B(g) in B(a) for the input a in A(S)); leaf/AND steps go through for y-atoms because y_{S,u} has a 1 at v in S only for v=u.

## Collision lemmas (gate g = a v b charged by S and S')
Non-D gate (a0=a1=a):
 (i) C1(S,T)/C1(S',T'): |S∩T'|<=1 or |S'∩T|<=1 (Thm X).
 (ii) C1(S,T)/C0(S',M'): NO condition. S-merge gives p!=q in S with a(e_p)=1=b(e_q) (any wire; p,q chosen in the two input B-sets). a(z_S')=0 and e_p<=z_{S'} unless p in S', so p,q in S∩S', contradiction with |S∩S'|<=1.
 (iii) C0(S,M)/C0(S',M'): the merge points p,q have a(y_{S,p})=1, a(z_S')=0, so y_{S,p} has a 1 inside S': p in S' or M_S∩S'≠∅. Fine iff M_S∩S'=∅ or M_S'∩S=∅ (then p,q in S∩S').
D gate:
 (iv) C1(S,T)/C0(S',·): only a0<=a1 is available. a1(z_T)=0 gives a0(z_T)=0. With y-atoms of S': a0(y_{S',p'})=1 only gives y ≰ z_T, but every 1-point of h meets every transversal T of h, so this is ALWAYS true: no information. With e-atoms for S' (needs h(e_u)=1 for all u in S', i.e. S' ⊆ singleton minterms) one gets p',q' in S'∩T: requires |S'∩T|<=1, impossible if |S'|>=2 since T must contain every singleton minterm.
 (v) C1/C1 and C0/C0 on D gates: as (i), (iii) (same monotone circuit).
So the hybrid gives: s >= 1 + (#charged OR gates) with #charged >= base - (#D gates charged by a C1-set and a C0-set). The ONLY unresolved collision type is C1 vs C0 on a gate downstream of N.

## Mutually absorbing pair, exact form
Let c=|S∩S'|. "S absorbs S'" (no T ⊇ S transversal with |T∩S'|<=1) iff: c=1: some minterm M ⊆ S'∖S; c=0: minterms of h inside S' have empty common intersection (and exist).
Mutual absorption => h has minterms inside S'∖S and inside S∖S'.
Then every assignment fails at the pair level: C1 for S needs T ⊇ S meeting S' in >=2 points; same for S'; C0 for S must take M_S ⊆ S'-side minterm (only minterms avoiding S lie ... in the minimal example the only one is M_1 ⊆ S'), so M_S∩S'≠∅, likewise M_S'∩S≠∅; (iii) fails. Mixed C1(S)/C0(S') passes on non-D gates by (ii) but on D gates fails by (iv).
Smallest example: n=5, S={0,1,2}, S'={2,3,4}, h = x0x1 v x3x4 (minterms {0,1},{3,4}). Even n=3, S={a,c},S'={c,b}, h=x_a v x_b (needs C0 test points e_u+1_M with M={b} touching S').

## Computer evidence (SAT, live951.build_live, NOT must be in an output cone; all UNSAT = no correct circuit)
 - n=5 {012},{234}: s=4,5 (base=4): UNSAT for every NOT position.
 - n=4 K4 minus edge (base 5): s=5,6 UNSAT; s=7=base+2 SAT (junk: NOT of an input, x v (~x & y)).
 - n=6 triangle {012},{234},{450} (base 6): s=7 UNSAT.
 - n=3 path (base 2): s=5 SAT (junk), s<=4 not live.
So no correct circuit of size <= base+1 with live NOT is known in these; I did not exhibit a correct circuit with a C1/C0 D-gate collision, so whether the obstruction is realizable is OPEN (guess: not realizable, but no proof).
Note: in the example h costs 3 gates + N =4 = base, so in that example the cost of computing h itself already pays base. A route not tried: charge h's gates (non-D, uncharged by OR-merges: AND gates and ORs outside A(S)) against absorbing pairs. 
