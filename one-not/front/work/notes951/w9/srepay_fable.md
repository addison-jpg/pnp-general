# srepay_fable.md — closing the cyc(H) gap (Fable, continuation of srepay_opus.md). Restart-safe log. Code: w9/sf/
Tags: PROVED / CHECKED / CONJECTURE / REFUTED / HEURISTIC.

## F0 Re-plan (after reading srepay_opus, referee, s_fable, r_fable, SORRY_DISSECTION, tractability-nominCE)
- (CHARGE) is an identity rewrite of Lemma J (referee R6); Lemma J = weight<=1 bound. On units, world 1 is the UNION/INTERSECTION model:
  B(g) = {u : g(e_u,1)=1}; OR = union, AND = intersection, B(F_w) ⊇ S_w (= S_w iff all units outside S_w are light).
  PROVED (F1 below): in that model the merge sets collapse (|∪M_w| << base) on nets, so NO refinement of the unit union-find can pay cyc(H).
- Coordinator: do not pursue Sokolov game lane; state results in lifted form (pre/post, interval outputs); target LiftClassFrac.

## F1 PROVED: LEAK LEMMA (weight >= 2 counting on a NON-join-closed zero domain) and its dual
Setting: any monotone circuit (fan-in 2 AND/OR, no constants) over variables Var; G a gate. In the application: M over (x,y).
DATA. Atoms a_i (i in I, |I| = k >= 2; the points need NOT be distinct). Moves: a finite set O and points π(X), X ⊆ O, with π MONOTONE
 (X ⊆ X' => π(X) <= π(X')). For a wire w:  B(w) = {i : w(a_i)=1},   λ(w) = min{|X| : w(π(X)) = 1} (∞ if none).
HYP. (i) every input variable v has |B(v)| <= 1 or λ(v) <= 1;  (ii) G(π(X)) = 0 for all |X| <= t (t >= 1);  (iii) G(a_i) = 1 for all i.
LEAK LEMMA.  #{gates w in cone(G) : λ(w) >= 2 and |B(w)| >= 2}  >=  min(t, k-1).
 ("private" gates: 0 on the base π(∅) and on every single-move point π({o}); 1 on at least two atoms.)
PROOF. For R ⊆ O, I' ⊆ I put λ_R(w) = min{|X| : X ⊆ O\R, w(π(R∪X))=1}, B'(w) = B(w)∩I'; w is (R,I')-private if λ_R(w) >= 2, |B'(w)| >= 2.
 Rules: B(s∨t)=B(s)∪B(t), B(s∧t)=B(s)∩B(t); λ_R(s∨t)=min; λ_R(s∧t) <= λ_R(s)+λ_R(t) (π monotone); λ_R - 1 <= λ_{R∪q} <= λ_R.
 Hence (R',I'')-private => (R,I')-private for R ⊆ R', I'' ⊆ I'; and (i) persists: an input has |B'| <= 1 or λ_R <= 1.
 CLAIM: for every gate g with θ := min(λ_R(g), |B'(g)|) >= 2, cone(g) contains >= θ-1 (R,I')-private gates. Induction on |I'|+|O\R|.
 θ = 2: g itself. θ >= 3: let w be the EARLIEST (R,I')-private gate in cone(g); its children are inputs or non-private gates.
  w = s∨t: λ_R(s),λ_R(t) >= λ_R(w) >= 2, so each child has |B'| <= 1 (input: by (i); gate: not private). So B'(w) = {u,u'}.
     Put I'' = I'\{u}: w is not (R,I'')-private, θ'' >= θ-1 >= 2, IH gives θ-2 (R,I'')-private gates, all (R,I')-private and != w. Total θ-1.
  w = s∧t: |B'(s)|,|B'(t)| >= |B'(w)| >= 2, so each child has λ_R <= 1 (input: (i); gate: not private); λ_R(w) >= 2 forces
     λ_R(s) = λ_R(t) = 1. Take q in O\R with s(π(R∪q)) = 1, R' = R∪q: λ_{R'}(w) <= 0+1, so w is not (R',I')-private; θ' >= θ-1 >= 2;
     IH gives θ-2 (R',I')-private gates, all (R,I')-private and != w. Total θ-1.   Apply to g=G, R=∅, I'=I: θ >= min(t+1,k). ∎
 REMARK (connected version): the same count holds inside the PRIVATE CONE of G (gates reachable from G through private gates only):
 treat every non-private wire as an input; it satisfies (i) by definition.
DUAL LEAK LEMMA (swap AND/OR, 0/1; atoms may all be ONE zero point Zp). π ANTITONE; G(Zp)=0; G(π(X))=1 for all |X| <= t; every variable v
 with v(Zp)=0 has v(π(X))=0 for some |X| <= 1. Then  #{gates w : w(Zp)=0, w(π(X))=1 for all |X| <= 1} >= t.
CHECKED (sf/hpriv.py, SAT): single set k=4, 4 off points, G = OR(L) on weight <= 3: no circuit with <= 9 gates has fewer than 3 private gates.

## F2 PROVED: THEOREM H1 (world 1) — lifted form: M = pre ++ post monotone over (x,y), F_w in [o_w∧(y∨h), o_w∨(y∧h)], h(0)=0
 τ_w := min size of a minterm of h disjoint from S_w (∞ if none).   P_w := {gates g of M : g(0,1)=0, g(e_p,1)=0 for all p ∉ S_w,
 g(e_u,1)=1 for >= 2 u in S_w}  ("unit support at level 1 inside S_w, >= 2 points").
 (a) |P_w| >= min(d_w, τ_w - 1).   (b) P_a ∩ P_b = ∅ for a != b (|S_a∩S_b| <= 1).
 Hence  #gates(M) >= Σ_w min(d_w, τ_w-1),  s >= 1 + Σ_w min(d_w, τ_w - 1).
 Proof of (a): Leak Lemma with atoms (e_u,1), u in S_w; O = [n]\S_w, π(X) = (1_X,1). (i): x_u is 1 on one atom; x_p (p off) has λ=1;
 y has λ=0. (ii): F_w(1_X,1) <= o_w ∨ h = 0 for X off, |X| <= τ_w-1. (iii): F_w(e_u,1) >= o_w∧(y∨h) = 1.
 COROLLARY H1 (951 for h WITHOUT SMALL MINTERMS): if every minterm P of h has |P| >= |S_w| for every w with P∩S_w = ∅ (e.g. h = Th_T,
 T >= max|S_w|; any h all of whose minterms have >= max|S_w| points), then s >= base + 1.  ANY (1,1)-disjoint system, cyclic or not.
 Tight: R's "AND of t+1 ORs" device (r_fable R3/R5) uses exactly t private gates per line.

## F3 PROVED: THEOREM H0 / H0+ (world 0)
 ρ_w(D) := max{|x| : x ⊆ S_w, h(D∪x)=0} for D ⊆ [n]\S_w with h(D)=0; t_w(D) := d_w - ρ_w(D); for h(D)=1: t_w(D) := d_w.  z_w := 1_{[n]\S_w}.
 Q^D_w := {gates g : g(z_w,0)=0, g(D∪S_w,0)=1, g(D∪S_w\{u},0)=1 for all u in S_w}.
 (a) |Q^D_w| >= t_w(D).  (b) Q^{D_a}_a ∩ Q^{D_b}_b = ∅ whenever D_a∩S_b = ∅ or D_b∩S_a = ∅ (a != b).
 Proof (a): Dual Leak Lemma, Zp = (z_w,0) (F_w(z_w,0) <= o_w(z_w) = 0), O = S_w, π(X) = (D∪S_w\X, 0): ones for |X| <= t_w(D)
 (lower bound o_w∧h; S_w\X nonempty). Variables 0 at Zp: x_u (0 at π({u})), y (0 at π(∅)).
 (b): if D_a∩S_b=∅ take u = the common point (any u if disjoint): D_a∪S_a\{u} <= z_b, so g(z_b,0)=0 contradicts g(D_a∪S_a\u,0)=1.
 THEOREM H0+: for every minterm P of h (or P = ∅):   #gates(M) >= Σ_{w: S_w∩P=∅} d_w + Σ_{w: S_w∩P≠∅} (d_w - ρ_w(∅))^+ .
 (P = ∅: Σ_w (d_w - ρ_w)^+, ρ_w = largest subset of S_w in U0.)  Sets avoiding P: the classical subcube classes; sets hitting P: NEW.
 Examples. h = Th_2, any system: s-1 >= base - min_{pairs P} #{w : S_w∩P ≠ ∅} (before: base - Σ_{w hits P} d_w).
 h = Th_T: s - 1 >= max( Σ_w min(d_w,T-1),  max_P [Σ_{w∩P=∅} d_w + Σ_{w∩P≠∅} (d_w-T+1)^+] )  >= base/2.
CHECKED (sf/chkH.py, sf/chkH0p.py): 7253 correct circuits with h(0)=0 (all data: w8/cx*, w8b, w9/*/*.json(l), w7/*.jsonl, chk/c.jsonl,
 /tmp/w5ess.jsonl; 4482 with essential NOT): 0 violations of |P_w| >= min(d_w,τ_w-1), |Q_w| >= d_w-ρ_w, |Q^P_w| >= t_w(P) (16643 minterm
 cases), 0 disjointness violations. base - max(W1,W0+) histogram: 0:347, 1:3704, 2:2526, 3:645, 4:29, 6:1.

## F4 PROVED (barrier, why subcube/privacy bounds could not see this): PG(2,q), h = Th_T
 Expander mixing (point-line graph, 2nd singular value sqrt q): a T-set misses <= q(n-T)n/((q+1)^2 T) ~ q^3/T lines. So every subcube
 bound (r_fable R1) is <= q^4/T (world 0) and <= (T-1)q (world 1): at T = q^{1.5} both are ~ q^{2.5} << base = q^3 (ratio 0.41 at q=16,
 0.06 at q=1024; sf/barrier.py; on PG(2,3) with T=4..6 the two subcube bounds sum to 12..15 of base 39). Corollary H1 gives base for T >= q+1.
