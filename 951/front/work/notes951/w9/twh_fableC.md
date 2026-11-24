# twh_fableC log (agent C: adversary + boundary finder). Tools in w9/fc/ (lib.py = independent verifier + family checker).

## C0 tooling (w9/fc/lib.py)
- verify(c): independent truth-table check (correct on all 2^n inputs, clean, all read, C0 wrong, C1 wrong, h(0)=0, hard N-sets, DD sets).
- family(c, permissive): EXHAUSTIVE search for a Theorem X family: per set all minimal Good Q ⊇ S_w (cone-masked: non-N-set => Q=S;
  else h(z_Q)=0, or all units have N=0; permissive variant also allows "N true at <= 1 unit of S"); backtracking over choices with
  pairwise (|S_a∩Q_b|<=1 or |S_b∩Q_a|<=1). Only minimal Q matter (condition monotone in Q). CHECKED: finds the cyclic family on cxtw3c.

## C1 CHECKED+PROVED: coin rule (fixed 1/2-1/2) is REFUTED INSIDE the sorry's case: cxE (w9/fc/cxe.py, cxe3.json)
Design: cxtw sunflower S_i={0,i,i+t} (t=3, n=7) with h' = x0 ∨ h_sun (h_sun = OR_i AND_{v∉S_i} x_v), T, G=x0∨T, m_i, o_i=G∨m_i as in cxtw,
plus two triples E={1..t} (inner), F={t+1..2t} (outer), each computed by the cx1 gadget o_P=((p1∧h)∨rest∨N)∧((p1∨h)∨rest). No {a,b} gadget.
Correctness (PROVED): sunflower part: C1 is correct everywhere; C0 needs T=1 when x0=x_i=0,x_{i+t}=1,h'=1, and there h'=h_sun (x0=0). Gadget correct for any h.
No family (PROVED): Good Q_i ⊇ S_i needs one more point p in another petal: p inner => |Q_i∩E|=2, p outer => |Q_i∩F|=2.
  Good Q_E, Q_F must contain 0 (h' >= x0), so |Q_E∩S_i|>=2 and |Q_F∩S_i|>=2 for all i: every choice has a mutual clash.
CHECKED: n=7, 5 sets, s=45, base=10; correct, clean, read, C0 wrong, C1 wrong, h(0)=0, 5 hard N-sets, DD sets = E,F; family() = None
(strict and permissive Good). canonical Hall 10/10, R* Hall 8/10, coin a=.5 load 1.5 (FAILS), a=.3 2.1, a=.7 1.0.
  fraclp free choice: all-gate menu L*=0.4545 (menus [2,5,5,4,2]), coneonly L*=1.0: FracMatch SURVIVES on cxE (canonical alone matches 10/10).
  JSON: w9/fc/cxe3.json.

## C1b CHECKED (coordinator's constraint): if h|_{x_k=1} >= o_w for all w∌k then C0|_{x_k=1} computes those o_w exactly
(where o_w=1: h=1 so real=C0; where o_w=0: C0 <= real = 0), a NOT-free circuit => s >= 1 + Σ_{w∌k} d_w. Argument is correct.
cxE has h >= x0 (k=0): sets avoiding 0 are E,F: bound 1+4=5 << s=45; numerically C0|x0=1 is exact on E,F. So cxE is not a
951 candidate anyway (s = base+35); it only refutes the fixed coin rule. Same reasoning gives the FracMatch-side constraint C3(c) below.

## C2 PROVED (reduction for triples) — tool w9/fc/pool.py
(a) o_w is counted by every legal system of w (o(z)=0, o(p_u)=1 all u) and by NO system of another set w' (o_w(z')=0 => z'=0 on S_w,
    then o_w(p'_x)=1 iff x∈S_w, and |S_w∩S_w'|<=1). So outputs are always private.
(b) Hence for families of triples (+pairs) free-choice MatchG <=> FracMatch <=> the sets
    M_w := ∪_{legal systems σ of w} cnt(σ) \ {o_w}  ("merge gates of w") have a system of distinct representatives over the triples.
    A counterexample = t triples whose merge gates in ALL legal systems lie in a pool of < t gates.
(c) t=2 is impossible (PROVED via the system z=0, unit atoms, legal since h(0)=0): the zero-input a of o_1 at z=0 is counted;
    pool={g} forces g to be that input for both outputs; OR/OR gives B_0(g) ⊆ S_1∩S_2, OR/AND gives S_2 ⊆ B_0(g) ⊆ S_1,
    AND/AND gives g = a'∨b' with B_0(g) ⊇ S_1 and each input holding <=1 point of S_1: contradictions.
CHECKED slack(c) = min_F |∪M_w|-|F| : cxtw3c 1 (M_i={G,m_i}), cx2 3, cxE 4, badT (15 triple circuits) >= 1, bad.jsonl >= 0. No violation.

## C3 PROVED (function-level two-world Theorem X) + tool w9/fc/compat.py  [sufficient condition, depends only on (sets,h)]
System σ=(z; p_u=e_u+T_u, T_u⊆ones(z)), legal iff h(z)=0 or #{u: h(p_u)=0}<=1 (Lean GoodT). Define
  sep(σ→σ') :  #{u∈S : NOT(p_u <= z' and h(p_u) >= h(z'))} <= 1.
(a) If sep(σ→σ') or sep(σ'→σ) then cnt(σ)∩cnt(σ')=∅ in EVERY circuit with this h (any K): every gate is monotone in (x,N), so
    p_u<=z', N(p_u)<=N(z') give g(p_u)<=g(z')=0; a gate counted by σ needs 2 atoms true. (Theorem X = unit atoms, world N=1; B4 = special case.)
(b) Because outputs are private (C2a), it suffices to separate the sets of size >=3 ("sep3"): then MatchG holds.
(c) Consequences for any free-choice counterexample family F (all merges in a pool of <|F| gates): F has NO pairwise-separated system
    family; e.g. every heavy unit j (h>=x_j) lies in some set of F, and the sets of F avoiding j have distinct private merges
    (systems z_S, atoms e_u+e_j). [Same mechanism as the coordinator's Nechiporuk constraint C1b.]
CHECKED (compat.famsearch = exhaustive CSP over all z and all minimal light/heavy atoms):
  cx1, cx2, cx3 (canonical fails), cxr, cxtw3c, cxtw4c (R* / coin fail): a separated family EXISTS -> these are all "easy" function-level cases.
  cxE: NO separated family, minimal obstructed subfamilies {S_i, E, F} (a 3-triple path). canonical works there.
  Data with >=2 big sets: sep3 fails in 14/15 badT, 42/44 bad, 24/24 cross5, 27/96 sampled c.jsonl -> function-level obstruction among
  triples is COMMON (so the proof must read gates), but canonical AND R* both satisfy Hall on every one of those.
  RULE "sep3 family, else canonical, else R*" : 0 failures on cx1-3, cxr, cxtw3c/4c, cxE, badT, bad, cross5, sampled c.jsonl.

## C4 CHECKED (exhaustive SAT, w9/fc/satpool2.py): free-choice counterexample search with ALL legal systems encoded
Encoding: correct one-NOT circuit, h(0)=0, size s, every gate read, colex symmetry breaking; for every triple w, every z (0 on S_w), every
pair u,v∈S_w and all fat atoms p_u,p_v: gate g non-output with g(z)=0,g(p_u)=g(p_v)=1 and (N(z)=1 or N(p_u)=0 or N(p_v)=0) must be in a
pool of <= t-1 gates. SAT <=> MatchG/FracMatch counterexample of that size (by C2b).
  triangle {012},{234},{450} (n=6, base 6): UNSAT for s = 7..11.   (more sizes/systems below)
  triangle: UNSAT for s = 7..13.  Pasch (4 triples, n=6, pool<=3): UNSAT s = 9, 10 (11+ not finished).
  Two 4-sets {0123},{0456} (n=7, base 6; satpool3.py, pool = all non-output counted gates of both sets, <= 3): UNSAT s = 8, 9.
  NOTE (coordinator): T1/T3 prove 951 for all |S|<=3, so the triple runs only bear on FracMatch-as-a-route, not on 951 itself.
  Sanity: with pool <= t the encoder is SAT and the decoded circuit's pool equals pool.py's merge sets (encoding CHECKED).

## C5 CHECKED: simple circuit-dependent rules (w9/fc/rules2.py, rule_ac.py, priv.py)
 RULE-3  "function-level separated family for the sets of size>=3 (C3), else canonical, else R*": 0 failures on everything I have.
 RULE-AC "set w uses canonical unless one of its canonical-counted gates is canonical-counted by another set; then w uses R*":
          integer Hall holds on cx1,cx2,cx3,cxr,cxtw3c,cxtw4c,cxE,badT(63),bad(160),cross5(24),cross5f(18),chk/c(2321),w5ess(2042): 0 failures.
          (mirror rule "R* unless R*-shared, then canonical": also 0 failures; EX2 "some per-set choice in {canonical,R*} has Hall": 0 failures.)
 REFUTED: PRIV "each set has a system with d_w counted gates that no other set counts in ANY system": fails on cx3, cxE, 1/63 badT, 3/160 bad.
 CAVEAT (fable A's A4): all data except cx1/cx3/cfgI are vacuous for sets of size<=3; real content needs |S|>=4.

## C6 boundary (analysis; PROVED where marked)
 canonical fails <= AND-cut o=r∧k, k(z_Q)=1, shared merges in r. PROVED necessary: a gate shared by canonical systems of a,b has
   B ⊆ Q_a∩Q_b with mutual clash; the cut input k must vanish on units j∈B(r)\S: j heavy (N(e_j)=0), or j∈Q_a light. In cx1-3 all such j
   are heavy => C0 exact on {x_j=1} => function-level separated family exists (C3) and R*/Σ(e_j) sees private chains.
 R* fails <= OR-cut with a merge G=x0∨T shared by all petals in C0. PROVED necessary for the sunflower design: {h=1, x0=0, petal i = 01}
   ⊆ {all petals nonzero}, hence z_{S_j∪{i}} ∈ {h=0} for all i≠j: the N=1 world is fat, a cyclic Theorem-X family exists among the petals,
   and it can only be destroyed by OTHER sets (E, F in cxE), which then are not confined themselves.
 So the two blind cuts need opposite shapes of h around the same family (heavy low points vs thin {h=1} near z_S). Not a theorem for
 general circuits, but every hand design (mine and, per coordinator, scaffold's) dies exactly there.

## C7 coordinator's lead (h = pq ∨ rs, a set of size>=4): function-level scan (w9/fc/lead.py)
 No separated family (C3) for: two 4-sets {0123},{0456} with EVERY h = OR of 2 or 3 pair-minterms making both hard (9/9, 162/162);
 {0123},{045},{146}: 8/75 (2 minterms), 159/915 (3); +{256}: 15/141, 291/1349; {0123},{345},{560}: 8/75, 159/915.
 e.g. h = x1x2 ∨ x4x5 on {0123},{0456}. These (sets,h) are the right hosts for a counterexample; the two-4-set case is UNSAT at s<=9 (C4).

## C8 coordinator's "relative sandwich" rule (w9/fc/relrule.py; my reading: z∈{0} ∪ {minimal 1-points of h of weight<=2 off S_w},
 Σ(z) system, charge I_z(w) ∪ (P_w∩cnt_z(w)), P_w = A4 sandwich class)
 CHECKED: L_rel = 0.75 on cx1, cx3, cfgI, cxr; 1.0 on cxE, cxtw3c; worst 1.0 on badT (63). No failure. No collision I_z(a)∩I_z'(b) occurs.
 Collision analysis: (PROVED, = fable B's (d)) for heavy units v,v' a common gate needs v∈S_b and v'∈S_a. For a triangle of 4-sets
 a={p,r,a1,a2}, b={p,q,b1,b2}, c={q,r,c1,c2}, heavy = {p,q,r}, the forced points are v_a=q, v_b=r, v_c=p and a fully shared relative merge
 tree EXISTS at function level:  P=x_q a1 ∨ x_r b1 ∨ x_p c1, Q=x_q a2 ∨ x_r b2 ∨ x_p c2, t=P∨Q, W=maj(p,q,r), U=t∨W;
 U = OR(S_a) on {x_q=1}, OR(S_b) on {x_r=1}, OR(S_c) on {x_p=1}; t,W,U lie in I(a)∩I(b)∩I(c), no sub-gate is a private merge.
 NOT COMPLETED: a correct circuit around it. Every exit from U to o_a I tried creates a rule-visible private gate (X_a = U∧x_q, or
 (N∨U)∨x_p, or a pure L_a merge of the light points a1,a2 at z=0), giving 3 outputs + 3 shared + >=3 exits = 9 >= demand 9 (tight, no
 violation). Hiding the light merges at z=0 needs the ∪∩-trick (a1∨a2 = Z_ab ∧ Z_ac with junk (b1∨b2)(c1∨c2)), whose junk must be killed
 by N, which creates weight-2 minterms {b_i,c_j} off S_a — exactly the extra z the rule allows. So the weight<=2 clause is load-bearing;
 the natural attack on L_rel is this triangle with 5-sets (pool t1,t2,W,U vs demand 12) — untested.

## C9 CHECKED+PROVED: triangle attack cxT(k) (w9/fc/tri5.py, cxT2.json, cxT4.json) — relative-sandwich rule REFUTED (in my reading), FracMatch SURVIVES
Design: a={p,r,a_1..a_k}, b={p,q,b*}, c={q,r,c*}; h = p∨q∨r (p,q,r heavy, private points light).
  t = OR_i (x_q a_i ∨ x_r b_i ∨ x_p c_i)   [shared relative merge tree: on {x_q=1} t ≡ OR(a*) + (terms <= p,r), same for b on x_r, c on x_p]
  Q_a = (N∨t∨x_p) ∨ (N∨t∨x_r), Q_b = (N∨t∨x_p)∨x_q, Q_c = (N∨t∨x_r)∨x_q;  P_a = h ∨ a_1 ∨ .. ∨ a_k;  o_a = P_a ∧ Q_a.
Correct (PROVED): h=0: Q=1, P=OR(a*)=OR(S_a). h=1: P=1; q=1: t∨p∨r = OR(S_a); q=0: p or r is 1.
No Theorem X family (PROVED): Good Q_a ⊇ S_a∪{q} ⊇ two points of S_b and of S_c, for every pair mutually.
CHECKED k=4: n=15, s=47, base=15, sets of size 6: correct on all 2^15 inputs, clean, read, C0 wrong, C1 wrong, h(0)=0, 3 hard N-sets,
  all three DD, family() = None (strict and permissive).
  Relative sandwich rule (reading of C8): each set's only useful z is its forced heavy unit (a: e_q, b: e_r, c: e_p); chargeable gates
  a: 8, b: 8, c: 7, UNION 13 < demand 15  =>  L_rel = 1.333 > 1.  (k=2: n=9, s=29, L_rel=0.818; k=3: tight; k>=4 fails.)
  Collisions are exactly the predicted ones: t-chain (3 gates), N∨t, N∨t∨x_p, N∨t∨x_r lie in I_z(a)∩I_z'(b) (∩I_z''(c)).
  The P-chains (h∨a_1∨..) are invisible to the rule (not <= o_a; P_a(z_{S_a})=1; =1 at e_q).
  Free choice: FULL Lean menu (allsys.menus, n=15) L* = 0.4412 all-gate AND coneonly; canonical Hall 15/15, R* Hall 15/15, coin 0.4545.
WHY free choice survives (PROVED sketch): the light points live in the exact cube {p=q=r=0} ⊆ {h=0}. System z_{S_a∪{q}}, unit atoms: every
  counted gate with a light atom a_i is 1 at z_b (e_{a_i} <= z_b, N equal), so only a gate with B_a ⊆ {p,r} can be shared; the k merges
  touching lights + o_a = d_a private gates. The rule loses because it refuses the P-chain (sandwich fails off the light cube).
  => any counterexample must make {h=0} thin around the light merges too (h >= Th_2-like on the lights), i.e. the ∪∩ regime.
JSON cxT4: w9/fc/cxT4.json.

## C10 CHECKED: two-4-set hosts {0123},{0456}
 SAT (satpool4.py, fixed h, pool = all non-output merges of both sets in all legal systems <= 3):
   h = x1x2 ∨ x4x5: UNSAT s = 9..12.   h = maj(1,2,3) ∨ maj(4,5,6): UNSAT s = 10..12.   (free h: UNSAT s = 8, 9.)
 Hand design cx44 (w9/fc/cx44.py): h = x1x2∨x4x5, world-0 merge tree g1,g2,g3 fully shared (g3 = OR(S_a) on {x4x5=1} and OR(S_b) on
   {x1x2=1}), o_a = (N∧W_a) ∨ x1x2 ∨ (x4x5∧g3). Correct, C0/C1 wrong, no family, DD (NOT clean: one duplicate function). L_rel = 0.571,
   full L* = 0.353 (all-gate and coneonly), canonical and R* Hall 6/6. Each set keeps a private exit gate x4x5∧g3 and private world-1 gates.
 Consistent with fable A's A5 (two-set Hall when |Q_b∩S_a| <= 2); for clash size 3 (maj h) only the SAT bound above.
