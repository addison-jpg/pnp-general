# chist_fable.md — Chistikov–Iván–Lubiw–Shallit fractional-covering charging adapted to one-NOT (1,1)-disjoint sums
Code: w9/chist/ (wl.py whole-class LP, wl2.py, wl3.py, ...). Tags: PROVED / CHECKED / CONJECTURE / REFUTED. Restart-safe log.

## C0 (formulation, PROVED — trivial counting; this is the exact analogue of the proof of Thm 13)
ENTRIES e in E; each entry has a gate class G_e (circuit-dependent) and a PROVED count |G_e| >= c_e.
RECTANGLE of a gate: R(g) = {e : g in G_e}.  DUAL WEIGHTS y_e >= 0.  FEASIBILITY: y(R(g)) <= 1 for every gate g.
Then  #gates >= Σ_g y(R(g)) = Σ_e y_e |G_e| >= Σ_e y_e c_e   (regrouping by entries, as in eq. (3) of the paper).
Target: Σ_e y_e c_e >= base (monotone M: base, lifted circuit has s-1 gates => s >= base+1).
In CILS the K-entry (i1,j1) has G_e = edges of the subnetwork N_{j1 i1} (>= OR(M) edges); feasibility is AUTOMATIC because
R(edge) projects to a 1-rectangle of K (correctness of the network) and y is an optimal dual of the rectangle-cover LP of K.
Our entries: e = (w, cfg), cfg = S2.1 configuration (Z join-closed zero set of F_w, atoms a_u), G_e = cl(Z,a), c_e = d_w.
"Semantic rectangle": R(g) = {(w,Z,a) : M_g = 0 on Z, M_g(a_u)=1 for >= 2 atoms}.

## C1 CHECKED/REFUTED: whole-class version (literal analogue: G_e = whole class)
wl.py: LP  max Σ y_e d_w  s.t. every gate load Σ_{e: g in cl_e} y_e <= 1  (lifted menu of w9/s/lift.py).
 - 2548 circuits with n <= 7: value = base on all, even with the per-set normalisation Σ_{e of w} y_e <= 1.
 - REFUTED as a method: cxT2 (n=9, base 9, s=29): whole-class LP = 6 < 9 (menu exhaustive in ceilings/min. atoms: 2 minimal classes/set);
   cxT4 (n=15, base 15): 10.  (ClassFrac with sub-selection of d_w units: L* <= 1 on both, s_fable S2.)
 So the per-entry "subnetwork" must be a d_w-subset of the class (merge set / free sub-selection), not the whole class.

## C2 PROVED: the three LP forms of the charging and their duals (what "fractional covering" means here)
 (W) whole-class:   max Σ y_e c_e  s.t. load_g = Σ_{e: g in cl_e} y_e <= 1.         dual: min Σ π_g s.t. π(cl_e) >= c_e for all e  (literal set-cover τ*).
 (U) unnormalised sub-selection: y_e >= 0, 0 <= x_{e,g} <= y_e (g in cl_e), Σ_g x_{e,g} = c_e y_e, Σ_e x_{e,g} <= 1; value Σ y_e c_e.
     Bound #gates >= Σ_g Σ_e x_{e,g} = Σ_e c_e y_e is pure arithmetic.  DUAL (derived, LP duality):
        min Σ π_g  s.t.  for every entry e: (sum of the c_e cheapest prices in cl_e) >= c_e.
     i.e. "COVER PRICE FORM": every price vector that pays c_e on the c_e cheapest gates of EVERY class has total >= base.
 (N) ClassFrac/LiftClassFrac = (U) + per-set normalisation Σ_{e of w} y_e = 1 (dual = Lean PriceIneq: Σ_w min_e cheap_e(π) <= Σπ).
 Implications: (W)>=base => (U)>=base;  (N) feasible => (U)>=base;  (U)>=base => s-1 >= base.  (U) is the weakest sufficient hypothesis
 (sets may substitute for each other; abstract example: classes of a = {1,2},{3,4}, class of b = {1,3}, d_a=d_b=2, 4 gates: (N) is infeasible,
 (U) = 4 = base with y_b = 0) and has the simplest
 price form (no min over configurations inside a sum). REMARK for Lean: `bound_of_coverPrice` would be a strictly weaker hypothesis than
 LiftClassFrac with the same conclusion. On data no separation ((N) holds everywhere).

## C3 PROVED: circuit-independent ("function-level") dual = exact analogue of "R(e) is a 1-rectangle of K"
Entries: function-level configurations e=(w,Z_e,atoms) of S2.3 (depend on S and h only), c_e = #atoms-1.
SERVABLE set T of entries: for every e in T at least two atoms of e lie below no point of ∪_{e' in T} Z_{e'}.
 LEMMA R. For every wire g of the lifted circuit, R(g) = {e : g in cl_e} is servable. (g=0 on ↓Z_{e'}, g=1 on >=2 atoms of e.) Conversely every
 servable T is contained in R(g) for the monotone function g = OR of the up-sets of the unblocked atoms of T, so the constraint family cannot be
 shrunk without reading the circuit.
 THEOREM F (fractional X+ / fractional Theorem X / fractional E0.1). Let V_fun(S,h) = max{Σ y_e c_e : y >= 0, y(T) <= 1 for all servable T}.
 Then every correct one-NOT circuit with this h (h(0)=0) has s >= 1 + V_fun. (CCP with whole classes + S2.1.) The integral case
 (one entry per set, pairwise unservable) is the "pairwise X+-compatible family" theorem of s_fable S5; the fractional version is a relaxation.
 Since all entries of one set are mutually servable-compatible (F_w itself serves them), Σ_{e of w} y_e <= 1 is automatic: V_fun <= base.
 MONOTONE CASE (h ≡ 0, no y): entry e_w = (↓z_{S_w}; unit atoms). T servable with a != b in T would need two units of S_a outside ↓z_{S_b}, i.e. in
 S_b: impossible by |S_a∩S_b| <= 1. So y ≡ 1 is feasible and V_fun = base: (1,1)-disjointness = "every gate rectangle is a single entry".
 WHERE ONE NOT BREAKS IT (PROVED, exact list):
  (i)  ceilings: ↓(c,1) is a zero domain only for c in U0 (function level), so for a hard set z_{S_w} is not available; with c < z_{S_w} two
       type-1 entries a,b are jointly servable iff >= 2 units of S_a lie outside c_b and >= 2 units of S_b outside c_a (Theorem-X condition).
  (ii) type 0 (Z^0_w, atoms (p_u,0), p_u in U1): a,b jointly servable iff >= 2 atoms of a hit S_b and >= 2 atoms of b hit S_a (E0.1/B4).
  (iii) CROSS TYPE: a pure type-0 entry (all atoms level 0) and a type-1 entry with level-1 atoms are ALWAYS jointly servable ((p,0), p in U1, is
       never below (c,1), c in U0; (p,1) is never below Z^0). Hence for pure menus the servable sets are exactly T0 ∪ T1 and
            V_fun(pure) = max(V_0, V_1)        ("one world at a time": the LP is  max τ V_0 + (1-τ) V_1).
       The only function-level cross-type blocking is a level-0 atom (p,0) inside a type-1 entry of a with p avoiding S_b (blocked by Z^0_b).
  (iv) 2-FREENESS SURVIVES ON y-FREE GATES: if M_g does not depend on y, g in cl(type-0 entry of a) ∩ cl(type-1 entry of b), a != b, forces two
       atoms p,p' of b with g(p)=g(p')=1 and g <= o_a everywhere, so both atoms hit S_a: impossible for unit atoms (two units of S_b in S_a), and
       impossible whenever all but one atom of b avoid S_a. So every cross-world shared gate is N-DEPENDENT (generalises s_fable S1(g) to the lifted menu).
 So: the dual of the monotone proof stays feasible on the N-independent part of the circuit and inside each world; the NOT breaks it only through
 gates above N serving a world-0 entry of one set and a world-1 entry of another, plus the loss of the top zero point for hard sets.

## C4 CHECKED: one-world ClassFrac (ow.py; lifted menu split by type; sub-selection LP)
 L*_0 (type-0 entries only), L*_1 (type-1 only), L*_1u (type 1, unit level-1 atoms only = a statement about C1 alone):
 n <= 7 (2555 circuits): L*_0 <= 1 on 2531, L*_1 <= 1 on 2554, L*_1u <= 1 on 2554; never both > 1 (cx2: L*_0=0.667, L*_1=1.5).
 n >= 8 (21 circuits incl. cxP1/5/6, cxstar44, hand_H*): cx1 (0.75, 1.33), cx3 (0.75, 1.5) need world 0; cxr (1.33, 1.0), cxT4 (1.6, 0.909) need world 1;
 all others both <= 1. min(L*_0, L*_1) <= 1 on ALL data.  CONJECTURE (weak evidence, data not adversarial for it): one-world ClassFrac.
 The mixed optimum is strictly smaller than both (cx1: 0.545), so mixing is slack, not necessity, on data.

## C5 REFUTED: universal (circuit-independent) weightings on the real B3 menu Σ(z) (pb.py, pb2.py, pb3.py, hw.py, cxrb.py, cxU3.py)
Candidate (the natural "uniform dual"): λ_{w,z} = product measure, each point outside S_w put in z with prob. p; classes cnt_z(w) (real circuit,
Lean test systems Σ(z)); sub-selection LP, L(p) = min max gate load.
 - p = 1/2: L <= 1 on ALL data: 2555 circuits n <= 7, all big ones (cx1 .625, cx3 .70, cxr 1.0, cxT2 .41, cxT4 .44, cxtw3/4 1.0, cxP1-6, cxstar, hand_H*,
   srepay_ref/*), 195 srepay/*.jsonl, 12300 chk/k.jsonl.   p = 3/4: fails cxr (1.125); p = .9, 1 (top rule): fail cxe3, cxtw (3.0), cxr.
 - REFUTED: cxrb(k) = two complementary k-sets, h = OR_i x_i x_{i+k}, o_A = h ∨ OR_i (N ∧ x_i), all OR trees BALANCED (cxr.json is k=4):
   L(1/2) = 1.0 (k=4), 1.0156 (k=6), 1.1875 (k=8; L(0.4) = 1.08). Chain-shaped trees give 0.667: the weighting depends on the tree shape.
   These have C1 correct. ESSENTIAL CLEAN version: w9/chist/cxU_8_4.json (n=20, s=57, base 17; correct, C0 wrong, C1 wrong, clean, read; third set
   {p1..p4} with o_D = (t1∨N∨p4) ∧ (t2∨h∨p1)): L(1/2) >= 1.039 (already for the two big sets alone).
 - h-adapted rules (hw.py): z=0 only (unit system) fails cx2 (1.5), cx3 (1.2); uniform on U0-part fails cx2, cx3, cxrb6; uniform on U1-part fails
   cxe3, cxtw (3-4), cxrb6; 1/2-1/2 mixture fails cxe3, cxtw, cxrb6; minimal points of U1 / maximal points of U0: fail 7 / 4 of the big circuits.
   Every single rule is refuted; "best of the six" fails on no data circuit (not a rule: the choice reads the circuit).
 Conclusion: unlike CILS Thm 13, the dual cannot be chosen from (S,h) by any of the natural product/uniform rules; it must read the gates.

## C6 PROVED + CHECKED: MergeFrac = the canonical "path/subnetwork" form of the charging (mg.py, mg2.py, mg3.py, mg4.py)
Real circuit (N kept as a gate), set w, ANY z vanishing on S_w. V_z = wires with value 0 at z, B_z(g) = {u in S_w : g(z+e_u)=1}.
Union-find on S_w over the gates of V_z in circuit order; M_z(w) = OR gates g=s∨t in V_z with B_z(s), B_z(t) nonempty in different blocks.
 LEMMA M (PROVED). |M_z(w)| = d_w EXACTLY, for every z, with no Good-condition: inputs have |B| <= 1; OR in V_z => both inputs in V_z, B = union;
 AND in V_z => an input s in V_z and B(AND) ⊆ B(s); N in V_z => h(z)=1 => h(z+e_u)=1 => B(N) = ∅; o_w in V_z with B = S_w; each merge lowers the
 number of blocks by one. (M_z(w) ⊆ cnt_z(w) of the Lean B3 menu Σ(z).)
 IDENTITY. For any probability measures μ_w on {z : z∩S_w=∅}:  Σ_g load(g) = base, load(g) := Σ_w μ_w{z : g in M_z(w)}; only OR gates carry load.
 MergeFrac(μ): load(g) <= 1 for every gate.  MergeFrac => Lean FracMatch (M ⊆ cnt, |M| = d_w) => s >= base; indeed => #OR gates >= base.
 Rectangle of a gate: R(g) = {(w,z) : g in M_z(w)} — the analogue of "edges of the subnetwork N_{j1 i1}"; dual feasibility = "every merge rectangle has
 μ-weight <= 1"; LP dual (exact): MergeFrac for some μ  <=>  for all prices π >= 0:  Σ_w min_z π(M_z(w)) <= π(all gates).
 CHECKED (free μ, LP): MergeFrac holds on ALL data: 2555 circuits n <= 7, the 20 big ones n = 8..11 (cx1 .667, cx3 .75, cxr .545, cxT2, cxtw3/4, cxP1/5/6,
 cxstar44, hand_H1-5), cxT4 (n=15), 195 srepay/*.jsonl, 12300 chk/k.jsonl, cxrb4/6, cxU_8_4 (n=20); 0 anomalies of Lemma M (|M|=d_w, block invariant).
 Robust under 300 random topological re-orderings of the gate list of the 25 hardest circuits (12 each): 0 failures.
 On the hard circuits the optimum is usually integral (cxtw3, cxT2, cxP6: one z-class per set, a partition of base OR gates), cx2 needs a 1/4-3/4 mix.
 This is strictly more rigid than ClassFrac (no sub-selection freedom, classes of size exactly d_w) and still never fails on data.
 CONJECTURE MergeFrac: every correct one-NOT circuit admits μ. (Equivalent in strength to proving 951 through FracMatch; implies #OR >= base.)
 PROVED (single-price case of the dual): the "universal merges" U(w) = ∩_z M_z(w) are pairwise disjoint: g in U(a) vanishes at every z avoiding S_a,
 so g <= o_a as a real function; g in U(a)∩U(b) is 1 on two units of S_a (z=0), which then lie in S_b. (π = 1_{g}: Σ_w min_z π(M_z(w)) <= 1.)

## C7 SUMMARY — strongest proved statement and the exact gap
PROVED (this log):
 1. CCP (C0) and its LP forms (C2): whole-class (W) ⊂ ClassFrac (N) ⊂ unnormalised cover-price form (U); (U) has dual
    "every π paying c_e on the c_e cheapest gates of every class has Σπ >= base" and is the weakest hypothesis giving s-1 >= base.
 2. THEOREM F (C3): s >= 1 + V_fun(S,h), V_fun = fractional packing number of function-level entries against servable sets (circuit-independent
    dual, the literal analogue of CILS Thm 13). Monotone case: V_fun = base, feasibility of y ≡ 1 IS (1,1)-disjointness. One NOT: V_fun(pure) =
    max(V_0,V_1); the NOT breaks feasibility exactly through (i) loss of the ceiling z_{S_w} for hard sets, (ii) mutually hitting zero points in world 0,
    (iii) unconstrained cross-world pairs; (iv) every cross-world shared gate is N-dependent (2-freeness survives on y-free gates).
 3. Lemma M + identity (C6): canonical merge sets of size exactly d_w at EVERY zero point z of the real circuit; Σ_g load = base; MergeFrac => 951
    (and #OR >= base); universal merges are pairwise disjoint.
REFUTED: whole-class charging on the lifted menu (cxT2 6 < 9, cxT4 10 < 15); every circuit-independent product/uniform weighting on Σ(z)
 (p = 1/2: cxrb(6), cxrb(8), essential clean cxU_8_4; p near 1: cxtw, cxe3, cxr; z = 0: cx2, cx3; U0-/U1-uniform, minterm/maxterm rules).
CHECKED: MergeFrac (free μ) on all ~15,300 data circuits incl. n = 15, 20 and 300 random re-orderings; one-world ClassFrac min(L*_0,L*_1) <= 1 on all data.
EXACT GAP. A CILS-type proof needs dual weights with "every gate rectangle has weight <= 1". Function-level weights exist iff V_fun = base (Theorem F),
 which fails already for two complementary 4-sets with h = Th_2 (s_fable S5) — and no rule reading only (S,h) can work (C5). So the weights must read
 the gates, and what is missing is exactly ONE of the equivalent statements
   (MergeFrac)  for all prices π >= 0:  Σ_w min_{z: z∩S_w=∅} π(M_z(w)) <= π(gates)          [real circuit, Lean FracMatch form]
   (U)          lifted cover-price form of C2 (weaker than LiftClassFrac, same conclusion),
 for which we have: the single-gate case π = 1_g (C6), the y-free part (C3(iv)), hyperforests (Lemma J), and no counterexample.
 The two-world / weight->=2 content needed: a bound on the total load that N-DEPENDENT gates receive from a world-0 entry of one set and a world-1
 entry of another (C3(iii)); on y-free gates and inside one world the monotone dual stays feasible wherever zero points exist.
SUGGESTED LEAN LANDINGS (no Lean written): (a) `bound_of_coverPrice` (form (U)); (b) `mergeSet_card : |M_z(w)| = d_w` for the B3 menu and
 `fracMatch_of_mergeFrac`; (c) Theorem F as `bound_of_servablePacking` (subsumes the X+ family theorem, gives a new minimality fact: V_fun < base).
