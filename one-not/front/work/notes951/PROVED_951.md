# L-meta-951: proved results, refuted statements, exact open statement

Status tags: **PROVED-LEAN** (compiled, no sorry), **PROVED-PAPER** (full proof written, checked by a second agent or by front, not formalised), **CHECKED** (verified on data/by code only), **REFUTED** (counterexample verified).
All statements below are copied from the agent logs (SORRY_DISSECTION.md, w9/fracmatch.md, HANDOFF_front.md, w9/twh_fable{A,B,C,E}.md, w9/twoworldhall.md, w9/t1lean_log.md, w9/r0lean_log.md, w8_hall_b.md). Paths `w9/...` are relative to the scratchpad `w9/` or `work/notes951/w9/`; Lean paths are `lean/PEqualNP/W951/` in the private repo `pequalnp-work`.

## 1. Setting and notation

**Problem (L-meta-951).** Sets S_1..S_m ⊆ [n], |S_w| ≥ 2, pairwise |S_a ∩ S_b| ≤ 1. Circuit: fan-in-2 AND/OR gates plus at most one NOT, N = ¬h, h an earlier (monotone) wire. Outputs o_w = OR(S_w) as Boolean functions. s = number of gates; d_w = |S_w|-1; base = Σ_w d_w. **Claim: s ≥ base.**

- C0 = circuit with N := 0, C1 = circuit with N := 1 (both monotone). The real circuit equals C1 on {h=0} and C0 on {h=1}; g0 ≤ f ≤ g1. (Exactness: C0 gives o_w(x) whenever o_w(x)=0 or h(x)=1; C1 gives o_w(x) whenever o_w(x)=1 or h(x)=0.)
- NOT is *essential* if C0 is wrong and C1 is wrong. *Clean*: no gate equals an earlier wire as a function (no constant wire, no duplicate wires). *Live*: every gate is read or is an output.
- z_Q = 0 on Q, 1 outside Q; e_u = unit vector. A set S is *hard* iff h(z_S)=1, else *easy*. *N-set*: N lies in cone(o_S). *DD set*: C1(z_S)(o_S)=1 and C0(e_u)(o_S)=0 for some u ∈ S.
- **Test system** σ = (z; atoms p_u, u ∈ S; K ⊆ gates) (Lean `TestSys`): p_u vanishes-on-z only at u (p_u ∩ Zero(z) = {u}), K read-closed, Good condition (N(z)=1, or at most one atom with N=1, etc.). **Counted gates** cnt_σ = gates g ∈ K with g(z)=0 and g(p_u)=1 for ≥ 2 atoms u ∈ S. Core fact (Lean `main_invT`, `countT_bound`): |cnt_σ(S)| ≥ |S|-1.
- **B3 menu Σ(z)** (PROVED-PAPER, w8_hall_b B3): for any z vanishing on S_w, atoms p_u = z+e_u, K = all gates is a legal TestSys; cnt_z(w) = {g : g(z)=0, g(z+e_u)=1 for ≥ 2 u ∈ S_w}. z = 0 is the unit system.
- **MatchG** (Lean): ∃ systems σ_w and an injective f : Σ_w Fin(d_w) → gates with f(w,j) ∈ cnt(σ_w) ⇒ s ≥ base. **FracMatch**: finitely many systems per set with weights, M_{w,j} ⊆ cnt, |M| ≥ d_w, every gate load ≤ 1. "Free choice" = the systems may depend on the circuit.
- Wire-level vocabulary used in proofs: D_w = {g ≤ OR(S_w), g(e_u)=1 for ≥ 2 u ∈ S_w} (dedicated-below); P_w = {g ≥ OR(S_w), g ≢ 1, g ≱ OR(S_j) for j≠w} (private-above); both contain o_w.

## 2. Results formalised in Lean

| tag | name | statement | file / branch |
|---|---|---|---|
| PROVED-LEAN | `bound_of_gapG`, `matchG_of_gapG` | Gap-G ⇒ MatchG | `GapG.lean`, `MatchG.lean` (front-gapg, front-match) |
| PROVED-LEAN | `bound_of_matchG` | MatchG S gates out ⇒ Σ(\|S_i\|-1) ≤ gates.length | `MatchG.lean` (front-match) |
| PROVED-LEAN | `bound_of_qdisj`, `charge_of_disjoint_c` | disjoint-Q charging | `DisjQ.lean` (front-disjq) |
| PROVED-LEAN | `main_invT`, `countT_bound`, `DT_mono` | counting lemma for test systems | `Frame.lean` (front-frame) |
| PROVED-LEAN | `bound_of_fracMatch`, `fracMatch_of_matchG` | FracMatch (ℝ) ⇒ base ≤ #gates; MatchG ⇒ FracMatch | `FracMatch.lean` (front-frac), axioms propext/choice/Quot.sound only |
| PROVED-LEAN | `matchG2_iff_simpleBMatching`, `matchG2_iff_simpleHall`, `matchG2_iff_exists_simpleHall`, `fracMatch_of_matchG'`, `fracMatch_of_matchG2'` | MatchG2 (two systems per set, gate capacity 2, one unit per (system,gate)) is equivalent to the simple b-matching / Hall interface; MatchG, MatchG2 ⇒ FracMatch | `MatchBase2.lean` (front-r0 tree); generic matching in `Base/Matching/Simple.lean` |
| PROVED-LEAN | `fracMatch_iff_priceIneq`, `bound_of_priceIneq`, `hardCase_of_priceIneq` | price (LP-dual) form: FracMatch ⇔ for all prices π ≥ 0, Σ_w min_σ (sum of the d_w cheapest π in cnt_σ) ≤ Σ_g π_g; PriceIneq ⇒ bound | `PriceForm.lean` (front-r0 tree) |
| PROVED-LEAN | `small_min2_bound` | s ≥ Σ_w min(d_w, 2) (direct injection: output + second gate per set) | `Small3.lean` (front-t1; also in the front-r0 tree) |
| PROVED-LEAN | `small3_bound` | if every \|S_w\| ≤ 3 then s ≥ base | `Small3.lean` (front-t1) |
| PROVED-LEAN | `r0_step`, `bound_all_core`, `hardCaseDD4_of_core`, `L_meta_951_of_core` | **R0'**: 951 holds given `HardCaseCore` (the open predicate of section 5); point deletion via `Restrict/Dead/Lower/Core.lean`: restriction D={x_v=false}, dead gates, `promise_bound` (base + \|DC\| ≤ L), `DC_lower` (\|DC\| ≥ deg v if ≤ 1 big set through v) | `Restrict.lean`, `Dead.lean`, `Lower.lean`, `Core.lean` (front-r0, ba4d780); axioms propext/Classical.choice/Quot.sound |
| PROVED-LEAN | earlier reductions (coord-951 branch `Eval, Count, Frame, Cleanup, Charge, Cone, GapG, Cases, TwoWorld, Hard, Main`) | NOT dead / h(0)=1; all sets easy; ≤ 1 hard set (Theorem X, also cone-restricted); cleanup (copy gates, unread gates deletable); removable NOT (C0 or C1 correct ⇒ monotone bound); Two-World ⇒ DD; `main_inv` counting; `bound_all` strong induction | `W951/*.lean`, map in `work/W951.md` |

Remark (R0 simplification, r0lean_log): in the Lean proof the "c is a gate / c is input x_u" case analysis of the paper proof is unnecessary: if every dead gate is a pair output o_w, its value x_v ∨ x_u is 1 at both toggle points directly.

## 3. Paper results with full proofs

Conventions: wires are inputs x_0..x_{n-1} then gates. F1: every wire before N is monotone, so N is antitone. Output gates are AND/OR (an output cannot be an input wire or N). F4: for j≠i there is u ∈ S_j \ S_i; OR(S_j) ≤ OR(S_i) ⇒ j=i.

### 3.1 T1 (PROVED-PAPER, Fable B, line-checked by front; CHECKED on 900+ clean circuits). Lean counterpart: `small3_bound`.
**Statement.** A clean circuit (no constant wire, no two wires equal as functions), one NOT, all |S_w| ≤ 3 has an integral free-choice MatchG with B3 systems Σ(z), hence s ≥ base. For arbitrary set sizes the same argument gives s ≥ Σ_w min(d_w, 2) and a matching saturating min(d_w,2) per set.

**Proof B (dedicated / star forest).** Every set takes its output o_w (o_w ∈ cnt_z(w) for every z; outputs are distinct wires). A triple i needs one more gate.
- *OR-top*, o_i = A∨B. Then A,B ≤ OR(S_i); at z = 0, A(0)=B(0)=0 and the three units are covered, so one input, say A, is 1 on two units of S_i. A is not a variable and not N (N antitone, N(0)=0 would force N(e_u)=0), so A is a gate in cnt_0(i). Take z_i = 0, φ(i) = A ("dedicated").
- *AND-top*, o_i = A∧B. Then A,B ≥ OR(S_i), A≠B (else unclean), neither a variable nor N. Edge e_i = {A_i,B_i} in the graph H on "above-gates".
- *Star-forest lemma*: every edge of H has an endpoint of degree 1. Otherwise e_i = {A,B}, A ∈ e_j, B ∈ e_k, j,k ≠ i; pick u ∈ S_j\S_i, v ∈ S_k\S_i, x = e_u ∨ e_v: OR(S_i)(x)=0 but A(x) ≥ OR(S_j)(x)=1, B(x) ≥ OR(S_k)(x)=1, so (A∧B)(x)=1, contradiction. Take the degree-1 endpoint L_i. L_i is non-constant (clean) and ≥ OR(S_i), so L_i(z)=0 for some z vanishing on S_i (otherwise L_i ≡ 1); at that z, L_i(z+e_u)=1 for all u ∈ S_i, so L_i ∈ cnt_z(i). Take z_i = z, φ(i) = L_i.
- *Distinctness.* Dedicated gates of different triples differ (A ≤ OR(S_j) with two units in S_i forces j=i). Dedicated/above gates are not outputs (OR(S_j) ≤ g ≤ OR(S_i) forces j=i and g ≡ o_i, unclean). Leaves of different edges differ (degree 1). So φ is injective and avoids outputs.

Facts F1–F10 used (for Lean) are listed in w9/twh_fableB.md ("T1 exact list of facts"). Not used: h(0)=0, hardness, essential NOT, DD, s<base.

**Proof A (sandwich classes, Fable A, "A4"; independent).** For each set a let
L_a = {g : g ≤ o_a on all inputs, g(e_u)=1 for ≥ 2 u ∈ S_a}, U_a = {g : g ≥ o_a on all inputs, g(z_{S_a})=0}, P_a = L_a ∪ U_a (o_a lies in both). System-free (no test systems, no Good); uses only that output gates are AND/OR.
1. The P_a are pairwise disjoint. (L_a∩L_b: two units of S_a lie in S_b. U_a∩U_b: o_b(z_{S_a})=1 since S_b ⊄ S_a. L_a∩U_b: o_b ≤ g ≤ o_a gives S_b ⊆ S_a.) Hence s ≥ Σ_a |P_a|.
2. |P_a| ≥ min(d_a, 2). (|S_a|=2: o_a. o_a = p∨q: B(p)∪B(q) = S_a for B(x) = {u : x(e_u)=1}; an input wire has |B| ≤ 1 and p ≠ N because p(0) ≤ o_a(0)=0 < N(0); so the input with |B| ≥ 2 is a gate of L_a if |S_a| ≥ 3. o_a = p∧q: p,q ≥ o_a; one of them, l, is 0 at z_{S_a}; l is not an input; l ∈ U_a.)
3. Corollary (T3 of A): all |S_w| ≤ 3 ⇒ s ≥ base. Lean-system form (circuit-dependent rule): OR-output set → z=0, unit atoms; AND-output set → z=z_S, atoms z+e_u.
4. More generally |L_a| ≥ (κ-1)+q (κ = components of the hypergraph of leaf blocks in the OR-closure of o_a; q = number of leaf gates with |B| ≥ 2), and |U_a| ≥ 1 + (gates on a zero-at-z_S AND chain below o_a plus its first OR gate). Residual demand r_a = d_a − |P_a| > 0 only if |S_a| ≥ 4 and the closures end in a "mixed cut". (A4(4) is stated as proved by A; not separately line-checked.)
CHECKED (w9/fa/sand.py): 12,126 circuits: P_a pairwise disjoint; |P_a| ≥ d_a for every set of size 2 (54,305 sets) and 3 (4,137 sets). The only short sets in all data are the five AND-output 4-sets of cx1/cx3.

### 3.2 T3: private classes and private-frontier lemma (PROVED-PAPER, Fable B; CHECKED on cx1-3, cxr, cxtw3c, badT, bad, tri_ess, chk/c)
D_i = {g ≤ OR(S_i), g(e_u)=1 for ≥ 2 u ∈ S_i}, P_i = {g ≥ OR(S_i), g ≢ 1, g ≱ OR(S_j) ∀ j≠i}, Π_i = D_i ∪ P_i (o_i ∈ Π_i).
1. The Π_i are pairwise disjoint (D_i∩D_j: common pair; P_i∩P_j: by definition; D_i∩P_j: OR(S_j) ≤ g ≤ OR(S_i)).
2. D_i ⊆ cnt_0(i); g ∈ P_i lies in cnt_z(i) for EVERY z vanishing on S_i with g(z)=0 (then g(z+e_u)=1 ∀ u ∈ S_i).
3. **Private-frontier lemma.** If o_i is AND-top, let F_i = OR gates reached from o_i through AND gates only (o_i = ∧F_i, all ≥ OR(S_i), none a variable or N). Some R ∈ F_i lies in P_i. (Otherwise each G ∈ F_i has j(G) ≠ i with G ≥ OR(S_{j(G)}); pick u_G ∈ S_{j(G)}\S_i, x = ∨_G e_{u_G}: every G(x)=1 so o_i(x)=1 but x misses S_i. Every AND on the path o_i→R is also in P_i.)
4. With m_i := max_z |Π_i ∩ cnt_z(i)| there is an integral free-choice matching saturating min(d_i, m_i) for all i at once; m_i ≥ 2 for |S_i| ≥ 3 (reproves T1). m_i ≥ 3 (4-set fully served) if (a) |D_i| ≥ 3, or (b) two gates of P_i \ {o_i} share a zero vanishing on S_i.
Open 4-set configurations after T3 (exactly): (I) o_i = A∨B, A ∈ D_i with ≥ 3 units, A = P∧Q, D_i = {o_i, A}; (II') o_i = R∧C, R = P∨Q ∈ P_i, C shared or in P_i with no common zero with R on Z(S_i).

### 3.3 R0 / R0' point deletion (PROVED-PAPER Fable E, front re-checked; Lean: `Restrict/Dead/Lower/Core`, see section 2; CHECKED 1602 (circuit, v) instances, 0 violations)
Restriction x_v := b. A gate is *dead* if its restricted function is constant, a variable, or equal to the restricted function of one of its inputs. All dead gates can be removed simultaneously, so s ≥ s(restricted) + #dead. Every gate reading x_v is dead (b=0: x_v∨c → c, x_v∧c → 0, ¬x_v → 1); for b=0 each pair output o_{v,u} is dead (≡ x_u).
**R0.** If at most one set through v has size ≥ 3, then #dead(x_v:=0) ≥ deg(v) = loss of base.
Proof. Sets through v: w0 (size ≥ 3, if any) and pairs {v,u_j}, j=1..p; the p pair outputs are dead and distinct. If no w0, done. Else suppose no further dead gate. Every direct reader of x_v is some o_j = x_v∘c; AND is impossible (o_j(e_{u_j})=1), so o_j = x_v ∨ c with c|ρ = x_{u_j}; if c is a gate it is dead and differs from every other o_j', contradiction; so c = x_{u_j}. Put x_{u_j}=1 ∀ j, all else 0: no wire changes when x_v is toggled, but OR(S_w0) does (u_j ∉ S_w0). Contradiction. ∎
**R0'.** (with small3) 951 holds for every system whose CORE (iterate: delete a point lying in ≤ 1 set of current size ≥ 3; drop sets of size ≤ 1) has no 4-set. A minimal counterexample (minimal n) satisfies
- (N1) every point lies in ≥ 2 sets of size ≥ 3;
- (N2) ∀ v: #(direct readers of x_v) ≤ #dead(x_v:=0) ≤ deg(v) − σ, σ = base − s ≥ 1;
- (N3) ∀ v: #(gates ≥ x_v) + #(unread after x_v:=1) ≤ Σ_{w∋v} d_w − σ.
(N2/N3 are CHECKED-level quantifications from the R0 proof; the Lean form is `r0_step`/`HardCaseCore.hcore`.) Structure of a degree-2 point in a minimal counterexample (from N2): exactly one gate r reads x_v; r = x_v∨c with c a non-constant x_v-free gate, c ≤ OR(S_a\v)∧OR(S_b\v); or r = x_v∧c with c(0)=1 downstream of N; r = ¬x_v gives h = x_v.

### 3.4 E0.1 conflict lemma (PROVED-PAPER, Fable E)
Notation: for z vanishing on S_w, system Σ(z); I^L_z(w) = {g ∈ cnt_z(w) : g ≤ OR(S_w) on the cube {x ≥ z}}; I^U_z(w) = P_w ∩ cnt_z(w); I_z = I^L ∪ I^U. Let w ≠ w'.
- (a) I^U_z(w) is disjoint from I_{z'}(w') for all z, z'.
- (b) If g ∈ I^L_z(w) ∩ I^L_{z'}(w') then [z ∩ S_{w'} ≠ ∅ or some u ∈ S_w has h(z+e_u)=0 and h(z∨z'+e_u)=1] and the same with (w,z),(w',z') exchanged.
- (c) For rule z ∈ {0} ∪ h^{-1}(1): (0,0) never collide; (heavy z, heavy z') collide only if z hits S_{w'} and z' hits S_w; (z=0, heavy z') only if z' hits S_w.
- Corollary: if z_w ∈ {0} ∪ h^{-1}(1) are chosen with no pair w≠w' having (z_{w'} hits S_w and (z_w=0 or z_w hits S_{w'})), then the I_{z_w}(w) are pairwise disjoint and s ≥ Σ_w min(d_w, |I_{z_w}(w)|).
No function-level pair budget beyond (b) exists (g_j = x_{c'}∧(partial OR S_w) ∨ x_c∧(partial OR S_{w'}) gives arbitrarily many shared gates). CHECKED w9/fe/rel.py: 0 violations of (a),(b) on cx1,cx2,cx3,cfgI,cxr,cxtw3c,cxe3,badT,bad,c.jsonl[:400].

### 3.5 Heavy-point bound (PROVED-PAPER, Fable E, E3)
For heavy v (h ≥ x_v): **s ≥ 1 + Σ_{w∌v} d_w + Σ_{w∋v} |P_w|.** (Sets avoiding v: systems (z_{S_w}; atoms e_u+e_v) are legal and pairwise separated, giving Σ_{w∌v} d_w distinct counted gates; P_w for w ∋ v is disjoint from them since g ∈ P_w, g ≥ x_v gives g(z_{S_{w'}})=1; N is counted by none.)

### 3.6 Theorem X+ (A2) and crossing lemma (PROVED-PAPER, Fable A; CHECKED on 734 signatures)
U0 = {h=0} (down-set), U1 = {h=1} (up-set); x ≤ y is *crossing* iff x ∈ U0, y ∈ U1.
- (A2.1) If x ≤ y is not crossing then every wire has w(x) ≤ w(y) in the real circuit.
- (A2.2) For systems s_a=(z_a; atoms p_u; K_a), s_b: blocked set P(a|b) = {u ∈ S_a : p_u ∩ Zero(z_b) ≠ ∅ or (p_u ∈ U0, z_b ∈ U1, neither system mono)}. Every wire g ∈ K_a∩K_b with g(z_b)=0 has B_a(g) = {u : g(p_u)=1} ⊆ P(a|b).
- (A2.3) **Theorem X+.** If for every pair a≠b, |P(a|b)| ≤ 1 or |P(b|a)| ≤ 1, the counted sets are pairwise disjoint (Gap-G), so s ≥ base. Theorem X is the case z=z_Q ∈ U0, unit atoms, P(a|b)=S_a∩Q_b.
Data: of 734 distinct signatures, 708 have a Theorem X family; of the other 26, 25 have an X+ family; the remaining class (n=5, {0,2,3},{1,2,4}, h=x0|x1) is covered by T1.

### 3.7 Pair budget (A3) (PROVED-PAPER, Fable A)
Union-find over gates in order for one system: a gate g with g(z)=0 whose B(g) meets two blocks merges them; exactly d = |S|-1 merge gates M (each an OR). **Lemma:** #{g ∈ M_a : g(z_b)=0} ≤ (|P(a|b)|−1)^+; in particular |M_a ∩ cnt_b| ≤ (|P(a|b)|−1)^+. **Corollary:** for Good systems, s ≥ |∪ M_w| ≥ base − Σ_{a<b} min((|P(a|b)|−1)^+, (|P(b|a)|−1)^+).

### 3.8 Two-set Hall (A5) (PROVED-PAPER, Fable A)
If |P(a|b)| ≤ 2 and |P(b|a)| ≤ 2, and each system's atoms meet the other set in at most one atom (e.g. unit atoms), then |cnt_a ∪ cnt_b| ≥ d_a + d_b. (I = cnt_a∩cnt_b; every g ∈ I has B_a(g) = P(a|b), so at most one g ∈ I is a merge of a; |cnt_a| ≥ d_a+|I|−1, same for b, union ≥ d_a+d_b+|I|−2. If |I|=1 and the union is short both sets are tight, all counted gates lie in the pure-OR tree under o_a, hence in L_a, contradicting A4(1).)

### 3.9 Conflict lemma C for relative classes (PROVED-PAPER, Fable B)
D_i^v = {g : g ≤ OR(S_i) on {x_v=1}, g(e_v+e_u)=1 for ≥ 2 u ∈ S_i}, v ∉ S_i (counted by i in Σ(e_v)).
(a) same v: D_i^v ∩ D_k^v = ∅ for i≠k. (b) D_i^v ∩ D_k ≠ ∅ ⇒ v ∈ S_k. (c) D_i^v ∩ P_k ≠ ∅ ⇒ S_k = {s,v} is a pair. (d) different heavy v≠v': D_i^v ∩ D_k^{v'} ≠ ∅ ⇒ v ∈ S_k and v' ∈ S_i. (e) for (II') with shared C the admissible v are V_i = {v ∉ S_i : C ≥ x_v}, R_i|_{x_v=1} = OR(S_i). Also: if C ≥ OR(S_j) then R(x) = OR(S_i)(x) for every x hitting S_j.
Not proved: a Hall argument over the choice of v (the regress has no function-level end).

### 3.10 B3 menu and companions (PROVED-PAPER, w8_hall_b)
- B1 privacy of pure gates: g ∈ cnt(w)∩cnt(w') (unit systems) ⇒ B_w(g) ⊆ S_w∩Q_{w'}, B_{w'}(g) ⊆ S_{w'}∩Q_w.
- B3 Σ(z) is a legal TestSys for every z vanishing on S_w (no reference to h, cones or hardness).
- B4 common-minterm separation: hard sets a,b avoiding one common minterm M of h: systems (z_S; atoms e_u+1_M) have disjoint counted sets.
- B7 top-down accounting (explains both canonical and R* failure modes).
- B8(1) Rado is strictly stronger than Hall here (no help). B8(2) the free-choice statement "∃ z_w with Hall for cnt_{z_w}, K=all" is padding-monotone. **B8(3) minimality**: deleting the outputs of a family F leaves a correct circuit for the rest; so in a minimal counterexample, for every proper F, #(gates in no cone outside F) < Σ_F d_w. No data circuit satisfies B8(3) (checked, fb/irr.py), so it cannot be tested on data.

### 3.11 Other PROVED-PAPER facts
- Exactness/restriction lemma (Fable B "L"): C0|ρ computes o_w|ρ iff h ≥ o_w on ρ; C1|ρ computes o_w|ρ iff h ≤ o_w on ρ. If h|_{x_k=1} ≥ o_w ∀ w∌k then C0|_{x_k=1} is a monotone circuit for {o_w : w∌k}, so s ≥ 1 + fanout(x_k) + Σ_{w∌k} d_w.
- Function-level two-world Theorem X (Fable C, C3; depends only on (sets,h)); reduction for triples (C2): outputs are private; for triples free-choice MatchG ⇔ FracMatch ⇔ the merge-gate sets M_w have an SDR; t=2 impossible.
- Fable A, A2.1/A1: merge-record analysis; in the R* world one gate may be a merge for arbitrarily many systems.
- Fractional/integral note: with one system per set, fractional = integral (bipartite b-matching is integral); only mixing zero points adds power.
- CHECKED (not proved): fractional LP data (w9/fraclp.py): cx1 0.41, cx2 0.55, cx3 0.50, cxr 0.55 (L* ≤ 1 needed); badT, bad, c.jsonl, w5ess, triple-heavy essential dumps (1,767): free-choice FracMatch L* ≤ 1 everywhere; L*=1.0 only when a set's sole counted gate set is forced private (not a conflict). Exhaustive SAT pool encodings UNSAT (triangle s=7..13, Pasch s=9,10, two 4-sets s=8,9; h=x1x2|x4x5 s=9..12; maj|maj s=10..12; free h s=8,9).
- CHECKED: Rule R1: #(gates N or downstream of N counted by no set) ≥ excess+1 on all data; ~800k raw circuits, 335k used for cone-D: Σ_w min_Q |D_cone| ≤ s−1 always; no live-NOT circuit of size ≤ base+1 in tested systems.

## 4. Refuted statements (do not retry)

| tag | statement | counterexample / file |
|---|---|---|
| REFUTED | Canonical-choice Hall (smallest Good Q, cone, unit atoms) | cx1 (n=9), cx2 (n=7, sunflower {0,1,4},{0,2,5},{0,3,6}, s=18; a family's counted union 5 < demand 6), cx3: `w8/` (cx1-cx3, allsys.py, verify.py). B2 example in w8_hall_b |
| REFUTED | Rule R* (z_w = z_{S_w}, atoms z+e_u, K = all) | cxr: n=8, 4-sets {0..3},{4..7}, "inner-product" design, s=24: `w8b/cxr.py`, `w8b/cxr.json` (cnt union 5 < 6) |
| REFUTED | Two-world Hall / fixed 1/2–1/2 "coin-flip NOT" rule | cxtw3c: `w9/tw/cxtw3c.json` (n=9, s=34, base 7; mixrule a=0.5 → 1.5; TWH: demand 4t, supply 3t+2); t=4 `cxtw4c.json` L=2.0; verified independently (Fable A A1). Has a Theorem X family, so outside the sorry case |
| REFUTED | Coin rule inside the sorry's case | cxE: `w9/fc/cxe3.json` (n=7, s=45, base 10; coin rule 1.5; no pairwise zero-set family, 5 hard N-sets, DD exists; free-choice FracMatch 0.4545) |
| REFUTED (restricted reading only) | Relative sandwich rule with z = 0 or minimal 1-points of h | cxT4: `w9/fc/cxT4.json` (n=15, s=47, base 15; L_rel 1.333). Under the rule as implemented (z any point vanishing on S_w of weight ≤ 2, P_w function-level private-above) L_rel = 0.706: not refuted. Free-choice FracMatch 0.44; not a core system |
| REFUTED | Full (non-cone) D counting / full-D ChargeOK; clean-only ChargeOK | 3 counterexamples (HANDOFF §3) |
| REFUTED | "No gate ever double counted"; per-read substitution of N; Wegener-style top-down AND elimination; first-kill-AND injection; variable-fixing induction (fan-out < degree) | HANDOFF §3 |
| REFUTED | Gap-G and Two-World at FUNCTION level (choice depending only on (sets,h)) | K4, h minterms {02,12,03,13,23} (9/1162 at n=4, 4569/197054 at n=5) |
| REFUTED | Type-B-only test systems | K4, h=Th_2, s=41, excess 9 |
| REFUTED | Rado instead of Hall helps | B8(1): Rado ⇒ Hall exactly |
| REFUTED as method | A3 on the relative systems Σ(e_v) (pair budget vacuous); one-variable induction (K) without stronger hypothesis; x_v=1 induction | twh_fableE E2/E3; twh_fableB C |
| REFUTED | PRIV "each set has a system with d_w gates counted by no other set in ANY system" | fails on cx3, cxE, 1/63 badT, 3/160 bad |

Surviving (unrefuted) statements: free-choice FracMatch/MatchG; "RULE-AC" (canonical unless a canonical-counted gate is shared, then R*) and RULE-3 (0 failures on all data); relative sandwich rule as implemented.

## 5. The exact open statement

`HardCaseCore` (`Core.lean`, front-r0 ba4d780) has 20 hypotheses; `L_meta_951_of_core : HardCaseCore → 951`. Everything except the problem itself is a consequence of minimality plus a proved lemma:

| hypothesis | meaning | source |
|---|---|---|
| hg, hU, hev, h2, hS | fan-in ≤ 2, ≤ 1 NOT, outputs OR(S_w), \|S\| ≥ 2, pairwise \|∩\| ≤ 1 | statement |
| hlt | s < base | counterexample |
| hclean, hlive | no gate equals an earlier wire; every gate read or output | cleanup reductions |
| hC0, hC1 | NOT essential (C0 and C1 both wrong) | removable-NOT reduction |
| hz | h(0) = 0 | NOT-dead case |
| hhard, h1, h1N | ≥ 2 hard sets, ≥ 2 hard N-sets | all-easy / Theorem X (≤ 1 hard) |
| hC | no Theorem X zero-set family | Theorem X (cone) |
| hDD | some DD set | Two-World |
| h4 | some \|S\| ≥ 4 | small3 |
| hcore | every point of a set lies in ≥ 2 sets of size ≥ 3 | R0' |

**Open statement ("no minimal counterexample").** There is no system and no correct one-NOT circuit with s < base satisfying all of the above, equivalently (planned refactor) `no_minCE : ¬ MinCE S gates out`, where IsCE = problem hypotheses ∧ hlt and MinCE = IsCE minimal in (gates.length, Σ|S_w|) lexicographically. Sufficient: free-choice MatchG/FracMatch (equivalently PriceIneq) for such circuits (Lean bridges are PROVED-LEAN, section 2).

**Minimality facts usable as hypotheses** (all PROVED from minimality + lemmas above):
1. clean, live, essential NOT, h(0)=0, ≥ 2 hard N-sets, no Theorem X family, a DD set exists, some |S| ≥ 4 (table above).
2. (N1) every point lies in ≥ 2 sets of size ≥ 3.
3. (N2) #readers(x_v) ≤ #dead(x_v:=0) ≤ deg(v) − σ; (N3) #(gates ≥ x_v) + #(unread after x_v:=1) ≤ Σ_{w∋v} d_w − σ, with σ = base − s ≥ 1.
4. (B8(3)) for every proper family F of outputs, #gates outside every cone of F^c < Σ_F d_w.
5. (Heavy point) h ≥ x_v ⇒ s ≥ 1 + Σ_{w∌v} d_w + Σ_{w∋v} |P_w|.
6. Every set has |P_w| ≥ min(d_w,2); all |S| ≤ 3 sets are fully served (T1/small3); residual demand only from |S| ≥ 4 below a mixed cut: configurations (I) and (II').
Smallest open systems: n=8 {1234},{156},{257},{367},{458},{268} (base 13; exhaustive SAT at s=12 not run) and the 4×3 grid (n=12, base 17). Conjecture ★ (Fable E, untested, unproved): #gates outside J^L ∪ J^U ≥ base, with J^L = gates ≤ OR(S_a)∧OR(S_b) (a≠b), J^U = gates ≥ two different sums (disjoint from all Π_w, PROVED).
No counterexample to FracMatch or to s ≥ base has been found anywhere.
