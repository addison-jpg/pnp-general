# w9 TWO-WORLD HALL log (restart-safe)

## T0 tooling (w9/tw/tw.py)
Dc_w = canonical: smallest Good Q ⊇ S_w (hallcheck order), cone-restricted, UNIT atoms e_u (g(z_Q)=0, g(e_u)=1 for >=2 u).
Dr_w = R*: z_{S_w}, atoms z_S+e_u, all gates. Two-world Hall checked as integral b-matching: nodes (w,c),(w,r) demand d_w,
gate capacity 2, each system uses a gate at most once (= half-weight LP by integrality).
NOTE: an early version used z+e_u atoms for canonical too: then cxr fails (Dc=Dr for easy sets). Fixed; mixrule.py's canon
uses unit atoms (correct).

## T1 CHECKED (data)
cx1,cx2,cx3,cxr,badT,bad,tri_ess,cross5,cross5f: 120 circuits with a set of size>=3: two-world 120/120, union-Hall (F_c=F_r) 120/120,
canonical Hall 117/120, R* Hall 119/120. chk/c.jsonl: 1681 circuits with a triple: all four statements hold (data is weak:
no canonical or R* failure there). Graph-only data is vacuous (R1: o_w private, in both worlds).

## CORRECTION (from coordinator) — target statement
2|∪D| >= Σd is only necessary. Exact condition (edge cap 1 per (system,gate), gate cap 2, demand d_x per system x=(w,c)/(w,r)):
  TWH: for every family X of systems: Σ_{x∈X} d_x <= Σ_g min(2, deg_X(g)) = |N(X)| + #{g counted by >=2 systems of X}.
tw.py's bmatch already enforces "one unit per (system,gate)" + cap 2, so it decides exactly TWH (T1 counts are for TWH).

## T2 REFUTED: TWO-WORLD HALL (and the 1/2-1/2 coin rule) — verified counterexample cxtw (w9/tw/cxtw.py, cxtw3c.json, cxtw4c.json)
Design (t triples, sunflower S_i={0,i,i+t}, main vars 0..2t, gadget set {a,b} on 2 fresh vars):
  h = OR_i AND_{v main, v∉S_i} x_v   (h(0)=0, h(z_{S_i})=1: all triples hard; all units light h(e_u)=0)
  T = AND(x_{t+1..2t}) ∧ Th_{t-1}(x_1..x_t)   (T <= h, monotone, no N)
  G = x0 ∨ T ;  m_i = x_i ∨ (x_{i+t} ∧ N) ;  o_i = G ∨ m_i ;  gadget o_c = ((a∧h)∨b∨N) ∧ ((a∨h)∨b)  (cx1 gadget)
Correctness (PROVED): o_i <= OR(S_i) since T<=x_{i+t}. Conversely only x0=x_i=0, x_{i+t}=1 needs care: if h=0, N=1 gives m_i=1;
if h=1 then zeros(x) ⊆ S_j for some j, containing 0,i ⇒ j=i ⇒ zeros ⊆ {0,i} ⇒ T=1.
Worlds: canonical Q_i = S_i+1 extra point (N=1 at z_Q and at all units): Dc_i = {m_i, o_i} (private).
  R*: at z_{S_i}+e_u (N=0): m_i has block {i} only (x_{i+t}∧N ≡ 0); G has block {0,i+t} (T(z_{S_i}+e_{i+t})=1): Dr_i = {G, o_i}, G SHARED by all t triples.
TWH for X = all 2t sunflower systems: demand 4t; supply Σ min(2,deg) = 2t (outputs) + t (m_i) + 2 (G) = 3t+2 < 4t for t>=3.
CHECKED (code): t=3: n=9, s=34 after cleanup, base 7: correct, clean, all read, C0 wrong, C1 wrong. Dc=[[29,30],[32,33],[35,36],[41,42]],
  Dr=[[27,30],[27,33],[27,36],[38,39,42]]; b-matching 13 < 14. mixrule.py: L=1.5 (>1, coin rule FAILS). t=4: s=51, L=2.0.
  fraclp.py (full Lean menu, all-gate and cone): L*=1.0 (ok) — FracMatch with free choice survives (support: canonical for all triples).
CAVEAT: Theorem X family EXISTS here (Q_i = S_i ∪ {i+1 mod t}, cyclic; Q_c = S_c ∪ {1,2}), so this circuit is outside the
Lean sorry's case (which assumes no pairwise zero-set family). Next: try to kill the family too.
