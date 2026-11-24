# research: negation-limited Fourier/influence bounds and the polynomial method — do they give gate counts for 951?
(owner request via front, 2026-11-24 ~09:45; report to front + coord)

Status words: TXT = read in the paper's text; MEM = standard result from memory; PROVED = short argument given here.

## 1. Verification of the claim (TXT: Blais, Canonne, Oliveira, Servedio, Tan, 'Learning circuits with few negations',
##    arXiv 1410.8420 = ECCC TR14-144; APPROX/RANDOM 2015, LIPIcs 40)
- Thm 1.1: f is k-alternating (at most k value changes along any increasing chain) iff f = h(m_1, ..., m_k) with every m_i
  monotone and h = PARITY or its negation (a Markov-style extension).
- Cor 1.2: every f computed by a circuit with t NOT gates (class C_t^n) is f = h(m_1, ..., m_T), h = PAR or ¬PAR, m_i monotone,
  T = O(2^t) (by Markov, f is (2^{t+1} - 1)-alternating).
- Influence (§3, derived inline, not a numbered theorem): monotone f has Inf(f) <= √n (Bshouty-Tamon), so by Cor 1.2 and a union
  bound every f ∈ C_t^n has Inf(f) <= O(2^t)·√n; hence Σ_{|S| > O(2^t)√n/ε} f̂(S)^2 <= ε (low-degree concentration).
- Thm 1.4: C_t^n is learnable under the uniform distribution in time n^{O(2^t √n / ε)}. Lower bounds: Cor 3.5/3.6 (2^{Ω(2^t √n/ε)}
  membership queries for t <= (1/28) log n); Thm 1.3 (almost every f needs (1/2) log n - O(1) NOTs even to 0.01-approximate).
=> The claim as stated (t NOTs => total influence O(2^t √n), via Markov's decomposition) is CORRECT.

## 2. Does any of this give a GATE-COUNT lower bound usable for 951? Honest answer: NO.
(a) These are statements about the FUNCTION computed, not about the circuit. In 951 every output is the fixed monotone function
    OR(S_w) (Inf = |S_w| 2^{1-|S_w|} <= 2, Fourier degree |S_w|), whatever the circuit; a function-level bound cannot separate a
    circuit of size base - 1 from one of size base. (PROVED, trivial.)
(b) Internal wires: every wire of a one-NOT circuit is in C_1^n, so it is PAR of at most 3 monotone functions, i.e.
    w = W(0, x) ∨ (W(1, x) ∧ ¬h(x)) with W monotone (Markov / Jukna BFC Lemma 10.7; Amano-Maruoka's 2^{t+1} - 1 = 3 functions).
    This is EXACTLY the team's two-world split (C0 on {h = 1}, C1 on {h = 0}, plus h): Cor 1.2 at t = 1 adds nothing beyond it.
(c) Influence/degree are not monotone in size in any usable way: one fan-in-2 gate can raise total influence from O(1) to
    Θ(√n) or Θ(n) (e.g. AND of two large ORs; a single XOR-like pair), and OR(S) has Fourier degree |S| with |S| - 1 gates. No
    known theorem turns influence, Fourier degree or sparsity into an EXACT count of fan-in-2 gates. (MEM)
(d) What the learning results do say: one NOT costs at most a factor 2 in the Fourier tail (2^t with t = 1); that is a statement
    about learnability / approximation, consistent with 'one NOT saves nothing' but not implying it.

## 3. The polynomial view (n copies of {±1}, x^2 = 1; every circuit computes a multilinear polynomial)
- Where the polynomial method gives lower bounds (MEM): Razborov 1987 / Smolensky 1987: AC0[p] (constant depth, unbounded fan-in,
  MOD_p) needs exponential size for MOD_q / MAJORITY, via low-degree approximation over F_p; Minsky-Papert and threshold/sign
  degree (perceptrons, Beigel-Reingold-Spielman); approximate degree for AC0 and query complexity. All are for DEPTH- or
  DEGREE-restricted models; none gives exact counts for unrestricted fan-in-2 circuits.
- Barriers (repo rows): natural proofs (L-lib-086, Razborov-Rudich) — Razborov-Smolensky is a natural proof, so this style
  cannot prove P/poly lower bounds if strong PRFs exist; algebrization (L-lib-065, L-lib-076, Aaronson-Wigderson, ACM TOCT 2009,
  doi 10.1145/1490270.1490272) — arithmetization-based techniques for UNIFORM class separations algebrize and cannot settle
  P vs NP. For 951 itself (a fixed restricted-model statement) neither barrier applies, but neither tool counts gates.

## 4. Recommendation
Do not pursue Fourier/influence/polynomial methods for 951's exact bound. The only part of this line that is already used is
Markov's t = 1 decomposition, which the two-world split, Amano-Maruoka Fact 3 (research-lit.md) and the lifted form already
contain. Effort is better spent on MergeSDR structure (research-hypergraph-hall.md: the 2-SAT / implication-cycle target).
