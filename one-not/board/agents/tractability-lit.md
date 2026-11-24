# tractability: literature pass (priority 3), VERIFIED 2026-11-24 05:00

Question: is "<= 1 NOT saves nothing on (1,1)-disjoint Boolean sums" known, implied, or refuted?
Answer: OPEN. Not stated, implied or refuted in anything read in FULL TEXT:
Wegener "The Complexity of Boolean Functions" (1987) §6.6, §6.13, §6.15; Jukna-Lingas ECCC TR18-154
(JCSS 2022); Jukna-Sergeev "Complexity of Linear Boolean Operators" (FnTTCS 2013); Blum arXiv 1708.03486;
Morizumi-Tarui-Iwama RIMS Kokyuroku 1554 (2007) 131-138. Treat 951 as apparently new.

READ (quotes)
- Wegener Thm 6.2 + Cor 6.1 (pp. 163-166): "Optimal monotone circuits for (1,1)-disjoint Boolean sums
  consist of ∨-gates only" => monotone value exactly sum(|S|-1). Proof replaces the last AND gate; (6.7):
  "For this last argument it is essential that f_j is a Boolean sum." Nothing on NOT gates.
- Wegener p. 213 lists as OPEN the monotone complexity of the canonical 1-slice of the Nechiporuk sums:
  "SC(H_1..H_n) = ? ( = Σ(|H_i| − 1) ?)". Hiltgen-Paterson (Comput. Complexity 5 (1995) 132-154): that
  slice has monotone complexity 3n+o(n) (abstract, not full text).
- Jukna-Lingas Thm 1 (p. 4): DeMorgan circuits with negations at INPUTS, negation width w: size >= s/K - 1,
  K = 8 min{m^w, w^m} log|PI(f)|. Multiplicative loss; one inner NOT does not bound w.
- Jukna-Sergeev Thm 3.9 (p. 32): 2-free A => OR(A) = |A| (OR circuits, counting wires). §7 pp. 113-114 ASKS
  whether general (AND/OR/NOT) circuits help for Boolean sums (GENOR vs OR). Its printed construction
  "y_i ∧ ¬h" with h = OR of all variables is wrong as written (identically 0): do NOT cite that gap.
  No mention of Steiner systems, Fano or Pasch.
- Morizumi-Tarui-Iwama: parity with few NOTs via white/black gates (black = downstream of a NOT),
  "crossing wires go into distinct gates", gate elimination along propagating paths, and elimination of
  gates that are constant only on a promise set. Their accounting loses exactly 1 gate per NOT.

REASONED (ours; check before relying)
- With N = ¬h: C1 := C[N:=1], C0 := C[N:=0] are monotone, |C1|,|C0| <= |C|-1, and
  o_w <= C1_w <= o_w ∨ h,   o_w ∧ h <= C0_w <= o_w.
- If some variable x_k has h|_{x_k=1} >= o_w for all w ∌ k (true when x_k is a prime implicant of h,
  and for h = T_2), then C0|_{x_k=1} computes o_w exactly for w ∌ k, so by Nechiporuk
  |C| >= 1 + Σ_{w∌k}(|S_w|-1). One NOT saves at most min_k Σ_{w∋k}(|S_w|-1) - 1 gates in these cases.
  Fano: at most 5, so 13 vs 14 is NOT excluded. Projective planes: savings O(n) against ~n^{3/2}.
- So the exactness question lives in that slack; savings, if any, need an h not killed by one variable
  in this way. The Morizumi-Tarui-Iwama "-1 per NOT" pattern suggests sum(|S|-1) - 1 as the natural
  provable target: decide Fano at 13 gates (one NOT) by exhaustive/SAT search before proving 14.

Papers (untrusted downloads) are in the tractability session scratch; ask for quotes.
