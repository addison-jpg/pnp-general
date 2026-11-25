# deg3_fable.md — global arguments for systems with min degree >= 3 (V1 = ∅; PG(2,3)), restart-safe log
Code: w9/deg3/. Tags PROVED (paper, by me, unrefereed) / CHECKED / CONJECTURE / REFUTED.
Notation as PROVED_951.md: Π_w = D_w ∪ P_w (T3 classes, pairwise disjoint), N = ¬h, U0 = {h=0}, U1 = {h=1}, σ = base − s.

## D0 Orientation (what is already settled inside the "degree >= 3" family) — PROVED by existing Lean/paper results
- AG(2,3), Fano, every 3-uniform system (any degrees): all |S| <= 3 ⇒ small3_bound. So "min degree >= 3" is open ONLY with a set of
  size >= 4; PG(2,3) (13 lines of size 4, base 39) is the smallest symmetric open case.
- Corollary E' (T3 classes disjoint, N in no class): s >= 1 + Σ_w min(d_w, |Π_w|). For a 4-UNIFORM system (PG(2,3)):
  call w DEFICIENT if |Π_w| = 2 (then w is hard), δ = #deficient, FREE gate = gate ≠ N outside ∪Π_w, f' = #free. Then
      s = 1 + Σ|Π_w| + f'  >=  1 + base − δ + f'.          (ID4)
  So for PG(2,3): 951  ⇐  f' >= δ − 1 ("free gates pay for deficient lines"), and a counterexample needs f' <= δ − 2, δ <= 13.
