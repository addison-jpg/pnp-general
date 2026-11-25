# tractability: dual prices for FracMatch (2026-11-24 05:15). Status: checked on data, rule CONJECTURE.
Code + instances: branch `tractability`, work/duals/ (README there).
- Free-choice L* <= 1 everywhere tested: cx1 .41, cx2 .55, cx3 .50, cxr .55, cfgI .35, ce1-3 ~.30,
  cxtw3/3c 1.0 (forced: a triple whose every counted set has exactly 2 gates), ~4.5k climb mutants.
- Plain optimal duals are 0/1 and uninformative (uniform, or unit mass on a forced private output).
- Restricted-world duals (menus split by h(z), h = NOT input): obstruction prices sit ONLY on monotone
  gates not downstream of the NOT lying in several output cones (h, gates below h, h∨x_c, x0∨T);
  never above the NOT. cx1 h(z)=0 world alone: L=4/3 on {g12,g13=h,g15=h∨x0}; cxtw3c h(z)=1 alone: L=3 on g27.
- Escape for the AND-output 4-sets: the OR chain N∨x0∨x1∨... in the h-live world (z = e_v, v in another set).
- CONJECTURED RULE (relative sandwich): for w and z vanishing on S_w, system Σ(z) (unit atoms, K=all), charge
  I_z(w) = {g in cnt_z(w) : g <= OR(S_w) on the cube {x >= z}} ∪ (P_w ∩ cnt_z(w)), z = 0 or a minimal 1-point of h
  off S_w of WEIGHT <= 2. Price target: Σ_w min_z cheapest_{d_w}(π, I_z(w)) <= Σπ (pool gates never enter I_z).
  Holds (L_rel <= 0.75, 1.0 only single-set tight) on all data incl. 2,429 rule-breaking mutants.
  Weight-1 z FAILS (inst/relfail1, needs e2+e3); z = 0 alone fails; naive exclusive-cone rule fails (inst/xfail1).
- NOT tested: two sets' relative classes colliding (front's open cross-set conflict); weight-2 rule not
  properly climbed against. Next: adversarial climb targeting cross-set collisions of I_z(w).

## CORRECTION 05:20 (exact rule = relrule.py; the summary above misstated z)
- z ranges over ALL points vanishing on S_w of weight <= 2 (h does not choose z).
- I_z(w) = {g : g(z)=0, g(z+e_u)=1 for >=2 u in S_w, g <= OR(S_w) on {x >= z}} ∪ {g in P_w : same counted cond.},
  P_w = resid.private (function-level private-above), NOT the sandwich class.
- cxT4 (front, L_rel = 1.333 under the "minimal 1-point of h" + sandwich-class reading): exact rule gives 0.7059
  (WT 3/4: 0.667). So the restricted reading is refuted, the coded rule is not; free choice of z rescues cxT4.

## 05:30 scaffold pass 2 (collision-maximizing climb, feasible mutants, 37 finals saved)
- No L_rel > 1. L_rel < 1 in 4 finals, = 1 in 33, and ALL 33 are FORCED (some set has only items of size |S|-1).
- Zero unforced L_rel = 1 although cross-set collisions grew to 25 gates. Rule (exact relrule.py semantics) survives.
- Implication for G2: only forced single-set tightness occurs; a proof can treat forced sets separately (their items
  are exactly d_w private-above gates) and needs slack elsewhere.
