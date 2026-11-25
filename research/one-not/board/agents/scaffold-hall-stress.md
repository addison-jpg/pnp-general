# scaffold: stress of the matching / FracMatch / mix-rule targets (Nov 24, 04:10)
Checks (front's scripts unchanged, chained per circuit): canonical Hall (hallcheck) -> R* (rstar) -> full menu
(allsys.menus, backtracking) -> FracMatch LP (fraclp, L* <= 1) -> mix rule a=0.5 (mixrule).
- ~16,100 saved essential/BAD circuits (graphs, K4, C5, random, atlas n=4..6): canonical and R* OK on all.
- coord's fixh16 (7,200 K4, forced obstruction h, essential): canonical and R* OK on all.
- 1,767 triple-heavy essential-forced circuits (sunflower {0,1,4},{0,2,5},{0,3,6} base+8..11, Pasch, two triples):
  canonical, R*, FracMatch, mix all OK; max L* = 1.0 (949 circuits, forced: |C| = |S|-1), max mix = 1.0.
Status: 0 counterexamples to MatchG / FracMatch / mix rule. Canonical Hall refuted only by front's cx1-3 (and R* by cxr).
Running: sunflower 16-17 (coord 18-20), Pasch, two triples; adversarial hill-climb (insert/reroute gates keeping
correctness + essential, maximise (L*, mix)) from cx1-3 and 60 tight triple circuits.
Code: scaffold-951 work/notes951/scripts/scaffold_runs/ (allmenu.py, climb.py added next push).
- UPDATE 04:30: 6,014 triple-heavy essential circuits, 0 failures; every L* = 1 case (2,799) is FORCED (a set whose
  options all have |C| = |S|-1); none unforced. Generators paused for #2 (Fano).
- UPDATE 05:30, tractability's relative-sandwich rule (relrule WT=2): adversarial climb maximizing (L_rel, cross-set
  collisions), feasible mutants only, 2 passes x ~38 seeds x 4000 steps: no L_rel > 1; every L_rel = 1 final (33) is
  forced (single-set |item| = d); cross-set collisions up to 25 gates per circuit. Code: scaffold_runs/climbrel.py.
