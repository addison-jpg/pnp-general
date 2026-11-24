# scaffold: free for downstream collaboration (06:30)
Owner asked scaffold to stop its compute and offer downstream help to front, in particular toward the P = NP subproblem
team (L-meta-612 board `board-612`, Lean `s612`; seat session_01GmnDheoRytFdZ9LUQXmuGK, coord session_01GmnDhckSb9NEwzEy2e7UWf).
What scaffold can do (4 cores, Opus/Fable/Sonnet agents):
- exact SAT on circuit sizes: one-NOT / monotone, exact size with padding (tools/w951 sat.build_channel = scaffold chan_sat),
  incl. graph edge functions f_G = OR_{uv in E} x_u x_v (612: C4-free G, claim >= |E| + tau - 1 monotone gates);
  enumeration of all optimal circuits; counterexample search (SAT, adversarial hill-climb, constructive Fable agents).
- stress-testing candidate lemmas on generated circuit data (charging / matching / LP rules), with re-checks via tools/w951.
- 951 leftovers available on request: uncovered-frontier SAT (scaffold-core-sat.md, restartable).
Ask: front, which downstream piece should scaffold take (612 or another subproblem), and who on that team to coordinate with?

## 06:35 lane (front's suggestion): L-meta-612 SAT / cross-check, with the P = NP subproblem team
Contacts: seat session_01GmnDheoRytFdZ9LUQXmuGK (board-612 / s612), its Research seat session_01GmnDhfeNJTFgW7ismYzbXh (girth 3/4).
Tasks: (1) cross-check synth2.py exact sizes for f_G on the 16 connected girth >= 5 graphs, n <= 6, with scaffold's encoder;
(2) girth >= 5 sweep at n = 7, 8 (Petersen, Heawood targets), monotone vs NOT column; (3) report any graph where NOT saves.
Privacy: their branches are public; nothing 951-specific goes to them. Status: waiting for the owner to restart scaffold compute.

## 06:50 owner: make the 612 team's public branches private ("if its not a huge deal to them")
- board-612 and s612 are already private (pequalnp-work).
- Mirrored the public-fork copies into pequalnp-work, same SHAs:
  - mirror/zealous-gates-i75uba (dd5fa81, pnp-subproblem seat)
  - mirror/happy-hypatia-zz54tp (81cc8b0, its Research seat)
  - mirror/funny-maxwell-o4s4k1 (25060e0, session_01GmnDhczcdJyEX4WwHrrzPx; owner of this session not confirmed)
- Asked both seats to push only to pequalnp-work, and to OK deleting the public copies.
- Public copies have NOT been deleted yet.
- 07:00 pnp-subproblem relayed the owner's "Yes, delete mine" for claude/zealous-gates-i75uba (public tip = mirror = dd5fa81, verified).
  The deletion from scaffold failed: git push --delete was disconnected, and the REST DELETE was blocked by the session permission check.
  The public branch is still present; the owner has been asked to delete it on GitHub by hand.
- 07:05 Research seat moved private: mirror/happy-hypatia-zz54tp now 2054137 (its newer commits), future pushes pequalnp-work only. Public claude/happy-hypatia-zz54tp still present (its proxy refuses deletion); left to the owner.
- 06:18 owner directive (via warden): all compute and subagents off except pnp-subproblem's; 612 SAT lane NOT started. Encoder fg_sat.py ready in scaffold's scratchpad.
