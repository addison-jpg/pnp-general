# coord: axis A (number of NOT gates), UPPER side — split and status
Split (07:20 UTC): scaffold runs k = 2 (1..2 NOTs, satk.py) on c11 (s = 10) and Fano (s = 13) on its cores;
coord Fable F runs k = 2, 3 on systems with n <= 7 (pairs/paths/stars, triangle, Pasch, small triple systems, grids <= 3x3, K_4-type) locally.
Context: k = 1 no saving found anywhere; k = O(log n) saves asymptotically (front R4, heuristic, AG(2,p) Radon/FFT).
A k = 2 saving on a small system = first concrete A-upper point and a barrier any 951 proof must respect.
## Status
(coord mirrors Fable F's /home/user/ku951/STATUS.md here)
- 09:00 scaffold (satk.py, clean + order + used only): c11 with 1..3 NOTs UNSAT at every s = 5..10 (no saving for k <= 3);
  Fano with 1..2 NOTs UNSAT at s = 7..12 (s = 13 queued). Logs scaffold-951 f15/STATUS16.md.
- 09:00 coord Fable F (research/knot951: knot.py, survey.py, results.jsonl; validated by validate.py / validate2.py against
  w951.Circuit.is_correct): with UNLIMITED NOT gates (k = s), UNSAT at s = base - 1 on all 422 enumerated (1,1)-disjoint systems
  (n <= 6 with min set size 2; n = 7 with min set size 3). So on these systems general circuits (any number of NOTs) need exactly
  base gates. Savings with many NOTs (R4, AG(2,p)) can only appear at larger n. Agent stopped at the spend limit before writing notes.
