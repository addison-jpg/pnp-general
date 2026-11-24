# research: core test systems for 951 (enumeration + coverage)

Status: checked by computer (exhaustive enumeration up to isomorphism, nauty genbg 2.8.8).
Core = sets pairwise share <= 1 point, every point lies in >= 2 sets of size >= 3, some set of size >= 4.
base = Σ(|S|-1).

Recipe: points = 1st class, sets = 2nd class, `-Z1` = two sets share <= 1 point.
- skeleton (sets >= 3 only): `nauty-genbg -q -Z1 -d2:3 n m`
- with size-2 sets: `nauty-genbg -q -Z1 -d2:2 n m 0:$((MAXBASE+m))` (edge cap bounds base = E - m)
- then filter: max |S| >= 4 and the core condition.

Counts:
- skeleton: n <= 7 none; n=8: 4 (base 11,12,13,15); n=9: 50 (min 13); n=10: 1538 (min 14).
- with size-2 sets: n=8: 266 (11:1, 12:3, 13:12, 14:26, 15:52, ...); n=9 base <= 16: 1305 (13:4, 14:34, 15:229, 16:1038).
- smallest: n=8 base 11 {0,1,2},{0,3,4},{1,5,6},{3,5,7},{2,4,6,7}: scaffold SAT, all UNSAT at s=10 (951 holds).

Coverage by front's cover.covered (front-match w9/g1/cover.py, run verbatim):
- everything with base <= 13 at n <= 9 is covered.
- uncovered: n=8 full 242 (min base 14: 18 systems, all contain a size-2 set; one is iso to front's U1);
  n=9 full base<=16 530 (min 15: 1 system); n=9 skeleton 20 (min 16); n=10 skeleton 1022 (min 18).
- frontier list: agents/research-uncovered.json (saved by scaffold; queued at s = base-1).

Refuted structure lemma: 'some point lies on exactly two sets, both of size 3' is FALSE
(n=8 base 12 {0,1,2},{0,3,4},{0,5,6},{1,3,5,7},{2,4,6,7}; fails for 2/4, 16/50, 400/1538 skeletons at n=8/9/10).

Files (research session scratchpad, ask research for any): cores_n{8,9,10}.sorted.txt, full_n8.txt, full_n9_le16.txt, *.uncovered.json.
