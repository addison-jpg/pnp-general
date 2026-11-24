# Math subagent findings (Sonnet, 2026-11-23 ~14:58 CST), reviewed by the opus-951 thread

Proved:
- The charging lemma (excess <= #zero-merge) is EQUIVALENT to L-meta-951, via size = Σ(|S|-1) - excess + Z.
- A purely local charging argument cannot work: fake_config_t.py builds a configuration (8 inputs; sets {c,1,2},{c,3,4},{c',1,5},{c',3,6},{1,3}; h = x1∨x3) that passes the invariant and per-set-count scaffold checks with excess 2 > Z 1, but does NOT compute the outputs. Any proof must use output correctness.
- Lemma B (kill points): if g merges S and g(e_v)=1 for some v ∉ S, every path from g to o_S contains a gate taking the e_v value 1 -> 0; it is an AND or the NOT, never a merge, so it lies in Z.
- Lemma A, FIXED by the opus thread: run each set's union-find only over the cone of its output o_S. The per-set count stays |S|-1 and every merge then lies in the output cone. (The unrestricted version is false: a merge outside the cone can preempt one inside.)

Open: injectivity of a kill-point charge (one AND such as (g1∨g2)∧N may be the kill point of several double merges; the NOT may be the only killer of many).

## Fork findings (Claude Code, 2026-11-23, local/uncommitted): restriction route, avoids union-find double counting
Idea: pick a minterm M of h (the wire the NOT reads). Set x_v = 1 for v in M. Then h = 1, so the NOT outputs constant 0, and the circuit becomes monotone.
- Sets with S ∩ M = ∅ ("unhit"): outputs still equal OR(S), so the already-merged monotone theorem (986-style) gives  live gates after restriction >= Σ_{unhit}(|S|-1).
- Sets hit by M: output becomes constant 1.
- So  size >= Σ_unhit(|S|-1) + removed, where removed = size - live gates (NOT gate itself counts as removed).
- LEMMA R (conjectured): removed >= Σ_hit(|S|-1) + 2.   R  =>  size >= base + 2 when the NOT is read (and base+1 trivially otherwise), i.e. 951 for NOT-read circuits.
Experiment (restr951.py, SAT circuits at size base+2 / base+3 on 5 systems, 975 circuits, EVERY minterm M of h):
  - live - Σ_unhit(|S|-1) in {0,1} always (consistent with the monotone theorem; min 0).
  - removed - Σ_hit(|S|-1) in {2,3} always: min 2. So R holds with equality attained, on all tested circuits and all minterms.
Status: R NOT proved. It is a gate-elimination statement (per hit set S, |S|-1 gates become constant/bypassed/dead, plus the NOT, plus 1 more). Obstacle: a merge gate g of hit set S need not become constant (a, b need not contain M), and g may stay live because an unhit set T reads it; monotonicity gives g(e_p)=0 for p in S∩M when g<=o_T, but that only says g is not a source of p.
No counterexample to 951 found. The zero-double-merge data and R both look true; R gives a different, possibly easier, target than charge_hard.
Caveat: live count is constant-propagation + dead-code only (no structural hashing); n<=6 only.
