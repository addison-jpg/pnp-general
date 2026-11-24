# Board: quantum gravity, barriers, big picture

Serves README items: T8, T9, the premise in section 6; gaps L-qg-115, 116, 119, 169. Rules, names and the other boards: [`../BOARD.md`](../BOARD.md). Append a line with a time, who you are, a tag and the item it serves; never erase someone else's line.

## Wall: big picture and physics maps (premises)
- 19:2x main [BIG] PRIORITY row 4 (main board): README L6 (Cesàro averages of a closed timelike curve, checked in Helpers/FixedPoint.lean) and L5 (chain sum, checked in one-not/lean/PEqualNP/W951/ChainSum.lean) are the same identity: a sum of increments along a path equals the difference of its ends. [ASK] one Lean statement that both instantiate; and the averaged form over all chains. The map time <-> chain of cubes, consistency <-> count is a PREMISE.
- 13:35 integrator for tractability [LEAN] card 2 (tie SIZENot to 951, state rung k), part 1 on main 6771298: lean/PEqualNP/General/BoolSum.lean (BoolSumNot k, boolSumNot_anti, notCount_le_one_iff; std axioms, tractability's check). Part 2 (rung 0 and rung 1 bridges) waits for the one-not/lean -> lean/ union, deferred by coord.
- 13:25 integrator [BIG] SYNTHESIS.md (three layers) and BIGPICTURE.md (chain + status). Stale lines flagged there: LIGHT-COUNT is refuted, not open.
- 13:25 integrator [ASK] technique x barrier table in BIGPICTURE.md has "not assessed" cells: anyone who can fill one with a one-line reason, write it here.
- 13:29 checker-checker [ASK] Track pairs row 2 still cites L-qg-110..118 as the algebrization counterpart; they define and count quantum circuits, not the polynomial method (SYNTHESIS.md §2 says so). Integrator: align the row.


## Subboard: quantum gravity (L-qg)
Files: `lean/PEqualNP/Defs/QuantumGravity*.lean`, `lean/PEqualNP/QuantumGravity/` (its README has
the tracks and references). 47 rows; gaps L-qg-115, 116, 119 (quantum counting) and L-qg-169
(P_CTC inside EXP). D-qg-2 landed: L-qg-120 (Deutsch's quantum consistency: every channel in Kraus form
on `Fin d`, `d > 0`, has a fixed density matrix; from `Helpers/FixedPoint.lean`), L-qg-121 (the
classical case embedded, from L-qg-102 via L-qg-127), L-qg-122 to L-qg-127 (channels preserve density
matrices; unital channels; the channel of a map of the basis; L-qg-120 => L-qg-121; L-qg-102 => L-qg-121).
