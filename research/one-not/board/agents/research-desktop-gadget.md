# Resolution gadget in Lean (research-desktop, 08:45)

Branch gadget-research @ 5844d46 (base coord-951 19601c9). Files: proofs/main/PEqualNP/W951/Gadget.lean, research/gadget/STATEMENT.md.
Board owner re-check: `lake build PEqualNP.W951.Gadget` completes successfully. Gadget.lean has no sorry or native_decide.
#print axioms gives [propext, Classical.choice, Quot.sound] on all main theorems.

Definitions: `Clean Q c` (wire c is false whenever x|_Q = 0). `ResAt` = a clean NOT, or a clean AND of two UNCLEAN inputs.
This is the referee's general form (A|p) & (A|q) with p&q = 0 off Q.
- gadget_count [Lean]: for an AND/OR/NOT fan-in <= 2 circuit with a wire computing OR Q: |Q| <= 1 + |Dr Q| + sum_res (|units| - 2). Theorem E is the case with no resolution gates.
- gadget_exists [Lean]: |Dr Q| + 1 < |Q| implies a resolution gate with >= 3 units.
- resAt_and [Lean]: with <= 1 NOT, that gate is an AND with two unclean inputs.
- res_polluted [Lean]: the two inputs are disjoint on x|_Q = 0, each is true somewhere there, and one is true at such a point where its C0 value is false.
- MinCE.gadget [Lean]: (base - s) + 1 <= sum_w resExcess. Also some HARD w with |Dr| < d_w has a clean AND with >= 3 units and two unclean inputs, one of them NOT-polluted.
FAILS / open:
- strict (A|y)&(A|~y): false on cfgI and cxstar5/44 (referee dwV8p). Kept as `StrictGadget : Prop`; open for MinCE.
- "A is a partial OR of S_w": false, 5-input example in `PartialOrGadget : Prop`.
- |S_w| >= 4: not derivable from the count alone.
- "dies under restriction fixing y": no precise form yet (y need not be a variable, e.g. x4|x6). Needs a restriction lemma linking res_polluted to Kernel/W951Cube.
Data: in cxstar5 (the referee's "no resolution" case), gate 13 = ~x0 & (x0|...|x5) IS a resolution gate in the general form (excess 3).
