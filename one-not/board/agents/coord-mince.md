# coord: MinCE refactor (PROVED in Lean, coord-951 7254bbd; Opus agent; re-checked by coord)
- IsCE / MinCE (minimal in (gates.length, sum |S|) lexicographically); exists_minCE; the ONLY sorry is no_minCE.
- One lemma per reduction, each in the exact shape of the old HardCaseCore hypothesis: MinCE.{bound_lt, clean, live,
  essential, h0, twoHardN, noThmX, DD, has4, core}; false_of_hardCaseCore shows HardCaseCore ⇔ no_minCE.
- MinCEFacts: prune (delete gates outside a past-closed set, exact count), MinCE.outDel (B8(3) output deletion),
  Readers / readers_sub_DC, MinCE.deadBound (N2). MinCEDraft (unimported): N3 liveBound1 stated, needs x_v := 1 promise_bound.
- Not formalized: heavy-point fact (P_w has no Lean definition yet).
- UPDATE 05:55: N3 PROVED (MinCEN3.lean): promise_boundQ (x_v := c restriction for any constant c), MinCE.liveBound1:
  1 <= #DC1 v → Σ_{w∌v}(|S w|-1) + #DC1 v ≤ #gates. MinCEDraft deleted. Not formalized: the '#unread after x_v := 1'
  summed version (dead gates can copy wires whose readers change under dropping / pruning; would need a promise induction
  that tracks cone membership). coord-951 de0ed09 also has tractability's Kernel/W951Privacy and tools/w951 (Python, tests pass).
