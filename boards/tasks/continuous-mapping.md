# Task: continuous-mapping

- **Serves:** README items L5 (chain sum: the step is the derivative, the count the integral), C4 (variable number of NOT gates), T7 (exact sizes, XOR extension).
- **Source:** owner, 2026-11-24 ~19:00, typed to Generalize: "the next step is building a messy continuous mapping on top of this". Messy is allowed; checked still means checked.
- **Statement (first reading, Generalize; correct it on this board):** extend the discrete results to a continuous object: a map from circuits or functions to real values (or a real parameter in place of the gate count, NOT count or XOR constant) that agrees with the discrete counts at integer points and whose discrete identities (L5 chain sum, the XOR bounds max + 3k <= C <= min + 4k) become continuous identities.
- **Done when:** one Definition of the continuous map, written in Lean or Python, and one Lemma relating it to a checked discrete row, with its word (checked / tested / premise).
- **Seats:** unassigned. Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner. Respect SLOW DOWN PROCESSES on BOARD.md.

## Lines (append only: time, who, tag, one line)
- 19:00 Generalize [ASK] which "this": the L5 chain sum, the XOR extension rows, or the whole README chain? If no answer in 15 minutes, take the L5 chain sum (it already reads as derivative / integral) as the base.
- 20:2x main [DECIDED] (15 minutes passed on Generalize's ASK; owner to main, 20:1x: "one well placed fable on the continuous aspect"): the base is the L5 chain sum. TAKEN by one Fable of main. Why a subagent (SLOW DOWN rule): the owner asked for exactly one Fable here, and no seat has taken the task.
- 20:2x main [IDEA] first formulation for the Fable to keep or kill: product measure μ_p on cubes (each point in Q with probability p), Φ(p) = E[slack(Q)]; Φ(1) = 0, Φ(0) = slack(∅); dΦ/dp is a Russo-Margulis sum of E[slack(Q + v) − slack(Q)] over points v. The count at every cube ⇒ Φ ≥ 0 on [0,1]. qg-d2's `sum_shapley` (telescope-l5-l6) is the uniform-order version. The uniform average of the FIRST step is negative on the twin trees (c3_avg.py), so Φ is not monotone there: the continuous statement must be weaker than monotonicity.

