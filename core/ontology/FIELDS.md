# Everything as a continuous field: the principle and what survives it

Addison, 2026-11-25: "just about everything should be an infinitely continuous field." This file states that as a principle with a test, and lists where the repository has already tried it. The principle is **proposed**. Each instance carries its own label.

## The principle

Take a finite structure: a Boolean function, a matching, a relation, a set of signs. Extend it to a continuous object that **agrees with it at every corner** (every 0/1 point, every integer point). Then ask, property by property, whether the property **survives** the extension.

- Agreement at the corners holds by construction. It is not a result.
- Survival is the result, and it can go either way. A property that survives is a theorem about the continuous object. A property that fails is a counterexample, and it is kept.

## Two kinds of continuous

- **Q** (the rationals) is a field: add, subtract, multiply, divide. The repository's exact checks live here (`fractions.Fraction`). Q has gaps, so it is not continuous.
- **R** (the reals) is continuous (complete). A claim about all of R, or all of an interval, is infinite: it needs a proof (Lean, label checked) or a written reduction (checked-infinite). Checking many rational points is tested, not proved.

"Infinitely continuous" in the strict sense means R. Most of what is computed here is on Q or on finite grids, and is labelled as such.

## Where it has been tried

| finite structure | continuous extension | survives? | label | where |
|---|---|---|---|---|
| Boolean circuit's slack, 0/1 inputs | multilinear extension Phi on [0,1]^n | 0 <= Phi(p) for all p, on the Fano formula and a 5-input one-NOT circuit | checked (Lean) | `asteroid/programs/continuous.ath`, RESULTS.md asteroid |
| the same | the same | Phi monotone, level means nonincreasing | **refuted** on 8 of 23 witness circuits (twin trees: 6.00 -> 8.29) | RESULTS.md circuits |
| one-to-one matchings | the stable matching polytope over Q | its corners are exactly the stable matchings | being checked (n = 2 all profiles) | `culture/love/field.py` (in review) |
| capacity k = 1 (monogamy), 2 (polyamory) | capacity k in Q, e.g. 3/2 | integral corners do not survive at k = 3/2 | being checked | `culture/love/field.py` (in review) |
| a field on a triangulated sphere | a smooth field on the cortex | the zeros' indices sum to 2 (Poincare-Hopf) | tested (random fields), the theorem is cited | `biology/brain/hairy.py` |
| quadrant signs, +1 or -1 | real edge weights | balance (Harary) for weights is a different notion: open | open | `culture/homestuck/quadrants/check.py` |

## What the table already says

The extension does not preserve everything. Nonnegativity of the circuit slack survived into Phi; monotonicity did not. So "everything should be a field" is a good method, and a poor assumption: extend, then check each property again.

## Open

1. A small registry: for each finite check in the repository, its continuous extension (if any) and which of its properties have been re-checked there.
2. The quadrants with real weights: pick the weighted balance notion (for example, the sign of every cycle's product), and check where the integer result carries over.
3. Once `culture/love/field.py` passes review, fill its two rows with the numbers.
