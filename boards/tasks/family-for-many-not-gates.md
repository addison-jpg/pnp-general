> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: family-for-many-not-gates

- **Serves:** README item C4.
- **Statement:** `witness` (any gate type) falls below base from 4 NOT gates (`general_count_below_base_t4.json`). Minimise that circuit, read off the mechanism, propose a family that has ≥ base members in every correct circuit.
- **Done when:** a definition + a hunt that does not break it.
- **Seats:** main, Generalize, tractability. Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 2026-11-24 18:55 UTC, tractability (desktop, great-hopper), [DECIDED] not taking: this seat is idle by its user's word and has no context on the one-NOT search tooling; main, Generalize or the cloud tractability seat are free to take it.
- 2026-11-24 19:18 UTC, main's Sonnet A TAKEN
- 2026-11-24 19:29 UTC, main's Sonnet A, [DATA] minimal counterexample: 10 gates, 4 NOT, n=7, 5 witnesses < base 6 (general_count_below_base_min.json; all of t4, t5, t6 minimise to it)
- 2026-11-24 19:29 UTC, main's Sonnet A, [DATA] mechanism: the x0+x6 merge is a falling AND of negations (1 at Z), invisible to witness; De Morgan of a 4-OR hides 1 merge. Note one-not/board/agents/sonnet-many-not-family.md
- 2026-11-24 19:29 UTC, main's Sonnet A, [TESTED 19/19] C4 count (flip): gates changing value at two atoms from a zero point, either direction; 240 s hunt, 6 NOT: no counterexample
- 2026-11-24 19:29 UTC, main's Sonnet A, [TESTED 19/19] C4 count (flip classes): flip gates up to complement is exactly 6 = base on the minimal counterexample (tight); hunt 240 s clean. C4 count (split) also 19/19 but weaker
