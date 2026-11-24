> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: rewire-read-not

- **Serves:** README item C2.
- **Statement:** Find a correct one-NOT circuit with every gate read, no gate-saving rewiring (`MinCE.no_rewire`), and the NOT gate still read; then test the one-point step on it.
- **Done when:** a file under `one-not/data/witnesses/` + a line here; or 10,000 such circuits tested with the count.
- **Seats:** scaffold, cTAHG (rewire_r6.py), main's hunter (`one-not/tools/search/`, needs a no-rewire filter). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 17:57 cTAHG TAKEN (with scaffold / main's hunter): run rewire_r6 + the one-point F2 step on cxT2 (fc) and every R4-clean repo circuit, then on the hunter's output
- 18:00 cTAHG [DATA] repo scan (one-not/tools/kill_tests/norewire_step.py; 154 correct one-NOT circuits: fano_sat66, witnesses, w951 test instances, research, front): only cxT2 (fc) has every gate read, the NOT read and no gate-saving rewiring; on it the one-point F2 STEP holds at every cube with positive base (step_fail 0, count_fail 0). Random walks (norewire_hunt.py, main's hunter moves + greedy R6 reduction): 3,684 walks, 0 new R6-irreducible circuits with the NOT read; longer runs going.
- 18:12 cTAHG [DATA] norewire_hunt.py, 2 seeds x 700 s from fano_sat66 + 6 witnesses + cxT2 (fc): 58,267 walks; the NOT gate dies under greedy R6 reduction in 58,188 (99.86%); R6-irreducible with every gate read and the NOT read: 7 new circuits (72 repeats), all n = 6, 12-13 gates, base 8, |F2(∅)| = base (tight), NOT input local on every cube; F2 step and count hold at every cube on all 7 (0 failures). With cxT2 (fc) (non-local cubes, step holds): 8 such circuits, no witness against the step. Reading: R6-irreducibility almost always kills the NOT; the board's 10,000 needs a generator that keeps the NOT alive (e.g. SAT near base, scaffold).
- 19:26 main's Sonnet B [TESTED 12/12] 12 distinct irreducible read-NOT circuits (one-not/tools/search/found/irreducible_seed7.jsonl, n 7-9, mostly cxT2 descendants) in 240 s; the one-point step held at every positive-base cube on all 12 (far from the 10,000).
- 22:50 cTAHG [STOPPED] lane closed (owner: only asteroid). Stopped after the hunt data line above: scripts norewire_step.py / norewire_hunt.py on main; 8 R6-irreducible one-NOT circuits found, F2 step holds on all; no witness. No background searches running.
