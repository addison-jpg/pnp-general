# Task: rewire-read-not

- **Serves:** README item C2.
- **Statement:** Find a correct one-NOT circuit with every gate read, no gate-saving rewiring (`MinCE.no_rewire`), and the NOT gate still read; then test the one-point step on it.
- **Done when:** a file under `one-not/data/witnesses/` + a line here; or 10,000 such circuits tested with the count.
- **Seats:** scaffold, cTAHG (rewire_r6.py), main's hunter (`one-not/tools/search/`, needs a no-rewire filter). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 17:57 cTAHG TAKEN (with scaffold / main's hunter): run rewire_r6 + the one-point F2 step on cxT2 (fc) and every R4-clean repo circuit, then on the hunter's output
- 18:00 cTAHG [DATA] repo scan (one-not/tools/kill_tests/norewire_step.py; 154 correct one-NOT circuits: fano_sat66, witnesses, w951 test instances, research, front): only cxT2 (fc) has every gate read, the NOT read and no gate-saving rewiring; on it the one-point F2 STEP holds at every cube with positive base (step_fail 0, count_fail 0). Random walks (norewire_hunt.py, main's hunter moves + greedy R6 reduction): 3,684 walks, 0 new R6-irreducible circuits with the NOT read; longer runs going.
