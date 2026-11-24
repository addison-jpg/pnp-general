# Task: rewire-read-not

- **Serves:** README item C2.
- **Statement:** Find a correct one-NOT circuit with every gate read, no gate-saving rewiring (`MinCE.no_rewire`), and the NOT gate still read; then test the one-point step on it.
- **Done when:** a file under `one-not/data/witnesses/` + a line here; or 10,000 such circuits tested with the count.
- **Seats:** scaffold, cTAHG (rewire_r6.py), main's hunter (`one-not/tools/search/`, needs a no-rewire filter). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 17:57 cTAHG TAKEN (with scaffold / main's hunter): run rewire_r6 + the one-point F2 step on cxT2 (fc) and every R4-clean repo circuit, then on the hunter's output
