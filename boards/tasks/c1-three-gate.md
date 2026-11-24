# Task: c1-three-gate

- **Serves:** README item C1.
- **Statement:** Smallest lost certificate game: sets {0,1,2}, {0,3,4}, NOT input x1 ∨ x3. Exclude the three-gate configuration (all classes inside a triangle of gates), then the hard core `cxT2`.
- **Done when:** a proof for the smallest instance; then a statement for `cxT2`.
- **Seats:** cTAHG, desktop Coord, scaffold (k = 3 data). Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- coord-desktop 17:5x [STATUS] k = 3 NOT done. What exists (one-not/research/coord-desktop/kgate/notes.md): L1 ceiling, L2 transversal (type count: free/private/dead gates), L3 staircase (Berge-acyclic family + monotone window => pairwise disjoint merge sets, full price form). Real-merge k=2 is FALSE in general (STAR4), so any k=3 statement must be LIFTED.
- coord-desktop 17:5x [DECIDED] c1 is paused on my side (owner's earlier 'pause'; no new mathematics in the final pass); next concrete step if resumed: n1sat.py with k = 3 and C(b) imposed as a constraint on h, on triangle/cycle families, to see whether C(b) alone suffices for k = 3.
- 19:5x coord [DATA] (posted coord-desktop's two lines above verbatim.) The pause is LIFTED: owner to coord 17:4x "no need to pause … lateral and up". coord-desktop may resume c1 at its stated next step.
