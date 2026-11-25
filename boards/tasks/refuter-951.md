# Task: refuter-951 (a refuter lane for the one-NOT target)

- **Source:** coord for Addison, 2026-11-25 (Addison approved the card).
- **Goal:** search for a counterexample to the current open statements of the one-NOT program, each search paired with the proof seats working on the same statement.
  - `BottomPay`: A10 §3 (`one-not/research/open/A10_light_absorption.md`); stated in Lean in `one-not/lean/PEqualNP/W951/Open/LightAbsorb.lean`.
  - `no_minCE` directly: a one-NOT circuit computing a Boolean sum, with pairwise |S_a ∩ S_b| ≤ 1, and fewer than base = Σ(|S_w| − 1) gates.
- **Methods:**
  - SAT exact synthesis at size base − 1, smallest families first: STAR4, C4, Pasch, then the PG(2,3) set systems.
  - Random and targeted search over DD states. `A14_bottom_hall.py` already reports union_fail 0, so extend it rather than start fresh.
  - Search near the known high-slack witnesses in `one-not/data/witnesses/`.
- **What counts:**
  - A witness file with its sha256, rechecked by a second seat: the word `refuted` on the target.
  - An UNSAT certificate for a cell (family, size, number of NOT gates): the word `tested`.
- **Compute:** this is where more cores pay off directly. BOARD.md's COMPUTE section points here.
- **Framing rule:** the card concerns this project's own statements only. It never says "refute P vs NP". The families here (Boolean sums, f_G) are computable in polynomial time, so no result in this lane bears on P versus NP either way.

## Seats

- OPEN (Sonnet): SAT cells at base − 1 for STAR4, C4 and Pasch, with one NOT gate. -> one-not/research/open/refuter_sat.py, refuter_sat.md
- TAKEN S6 (Sonnet): extend A14_bottom_hall.py to random and targeted DD states on larger circuits, and near one-not/data/witnesses/. -> one-not/research/open/refuter_dd.py, refuter_dd.md

- TAKEN T1 (Sonnet): tensor backend. One module, `one-not/tools/tensor/`: bit-sliced truth tables (uint64 words, one array op per gate), slack at all cubes, and the mixed slack at all 3^n states, as array programs. NumPy first; the same code via `torch` or `jax.numpy` if a GPU is present (auto-detect, never required). Cross-check against the existing slow evaluators on the stored corpus (exact equality), then benchmark against `A14_bottom_hall.py` and the A5 transfer test. -> one-not/tools/tensor/, one-not/tools/tensor/BENCH.md

## Lines (TAKEN / DECIDED only)
