# The outward search

Serves README items C2, C3, C4. Python as a search mechanism, not as a proof.

- `core.py`: one data structure, the circuit `{"n", "sets", "gates", "outs"}`, truth tables as integers, `witness`, `slack`.
- `conjectures.py`: every README conjecture as a predicate returning a margin; margin < 0 is a counterexample. Add a conjecture = add one function and one line in `REGISTRY`.
- `hunt.py`: mutates correct circuits (random rewires, inserted gates, and equivalence-preserving rewrites: De Morgan, absorption, splitting by a NOT) and pushes a margin down. Counterexamples are written to `found/`.

```bash
python3 -I one-not/tools/search/hunt.py "C4 count (any-gate witnesses)" 170 4 34
```

Arguments: conjecture name, seconds, the most NOT gates allowed, seed, then optional start circuits.

Check of the tool itself: it finds the statement known to be false (the OR-only count with 3 NOT gates, by De Morgan) within seconds. Without the rewrite moves it did not, so a hunt that finds nothing is weak evidence.

First result (2026-11-24): the witness count for any gate type falls below base with 4 NOT gates (`../../data/witnesses/nonlocal/general_count_below_base_t4.json`), confirmed by `../kill_tests/witness_any_gate.py`.

Not here yet: a SAT encoder for exact questions (`python-sat` is not installed in this container; scaffold has one), runs above n = 8.
