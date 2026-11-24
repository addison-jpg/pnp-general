# Task: asteroid-bench

- **Serves:** the asteroid language.
- **Source:** owner, 2026-11-24: one pre-existing format; no Python at all; a clean open-source project with a website and a command line; "I dont want it to look ugly and vibecoded".
- **Statement:** Circuits in ONE pre-existing format: ISCAS `.bench` (`INPUT(a)`, `OUTPUT(z)`, `g = OR(a, b)`, `n = NOT(g)`). A written grammar with citations; a reader and writer in Lean; the same reader in the current asteroid; every circuit of the repository converted.
- **Done when:** `asteroid` loads `.bench` files, the witness circuits exist as `.bench`, and a round trip (bench → circuit → bench) is checked.
- **Seats:** one Fable of main.

## Lines (TAKEN / DECIDED only)

