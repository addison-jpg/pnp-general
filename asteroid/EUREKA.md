# "Lean Eureka" and asteroid (task lean-eureka-asteroid)

Owner: "get a small agent on lean eureka --> asteroid". Nothing named eureka is in this repository or its Lake packages.

## Candidates (web search, generic queries only)
| Candidate | Result | Opened |
|---|---|---|
| A Lean 4 tool / prover / tactic / model named Eureka | none found in four searches (theorem proving, autoformalization, agents, Mathlib search) | search result lists only |
| GitHub repository search "eureka lean4" | one hit: `joestubbs/Curly_Eureka_`, "Lean4 theorem proven samples", 0 stars, last updated Nov 2024: a sample collection, not a tool | https://github.com/search?q=eureka+lean4&type=repositories |
| LeanExplore (search engine for Lean 4 declarations, Python API) | real, but not named Eureka; needs network; licence not stated on the page | https://arxiv.org/abs/2506.11085 |
| Lean Finder, Moogle, LeanSearch, Loogle, Gödel's Poetry, Ax-Prover, Prover Agent | real Lean tools, none named Eureka | seen only as search hits, not opened |
| NVIDIA "Eureka" (LLM-written reward functions for robotics, not Lean) | from memory only, not opened; shares the name, nothing to do with Lean | no |

## Decision: (b), most likely there is no such tool
Most likely guess: the owner remembers a name loosely; the closest real things are the Lean search engines (LeanSearch, Loogle, LeanExplore) or LLM provers (Gödel-Prover, Ax-Prover). Low confidence (about 25% that any single one is meant). Not usable here anyway: all need network or a model/API, and a new Lake dependency would need `lake update` (forbidden). Trial: `#loogle` from LeanSearchClient in this container gives "Could not contact Loogle server", so `find "QUERY"` would not work offline either.

## What was built (a stand-in, not Eureka)
Verb `prove "STATEMENT" by TACTIC` in `asteroid/ext_eureka.py`: writes `theorem asteroid_prove : STATEMENT := by TACTIC` (import Mathlib) and checks it with `lake env lean`. Tactics: decide, omega, simp, aesop, norm_num, rfl, simp_arith, trivial, `decide +kernel`. No network, no key.
- Example `asteroid/examples/prove.ath`: 3 statements accepted in about 15 s with Lean; `python3 -m asteroid test --no-lean` passes all 5 examples (the verb is skipped there).
- A false statement (`2 + 2 = 5` by decide) is REJECTED and the run exits 1.
- Use: `export PATH="/home/user/pequalnp-proofs/tools/bin:$PATH"; python3 -m asteroid run asteroid/examples/prove.ath`.
- If the owner names a link for the real "Eureka", write it on `boards/tasks/lean-eureka-asteroid.md`.
