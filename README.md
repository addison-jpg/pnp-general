# asteroid: one language, one standard of proof, every field

asteroid is a small language for claims that are checked, not trusted. Programs are `.ath` files. Each claim is one plain line, and each claim is checked when the program runs.

## Start here: base, the dual boot

`workshop/pair/c/base` is a small static Linux prompt, written in plain C. It has four commands:

- `:big` runs `big.ath` through the asteroid binary. The result is 9 claims true, 0 false.
- `:bus` runs `workshop/bus/bus.ath`.
- `:hello` runs `hello.ath`.
- `:quit` leaves the prompt.

Download it from this branch: https://github.com/addison-jpg/pnp-general/raw/refactor/pillars/workshop/pair/c/base

Run it from the repository root, so the `.ath` files resolve:

    chmod +x base && ./base

Limits, stated plainly:

- It is Linux only. There is no Windows `base.exe` yet.
- The asteroid binary it calls still carries Python internally.

## Native checker (ast)

The file `ast` at the top level of the repository is the native Linux checker. It is built from the Lean project. It runs little programs without Python.

    ./ast little.ath

`little.ath` gives 4 claims true, 0 false, and exit code 0.

`ast` does not yet run the checks in `big.ath`. It skips them, so it reports 0 claims on `big.ath`. The full asteroid runs them.

See [`dist/linux`](dist/linux/README.md) for the Linux files, and [`asteroid/NATIVE.md`](asteroid/NATIVE.md) for building the native binary.

## The language

A `.ath` program is made of claims and frames.

- A claim is one plain line.
- Claims are checked by Python (asteroid). A claim marked `by lean` is also checked by Lean.
- A frame records a reading, with its label.

The labels are:

- `checked`
- `checked-finite`
- `checked-infinite`
- `tested`
- `refuted`
- `analogy`
- `open`

A label says how strong a claim is. No label is stronger than its evidence.

The grammar is in [`asteroid/SPEC.md`](asteroid/SPEC.md). Editor support for `.ath` files is on the [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=asteroid.asteroid).

## What is proved

Checked-finite results exist for many small exact facts. They are listed, with how to rerun each one, in [`RESULTS.md`](RESULTS.md).

The P versus NP question is open. Nothing here settles it.

## What is open

- The native port of the `big.ath` checks. Until it is done, `ast` reports 0 claims on `big.ath`.
- The two-way bus laws L3 and L4. They are not checkable in asteroid yet.
- The Windows binary. `base` is Linux only.
- P versus NP. Nothing here settles it.

## Where things are

- `RESULTS.md`: verified results.
- `BOARD.md`: status.
- `frames.jsonl`: readings, with their labels.
- `asteroid/SPEC.md`: the language.
- `center/`: the record store.
- `workshop/`: work in progress.
- `philosophy/`, `physics/` and `culture/`: the pillars.

## Model layer

These are the Qwen2.5 model weights, counted from their headers. The counts are exact integers.

| model | tensors | parameters |
|---|---|---|
| Qwen2.5 0.5B | 290 | 494,032,768 |
| Qwen2.5 1.5B | 338 | 1,543,714,304 |
| Qwen2.5 3B | 434 | 3,085,938,688 |
| Qwen2.5 7B (4 shards) | 339 | 7,615,616,512 |

Input embeddings for memory names are in:

- `workshop/route/memory_vectors.json` (0.5B)
- `workshop/route/memory_vectors_7b.json` (7B)

These are static token embeddings. They are not meanings.

A smaller model doing the same semantic work is an open question, not a result.

## The natural sciences, as mapped

Counts come from `RESULTS.md`: verified findings only. Each one names its evidence and can be rerun.

| field | what is verified | what it is | limits |
|---|---|---|---|
| Circuit complexity | 48 checked (Lean), 6 tested, 6 refuted | Boolean circuits: gate counts, the one-NOT question, refuted lemma candidates kept as counterexamples | the open question is still open |
| Quantum computing and gravity | 13 checked (Lean) | gate-count bounds (KAK, Knill), complexity of closed timelike curves | quantum computation near gravity, not general relativity |
| Physics: curvature | 1 checked-finite | discrete Gauss-Bonnet on all 218 closed triangulated surfaces with up to 6 vertices, plus an icosahedron and a torus | a sphere's total curvature, not a derivation of Einstein's equation |
| Physics: cosmology and time | 1 and 4 checked-finite | an exact cosmology check, and the time-frame checks (S5, the git DAG) | toy models, labelled as such |
| Physics: black holes | scaling laws (typed in); two negative simulations | radius, temperature, entropy and evaporation time scale with exact powers of mass, as cited formulas | the exponents are typed in, not derived; the discrete evaporation rule gives exponent 0, not 3 |
| Biology: brain | 10 checked-finite | exact counts for neurons, complexes, cortex and networks (tree and growth counts) | structure only, not function |
| Biology: genomics and privacy | 1 and 3 checked-finite | compbio counts; privacy equality patterns and Bell numbers | counts, not biology |
| Biology: specialized species | not verified | fly connectome, mouse, dolphin and great-ape papers, from abstracts only | cited, not checked |

Negative results are kept as found. Two simulations of stated rules did not reproduce black-hole scaling, and they stay in the repository.

## The past hour

- **The dual boot.** `workshop/pair/c/base` is a Linux prompt. `:big`, `:bus` and `:hello` run `.ath` programs through the asteroid binary.
- **The two-way bus.** A design for routing from programs down to memory and back. Its layer order is a checked claim. Its laws L3 and L4 are not yet checkable in asteroid. Its record is in `workshop/bus/`.
- **The native checker.** `ast` runs `little.ath` with 4 claims true. It does not yet run the checks in `big.ath`.
- **Memory out.** Input embeddings for the memory's own names, from the 0.5B and 7B Qwen models, read by byte range. These are static token embeddings, not meanings.

Nothing above settles P versus NP.

## Why this is open

The project is public on purpose. Every claim names its evidence and its label, so a reader can check both.

## License

MIT; see [`LICENSE.md`](LICENSE.md). Exception: files taken or derived from [`brilliant-hq/pequalnp-proofs`](https://github.com/brilliant-hq/pequalnp-proofs) remain under the Apache License 2.0; see [`LICENSE-APACHE`](LICENSE-APACHE). These are the upstream Lean library under `lean/PEqualNP/` (`CircuitLowerBounds`, `Defs`, `Gct`, `Library`, `MetaComplexity`, `Outside`, `ProofComplexity`, `Search`), the copy of `Defs` in `one-not/lean/PEqualNP/Defs/`, upstream files modified here (e.g. `lean/PEqualNP.lean`, `lean/PEqualNP/Defs.lean`, `lean/CheckLemma.lean`, `one-not/lean/PEqualNP.lean`, `one-not/lean/PEqualNP/Defs.lean`), `tools/build.sh`, `one-not/tools/build.sh` and `workshop/notes/note-1-edge-function-exact-size.md` (with its copy in `one-not/notes/`). New work in this repository is by addison-jpg and contributors.
