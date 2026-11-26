# Brains as graphs, read through the bus and Mobius model

Status: question and hypotheses only. Nothing is checked; no asteroid run was made. The link between brains and the repo's bus and Mobius model is an **analogy**. Connectome facts are from memory, not checked.

## Question

Can a connectome, taken as a directed graph, be read through the repo's bus and Mobius model, with specialised regions as sinks, from worm to fly to mouse to a human fragment?

## Terms (one meaning each)

- **bus**: as in `workshop/bus/README.md`: a two-way route over files. Applying it to brain regions is a new reading.
- **Mobius strip**: as in `workshop/mobius/SPEC.md`: the twist (x, 0) ~ (1 - x, 1). Only the finite twist is checked there.
- **sink**: a node with out-degree 0. *Proposed here; to be confirmed.*
- **n-partite**: a graph whose nodes split into n classes with no edge inside a class. *Proposed here; to be confirmed.*
- **cone**: not defined in the repo. Needs a definition before use.

## Data (from memory)

- Exists: *C. elegans* (302 neurons); adult *Drosophila* (about 139,000 neurons); a cubic-millimetre piece of mouse cortex; a roughly cubic-millimetre fragment of human cortex.
- Missing: any whole human brain (about 86 billion neurons); any dolphin connectome known to me.

## Hypotheses (all open)

**B1 (sinks).** In a directed connectome, sinks exist and cluster in identifiable regions.
- Refuted by: no sinks, or sinks no more clustered than in degree-preserving random graphs.
- Data needed: a directed fly or worm graph with cell classes.

**B2 (n-partite).** Cell classes form an n-partite quotient of the graph.
- Refuted by: edges inside classes. Recurrent connections make this likely false for strict n-partite; a quotient may still be useful.
- Data needed: same graph.

**B3 (scale).** The same B1 statistic holds at worm, fly and mouse scale.
- Refuted by: a statistic that differs across scales beyond sampling error.
- Data needed: all three graphs, one pipeline.

**B4 (Mobius, analogy).** A half-twist identification describes how up-passes return to down-passes in the bus.
- Needs: a brain observable that the twist predicts. None defined.

## Barrier rule

If a hypothesis fails, the failure is recorded as the result. It is not replaced by a different target, such as mapping quantum-gravity fields.

## Not claimed

- That any whole human or dolphin brain has been mapped.
- That brains are black holes or Mobius strips.
- Anything about consciousness.

## Open

- Definitions of the cone, the sink, and the bus-through-a-region, from the user.
- **Route, not Lean.** The checks here run with `--no-lean`. Brute-forcing Lean builds is intractable for this project, so none of the hypotheses here depends on a Lean build. The checks go in the `.ath` files: 98 in the repo today. "Megacluster" is not a term the repo defines, so its scope needs a definition from the user.
