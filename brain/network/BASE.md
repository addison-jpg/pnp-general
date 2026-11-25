# Neurons join into networks: directed graphs and their cliques

What this is: the level where single neurons join into a network. A synapse runs one way, so the object is a **directed graph** (digraph): nodes are neurons, arcs are connections. Above the graph sits its **directed flag complex**, built from directed cliques. What this is not: a model of the mind, or any clinical claim. Everything runs in `check.py` (`python3 -I brain/network/check.py`, under one second). Labels as in `compbio/BASE.md` and `philosophy/PSYCHOSIS.md`: **fact**, **checked-finite**, **tested**, **join**, **analogy**, **open**.

## 1. Motifs

A **motif pattern** is a weakly connected digraph up to isomorphism (weakly connected: connected when arc directions are ignored). Milo et al. (2002) count which small patterns occur more often than chance in real networks, neuronal wiring among them.

| n | all digraphs up to iso | weakly connected | how |
|---|---|---|---|
| 1 | 1 | 1 | enumeration + Burnside |
| 2 | 3 | 2 | enumeration + Burnside |
| 3 | 16 | 13 | enumeration + Burnside |
| 4 | 218 | 199 | enumeration + Burnside |
| 5 | 9608 | 9364 | Burnside |
| 6 | 1540944 | 1530843 | Burnside |

- n = 1..4: **checked-finite** by canonical forms over all labelled digraphs. n = 5, 6: exact **counting**, not enumeration (no graph is listed one by one), by Burnside's lemma (count fixed digraphs per permutation) and the inverse Euler transform (all graphs to connected ones); the two methods agree on n = 1..4. All expected values matched.
- The 13 three-node patterns are the triad patterns used by Milo et al. That the paper uses exactly these 13: **from memory**; the search confirmed the paper, not the figure.

## 2. Directed cliques and the flag complex

A **directed k-simplex** is k + 1 neurons v0, ..., vk with an arc vi → vj for every i < j (a transitive tournament: one source, one sink). The **directed flag complex** has these as its simplices; a face drops one neuron. **Betti numbers** count holes in each dimension; here computed over GF(2) (arithmetic mod 2) by exact rank.

- **Checked-finite:** for all 4165 labelled digraphs on 1..4 nodes, Betti numbers are non-negative and the Euler–Poincaré formula holds (alternating sum of simplex counts = alternating sum of Betti numbers).
- Holes appear early. Labelled digraphs with β1 > 0: 0, 1, 26, 1842 (n = 1..4); with β2 > 0: 0, 0, 1, 498. The n = 2 case is a reciprocal pair: two 1-simplices on the same two neurons make a loop. Checked-finite.
- Labelled digraphs on 3 nodes by number of directed 2-simplices (0..6): 39, 12, 6, 6, 0, 0, 1. For 4 nodes: see `fingerprints.json`. Checked-finite. (An earlier guess of 48, 12, 3, 1, made while building this level, was wrong; the table above is the computed value.)
- Reimann et al. (2017) apply this complex to a reconstructed neocortical microcircuit and find many high-dimensional directed cliques and cavities. **Fact** (abstract).

## 3. Expected count in a random digraph

In a random digraph where each of the n(n − 1) arcs is present independently with probability p:

E[number of directed k-simplices] = n! / (n − k − 1)! · p^(k(k+1)/2).

Reason: a simplex is an ordered (k+1)-tuple of distinct neurons, and it needs its k(k+1)/2 forward arcs. **Checked-finite** as an exact polynomial identity in p for n = 1..4, all k: both sides agree at n(n − 1) + 2 rational points, more than the degree, in exact fractions (90 evaluations).

## 4. Tree against rhizome

A connection is **critical** if deleting it leaves the network disconnected.

| n | weakly connected | every arc critical (oriented trees) | no arc critical |
|---|---|---|---|
| 1 | 1 | 1 | 0 |
| 2 | 2 | 1 | 1 |
| 3 | 13 | 3 | 8 |
| 4 | 199 | 8 | 146 |

Convention: the single neuron (n = 1) has no arcs, so "every arc critical" holds vacuously and it is counted as a tree; "no arc critical" is counted only for graphs with at least one arc, so n = 1 gives 0 there. (Counting it vacuously in both columns would give 1, 1, 8, 146.)

Fractions of critical arcs at n = 4: 0 (146 graphs), 1/7 (2), 1/6 (6), 1/5 (19), 1/4 (8), 1/2 (10), 1 (8). Checked-finite.

- **Join:** `philosophy/rhizome.py` checks that a connected graph is a tree exactly when every edge is critical. Here the same holds for digraphs: every arc is critical exactly when the digraph is an oriented tree (no reciprocal pair, n − 1 arcs). Checked-finite for n ≤ 4. One neuron's branching arbor is a tree, every segment critical; a network with loops is not.
- Deleuze and Guattari (*Mille plateaux*, 1980, introduction) set the tree against the rhizome and speak of the brain in these terms. **Analogy**; read status: from memory, not opened.

## 5. Real connectomes

C. elegans has 302 neurons. Varshney et al. (2011) assembled its hermaphrodite chemical and gap-junction networks; Cook et al. (2019) give whole-animal connectomes of both sexes. The data were not downloaded or analysed here. **Open.**

## Joins

- Digraph motif counts: the same counting-sequence route as `compbio/BASE.md` (fingerprints).
- Critical edges and trees: `philosophy/rhizome.py` (join, the same statement on undirected graphs, extended to directed).
- Euler–Poincaré on a simplicial complex: not a join yet, because no repo file with a chain complex has been named. **Open.**

## Open items

1. Run motif counts and the flag complex on the C. elegans data (Varshney 2011, Cook 2019).
2. Euler–Poincaré exhaustively at n = 5 (1,048,576 labelled digraphs; too slow by the present method).
3. Confirm the 13-triad figure in Milo et al. full text and the Deleuze–Guattari passage.

## Sources

- R. Milo, S. Shen-Orr, S. Itzkovitz, N. Kashtan, D. Chklovskii, U. Alon, "Network motifs: simple building blocks of complex networks", *Science* 298 (2002) 824–827. Read: search result only.
- M. W. Reimann et al., "Cliques of neurons bound into cavities provide a missing link between structure and function", *Front. Comput. Neurosci.* 11:48 (2017). Read: abstract only.
- L. R. Varshney, B. L. Chen, E. Paniagua, D. H. Hall, D. B. Chklovskii, "Structural properties of the Caenorhabditis elegans neuronal network", *PLoS Comput. Biol.* 7, e1001066 (2011). Read: search result only.
- S. J. Cook et al., "Whole-animal connectomes of both Caenorhabditis elegans sexes", *Nature* 571 (2019) 63–71. Read: search result only.
- G. Deleuze, F. Guattari, *Mille plateaux*, Minuit, 1980, introduction "Rhizome". Read: from memory, not opened.
