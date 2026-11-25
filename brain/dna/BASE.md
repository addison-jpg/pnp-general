# DNA topology: the lowest level

DNA in a cell is closed loops (plasmids, minicircles) or long loops tethered at both ends. A closed loop of double-stranded DNA is two closed curves, so it has a **linking number** (Lk): the number of times one strand winds around the other, an integer that does not change unless a strand is cut. Enzymes called **topoisomerases** change it. This file checks the topology with exact integer arithmetic and says which objects it shares with other files. It is about molecules, not about minds or patients.

Labels as in `philosophy/PSYCHOSIS.md`: **fact** (published, cited), **checked-finite** (exact and exhaustive over a stated finite set, rerunnable), **tested**, **join** (the same object as a repo file, named), **analogy**, **open**.

Run: `python3 -I brain/dna/check.py` (under a second). It reuses `philosophy/milnor.py` unmodified: links are integer polygons, a diagram is computed exactly, and lk is counted from crossing signs two ways plus a Magnus coefficient.

## What is checked

| # | Statement | Label | Checked set |
|---|---|---|---|
| 1 | A closed ribbon (two strands) whose edge turns n full times (right-handed) around a flat circular core has lk = n | checked-finite | n = -6..6 |
| 2a | Changing one crossing between two different closed curves (one strand passage) changes their lk by exactly 1, with sign minus the crossing's sign | checked-finite | all 22 inter-strand crossings of ribbons n = -3, 0, 2, 5 |
| 2b | A duplex passage (the duplex passes through itself: four strand crossings flipped together) changes Lk by exactly 2 | checked-finite | figure-eight core, n = -2, 0, 1, 3; Lk went n+1 -> n-1. The offset Lk - n = 1 is measured at the first n and asserted equal for the others; its cause is not checked |
| 3 | The torus link T(2,2k) (a replication catenane) has lk = -k in this parametrisation, and a greedy choice of passages reaches lk = 0 in exactly |k| | checked-finite | k = -5..-1, 1..5; one greedy sequence per k |
| 3' | At least |k| passages are needed to reach lk = 0 | argument (from 2a: each passage changes lk by 0 or ±1); not enumerated over all passage sequences | - |
| 4 | Chainmail on a honeycomb patch, each ring linked once to each neighbour: the matrix of |lk| equals the adjacency matrix | checked-finite | 13 hexagons, 42 rings, 54 links; 24 interior rings of valence 3, 18 rim rings of valence 2 |
| 5 | Borromean rings: every pairwise lk is 0, Milnor's triple number mu(123) = -1 (sign depends on orientation) | checked-finite | the polygon in `milnor.py`, one view |

Notes and limits:
- 1 is one instance of **Lk = Tw + Wr** (Calugareanu 1959, White 1969, Fuller 1971; fact). Twist (Tw) measures how the edge turns about the core; writhe (Wr) measures how the core coils in space. For a flat circle Wr = 0, so Lk = Tw = n. The script does not compute Tw or Wr separately (they are not integers in general); it checks only Lk.
- In 2b the core is a figure-eight curve in space with a fixed frame, and its Lk is n + 1, not n. The script measures this offset (1) and checks it is the same for every n tried. Where it comes from (the core's writhe, the frame's turning, or both) is not computed: Wr is not an integer in general. That explanation is **open**. In 2b the four flipped crossings are picked by a heuristic (crossings far apart along the strand); the script asserts it finds exactly four.
- 3 shows lk = 0 after |k| passages. lk = 0 is necessary for unlinking, not sufficient; the script does not check that the result is the unlink. Topoisomerase IV unlinking replicated catenanes is fact in the literature (from memory, not opened; not cited here by name).
- 2a is a statement about diagrams: a type II topoisomerase cuts one duplex and passes another through it (fact), which on a diagram is a crossing change.
- 4 is a model of a model. The hexagonal, valence-3 network is the Chen et al. 1995 reading of bulk data; a 2022 single-molecule study finds mean valence near 3 but a broad spread, not a perfect hexagonal lattice.

## Joins

- **Join** with `philosophy/milnor.py`: item 5 is the same polygon (`milnor.borromean()`, imported unmodified) and gives the same mu(123) = -1.
- **Join of link type** with `philosophy/PSYCHOSIS.md`: that file uses the Borromean rings, and its table reports mu = -1 computed by `milnor.py`. This script does not read PSYCHOSIS.md, so only the link type is claimed shared, not the polygon. The figure Lacan draws is not a polygon at all. Mao, Sun and Seeman built this link from DNA strands in 1997. The join is in the mathematics only; it says nothing about psychology.
- **Join** inside this file: items 1-4 all use one invariant, the Gauss linking number, computed by the same code. Item 4's matrix is the adjacency matrix of a planar graph, the same object as any graph adjacency in the repo; no specific graph file is named here (open).
- **Analogy**: knotted proteins (below) are open chains, so knot type there needs a closure rule; it is not the closed-curve invariant computed here.

## Sources

| Source | What it supports | Read status |
|---|---|---|
| Calugareanu, G., 1959 (Czech. Math. J.); White, J. H., Amer. J. Math. 91, 1969; Fuller, F. B., PNAS 68, 1971 | Lk = Tw + Wr | from memory, not opened |
| Milnor, J., "Link groups", Annals of Math. 59, 1954 | mu invariants (via milnor.py) | from memory, not opened (as cited in milnor.py) |
| Chen, J., Rauch, C. A., White, J. H., Englund, P. T., Cozzarelli, N. R., "The topology of the kinetoplast DNA network", Cell 80(1):61-69, 1995 | kDNA of Crithidia fasciculata, mean valence 3, hexagonal model | search result only |
| He, P., Katan, A. J., Tubiana, L., Dekker, C., Michieletto, D., "Single-molecule structure and topology of kinetoplast DNA networks", arXiv 2209.01293 (2022); published in Phys. Rev. X 13:021010 (2023) | broad valence distribution; not a perfect lattice | search result only |
| Mao, C., Sun, W., Seeman, N. C., "Assembly of Borromean rings from DNA", Nature 386:137-138, 1997 | Borromean rings made from DNA | search result only |
| Virnau, P., Mirny, L. A., Kardar, M., "Intricate knots in proteins: function and evolution", PLoS Comput. Biol. 2(9):e122, 2006 | 5_2 knot in UCH-L3; UCH-L1 (PDB 2etl) listed as 5_2 on the authors' lab table | search result only |

## Open

1. Compute Tw and Wr separately (exactly, for polygons where possible) on the figure-eight core, and so explain the measured offset Lk - n = 1 in 2b.
2. Check that the catenane after |k| flips is the unlink (needs a stronger invariant or an explicit isotopy).
3. Kinetoplast with a realistic valence distribution, and the joint matrix of a replicating network (valence near 6 is reported in reviews; search result only).
4. Name the repo's graph files that item 4's adjacency matrix should be matched against.
