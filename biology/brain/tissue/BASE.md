# Tissue: cells join into sheets

What this is: the **combinatorics and topology** of an epithelium. An *epithelium* is a sheet of cells packed side by side; the nervous system starts as one (the neural plate). Seen from above, each cell is a polygon. Usually three cells meet at each corner, so the sheet is a *trivalent* tiling: every corner has three walls. What this is not: a model of the mind, a clinical claim, or a claim about any person. Run: `python3 -I biology/brain/tissue/check.py`. It prints PASS and `{"states": 37302, ...}` in about a second. Labels: **fact** (cited), **checked-finite** (exact and exhaustive over a stated finite set), **tested** (sampled or floating point), **join**, **analogy**, **open**.

One tool runs through the whole file. The *dual* of a trivalent tiling puts a point in each cell and joins neighbouring cells. Because three cells meet at each corner, the dual is a *triangulation*. A cell with s sides is a dual vertex of degree s. The script stores every sheet as its dual triangulation.

## Results

| # | Statement | Label | How |
|---|---|---|---|
| 1 | On a closed sheet (a sphere) with F cells and three cells per corner, the sum over cells of (6 − sides) is 12, so the mean number of sides is 6 − 12/F. | fact (Euler's formula V − E + F = 2); checked-finite on prisms with n = 3..40 and on every simulated map | exact integers |
| 1b | On a flat sheet the mean tends to 6 as F grows. | fact (follows from 1); the formula 6 − 12/F is checked, the limit is not computed | — |
| 2 | Gibson chain: stationary shares of cells with 5, 6, 7, 8, 9, 10 sides are 28.88, 46.40, 20.85, 3.59, 0.27, 0.01 percent; no 4-sided cells; mean 6. | checked-finite for the chain cut off at 24 sides (exact Fraction eigenvector, verified π P = π); the cut-off at 16 agrees to 1e−12 | exact |
| 3 | A direct simulation of topological division does **not** reproduce the chain's distribution (see below). | tested | 3 seeds × 6144 cells |
| 4 | A T1 transition (neighbour exchange) is an edge flip of the dual triangulation: two cells lose a side, two gain one, nothing else changes, χ stays 2. | tested: 200 random flips, each verified exactly (the counts are exact; the flips are sampled). That a T1 is the dual edge flip is standard in the literature, from memory, not cited here; the counting rule itself follows from the definitions | exact |
| 5 | Lewis's law and the Aboav–Weaire law | fact (empirical), not derived here | — |
| 6 | Flat sheet χ = 1; tube χ = 0; tube closed at both ends χ = 2. | checked-finite on square-grid complexes m = 3..8, n = 1..8 | exact counts |

*χ* (Euler characteristic) = vertices − edges + faces of a cell complex. It does not change under stretching, so it records shape up to topology.

### 2. The Gibson chain

Gibson, Patel, Nagpal and Perrimon (2006) model one round of division as a Markov chain on the number of sides. A cell with s sides divides. The new wall cuts two of its walls, so the two daughters have s + 4 sides in all, at least 4 each. In the model each daughter gets 4 + Binomial(s − 4, 1/2) sides. Then each cell gains one side from neighbours' divisions. The script checks that the daughters' mean is s/2 + 2, then solves for the stationary distribution exactly.

The orchestrator remembered 28.9, 46.4, 20.8, 3.6, 0.3 percent. The computed values round to 28.9, 46.4, **20.9**, 3.6, 0.3. The heptagon share 20.85 rounds to 20.9, not 20.8; this is a rounding difference only. I could not open the paper or its supplement (the download was blocked), so I have not compared these numbers with the published prediction or the published measurements. The rule I implemented was chosen because it is the one I recalled; it reproduces the remembered numbers to 0.1, and it is the only one of three variants I tried that does. Whether it is exactly the paper's rule: open item 1.

### 3. The simulation

The script divides every cell once per round, in random order, on a closed sheet that starts as a cube (6 squares), for 10 rounds. Bookkeeping is exact: the division is a vertex split in the dual, and the two cut neighbours each gain a side. Percent of cells with 4, 5, ..., 10 sides after 10 rounds:

| Rule for the cut | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|
| Gibson chain (exact) | 0 | 28.88 | 46.40 | 20.85 | 3.59 | 0.27 | 0.01 |
| Simulated, uniform pair of non-adjacent walls | 26.2 | 27.1 | 18.0 | 11.2 | 6.5 | 4.1 | 2.5 |
| Simulated, binomial split as in the chain | 17.4 | 27.2 | 23.5 | 15.3 | 8.7 | 4.4 | 2.0 |

The simulation is much broader than the chain and has many 4-sided cells. The likely reason: the chain assumes each cell gains exactly one side per round, while in the simulation the gain varies from cell to cell, and no relaxation moves (T1s) are applied. This is tested, not proved. Real epithelia also rearrange; the simulation does not.

### 5. Empirical laws (cited, not derived)

- **Lewis's law**: a cell's mean area grows roughly linearly with its number of sides. Lewis, F. T. (1928), *Anatomical Record*. From memory, not opened.
- **Aboav–Weaire law**: the mean number of sides of the neighbours of an n-sided cell is about 5 + 6/n (Aboav 1970, *Metallography*; Weaire 1974, *Metallography*). From memory, not opened. These are fits to data, not theorems.

### 6. Neural tube closure

The neural plate is a disc (χ = 1). It folds, and two opposite edges fuse: the result is an open tube (χ = 0). Fusing a path of k walls identifies k + 1 corners and k walls, so χ drops by exactly 1. The tube then closes at its two ends (the neuropores). Adding one cap cell at each end gives a sphere (χ = 2). Checked on square grids: the capped complex is built explicitly (squares plus two m-gon caps), every edge is checked to lie on exactly two faces, and V − E + F = 2 is counted for m = 3..8, n = 1..8. That closure happens this way in embryos is a fact of developmental biology (standard textbooks, from memory); only the counts are computed.

## Joins

- **Edge flip.** A T1 transition is the flip of one edge of the dual triangulation. That is the same move `biology/brain/membrane/check.py` uses to enumerate triangulations of the sphere by breadth-first search over edge flips. Join: `biology/brain/membrane/check.py` (section 1, `flips`).
- **Euler characteristic.** The same invariant χ as in `biology/brain/dna/` (topology of DNA loops is counted there by linking number, a different invariant; the shared object is the closed surface). Analogy until a shared computation exists.
- **Markov chain stationary vector.** An exact eigenvector computation in Fractions. Any other level with a finite Markov chain can reuse `stationary()`.

## Limits

- The chain is cut off at 24 sides; the true chain has no upper bound. The tail mass beyond is below 1e−12 by the agreement test, not by a proof.
- The simulation is on a sphere, not on a flat sheet with a boundary.
- No geometry: areas and lengths are not modelled, so Lewis's law cannot be tested here.

## Open items

1. Open the Gibson paper and supplement (hosted by the Perrimon lab); confirm the exact transition rule and their published prediction and measurements, and compare with the table above.
2. Add T1 relaxation to the simulation and see whether it moves towards the chain.
3. A flat sheet with a boundary, and a count of tilings (an integer sequence for fingerprints). None is produced here, so there is no fingerprints.json.

## Sources

- Gibson, M. C., Patel, A. B., Nagpal, R., Perrimon, N. (2006). "The emergence of geometric order in proliferating metazoan epithelia." *Nature* 442, 1038–1041, doi:10.1038/nature05014. Search result only: the search confirmed the title, authors, journal, and that the paper uses a Markov chain whose equilibrium polygon distribution is compared with tissue from several animals. The transition rule and numbers are from memory.
- Sandersius, S. A., Chuai, M., Weijer, C. J., Newman, T. J. (2011). "Correlating cell behavior with tissue topology in embryonic epithelia." *PLoS ONE* 6(4): e18081, doi:10.1371/journal.pone.0018081, arXiv:1201.5137. Search result only. Supports: non-spatial (Markov) models do not robustly reproduce the neighbour statistics of proliferating epithelia; spatial simulation does. A specific statement about 4-sided cells was not confirmed and is not claimed.
- Euler's polyhedron formula. Standard, from memory.
- Lewis 1928; Aboav 1970; Weaire 1974. From memory, not opened.
