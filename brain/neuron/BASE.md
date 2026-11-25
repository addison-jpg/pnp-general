# One neuron: the dendritic arbor as a rooted binary tree

What this is: the branching **shape** of one neuron's dendrites, counted and checked. A dendrite is a branch of a nerve cell that receives input. What this is not: a model of what the neuron computes, or anything clinical. Labels: **fact** (cited), **checked-finite** (exact, exhaustive, rerunnable), **tested**, **join** (same object as a repo file), **analogy**, **open**. Every number below was printed and asserted by `check.py` (`python3 -I brain/neuron/check.py`, under one second).

## The object

An **arbor** is a rooted binary tree. A **tip** is a free end. A **branch point** splits one segment into two. A **segment** is the piece between two of these, including the trunk from the cell body. With n tips there are n − 1 branch points and 2n − 1 segments (checked-finite, every ordered tree, n ≤ 9). **Shape** means the tree without lengths. **Ordered** means left and right are told apart; **unordered** means they are not.

## 1. How many shapes (checked-finite, n ≤ 9; recurrence to 11)

| n tips | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| ordered (Catalan) | 1 | 1 | 2 | 5 | 14 | 42 | 132 | 429 | 1430 | | |
| unordered (Wedderburn–Etherington) | 1 | 1 | 1 | 2 | 3 | 6 | 11 | 23 | 46 | 98 | 207 |

Each row is counted by listing all trees and agrees with its recurrence. The orchestrator's expected values agree.

## 2. Two growth models

A **growth history** is the sequence of branchings that builds a tree from one tip. Two hypotheses. They predate 1983: Verwer, van Pelt and Noest 1987 credit Berry et al. 1980 (not opened; cited only as credited there) alongside van Pelt and Verwer 1983. The exact probabilities under both are given by van Pelt and Verwer 1983 (fact, from the abstract only):

- **Terminal growth**: each new branch forms on a tip chosen uniformly. Histories: (n − 1)! = 1, 1, 2, 6, 24, 120, 720, 5040, 40320.
- **Segmental growth**: each new branch forms on any segment chosen uniformly, tip or inner. Histories: (2n − 3)!! = 1, 1, 3, 15, 105, …, 2027025.

The exact probability of every unordered shape, n ≤ 9, is the share of histories that end in it (checked-finite; summed over all histories, and also listed one history at a time for n ≤ 7 by a second, separate implementation that stores each tree as a child list and does not reuse the first one's growth code; they agree). Examples (`*` is a tip):

| shape | terminal | segmental |
|---|---|---|
| n=4 chain `(((**)*)*)` | 2/3 | 4/5 |
| n=4 balanced `((**)(**))` | 1/3 | 1/5 |
| n=5 chain | 1/3 | 4/7 |
| n=5 `(((**)(**))*)` | 1/6 | 1/7 |
| n=5 `(((**)*)(**))` | 1/2 | 2/7 |

## 3. Join: the same two models in phylogenetics

For all 93 shapes with 2 ≤ n ≤ 9 (checked-finite):

- terminal growth = the **Yule** (equal-rates) model, computed by its product formula 2^(n−1−s) ∏ 1/(m_v − 1), where s counts branch points with two identical sides and m_v is the number of tips below branch point v;
- segmental growth = the **uniform (PDA)** model: probability = (number of leaf-labelled trees of that shape, n!/2^s) / (2n − 3)!!.

**Join:** (2n − 3)!! is the count of rooted binary phylogenetic trees already in `compbio/fingerprints.py` and `compbio/BASE.md`. Here it is also the number of segmental growth histories, and the labelled counts summed over shapes give it again (asserted). A neuron's arbor and a species tree are the same object under two growth rules.

## 4. The models are told apart by shape alone (checked-finite, n = 3..9)

**Partition asymmetry** of a branch point with r and s tips on its two sides is |r − s|/(r + s − 2), and 0 for r = s = 1. **Tree asymmetry** is its mean over all n − 1 branch points (van Pelt et al. 1992; the formula here is from memory and was not checked against the paper's text). **Horton–Strahler order**: a tip has order 1; a branch point takes the larger child order, plus 1 if the two are equal.

| n | E[asymmetry] terminal | segmental | E[Strahler] terminal | segmental |
|---|---|---|---|---|
| 3 | 1/2 | 1/2 | 2 | 2 |
| 4 | 4/9 | 8/15 | 7/3 | 11/5 |
| 5 | 11/24 | 47/84 | 8/3 | 17/7 |
| 6 | 34/75 | 359/630 | 43/15 | 55/21 |
| 7 | 247/540 | 1147/1980 | 133/45 | 91/33 |
| 8 | 1006/2205 | 26354/45045 | 946/315 | 408/143 |
| 9 | 513/1120 | 354587/600600 | 3851/1260 | 2088/715 |

For each n = 4..9, segmental growth gives higher expected asymmetry and lower expected Strahler order (checked-finite: both inequalities are asserted in the script, n = 4..9 only).

## 5. Criticality

A segment is **critical** if cutting it disconnects the arbor. In all 94 shapes for n ≤ 9, with the cell body as a vertex, the arbor is connected with 2n − 1 segments and 2n vertices, and every segment is critical (checked-finite). **Join:** `philosophy/rhizome.py` checks that a connected graph is a tree exactly when every edge is critical. One neuron's arbor is a tree in exactly that sense. That this matters for the cell (losing a segment loses everything beyond it) is a structural fact about trees, not a claim about any particular neuron.

## Limits

Only shape. No lengths, diameters, electrical properties, or the axon. Real arbors can have branch points with three children; these are excluded. Growth probabilities depending on segment order or type (van Pelt and Verwer 1985; Verwer, van Pelt and Noest 1987) are not computed.

## Open

1. The one-parameter family between terminal and segmental growth (Verwer, van Pelt and Noest 1987): compute exact shape probabilities as functions of the parameter.
2. Fitting to measured arbors: not done here. Which model fits which measured neurons is not claimed here.
3. Matching the Catalan row with the non-crossing structures named in `compbio/BASE.md`: for the matcher.

## Sources

- J. van Pelt, R. W. H. Verwer, "The exact probabilities of branching patterns under terminal and segmental growth hypotheses", *Bulletin of Mathematical Biology* 45 (1983) 269–285, doi 10.1007/BF02462361. Read status: search result only (abstract summary).
- R. W. H. Verwer, J. van Pelt, A. J. Noest, *Bulletin of Mathematical Biology* 49 (1987) 363–378, doi 10.1007/BF02460126. A one-parameter growth model with terminal and segmental growth as special cases; credits Berry et al. 1980 for the models. Search result only (bibliographic details from an independent checker's search).
- J. van Pelt, H. B. M. Uylings, R. W. H. Verwer, R. J. Pentney, M. J. Woldenberg, "Tree asymmetry: a sensitive and practical measure for binary topological trees", *Bulletin of Mathematical Biology* 54(5) (1992) 759–784, doi 10.1007/BF02459929. Search result only (from an independent checker's search); the asymmetry formula was not confirmed against the text.
- D. Aldous, "Stochastic models and descriptive statistics for phylogenetic trees, from Yule to today", *Statistical Science* 16(1) (2001) 23–34. From memory, not opened (Yule and uniform/PDA models).
