# The cortex: the hairy ball made exact, and fields without arrowheads

What this is: the top level. Each hemisphere's cortical surface is, topologically, a sphere. `brain/hairy.py` tests the hairy ball theorem on it with random smooth functions (floating point). This level makes the theorem **exact and exhaustive** on small spheres, extends it to **direction fields without arrowheads** (line fields, as in the orientation map of visual cortex), and tests the **pinwheel density** of a random field. What this is not: a model of perception or of the mind, or a clinical claim. These are structural facts about surfaces and fields. Labels: **fact** (in the literature, cited), **checked-finite** (exact and exhaustive over a stated finite set, rerunnable), **tested** (sampled or floating point), **join** (the same object as an existing repo file), **analogy**, **open**.

Run: `python3 -I brain/cortex/check.py` (about 8 s). `--full` adds the octahedron (about 75 s more).

Terms. A *triangulated sphere* is a sphere cut into vertices, edges and triangles (cells). A *discrete vector field* (Forman) pairs some cells with one neighbouring cell of one dimension higher (a vertex with an edge on it, or an edge with a triangle on it); each cell is in at most one pair, and following pairs never closes a loop. A cell in no pair is *critical*. A *line field* is a field of directions with no arrowhead (a line, not an arrow). A *defect* (singular point) is where the field is undefined; its *strength* is how many half-turns the line makes going once around it, divided by two. A *pinwheel* is such a defect in an orientation map.

| # | Claim | Label | Result |
|---|---|---|---|
| 1 | Boundary of the tetrahedron: there are 4333 discrete vector fields; in every one, critical vertices − critical edges + critical triangles = 2; so none is free of critical cells (minimum 2). | checked-finite | exhaustive enumeration |
| 2 | Octahedron: 12845921 discrete vector fields; the same alternating sum is 2 in every one; minimum 2 critical cells. | checked-finite (with `--full`) | exhaustive enumeration |
| 3 | Circle (cycle C_n): number of fields for n = 3..10 is 16, 45, 121, 320, 841, 2205, 5776, 15125, equal to Lucas L_2n − 2; critical vertices − critical edges = 0 always. | checked-finite | enumeration, compared with Lucas numbers |
| 4 | 20 random smooth line fields on a 5120-triangle sphere: every defect has strength +½ or −½; strengths sum to 2 every time; 4 to 24 defects per field. | tested | floating point, parallel transport on the sphere |
| 5 | Random superposition of 40 plane waves of one wavelength L (random directions, phases): phase singularities per L² = 3.054 ± 0.046 (standard error, 8 samples of 16L × 16L). Theory for such a field: π ≈ 3.142. | tested | grid count of phase winding |

Item 1 and 2 are the discrete hairy ball theorem: Forman's weak Morse inequality says the alternating count of critical cells equals the Euler characteristic χ (fact, Forman 1998). The script checks it on every field, not on a sample. The icosahedron (62 cells) was not enumerated: the octahedron (26 cells) already has about 1.3 × 10⁷ fields.

Item 5 is about 1.9 standard errors below π. The likely cause is the grid (24 points per L): two singularities closer than one grid step can cancel and be missed. Kept as computed.

What item 5 shows and does not show. Bonhoeffer and Grinvald (1991) found orientation preference in cat visual cortex arranged around pinwheel centres (fact). Orientation repeats after a half-turn, so its phase is twice the orientation, and pinwheels are the ±½ defects of item 4. Kaschube et al. (2010) measured pinwheel density close to π per squared column spacing in three distantly related species (fact). A random field built from one wavelength already gives π (item 5), so π is the baseline the measurement is compared with. It does not explain the cortex. Kaschube et al. also report that randomized maps keeping the measured spectrum gave a higher density (about 3.5; search snippet), and use that difference as their argument; this script does not reproduce it.

## Joins

- **join: `brain/hairy.py`.** Same sphere, same χ = 2. There: indices of critical points of functions sum to 2 (tested). Here: the discrete version, exact (items 1–2).
- **join: `brain/membrane/` (item 6 and the *Hydra* actin note).** The same object: a line field on the sphere whose ±½ defects sum to χ = 2. Membrane checks one example; item 4 here checks 20 random fields with the same rule. Actin defects in *Hydra* and pinwheels in cortex are both defects of a line field; that the biology is related beyond this shared rule is not claimed.
- **join: `brain/tissue/`.** Same Euler characteristic of a closed sheet, there read through cell side counts (6 − sides sums to 12).
- **`philosophy/PSYCHOSIS.md`: no join.** Its objects are links of rings (knots). Nothing computed here is the same object. None is forced.
- Item 3 is a fingerprint (`fingerprints.json`): Lucas L_2n − 2, for the matcher.

## Limits

Small complexes only for the exact checks. Line-field and pinwheel results are floating point. The random field is a null model, not a cortex.

## Open

1. Run items 1 and 4 on a real cortical surface mesh (a public template such as fsaverage). Not downloaded here. Open.
2. Icosahedron count of discrete vector fields (needs a smarter count, e.g. transfer matrices).
3. Reproduce the Kaschube randomized-map control (density above π).

## Sources

- R. Forman, "Morse theory for cell complexes", *Advances in Mathematics* 134 (1998) 90–145, doi 10.1006/aima.1997.1650. Read status: search result only.
- T. Bonhoeffer, A. Grinvald, "Iso-orientation domains in cat visual cortex are arranged in pinwheel-like patterns", *Nature* 353 (1991) 429–431. Read status: search result only (abstract-level).
- M. Kaschube, M. Schnabel, S. Löwel, D. M. Coppola, L. E. White, F. Wolf, "Universality in the evolution of orientation columns in the visual cortex", *Science* 330 (2010) 1113–1116, doi 10.1126/science.1194869. Read status: search result only.
- Lucas numbers and matchings of a cycle: from memory, not opened (the script checks the equality for n = 3..10).
