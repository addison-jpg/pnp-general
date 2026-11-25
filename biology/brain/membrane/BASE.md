# Membranes and cages: Euler's formula inside the cell

What this is: the counting rules that hold on any closed surface, checked on the surfaces a cell is made of. A cell membrane and a vesicle (a small membrane bubble) are closed surfaces. So the **Euler characteristic** constrains every network drawn on them. What this is not: a model of any cell's behaviour, or of the mind. Labels: **fact** (in the literature, cited), **checked-finite** (exact and exhaustive over a stated finite set, rerunnable), **tested** (floating point), **join** (the same object as an existing repo file), **analogy**, **open**.

Terms. A *cell complex* is a surface cut into vertices (V), edges (E) and faces (F). Its **Euler characteristic** is χ = V − E + F. For a sphere χ = 2. For a closed orientable surface with g handles (genus g), χ = 2 − 2g. A *triangulation* is a cell complex where every face is a triangle. The *degree* of a vertex is the number of edges at it.

Run: `python3 -I biology/brain/membrane/check.py` (about 16 seconds, 174 886 flip states).

## What was checked

| # | Statement | Label | How |
|---|---|---|---|
| 1 | Triangulations of the sphere with n = 4, …, 12 vertices number 1, 1, 2, 5, 14, 50, 233, 1249, 7595 (up to isomorphism, mirror images identified). | checked-finite (given Wagner's theorem, a fact) | breadth-first search over edge flips from one triangulation; canonical code merges isomorphic ones |
| 2 | Every one of those 9 150 triangulations has E = 3V − 6, F = 2V − 4, and Σ(6 − degree) = 12. | checked-finite | exact integers, every triangulation |
| 3 | Icosahedral triangulations for (h, k) = (h, 0) and (h, h), h = 1..5, and one more T = 9 built a second way: V = 10T + 2, F = 20T, exactly 12 vertices of degree 5, all others degree 6. | checked-finite (on these 11 cases) | exact face subdivision, and the √3 operation (T → 3T) |
| 4 | The dual cage of each (one corner per triangle) has three faces at every corner, exactly 12 pentagons, the rest hexagons, 20T corners, and χ = 2. Subunit count 3 per triangle gives 60T. | checked-finite (11 cases); the general rule is fact (Euler) | exact |
| 5 | Two nested spheres joined by N tubes ("pores") form a closed surface with χ = 2 − 2(N − 1), for N = 1..8. | checked-finite (8 cases); genus N − 1 by the classification of surfaces, fact | explicit cell complex; each edge lies on exactly two face sides |
| 6 | A line field on the sphere with four +½ defects has charge 0 at the remaining point; the charges sum to 2. | tested (floating point) | winding of the line angle (mod π) on small loops, in two charts |

Why item 2 holds in general (fact): each triangle has 3 edges and each edge 2 triangles, so 2E = 3F; with V − E + F = 2 this gives E = 3V − 6. The degrees sum to 2E, so Σ(6 − deg) = 6V − 2(3V − 6) = 12. A cage with three faces per corner is the dual: faces become vertices, so Σ(6 − sides) = 12, and with only pentagons and hexagons there are exactly 12 pentagons.

The first T numbers, T = h² + hk + k²: 1, 3, 4, 7, 9, 12, 13, 16, 19, 21, 25, 27. Skew cases (h ≠ k, both nonzero, such as T = 7) are listed but not constructed. Open item 1.

## The biology the counts sit under

- **Virus capsids.** Caspar and Klug (1962): a spherical virus shell is built on an icosahedral triangulation with T = h² + hk + k², has 60T protein subunits, 12 pentamers and 10(T − 1) hexamers. Fact (cited). Items 3–4 check the counting part exactly for the cases built.
- **Clathrin coats.** Clathrin forms a cage of pentagons and hexagons around a budding vesicle, including synaptic vesicles being recycled at the nerve terminal. Each clathrin triskelion sits at a three-way corner. Then item 4's rule says such a closed cage has 12 pentagons. The rule is fact; that real coats are closed pentagon-hexagon cages (some also have heptagons, which the count then allows, one extra pentagon per heptagon) is from memory. Open item 2.
- **Nuclear envelope.** Two membranes joined at each nuclear pore. As a surface, a sphere with N tubes to an inner sphere has genus N − 1 (item 5). A nucleus with thousands of pores is therefore, topologically, a surface of genus in the thousands. Counting part checked-finite; biological numbers not cited here.
- **Actin line fields.** Maroudas-Sacks et al. (2021) report that defects in the aligned actin fibres of regenerating *Hydra* sit where the head and foot form. An aligned-fibre field has no arrowhead, so defects can have strength ½. On a sphere they must sum to 2 (Poincaré–Hopf for line fields, fact). Item 6 is a numeric example only.

## Joins

- **join: `biology/brain/hairy.py`.** The same Euler characteristic χ = 2 of the sphere. There the indices of critical points of a function on a model cortex sum to 2; here vertex curvatures (6 − degree)/6 sum to 2, and line-field defects sum to 2. One invariant, three readings.
- **join: `biology/brain/tissue/BASE.md` row 1.** The same sum Σ(6 − sides) = 12 for cells of a sheet with three cells per corner is item 4 here, the cage rule. Tissue counts cells; capsids and clathrin count protein faces.
- Shared object for the matcher: the triangulation counts are OEIS A000109 (from memory, not opened). The T numbers are the integers of the form h² + hk + k² (Löschian numbers, from memory).

## Limits

- The enumeration stops at 12 vertices (about 16 s). It is exhaustive only because Wagner's flip theorem says one flip class contains all triangulations; that theorem is cited, not rechecked.
- Counts identify a triangulation with its mirror image. The expected values (A000109) agreed with the computation; no disagreement.
- Icosahedral cases are only (h, 0) and (h, h). The check is combinatorial; no geometry or symmetry group is computed.
- Item 6 is floating point and one example.

## Open items

1. Construct skew capsids (h ≠ k, hk ≠ 0, e.g. T = 7) exactly, for example by the Goldberg–Coxeter construction.
2. Cite and read a clathrin cage structure paper; check heptagon counts (P − H₇ = 12) on real coat data.
3. A line-field check that is exact (combinatorial, on a triangulation) rather than floating point.

## Sources

- D. L. D. Caspar and A. Klug, "Physical principles in the construction of regular viruses", *Cold Spring Harbor Symposia on Quantitative Biology* 27 (1962) 1–24. Read status: search result only (title, venue, T formula, 60T, 12 pentamers confirmed by search).
- Y. Maroudas-Sacks, L. Garion, L. Shani-Zerbib, A. Livshits, E. Braun, K. Keren, "Topological defects in the nematic order of actin fibres as organization centres of *Hydra* morphogenesis", *Nature Physics* 17 (2021) 251–259. Read status: search result only (abstract-level summary).
- K. Wagner, "Bemerkungen zum Vierfarbenproblem", *Jahresbericht der DMV* 46 (1936): any two triangulations of the sphere with n vertices are joined by flips. Read status: from memory, not opened.
- OEIS A000109, triangulations of the sphere. Read status: from memory, not opened.
- Euler's polyhedron formula; Poincaré–Hopf theorem; classification of closed surfaces. Standard, from memory.
- Clathrin coats as pentagon-hexagon cages. Read status: from memory, no paper opened. Open item 2.
