# The brain, through the hairy ball

What this is: a **structural** fact about the cortex, checked. What it is not: a model of the mind or of subjective experience. Labels as elsewhere: **fact**, **checked-finite**, **open**.

## 1. The fact

- Each cortical hemisphere's surface is topologically a sphere. Neuroimaging uses this directly: cortical surfaces are inflated and mapped to a sphere for registration across people (Fischl, Sereno, Dale, *NeuroImage* 1999). Fact.
- The hairy ball theorem (Poincaré–Brouwer) says a continuous tangent field on a sphere vanishes somewhere. Poincaré–Hopf sharpens it: the indices of the zeros sum to the Euler characteristic, 2.
- So any smooth map on the cortex (thickness, an activation map, the gradient of any field) has critical points, at least two, with indices summing to 2. There is no "perfectly combed" cortex. Fact.

## 2. The check (`checked-finite`)

`hairy.py`: random smooth functions on subdivided icospheres (42, 162, 642 vertices), with the Banchoff index at every vertex. The index sum is 2 in every run (300 fields per size by default, 100 per size in the logged run), and every field had at least 6 critical points. Run: `python3 brain/hairy.py`.

## 3. What it joins

- **The sphere of fields** (BOARD.md): the same hairy-ball picture, with fields as the hairs. Here the sphere is literal.
- **Gravity** (`../gravity.ath`, `../essays/knowing.md`): there, every route falls back to others; here, every field has a point where it stops. Analogy, not theorem.

## 4. The limit

Topology constrains every map on the cortex, but it says nothing about which map a mind is, or what it is like to be one. Going from a surface to experience is the hard problem of consciousness, and nothing here touches it.

## Open

1. Run the check on a real cortical mesh (a public template surface), with its Euler characteristic computed from the mesh, not assumed.
2. Critical points of a real cortical map (e.g. a published thickness atlas): count and index them.
