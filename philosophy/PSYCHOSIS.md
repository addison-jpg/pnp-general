# Psychosis in Lacan and in Deleuze–Guattari: the structures, computed where they can be

What this is: the **formal structures** two bodies of theory use to describe psychosis, with every checkable part checked. Lacan chose a mathematical object (a link of rings) as his model, so his claims about it can be computed. What this is not: a clinical model, a diagnosis tool, or evidence that either theory is right about people. Sources are cited in the original French with read status; nothing is quoted. Labels: **checked-finite** (exact, exhaustive, rerunnable), **tested**, **join** (a repository result covers it), **analogy**, **open**.

## 1. Lacan

- **Foreclosure** (*Le Séminaire III: Les psychoses*, 1955–56; "D'une question préliminaire à tout traitement possible de la psychose", *Écrits*, 1966; read: secondary only). Psychosis is structural: a founding signifier (the Name-of-the-Father) was never admitted to the symbolic order, and what is refused there returns from outside, in the real. Formal reading: a chain of signifiers with a missing anchor. Analogy; open item 2.
- **The Borromean knot** (introduced in *Le Séminaire XIX*, 1972; *R.S.I.*, 1974–75; *Le Séminaire XXIII: Le sinthome*, 1975–76; read: secondary only). Real, Symbolic and Imaginary are three rings: no two are linked, yet all three hold together, and cutting any one frees the other two. Psychosis is the knot failing. The **sinthome** is a fourth ring that holds the three when they do not hold by themselves.
- **Against therapy as adjustment.** Lacan's analysis does not aim to return a person to a norm. For psychosis the later teaching aims at a sinthome that holds: a construction the person can live with, not a cure by interpretation. This is a value, not a result, and it is recorded as one.

### What was computed (`milnor.py`)

A link here is a set of closed polygons with integer coordinates. The program turns it into a diagram and computes Milnor's invariants (Milnor, "Link groups", *Annals of Mathematics* 59, 1954; read: statement only) in exact integer arithmetic. The linking number lk says whether two rings are linked. The triple number μ(ijk) detects three rings that hold together with no two linked. μ(ijkl), defined once all shorter invariants vanish, detects one kind of four-ring inseparability. Each result is the same in every view tried, and the Borromean triple number is confirmed by a second method (counting the one point where three flat discs meet: Mellor and Melvin, *Algebraic & Geometric Topology* 3, 2003; read: abstract and theorem statement).

| Lacan's structure | The link | Computed | What it shows |
|---|---|---|---|
| The knot holds | Borromean rings R, S, I | every lk = 0; μ(RSI) = μ(SIR) = μ(IRS) = −1 | No two rings are linked. No ring can be pulled away from the others. Cutting any one ring frees the other two (row below), so no ring is more critical than another. (That μ is the same from each ring is cyclic symmetry, true for every link, so it is not evidence here.) |
| One ring is cut | any two of the three | lk = 0 | The remaining two come apart. |
| An error at one crossing (Lacan on Joyce, *Sém. XXIII*) | Borromean rings with one R–S crossing changed (16 cases) | lk(R, S) = ±1; lk(R, I) = lk(S, I) = 0 | R and S lock together, and I is free. This is what Lacan says of Joyce: the imaginary slips away. |
| Three loose rings and a sinthome | four rings R, S, I, Σ (Bing double) | every lk = 0; every μ(ijk) = 0; μ(RSIΣ) = +1 | The three alone fall apart. With Σ, all four hold. Every ring is still critical, Σ included. |
| Paranoia: the three in one continuous ring, knotted (*Sém. XXIII*, 16 December 1975) | trefoil | 9 Fox 3-colourings; a plain ring has 3 | The single ring is knotted. |

How to read "come apart": the invariants classify links up to **link homotopy**, where a ring may pass through itself but not through another ring. For two and three rings they are complete (Milnor 1954), so "all invariants zero" means the rings separate in that sense. That they separate without any self-crossing is the classical property of these links, cited, not computed. "Hold together" is the stronger direction and needs no qualifier: a nonzero invariant rules out separating any ring or group of rings.

Two facts from the computation worth stating:

- The triple number is **unchanged by a mirror image** and changes sign when one ring's direction is reversed. (A mirror multiplies an invariant of length r by (−1)^(r−1): linking numbers flip, the triple number does not, the fourfold one does.) So this number cannot tell the knot from its mirror image. That fits the classical fact, cited and not computed here, that the Borromean rings are the same as their mirror image.
- The four-ring chain is exactly as fragile as the three-ring knot. The sinthome makes the rings hold; it does not make the structure robust.

Not encoded: Lacan's own drawing of Joyce's repaired knot, which is not the four-ring chain (in it R and S stay linked and the fourth ring catches I at the site of the error). It needs the figure from the primary text. Open item 1.

`borromean.py` is the earlier numerical version (Gauss integral, **tested**); `milnor.py` supersedes it.

## 2. Deleuze and Guattari

- *L'Anti-Œdipe* (1972) and *Mille plateaux* (1980), together *Capitalisme et schizophrénie* (read: secondary only). Their "schizophrenia" is a **process**: the free flow of desire, which capitalism both releases and binds again. They separate it, in their own text, from the clinical schizophrenic, whom they describe as that process halted. The two must not be merged.
- **Rhizome against tree** (*Mille plateaux*, introduction). A tree has one root and one path to each point. A rhizome connects any point to any other, and a break does not end it. **Join:** the tree-against-DAG distinction of `DAG.lean`, and `lost_forever_iff_clash`.
- **Desiring-machines, flows and cuts.** Each machine cuts a flow from another. Formal reading: a network of couplings with no central controller. Analogy.
- **Guattari at La Borde** (institutional psychotherapy, with Jean Oury): the institution is treated, not only the patient. A practice, recorded as history.

### What was computed (`rhizome.py`)

Call an edge **critical** if removing it disconnects the graph. Over every labelled graph on up to 6 vertices (33,867 graphs, none sampled):

- A connected graph is a tree exactly when **every** edge is critical.
- Adding one edge to a tree leaves exactly (n − 1) − d bridges, where d is the tree distance between its ends: the d + 1 edges of the cycle it closes stop being critical. (The program checks the count; that the freed edges are those of the cycle is the standard argument.)
- Graphs with **no** critical edge (the rhizome's defining property) number 1, 0, 1, 10, 253, 11968 for 1 to 6 vertices, against 1, 1, 3, 16, 125, 1296 trees.

## 3. Where the two differ, exactly

The usual summary is "Lacan keeps a centre, Deleuze and Guattari reject it". The computations say something more precise.

- The Borromean knot has **no centre**. No ring is privileged: cutting any one of them frees the others. And no two rings are even linked. It is not a tree with a root.
- What the Borromean knot shares with the tree is **criticality**: every element is critical. Cut any ring and everything comes apart; cut any edge of a tree and it disconnects. The four-ring chain keeps that property.
- The rhizome is the opposite extreme: no element is critical.

So the formal difference between the two models is not centre against no centre. It is **every part critical against no part critical**. Read that way:

- For Lacan, psychosis is the failure of a critical element, and stabilisation is an added element that makes the rest hold again (the sinthome).
- For Deleuze and Guattari, a structure in which one failure undoes everything is itself the problem, and their "process" is a structure with nothing critical in it.

The two graph and link facts are checked. The reading of the two theories through them is an **analogy**, and it is mine: neither text states it this way.

## 4. Limits, stated plainly

- These are philosophical and psychoanalytic theories. They are not established by clinical evidence, and they are contested within psychiatry.
- The current clinical research programmes are different in kind: aberrant salience (Kapur, *American Journal of Psychiatry* 160, 2003) and predictive-processing accounts. Neither is modelled here.
- The computations establish facts about links and graphs. They show that Lacan's topological claims are correct as mathematics. They do not show that minds are links.
- Nothing here describes any particular person, and nothing here is advice about treatment.

## Open

1. Encode Lacan's drawing of Joyce's repaired knot from the primary text (page cited), and compute its invariants.
2. A small signifier-chain model of "sliding": a graph with and without an anchor node, comparing the fixed points.
3. Read the primary texts and change the read status.
4. A criticality measure that puts links and graphs on one scale (the fraction of elements whose removal frees everything), and where Lacan's other drawings fall on it.
