# Psychosis in Lacan and in Deleuze–Guattari: the structures, labelled

What this is: the **formal structures** two bodies of theory use to describe psychosis, with what is checkable checked. What it is not: a clinical model, a diagnosis tool, or a claim that these theories are right. Sources are cited in the original French and read status is given; nothing is quoted. Labels: **checked-finite**, **join** (a repository result covers it), **analogy**, **open**.

## 1. Lacan

- **Foreclosure** (*Le Séminaire III: Les psychoses*, 1955–56; read: secondary only). Psychosis is structural: a founding signifier (the Name-of-the-Father) was never admitted to the symbolic order, and what is refused there returns from outside, in the real (hallucination). Formal reading: a chain of signifiers with a missing anchor, so meanings slide with no fixed point. Analogy; the fixed-point language is ours.
- **The Borromean knot** (*R.S.I.*, 1974–75; *Le Séminaire XXIII: Le sinthome*, 1975–76; read: secondary only). Real, Symbolic and Imaginary are three rings tied so that no two are linked but all three hold together; cut any one and the other two fall apart. Psychosis is the knot coming undone. The **sinthome** is a fourth ring that holds the three when the knot fails (Lacan's case is Joyce's writing).
  - **Checked-finite:** `borromean.py` computes the Gauss linking number of each pair of Borromean rings (0, 0, 0) against a Hopf-link control (±1). No two rings are linked. That all three are inseparable is Milnor's triple invariant μ(123) = ±1 (Milnor, *Annals of Mathematics* 59, 1954); cited, not computed here.
- **Against therapy as adjustment.** Lacan's analysis does not aim to return a person to a norm; for psychosis the later teaching aims at a sinthome that holds, a workable construction, not a cure by interpretation. This is a value, not a result. Recorded as such.

## 2. Deleuze and Guattari

- *L'Anti-Œdipe* (1972) and *Mille plateaux* (1980), together *Capitalisme et schizophrénie* (read: secondary only). Their "schizophrenia" is a **process**, the free flow of desire that capitalism both releases and re-binds. They separate it, in their own text, from the clinical schizophrenic, whom they describe as that process halted or broken. The two must not be merged.
- **Rhizome against tree** (*Mille plateaux*, introduction). A tree has one root and one path to each node; a rhizome connects any point to any other. **Join:** this is the tree-against-DAG distinction of `DAG.lean` (branches that can rejoin), and `lost_forever_iff_clash`.
- **Desiring-machines, flows and cuts.** Each machine cuts a flow from another. Formal reading: a network of couplings with no central controller. Analogy.
- **Guattari at La Borde** (institutional psychotherapy, with Jean Oury): the institution itself is treated, not only the patient. A practice, recorded as history.

## 3. Where the two meet and differ

Both refuse the family story as the whole explanation, and both treat psychosis as structural, not as a deficit to be trained away. They differ on the centre: Lacan keeps a knot that must hold (three rings, or four), and Deleuze–Guattari reject the central organizer altogether. In graph terms: a linked structure with a critical ring, against a rhizome with none. Analogy.

## 4. Limits, stated plainly

- These are philosophical and psychoanalytic theories. They are not established by clinical evidence, and they are contested within psychiatry.
- The current clinical research programmes are different in kind: aberrant salience (Kapur, *American Journal of Psychiatry* 160, 2003) and predictive-processing accounts. Neither is modelled here.
- Nothing here describes any particular person, and nothing here is advice about treatment.

## Open

1. Compute μ(123) for the three rings (a second checked-finite claim), and the same for a four-ring chain with the sinthome: remove one of the original three and check whether the rest still hold.
2. A small signifier-chain model of "sliding": a graph with and without an anchor node, comparing the fixed points.
3. Read the primary texts and change the read status.
