# Social: humanities with a finite check under each reading

Labels, used exactly: **checked-finite** (exact, exhaustive over a stated finite set), **tested**, **analogy** (a reading), **open**.
Every citation is "cited from memory" unless read. None was read here.
Run all: `bin/asteroid --no-lean culture/social/humanities.ath` (about 1 s). Each script: `python3 -I culture/social/NAME.py`, standard library, prints PASS then JSON.

Addison's view, followed here: in the humanities the value is the interpretable qualitative reading. The check is small and sits under it. Checking against published research is welcome. Sociology can become foundational for the project's philosophy.

## Small: the results
1. `condorcet.py` (checked-finite). 3 voters, strict rankings. 3 options: 216 profiles, 12 have a majority cycle (1/18), 204 have a Condorcet winner. 1/18 matches the known figure (cited from memory); two independent computations agree (tournament 3-cycle search, and win-count test). 4 options: 13824 profiles, 2352 with a cycle, 12288 with a Condorcet winner, 1536 without. The 4-option numbers are derived here, not remembered.
2. `weakties.py` (checked-finite). Every labelled graph on 1..5 vertices (1099) and every strong/weak labelling (59809). 896 graphs have a local bridge. 23862 labellings satisfy strong triadic closure. Easley-Kleinberg form (cited from memory): under strong triadic closure, a local bridge with an endpoint having two strong edges is weak. Holds in all, tested both with STC at every vertex and with STC only at the endpoint (as stated); a control without STC fails (smallest: path 0-1, 0-2, both strong), so the check is not vacuous. The bare form "every local bridge is weak" is false: one strong edge between two vertices is a counterexample (6652 strong local bridges among the closed labellings).
3. Deontic, no new code. "Ought implies can" is axiom D (O p -> P p), valid exactly on serial frames. `core/ontology/beauvoir.py` checks it on all relations up to 3 worlds; `humanities.ath` reuses it by a check line. That morality is this logic is a reading.
4. `ecology.py` (checked-finite for structure only). A chain on 2..5 levels is a non-symmetric preorder with least and greatest element, and maps onto the 2-chain. `asymmetry.py` runs at import and exposes no function, so the p-morphism test is repeated here. That Bronfenbrenner's five systems are such a chain is analogy.
5. `propp.py` (checked-finite for counts). m ordered functions: 2^m tales. Pairing rule (my assumption): function 2i+1 may appear only if 2i does. Count 3^(m//2) * 2^(m%2): 1, 2, 3, 6, 9, 18, ... for m = 0..5; checked for m up to 12. That tales obey the rule is analogy.

## Middle: readings (analogy, not checked)
- Granovetter is foundational for the philosophy: a weak tie between clusters carries what no strong tie can, the shape of a rhizome bridge. Strong triadic closure is a tree-like pressure toward closed clusters.
- Condorcet: a group can be cyclic when each member is not. Beauvoir: freedom needs the other's going on (seriality).
- Bronfenbrenner: nested contexts, one way out to the larger system, as the 2-chain.
- Propp: a tale is a sequence read in a fixed order, as a poem is a sequence of lines.

## Big: what is open
- Whether the exact claims survive on larger graphs and more voters: not checked, only up to the sizes above.
- Whether real social data satisfy strong triadic closure: not tested.
- All citations are unread. The 1/18 and the Easley-Kleinberg form agree with memory; that is not a check against the literature. Works, from memory: Condorcet 1785 Essai; Granovetter 1973 AJS; Easley-Kleinberg 2010 Networks, Crowds, and Markets; Kant, Critique of Pure Reason; Bronfenbrenner 1979 The Ecology of Human Development; Propp 1928 Morphology of the Folktale.

## Lateral links
- love: profiles. Condorcet enumerates profiles (rankings per voter) as `culture/love/check.py` enumerates profiles.
- philosophy: rhizome bridges. A local bridge is a bridge in the sense of `philosophy/rhizome.py`, weakened to "no shared neighbour". Beauvoir seriality is the deontic D check.
- ontology: the 2-chain of `core/ontology/asymmetry.py`; the ecology chain maps onto it.
- poetry: sequences. Propp's ordered functions and a poem's lines are both ordered subsets or sequences.

Side effect: running `humanities.ath` writes `frames.jsonl` at the repository root and updates `boards/`; use `ASTEROID_FRAMES=path` to keep frames elsewhere.
