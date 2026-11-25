# Computational biology, entered through combinatorics

Comp bio is too large to add by hand, and the aim (top of BOARD.md) is to absorb fields through their counting sequences. This is that route's first test: three exact sequences, each by exhaustive enumeration and checked two independent ways (`fingerprints.py`, assertions).

| Object | Sequence (n = 0 or 2 upward) | Known as | Source |
|---|---|---|---|
| Rooted binary phylogenetic trees on n labelled leaves | 1, 3, 15, 105, 945, 10395, 135135 | (2n−3)!! | Schröder 1870; Felsenstein 1978 |
| RNA secondary structures, hairpin loop ≥ 1 | 1, 1, 1, 2, 4, 8, 17, 37, 82 | OEIS A004148 | Waterman 1978; Stein–Waterman 1979 |
| The same with loop ≥ 0 | 1, 1, 2, 4, 9, 21, 51, 127, 323 | Motzkin numbers | — |

These are the fingerprints the centre will match across fields. The Motzkin and Catalan family also counts non-crossing structures in other areas: lattice paths, and the non-crossing pairings that sit behind the point-program and payment structures of the circuit work (non-crossing, as in B9's programs). Whether that shared family is a real join or a rhyme is for the matcher to propose and a seat to check. Source read status: from memory; to be checked before anyone cites them.

Open: the matcher itself (fingerprint fields on centre records, exact and transformed matches, OEIS lookup).
