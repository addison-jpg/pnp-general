# The formal structure of cryptographic assumptions

`structure.py` treats known implications between assumptions as a directed graph. It checks the equivalence classes (strongly connected components) and the reachability closure. It passes: OWF and PRG are the only mutually implying pair, and OWF reaches P != NP.

**Scope.** This is the shape of implications between assumptions, from published reductions cited from memory. It computes no attack, and it does not suggest any. Breaking an assumption is not what the file does.

**Gaps are not claims.** Edges that are absent are not recorded as separations, except the one listed as such. The known separations (for example, that public-key encryption is not implied by one-way functions in a black-box way; Impagliazzo and Rudich 1989) would be added as a separate kind of fact, with its source.
