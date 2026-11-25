# Transfer: when extending a field solves a subclass

Proposed by Addison (2026-11-25): for a subclass of an open problem with a large literature, solving the subclass could be as simple as extending it to a larger, related, proven field. This file states the precise version, shows why the broad version is false, and gives a checkable case.

## 1. The precise lemma (true)

**Transfer lemma.** Let P be a question on instances, S a subclass of instances, and T a proven theory. Suppose a map φ sends each instance of S to an instance of a question Q in T, and P(x) holds exactly when Q(φ(x)) holds. Then deciding Q on the image of φ decides P on S.

This is a reduction. It is true, and it is only as strong as φ. Everything depends on whether φ is computable, preserves the property both ways, and reaches the subclass that matters.

## 2. Why the broad version is false

The broad claim would be: for any open problem and any subclass with a large literature, some proven field extends it, so solving is as simple as extending. Published barriers rule out the methods that such extensions usually need (cited from memory, not re-read here):
- **Relativization** (Baker, Gill, Solovay, 1975): a proof technique that works relative to every oracle cannot separate P from NP.
- **Natural proofs** (Razborov, Rudich, 1997): a broad, constructive lower-bound method, under a cryptographic assumption, cannot separate the classes.
- **Algebrization** (Aaronson, Wigderson, 2009): extending relativization with algebraic oracles leaves a similar limit.

So an extension that is too general hits a barrier, and one that avoids the barriers is narrow. The claim "as simple as extending" fails exactly where the literature is large.

## 3. The checkable case in the repo

`core/ontology/asymmetry.py` checks a transfer: every non-symmetric preorder on up to four worlds maps onto the 2-chain, preserving non-symmetry. The map is explicit and the property is preserved both ways on every case checked. The transfer is real, and it is small, which is why it can be checked.

## 4. The honest form for the front page

A subclass is solved by transfer when (a) φ is explicit, (b) the property is preserved both ways, and (c) the barriers do not apply to the method used. Each of these is a checkable condition. The general claim, without the conditions, is not a theorem and is not stated as one here.
