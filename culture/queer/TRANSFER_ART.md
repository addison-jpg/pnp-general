# Transfer to queer art: works and their relations, not people

Downstream of `core/ontology/TRANSFER.md`. The lemma applies here as follows. Let the instances be a finite set of artworks with a relation "A speaks to B" (one work reads, answers or cites another). A property P is a question about that set. If φ maps the artworks into a proven field where P is decided, then deciding there decides P for the artworks.

## The map that is checked

- **Works to worlds, and "speaks to" to a relation R.** A work's reading of another is an edge A R B.
- **The property to the mirror.** `core/ontology/mirror.py` decides when R is a mirror: reciprocal, and every reached work can go on. On 1 to 3 works there are 2, 8 and 64 mirrors, with the two encodings agreeing on every relation.
- **Both directions hold by construction.** A relation is a mirror of works exactly when it is a mirror of worlds. The map is the identity on structure, so the transfer is exact.

## What this does and does not say

- It says that a *reciprocal* reading, where each work answers the other and every answered work can answer back, is a checked structure. It does not say a work is good, true or queer enough.
- The reading that reciprocity is what makes speaking to someone more than a broadcast is analogy. It connects to `culture/art/reference.py`: on a broadcast star no listener is singled out, and a lateral link is what singles one out.
- Nothing here classifies a person. The works are the instances; artists and audiences are not coded.
- The broad claim, that queer art as a whole is formalized by this map, is not made. The lemma needs the property and the map to match, and that is shown only on the small case above.

## Limits from the barriers

As in `core/ontology/TRANSFER.md`, a map too general to be checked is not a transfer. Here the checked case is small; extending it to a whole corpus is a separate claim, to be checked the same way, one relation at a time.
