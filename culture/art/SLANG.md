# Gay and ballroom slang, mapped onto the repository's structures

Addison: "gay slang mapping aint that hard." This file maps a few terms onto structures already in the repo, so the vocabulary can be queried and reasoned about. **Every mapping is a reading (analogy).** The checked part is only that the mapping is consistent (`slang.py`): one structure per term, every target exists, every term has a source.

**Care.** These words belong to the communities that use them, and many come from Black and Latino ballroom culture. The mapping says where a term's form would sit in this repo. It does not say what the word means to its users, and it must never be used to classify, label or police anyone. The structure "being recognised as something" is supplied by the listener, not by the person.

| term | the usage | where it sits here | the reading |
|---|---|---|---|
| camp | a theatrical, knowing exaggeration of style | `culture/art/camp.ath` | a broadcast read as style |
| read | a witty takedown that holds up | `core/ontology/qualquant.py` | a refutation with a counterexample, kept on the record |
| shade | an indirect hostility | `culture/homestuck/quadrants/check.py` | a negative edge (kismesis) |
| clocked | recognised as something | `culture/art/reference.py` | supplied by the listener; a broadcast cannot single you out |
| house | a chosen family, led by house parents | `culture/love/family.py` | a household in which no one is alone |
| tea | gossip that travels | `culture/art/reference.py` | a lateral link, not a broadcast from the hub |
| come for | to challenge someone | `core/ontology/asymmetry.py` | a one-way relation |

## Sources (cited from memory)

- *Paris Is Burning* (1990), directed by Jennie Livingston, documents New York ballroom culture, where "read", "shade", "house" and "realness" are used.
- Susan Sontag, "Notes on 'Camp'" (1964), took camp into wider culture; the word's queer usage is older. Its etymology is not checked here.
- Ballroom houses are commonly dated to Harlem in the 1920s and 30s.

## The check

`python3 -I culture/art/slang.py`: seven terms, each mapped to one existing file, each with a source note. It passes. It checks structure, not meaning.
