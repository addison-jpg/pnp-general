# Sociology into the ontology

Addison, 2026-11-25: "sociology really worth a direct workflow to phil/ontology." This file is that workflow, small to big.

**Labels:** checked-finite (exact, exhaustive over a stated finite set), tested, analogy (a reading), open.
**Read status:** every work below is cited from memory. None was read for this file. Years and titles may be off.

## Small: what is computed

| sociology | in the repository | label |
|---|---|---|
| Granovetter, "The Strength of Weak Ties" (1973); Easley and Kleinberg, *Networks, Crowds, and Markets* (2010) | `culture/social/weakties.py` counts local bridges. `core/ontology/joins/bridges.py`: every bridge of `philosophy/rhizome.py` is a local bridge, not conversely, on every connected labelled graph on 1..6 vertices. | checked-finite |
| Heider (1946); Cartwright and Harary (1956), structural balance | `culture/homestuck/quadrants/check.py`: balanced quadrant labellings 4, 36, 864, 63504 for 2..5 trolls. `culture/love/check.py` imports the same test for refusals. | checked-finite for the counts; the join is open (`core/ontology/joins/candidates.ath`) |
| Condorcet, *Essai* (1785) | `culture/social/condorcet.py` counts 3 voters on 3 or 4 options. `core/ontology/joins/social_love.ath` checks only the love side, 1, 16, 46656 = ((n!)^n)^2. The two meet only at n = 3 (216), so there is no record. | checked-finite for each side's own count; the join is open |
| Simmel, *Soziologie* (1908), the dyad and the triad | A dyad is one edge, a love pair. A triad adds a third person; strong triadic closure (`weakties.py`) is the rule that a triad with two strong ties closes. | checked-finite for the closure counts; analogy for Simmel |

## Middle: readings

| sociology | in the repository | label |
|---|---|---|
| Goffman, *Frame Analysis* (1974) | The repository's `frame` statement: a frame ties a source to the reading a claim formalizes (`asteroid/ext_frame.py`). Goffman's frame is how a situation is read; here the reading is written down with its label. | analogy |
| Bourdieu, fields (for example *Les Règles de l'art*, 1992) | `core/ontology/FIELDS.md`. A field is a space of positions with its own stakes; a universe here is a field with its own checks. | analogy |
| Durkheim, *Les Règles de la méthode sociologique* (1895), social facts | The centre store (`center/shards`). A social fact is external to each person and constrains them; a record in the centre is external to each seat and constrains what the next seat may claim. | analogy |
| Granovetter and Easley-Kleinberg, again | Lateral links in `philosophy/cone.py`: a record of one universe citing another is a weak tie between clusters. | analogy |

## Big: the map

| sociology | in the repository | label |
|---|---|---|
| Latour, actor-network theory (for example *Reassembling the Social*, 2005) | Lateral links without a hub. Each join in `core/ontology/joins/` links two universes directly, not through `big.ath`. Enough of them make the hub not critical (`philosophy/cone.py`, fact 1). | analogy for Latour; checked-finite for the graph fact |
| Lyotard, *La Condition postmoderne* (1979) | `core/ontology/joins/postmodern.ath`: postmodern-safe = valid on every frame of a class; S5 = no privileged world; a hub is critical exactly when its base is disconnected. A free hub is not yet a disk: the cone is a disk only over one path or one cycle (`philosophy/cone.py` fact 3). | checked-finite for the S5 and cone facts; analogy for the reading, and for reading the free hub or the disk as postmodernism |

## The map, measured

Measured with `python3 -I center.py`, then `python3 -I philosophy/cone.py` and `python3 -I core/universes/network.py`, 2026-11-25. Exact for the store at that time. The store changes with every record.

- Before the joins: 26 universes, 9 lateral links, 17 pieces, 14 isolated. Links still needed to free the hub: 16. These numbers rest on the builder's run; the review did not reproduce them.
- Join records: 6, each with a shared fact computed from both sides and confirmed by a second seat. Two candidates (social and love, cosmos and time) were demoted to open frames with no record. Their shared fact was not computed from both sides.
- Each join record also cites its `.ath` file under `core/ontology/`, so `cone.py` links its universe to ontology too. 4 links (brain, curvature, privacy and time to ontology) come only from that file placement. They are not shared facts.
- After the joins, shared facts only (placement links left out): 29 universes, 16 lateral links, 14 pieces, 11 isolated. Links still needed to free the hub: 13. Pieces: one of 13 universes, poetry with privacy and time, and cosmos with essays.
- After the joins, as `cone.py` prints it (placement links counted): 20 lateral links, 13 pieces, 11 isolated. Links still needed to free the hub: 12. A disk needs a ring through all 29 universes.
- Without any join record the same store has 10 links, 19 pieces and 16 isolated. Three of the 29 universes (narrative, queer, race) came from another build during this run.
- No join frees the hub, and none makes a disk. The hub is still critical.
- Keystones as `cone.py` counts the map (a universe whose loss splits its piece): asteroid, brain, circuits, ontology, philosophy. Transit is no longer one: brain, curvature, philosophy and transit close a cycle, and those links are shared facts.
- Still isolated: carseat, homestuck, lateral, love, methods, narrative, prompt-method, quantum-gravity, queer, routing, worlds.

## Open

1. Read the sources and change the read status.
2. A balance script in `culture/social` that recounts the quadrant numbers, to join social and homestuck.
3. Two open joins need a count from both sides: a social count of n voters on n options for n = 1..3 (social and love), and a function from `physics/time` that enters the cosmos computation (cosmos and time).
