# Metaphysics: possible worlds as finite frames

Source: Addison, 2026-11-25 (ontology/SOURCES.md). Checks: `metaphysics/metaphysics.ath`, run with `bin/asteroid metaphysics/metaphysics.ath --no-lean`.

Labels: **fact** (a cited theorem), **checked-finite** (exhausted by asteroid), **join** (the same object as a checked file elsewhere), **analogy (reading)**, **open**.

## Sources and read status

- Saul A. Kripke, "Semantical Considerations on Modal Logic", *Acta Philosophica Fennica* 16 (1963), 83–94. Read status: citation confirmed by web search; the paper was not opened here.
- Patrick Blackburn, Maarten de Rijke, Yde Venema, *Modal Logic*, Cambridge Tracts in Theoretical Computer Science 53, Cambridge University Press (2001). Read status: listing confirmed by web search; not opened here. Its correspondence results are cited, not quoted.
- David Lewis, *On the Plurality of Worlds*, Blackwell (1986). Read status: confirmed by web search; the indexical account of actuality is taken from the Stanford Encyclopedia supplement on possibilism and actualism, not from the book.
- Jean-François Lyotard, *La Condition postmoderne* (1979). Already cited in `cosmos/BASE.md` section 7.

## 1. The checked facts

A frame is a set of worlds and an accessibility relation. `[]p` is true at w when p holds at every world w sees.

| axiom | formula | valid on exactly | checked |
|---|---|---|---|
| T | `[]p -> p` | reflexive frames | all 512 relations on 3 worlds, all 65536 on 4 |
| 4 | `[]p -> [][]p` | transitive frames (3994 on 4 worlds) | all 65536 on 4 |
| B | `p -> []<>p` | symmetric frames | all 65536 on 4 |
| 5 | `<>p -> []<>p` | euclidean frames | all 65536 on 4 |
| S5 | T and 5 | equivalence relations (15 on 4 worlds) | all 65536 on 4 |

Each row is checked-finite. For every size it is a fact: the correspondence theorems (Blackburn, de Rijke, Venema 2001, ch. 3).

## 2. The one difference: axiom 5

`<>p -> []<>p` is valid on every S5 frame. It fails on an S4 frame (reflexive, transitive). The countermodel asteroid prints: worlds 0, 1, 2; world 0 sees 0 and 1; p only at 0. World 0 sees a p-world, but world 1 does not. A tree with a root and two branches fails the same way. Checked-finite.

So the precise difference between a flat picture and a directed history is this one axiom. In S5 what is possible from one place is possible from every place. In S4 a step forward can close off a possibility.

## 3. Readings (analogy)

- **Lewis: indexical actuality.** "Actual" picks out the speaker's own world. No world is privileged. Reading: an S5 frame with one class, where every world sees every world. Analogy.
- **Lyotard: incredulity toward metanarratives.** Reading: choosing a frame with no privileged vantage, so the symmetric, euclidean frame. Analogy.
- **A history with a direction.** Reading: S4. A partial order is a reflexive, transitive frame. Join: `lean/PEqualNP/Philosophy/DAG.lean` works with partial orders (`Lost`, `Rejoin`); a tree is a DAG where branches never rejoin, and `lost_forever_iff_apart` says when loss is permanent. The S4 countermodel above is the finite shape of a lost future. Join for the frame class; the modal reading of `Lost` is analogy.
- **The measure problem.** In an S5 frame no world is singled out, so nothing anchors a probability over worlds. `cosmos/BASE.md` shows that the ordering alone decides the frequency. Analogy; the cosmos toy is the checked part.

## 4. Open

- Count S4 frames that are trees (forests of rooted orders) and state the tree axiom.
- A Lean statement of the 4-world correspondence (`decide`), so the label could be checked by the kernel.
