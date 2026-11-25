# The ontology: one grid, shaped like a lantern

Source: Addison, 2026-11-25. "WE NEED ONTOLOGY and work down from outer balloon just as we work up from the brain." "each mapped subfeild is kind of like a perimeter or circumference of a cone shape ... we seriously have to work on the sides. its a bit of a tube." "infinite infinities must work towards the ouside of sphere. its a lot like if you squish the top and bottom and make a chinese lantern."

## The picture, and the object it names

| Addison's word | In the grid | The mathematical object |
|---|---|---|
| top and bottom | the largest and the smallest scale | the two poles |
| a perimeter, a ring | one **level**: one mapped subfield at one scale | a parallel (a circle of latitude) |
| a tube from every mapped science | one **rib**: a science followed from pole to pole | a meridian |
| the sides | **arrows**: maps between neighbouring levels and neighbouring ribs | the panels between the ribs |
| the outside | the **infinite family** at each level (all sizes n) | the direction pointing away from the axis |
| squish the top and bottom | pinch each end of the tube to a point | the suspension: a tube (a circle times an interval) with each end pinched is a sphere; the suspension of a circle is S² |

The choice of this shape is a design decision, an analogy. The facts about the shape are mathematics; they will be checked in `ontology/shape/` (planned, not yet written).

## A level is one file: `level.json` in the level's directory

```json
{
 "id": "biology/brain/dna",
 "ladder": "brain",
 "name": "DNA topology",
 "scale_m": [2e-9, 1e-6],
 "carriers": ["link"],
 "invariants": ["linking number"],
 "moves": ["crossing change"],
 "infinity": [
  {"family": "closed ribbons with n twists, every n",
   "handled_by": "moves",
   "reduction": "each full twist adds two crossings of the same sign, and the count is additive",
   "word": "checked-infinite"}
 ],
 "checks": [
  {"id": "ribbon-lk", "statement": "a closed ribbon with n twists has linking number n", "word": "checked-finite", "runner": "python3 -I biology/brain/dna/check.py"}
 ],
 "arrows": [
  {"to": "philosophy", "kind": "same_invariant", "what": "the linking number of Lacan's rings and of DNA circles is one invariant", "status": "join"}
 ],
 "new_terms": {}
}
```

- `ladder`: `brain` (from the cell upward), `cosmos` (from the whole downward), or the name of another rib.
- `scale_m`: the smallest and largest length, in metres, of the things at this level; `null` for a level with no physical scale.
- `carriers`, `invariants`, `moves`: terms from `vocab.json`. A new term goes in `new_terms` with a one-line definition.
- `infinity`: one entry per infinite family. `handled_by` is one of `formula`, `moves`, `limit`, `edge`, `open`, `impossible` (defined in `vocab.json`).
- `arrows`: `kind` from `vocab.json`; `status` is `join` (the same mathematical object, checked), `analogy`, or `proposed`.

## The rule about infinity

Every level names its infinite family and says how the infinity is handled. There are four ways, and two honest failures:

1. **formula**: a closed formula or recurrence valid for every n, confirmed by a finite count done another way.
2. **moves**: finitely many kinds of local move reach every case, and the claim survives each move.
3. **limit**: a limit object or a compactness theorem.
4. **edge**: a physical cutoff past which the family does not continue.
5. **open**: not handled. 6. **impossible**: provably not reducible to a finite check.

A statement about every n is `checked-infinite` only with a finite check and the reduction: a short proof written out, or `cite:` a named theorem with its read status.

## Why this serves the aim

A level that declares its carrier inherits every check that exists for that carrier. Two levels with the same carrier and invariant are a proposed join before anyone has looked. That is the planned automated part: a reader (under `workshop/compute/monqwensor/`, which is stopped and not yet written) would read these files and propose connections; a person or a checker decides.
