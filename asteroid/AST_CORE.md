# ast: the core (proposed, 2026-11-25)

This is a design, not a result. Nothing here is built yet.

## The rule

- **Rust is only the exe.** It holds the prompter (the `4ST>` prompt), file loading, the parser, a small evaluator for the core statements below, and a small checking kernel. Addison: Rust "should really only be for exe prompter". Target: a few thousand lines, measured and reported in this file once built.
- **`.ath` holds all domain logic.** Love, cone, curvature, poetry, quadrants: every check is a `.ath` program, readable and frameable by the ontology.
- **Python is the reference.** It stays as the differential oracle: every core statement must give the same verdict in Rust and in Python on every root program. It is not extended further.
- **Lean is the archive.** The 91 Lean-checked results keep their label `checked` and are not rerun. No new `by lean` claims.

## What `.ath` needs that it lacks

Today `forall` and `count` range only over circuits, and finite mathematics runs in Python behind `check` lines. The core adds a few general primitives, all finite, all exact:

| primitive | meaning |
|---|---|
| `range a..b`, `{1, 2, 3}` | finite sets of integers |
| `pairs(S)`, `subsets(S)`, `perms(S)`, `S x T` | standard finite constructions |
| integers, exact rationals, booleans, tuples | values; no floating point |
| `forall x in S: e`, `exists x in S: e`, `count x in S: e`, `sum x in S: e` | quantifiers over finite sets |
| `components(V, E)`, `reach(E, x)` | reachability, used by graphs, Kripke frames and the centre store alike |
| `let NAME = e` | a name for a value |

**Size limits.** Every quantifier states its size before it runs. A program whose total enumeration exceeds a set limit (10^7 steps by default) is refused, not truncated. A refused claim is FALSE, as in `asteroid/SPEC.md`.

## What counts as a proof without Lean

- **Finite claims.** The exhaustive run is the proof. Anyone can rerun it with the exe. Label: checked-finite.
- **Boolean and circuit claims beyond enumeration.** An unsatisfiability certificate (DRAT) from any SAT solver, checked by a small checker inside the kernel. Label: a new word, `certified`, kept separate from Lean's `checked` until the kernel has earned the same trust through differential testing and review.
- **Infinite claims.** A written reduction to a finite or certified claim. Label: checked-infinite.

## The test: can `philosophy/cone.py` be written in it?

`cone.py` is 114 lines of Python. Its four facts in the proposed core:

```
# vertices 0..n-1, apex n; G ranges over every base graph
claim forall n in range 1..6: forall G in subsets(pairs(range 0..n-1)):
    (not connected(range 0..n-1 without {n}, cone(G, n))) == (n >= 2 and components(range 0..n-1, G) > 1)
```

Writing it shows what is still missing: `cone(G, n)` (add the apex's edges) and `without` (drop a vertex) are simple set expressions, but fact 3 (the cone is a disk) needs the link of every vertex, which is a set comprehension: `{ e in G : v in e }`. So the core also needs:

| primitive | meaning |
|---|---|
| `{ x in S : e }` | set comprehension |
| `S union T`, `S minus T`, `len(S)` | set operations |

With these, all four facts of `cone.py` are expressible in roughly 15 lines of `.ath`, and the Rust stays domain-free. This is a paper check, not a run.

## Next

1. Write the core grammar into `asteroid/SPEC.md` as a new section, once agreed.
2. Build the Rust exe for the core statements only, with the differential test against Python on every root program.
3. Port one real check (`philosophy/cone.py`) to `.ath` and compare: same verdicts, timing, line counts.
4. Then decide whether `culture/love/native/` (domain logic in Rust today) moves to `.ath`.
