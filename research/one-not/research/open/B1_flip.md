# B1: the per-set flip lemma S3(a), proved in Lean

`proofs/w951/PEqualNP/W951/Open/FlipLemma.lean::PEqualNP.W951.FlipLemma.Concrete.flip_lemma`
(axioms: propext, choice, Quot.sound; builds with `lake build PEqualNP.W951.Open.FlipLemma`).

For every `SearchCheck.Circ` with `correctB C = true` (opcodes 0 = AND, 1 = OR, anything else = NOT;
any number of NOT gates, forward wire references read as 0), every pair `(S, o)` of `C.sets.zip C.outs`
with all `u ∈ S` below `n`, and every zero point `Z` of `S`:
`|S| ≤ #flip classes + 1`, where a flip class is a wire function on the `2^n` rows up to complement,
taken over wires with `|D| ≥ 2` at `(S, Z)`.

The abstract form `Core.core` is the graph argument with colourings: any list of wire functions in
which each `D` has at most one point or lies in the union of the `D`s of two earlier wires (or
constants), and some wire has `D = S`. The example at the end applies it to `SearchCheck.t4`
(the 4-NOT counterexample to C4w).

What remains open is S3(b): the classes over ALL sets number at least `base`, i.e. the sharing
statement (Hall form in `research/notes/beyond-one-not.md`). The per-set lemma says nothing about two sets.
