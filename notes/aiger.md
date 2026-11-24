Serves the asteroid language (task asteroid-bench)

# AIGER: what it is, why asteroid does not use it for circuits, what it is used for

## The format

AIGER is the file format for And-Inverter Graphs of A. Biere (FMV Reports 07/1, 2007; version 1.9:
Biere, Heljanko, Wieringa, FMV Reports 11/2, 2011). It is the input format of the hardware model
checking competition and, with an extension for controllable inputs, of the reactive synthesis
competition SYNTCOMP.

1. A variable is a positive integer `v`. A literal is `2v` (the variable) or `2v + 1` (its negation).
2. The literals `0` and `1` are the constants false and true.
3. The ASCII form starts with the header `aag M I L O A`: the largest variable index, the number of
   inputs, of latches, of outputs, of AND gates.
4. Then `I` lines, one input literal each; `L` lines `current next` for the latches; `O` lines, one
   output literal each; `A` lines `lhs rhs0 rhs1`, meaning `lhs = rhs0 AND rhs1`.
5. An optional symbol table (`i0 name`, `o0 name`) and a comment section after a line `c` follow.
6. The binary form has the header `aig M I L O A`. Inputs are implicit (`2, 4, …, 2I`), the left
   sides of the AND gates are implicit and consecutive, every gate satisfies `lhs > rhs0 ≥ rhs1`,
   and a gate is stored as the two differences `lhs − rhs0` and `rhs0 − rhs1` in a
   variable-length code of 7 bits per byte.
7. AND is the only gate. Negation is the low bit of a literal: it is on the edge, not a node.
8. OR does not exist: `a OR b` is written as the negation of `(NOT a) AND (NOT b)`.
9. Version 1.9 adds bad-state, constraint, justice and fairness sections to the header.
10. Lean has its own verified AIG, `Std.Sat.AIG` (from LeanSAT; the tactic `bv_decide` builds one and
    hands its CNF to a SAT solver). Its nodes are constants, atoms and AND gates whose two inputs
    each carry an inversion flag: the same data model as AIGER.

## Why AIGER cannot carry the theorem

The theorem of this project is about circuits over AND, OR and NOT in which the NOT gates are
counted: "one NOT gate saves nothing". In AIGER a negation is a bit on an edge and costs nothing, and
an OR is an AND with negated edges. The number of NOT gates, the parameter of the whole project, is
therefore not a property of an AIGER file: the monotone circuit `OR(a, b)` and the circuit
`NOT(AND(NOT a, NOT b))` with three NOT gates are the same AIGER file. The same holds for the number
of OR gates, which is what the witness count of the theorem counts. A circuit of this project cannot
be stored in AIGER without losing the quantities the theorem is about. This is why the circuit
format is `.bench` (`asteroid/BENCH.md`), where every AND, OR and NOT is a line.

## What AIGER is used for here

An export, for interoperability with model checkers and with `Std.Sat.AIG`:
`AsteroidLang.Bench.toAag : SearchCheck.Circ → String` (ASCII AIGER, no latches). It is implemented
in `one-not/lean/PEqualNP/AsteroidLang/Bench.lean` and tested on the hello circuit and on one circuit
with a NOT gate in `BenchTest.lean`. It is not yet a verb of the asteroid language.

The translation, for a circuit with `n` inputs:

- input `i` is the variable `i + 1`, literal `2(i + 1)`;
- `AND(a, b)` becomes one AIGER AND gate with a new variable `v`: `2v = lit(a) AND lit(b)`; the wire
  has literal `2v`;
- `OR(a, b)` becomes one AIGER AND gate with three negated edges: `2v = ¬lit(a) AND ¬lit(b)`, and
  the wire has the negated literal `2v + 1`;
- `NOT(a)` becomes no gate: the wire has the literal `¬lit(a)`;
- the outputs are the literals of `outs`, in order. Header: `aag (n + A) n 0 O A`, where `A` is the
  number of AND and OR gates of the circuit.

Kept by the translation: the function computed at every output. Not kept: the number of gates (the
NOT gates vanish), the number of NOT gates, the difference between AND and OR, the sets (AIGER has
no place for the `#@ or` directives). The export of hello is

```
aag 7 4 0 2 3
2
4
6
8
13
15
10 5 3
12 10 7
14 9 7
```

Status of the statement "kept: the function": true by construction (De Morgan), tested on two
circuits by comparing the output text, not proved in Lean. A proof would state it against
`Std.Sat.AIG`'s evaluator; that is an open item.

Sources and their read status: `LITERATURE.md`, section "Circuit file formats". The AIGER reports
were not opened in this session (the host fmv.jku.at is not reachable from the container); the
description above is from memory of the format and is to be re-read against `FORMAT.aiger` before
anyone relies on a detail of the binary encoding.
