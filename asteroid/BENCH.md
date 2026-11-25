# The `.bench` circuit format, as asteroid reads it

Every circuit in this repository is a `.bench` file. This page is the specification: the grammar, the
meaning of a file, and the one addition asteroid makes. Two readers implement it and are compared on
every file: `asteroid/native/AsteroidLang/Bench.lean` (Lean) and `asteroid/ext_bench.py` (Python).

## Origin

The format comes from two benchmark sets of the IEEE International Symposium on Circuits and Systems.

- F. Brglez and H. Fujiwara, "A neutral netlist of 10 combinational benchmark circuits and a target
  translator in Fortran", Proc. IEEE ISCAS, 1985 (the ISCAS-85 circuits, c17 to c7552).
- F. Brglez, D. Bryan and K. Kozminski, "Combinational profiles of sequential benchmark circuits",
  Proc. IEEE ISCAS, May 1989, pp. 1929-1934, doi:10.1109/ISCAS.1989.100747 (the ISCAS-89 circuits).

The format has no formal grammar. The 1985 paper describes a numeric node-list form and a Fortran
translator; the `INPUT(…)` / `OUTPUT(…)` / `name = GATE(…)` text form is the one in which both sets
circulate today, and its definition is the behaviour of the tools that read it: ABC (`read_bench`,
`write_bench`), Atalanta, and the parser library lorina. This page is the grammar asteroid uses. Where practice
varies, the choice made here is marked *asteroid's choice*. Read status of every source:
`research/LITERATURE.md`, section "Circuit file formats".

## Grammar

```
file      = [ line ] { "\n" line } ;
line      = ws [ statement ws ] [ comment ]  |  ws directive ;
statement = input | output | assign ;
input     = "INPUT"  ws "(" ws name ws ")" ;
output    = "OUTPUT" ws "(" ws name ws ")" ;
assign    = name ws "=" ws operator ws "(" ws name { ws "," ws name } ws ")" ;
operator  = "AND" | "OR" | "NOT" | "BUFF" ;
name      = namechar { namechar } ;
namechar  = "A".."Z" | "a".."z" | "0".."9" | "_" | "." | "[" | "]" ;
comment   = "#" { any character except "\n" } ;
directive = "#@" ws "or" blank ws name ws "=" ws name { blank ws name } ws ;
ws        = { blank } ;      blank = " " | "\t" | "\r" ;
```

- One statement per line. Blank lines are ignored. A statement cannot continue on the next line.
- A comment runs from `#` to the end of the line and may follow a statement. A line whose first
  non-blank characters are `#@` is a directive; `#@` after a statement is an ordinary comment.
- `INPUT`, `OUTPUT` and the operators are read in any letter case and written in upper case
  (*asteroid's choice*: the benchmark files use upper case; some tools write lower case).
- Names are case-sensitive. A name may consist of digits only, as in the ISCAS-85 files
  (`10 = NAND(1, 3)`). The character set of names is *asteroid's choice*. There are no reserved words.
- The reader `parse` accepts any name as an operator, so that an error can name it. A file is a
  circuit only with the four operators above: `AND` and `OR` with exactly two operands, `NOT` and
  `BUFF` with exactly one. `NAND`, `NOR`, `XOR`, `XNOR`, `DFF`, the `LUT` lines that ABC writes, and
  gates with three or more operands are rejected with an error that names the line
  (*asteroid's choice*: the theorem counts AND, OR and NOT gates with two inputs, and a wider gate
  would hide a count).
- Errors, each with its line where one line is at fault: an input or an output declared twice; a
  signal assigned twice; an input that is also assigned; a signal used and never defined; a cycle.

## Directives

A plain `.bench` file says what a circuit is, not what it must compute. asteroid adds one directive,
written as a comment so that every other `.bench` tool still reads the file:

```
#@ or b = x0 x1 x2
```

"The output `b` must compute the OR of the inputs `x0`, `x1`, `x2`." The first name must be declared
with `OUTPUT`, the names after `=` with `INPUT`. An output may carry several directives. Either every
output has a directive or none has. A file with no directive is a plain circuit with no sets. Any
other `#@` line is an error; the directive word `or` is lower case.

## Semantics

A file denotes a circuit `(n, sets, gates, outs)`, the `Circ` of `SearchCheck.lean` and the JSON
dictionary of `research/one-not/tools/search/core.py`.

- **Inputs.** `n` is the number of `INPUT` lines. Inputs are numbered 0, 1, … in order of appearance.
- **Wires.** Wire `i < n` is input `i`; wire `n + k` is gate `k`.
- **Gates.** Every `AND`, `OR` and `NOT` line is one gate. A `BUFF` line is zero gates: its name is a
  second name for the wire of its operand.
- **Order.** Gates are numbered in file order when every operand is defined above its use. A file
  may be written in any order; the reader then sorts: it scans the lines not yet placed from top to
  bottom, places each line whose operands are placed, and repeats.
- **Outputs and sets.** With directives, `sets` and `outs` follow the directives in file order: set
  `k` is the list of input numbers of directive `k`, and `outs[k]` is the wire of its output. With
  no directive, `sets` is empty and `outs` lists the wires of the `OUTPUT` lines in order.
- **First line.** If the first line is an ordinary comment, its text is the name of the circuit.

The writer prints, in this order: the name, the inputs, the outputs, the directives, the gates. A
circuit that is not read from a file gets the names `x0, x1, …` for inputs and `g0, g1, …` for gates.

## Examples

`hello.bench` (three gates, no NOT gate):

```
# hello: two sets sharing the point x2
INPUT(x0)
INPUT(x1)
INPUT(x2)
INPUT(x3)
OUTPUT(b)
OUTPUT(c)
#@ or b = x0 x1 x2
#@ or c = x2 x3
a = OR(x0, x1)
b = OR(a, x2)
c = OR(x2, x3)
```

It denotes `n = 4`, `sets = [[0, 1, 2], [2, 3]]`, `outs = [5, 6]`, gates `OR(0, 1)`, `OR(4, 2)`,
`OR(2, 3)`.

The OR of two inputs written with one NOT gate (three gates, of which one NOT):

```
# OR of two inputs with one NOT gate
INPUT(a)
INPUT(b)
OUTPUT(z)
#@ or z = a b
t = NOT(a)
u = AND(t, b)
z = OR(a, u)
```

## Differences from other formats

- **AIGER** (A. Biere, "The AIGER And-Inverter Graph (AIG) Format Version 20071012", FMV Reports
  07/1, Johannes Kepler University Linz, 2007). The only gate is AND and negation is a free bit on
  every edge, so the number of NOT gates is not a property of an AIGER file. asteroid exports to
  AIGER (`AsteroidLang.Bench.toAag`) and does not read it; see `research/notes/aiger.md`.
- **BLIF** (University of California, Berkeley, "Berkeley Logic Interchange Format (BLIF)", 1992,
  distributed with SIS). A gate is a `.names` block, a truth-table cover with any number of inputs,
  so "one gate" has no fixed cost and a negation can sit inside any cover.

## Implementation

`Bench.lean` exports `Netlist`, `parse`, `print`, `toCirc`, `ofCirc`, `read` (= `parse` then
`toCirc`, with line numbers) and `toAag`. The reader uses the public standard library only:
`String.splitOn`, `String.trimAscii`, `String.replace`, `String.splitToList`, `List`, `Array`,
`Except`, `Std.HashMap`. `BenchTest.lean` holds the tests. Nothing about the reader is proved; the
round trips are tests. The comparison of the two readers on every `.bench` file of the repository:
`python3 -I asteroid/tests/test_bench.py`.
