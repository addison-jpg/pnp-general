import AsteroidLang.Bench
/-!
Helper of `asteroid/tests/test_bench.py`: read each `.bench` file given on the command line with the
Lean reader and print one line per file, the circuit or the error, and whether `print (parse src)`
is the file itself and parses back to the same netlist.

Run from `proofs/w951`: `lake env lean --run ../../asteroid/tests/bench_dump.lean FILE.bench ...`
-/
open AsteroidLang.Bench

/-- One circuit on one line, in the notation `test_bench.py` rebuilds from the Python reader. -/
def showCirc (C : SearchCheck.Circ) : String :=
  let gs := C.gates.map fun g => s!"[{g.op},{g.a},{g.b}]"
  s!"OK n={C.n} sets={C.sets} outs={C.outs} gates=[{",".intercalate gs}]"

def main (args : List String) : IO Unit := do
  for f in args do
    let src ← IO.FS.readFile f
    let canonical := match parse src with
      | .ok nl => print nl == src && (match parse (print nl) with
        | .ok m => m == nl
        | .error _ => false)
      | .error _ => false
    match read src with
    | .ok C => IO.println s!"{f}\t{showCirc C}\tcanonical={canonical}"
    | .error e => IO.println s!"{f}\tERR {e}"
