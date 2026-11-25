/-
auto951 audit: read the COMPILED result of a tree and report, for the final 951 theorem,
what the auto-merge gate needs. Run from lean/ as:

  lake env lean --run ../.github/auto951/Audit.lean <final module> <final theorem> <statement file>

Prints (always, in this order):
  STATEMENT ok|mismatch|error <detail>   the final theorem proves the recorded statement (kernel check;
                                         the statement is read against Mathlib + PEqualNP.Defs only)
  AXIOMS <a> <b> ...                     transitive axioms of the final theorem
  SORRY <holder> <fingerprint>           one line per constant under the final theorem whose own type or
                                         value uses sorryAx; fingerprint = hash of its type and of every
                                         project constant that type mentions, transitively (so changing
                                         a definition the open goal is stated with changes it)
  DONE
Exit 0 when it ran (the verdict is in the lines), 3 when it could not.
-/
import Lean
open Lean

namespace Auto951

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `PEqualNP
  | none => false

partial def closure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[start]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do
        unless seen.contains c do todo := todo.push c
  return seen

/-- Hash of `n`'s type, mixed with the type and value hashes of every project constant reachable
from that type (sorted by name, so the result does not depend on traversal order). -/
def fingerprint (env : Environment) (n : Name) : UInt64 := Id.run do
  let some ci := env.find? n | return 0
  -- constants reachable from the TYPE only (the value is the sorry itself)
  let mut seen : NameSet := {}
  let mut todo : Array Name := ci.type.getUsedConstants
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isProject env c then
      if let some d := env.find? c then
        for x in d.getUsedConstantsAsSet do
          unless seen.contains x do todo := todo.push x
  let names := (seen.toList.filter (isProject env ·)).toArray.qsort (·.toString < ·.toString)
  let mut h : UInt64 := mixHash (hash ci.type) (hash ci.levelParams.length)
  for c in names do
    if let some d := env.find? c then
      h := mixHash h (hash c)
      h := mixHash h (hash d.type)
      if let some v := d.value? (allowOpaque := true) then h := mixHash h (hash v)
  return h

unsafe def run (modStr thmStr stmtPath : String) : IO UInt32 := do
  let mod := modStr.toName
  let thmName := thmStr.toName
  initSearchPath (← findSysroot)
  let stmt ← IO.FS.readFile stmtPath
  enableInitializersExecution
  -- statement environment: Mathlib and the definitions root only
  let stmtEnv ← importModules #[{ module := `Mathlib }, { module := `PEqualNP.Defs }] {}
    (trustLevel := 0) (loadExts := true)
  let full ← importModules #[{ module := mod }] {} (trustLevel := 0)
  let some ci := full.find? thmName
    | IO.println s!"STATEMENT error no constant {thmName} in {mod}"; IO.println "AXIOMS"; IO.println "DONE"; return 0
  -- 1. statement
  let src := "set_option autoImplicit false\ntheorem Auto951.recorded :\n(\n" ++ stmt ++ "\n) := sorry\n"
  let (stmtEnv', msgs) ← Elab.process src stmtEnv {} (fileName := "<recorded statement>")
  if msgs.hasErrors then
    IO.println "STATEMENT error the recorded statement does not elaborate"
  else match stmtEnv'.find? `Auto951.recorded with
    | none => IO.println "STATEMENT error no declaration"
    | some rec =>
      if rec.levelParams.length != ci.levelParams.length then
        IO.println "STATEMENT mismatch universe parameters differ"
      else
        let us := ci.levelParams.map mkLevelParam
        let goal := rec.type.instantiateLevelParams rec.levelParams us
        let witness := Declaration.thmDecl {
          name := `Auto951.witness, levelParams := ci.levelParams, type := goal, value := mkConst thmName us }
        match full.toKernelEnv.addDeclCore 0 0 witness (cancelTk? := none) with
        | .ok _ => IO.println "STATEMENT ok"
        | .error _ => IO.println s!"STATEMENT mismatch it proves: {ci.type}"
  -- 2. axioms and sorry holders under the final theorem
  let cl := closure full thmName
  let mut axioms : Array Name := #[]
  let mut holders : Array Name := #[]
  for n in cl.toList do
    if let some d := full.find? n then
      if d matches .axiomInfo _ then axioms := axioms.push n
      if n != ``sorryAx && d.getUsedConstantsAsSet.contains ``sorryAx then holders := holders.push n
  IO.println s!"AXIOMS {" ".intercalate ((axioms.qsort (·.toString < ·.toString)).toList.map toString)}"
  for n in holders.qsort (·.toString < ·.toString) do
    IO.println s!"SORRY {n} {fingerprint full n}"
  IO.println "DONE"
  return 0

end Auto951

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [mod, thm, stmt] =>
    try Auto951.run mod thm stmt
    catch e => IO.eprintln s!"audit fault: {e}"; return 3
  | _ => IO.eprintln "usage: Audit <final module> <final theorem> <statement file>"; return 3
