import Lean.Data.Json
import PEqualNP.AsteroidLang.Emit
/-!
# asteroid: the command line

```
asteroid FILE.ast             run a program: evaluate its claims, then have Lean check the proofs
asteroid FILE.ast --no-proof  evaluate only
asteroid version
```

The program is one executable. The verdicts come from `run` (`AsteroidLang/Eval.lean`), compiled.
For the claims marked `by lean` it writes the proof modules (`AsteroidLang/Emit.lean`) into the
Lean project it was built from and runs `lake build` on them as a child process.
-/
namespace AsteroidLang
open Core

/-- the version line -/
def version : String := "asteroid 0.4 (Lean: compiled evaluator, proofs checked by the Lean kernel)"

/-- how to call the program -/
def usage : String :=
  "usage: asteroid FILE.ast [--no-proof]    run a program (--no-proof: evaluate only)\n" ++
  "       asteroid version"

/-- a circuit from the JSON form `{\"n\", \"sets\", \"gates\", \"outs\"}` -/
def circOfJson (src : String) : Except String Circ := do
  let j ← Lean.Json.parse src
  let n ← j.getObjValAs? Nat "n"
  let sets ← j.getObjValAs? (List (List Nat)) "sets"
  let outs ← j.getObjValAs? (List Nat) "outs"
  let gates ← (← j.getObjValAs? (List Lean.Json) "gates").mapM fun g => do
    let op ← (← g.getArrVal? 0).getStr?
    let a ← (← g.getArrVal? 1).getNat?
    match op with
    | "and" => pure (⟨0, a, ← (← g.getArrVal? 2).getNat?⟩ : Gate)
    | "or" => pure ⟨1, a, ← (← g.getArrVal? 2).getNat?⟩
    | "not" => pure ⟨2, a, a⟩
    | _ => throw s!"unknown gate type {op}"
  pure ⟨n, sets, outs, gates⟩

/-- the first folder, from `dir` upwards, that holds the Lean project of asteroid -/
partial def findProject (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← (dir / "lakefile.toml").pathExists) && (← (dir / "PEqualNP" / "W951").isDir) then
    return some dir
  match dir.parent with
  | some up => if up == dir then return none else findProject up
  | none => return none

/-- the Lean project: above the executable, above the current folder, or in `one-not/lean` -/
def locateProject : IO (Option System.FilePath) := do
  let cwd ← IO.currentDir
  let app ← IO.appPath
  for start in [app, cwd, cwd / "one-not" / "lean" / "PEqualNP"] do
    if let some dir ← findProject (← IO.FS.realPath start) then return some dir
  return none

/-- the command `lake`: on the path, or where elan installs it -/
def locateLake : IO (Option String) := do
  let home := (← IO.getEnv "HOME").getD ""
  for cmd in ["lake", s!"{home}/.elan/bin/lake"] do
    try
      let out ← IO.Process.output { cmd, args := #["--version"] }
      if out.exitCode == 0 then return some cmd
    catch _ => pure ()
  return none

/-- milliseconds as seconds with one decimal -/
def seconds (ms : Nat) : String :=
  let tenths := (ms + 50) / 100
  s!"{tenths / 10}.{tenths % 10}"

/-- `path` relative to the folder `root`, if it is inside it -/
def relativeTo (root path : System.FilePath) : String :=
  let prefix_ := root.toString ++ "/"
  if path.toString.startsWith prefix_ then (path.toString.drop prefix_.length).toString
  else path.toString

/-- build one module of the project; returns success and the time in milliseconds -/
def lakeBuild (lake : String) (project : System.FilePath) (mod : String) : IO (Bool × Nat) := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output
    { cmd := lake, args := #["build", s!"PEqualNP.W951.{mod}"], cwd := some project }
  let t1 ← IO.monoMsNow
  if out.exitCode != 0 then
    let errors := ((out.stdout ++ out.stderr).splitOn "\n").filter fun l =>
      (l.splitOn "error").length > 1
    IO.println ("\n".intercalate (errors.take 12))
  return (out.exitCode == 0, t1 - t0)

/-- where the proofs are checked: the project and the command `lake` -/
structure Prover where
  /-- the folder with `lakefile.toml` -/
  project : System.FilePath
  /-- the command `lake` -/
  lake : String

/-- what a run has printed and collected so far -/
structure Tally where
  /-- the circuits in scope -/
  env : Env := {}
  /-- the verdicts not printed yet -/
  verdicts : List Verdict := []
  /-- the claims for the proof checker -/
  claims : Array LeanClaim := #[]
  /-- true claims -/
  good : Nat := 0
  /-- false claims -/
  bad : Nat := 0
  /-- statements this version does not run (other than `plot`) -/
  skipped : Nat := 0

/-- print one statement and update the tally -/
def step (t : Tally) (l : Line) : IO Tally := do
  match l.stmt with
  | .circuit name C =>
    IO.println s!"{l.num}: {name} defined ({C.n} inputs, {C.gates.length} gates, \
      correct {showBool C.correct})"
    return { t with env := t.env.insert name C }
  | .load name _ =>
    match t.env[name]? with
    | some C => IO.println s!"{l.num}: {name} loaded ({C.n} inputs, {C.gates.length} gates)"
    | none => pure ()
    return t
  | .display name =>
    match t.env[name]? with
    | some C =>
      IO.println s!"{l.num}: {name}: gates {C.gates.length}, nots {C.nots}, base {C.base 0}, \
        witness {C.witness}, orwitness {C.orWitness 0}, correct {showBool C.correct}"
    | none => IO.println s!"{l.num}: show {name}: no circuit of this name"
    return t
  | .claim force text e byLean =>
    match t.verdicts with
    | [] => return t
    | v :: rest =>
      let send := byLean && (v.value || force)
      let (claims, note) :=
        match send, e.leanStatements v.env with
        | true, some stmts => (stmts.map fun (c, stmt) => (⟨c, stmt, text⟩ : LeanClaim), "")
        | true, none => ([], "  (NO LEAN FORM for this expression yet: evaluated only)")
        | false, _ => ([], "")
      IO.println s!"{l.num}: claim {text}: evaluated {if v.value then "TRUE" else "FALSE"} \
        ({e.detail v.env}{note})"
      return { t with verdicts := rest, claims := t.claims ++ claims,
                      good := t.good + (if v.value then 1 else 0),
                      bad := t.bad + (if v.value then 0 else 1) }
  | .unsupported what =>
    IO.println s!"{l.num}: not in the Lean version yet: `{what}` (line skipped)"
    return { t with skipped := t.skipped + (if (words what).head? == some "plot" then 0 else 1) }

/-- read the files a program loads; the result is the program as `run` takes it -/
def resolve (root : System.FilePath) (lines : List Line) : IO (List Line × List Item) := do
  let mut out := #[]
  let mut items := #[]
  for l in lines do
    match l.stmt with
    | .circuit name C => items := items.push (.circuit name C); out := out.push l
    | .claim _ _ e _ => items := items.push (.claim l.num e); out := out.push l
    | .load name path =>
      if path.endsWith ".json" then
        let file := if ← (root / path).pathExists then root / path else path
        match circOfJson (← IO.FS.readFile file) with
        | .ok C => items := items.push (.circuit name C); out := out.push l
        | .error e => throw <| IO.userError s!"line {l.num}: cannot load {path}: {e}"
      else
        out := out.push ⟨l.num, .unsupported s!"let {name} = load {path}"⟩
    | _ => out := out.push l
  return (out.toList, items.toList)

/-- check the claims with Lean; returns whether both modules were accepted and how many proved -/
def prove (p : Prover) (script mod : String) (t : Tally) : IO (Bool × Nat) := do
  let claims := t.claims.toList
  let dir := p.project / "PEqualNP" / "W951"
  IO.FS.writeFile (dir / s!"{mod}.lean") (proofModule script mod t.env claims)
  let (ok, ms) ← lakeBuild p.lake p.project mod
  if !ok then
    IO.println s!"NOT PROVED: the proof checker rejected this program's claims ({seconds ms} s)"
    return (false, 0)
  IO.println s!"proved: {claims.length} claims accepted by the proof checker in {seconds ms} s"
  match soundModule mod claims with
  | none => return (true, claims.length)
  | some (text, made) =>
    IO.FS.writeFile (dir / s!"{mod}_sound.lean") text
    let (ok, ms) ← lakeBuild p.lake p.project s!"{mod}_sound"
    if ok then
      IO.println s!"proved: {made} of them also hold in the project's own definitions \
        ({seconds ms} s)"
    else
      IO.println s!"NOT PROVED: the restatement in the project's own definitions failed \
        ({seconds ms} s)"
    return (ok, claims.length)

/-- run one program; the result is the exit code -/
def runFile (file : String) (noProof : Bool) : IO UInt32 := do
  let project ← locateProject
  let root := (project.bind (·.parent)).bind (·.parent) |>.getD "."
  let script := relativeTo root (← IO.FS.realPath file)
  let lines ← match parse script (← IO.FS.readFile file) with
    | .ok lines => pure lines
    | .error e => IO.eprintln e; return 2
  let (lines, items) ← resolve root lines
  let verdicts ← match run {} items with
    | .ok vs => pure vs
    | .error e => IO.eprintln s!"{script}: {e}"; return 2
  let t ← lines.foldlM step { verdicts }
  let prover ← if noProof || t.claims.isEmpty then pure none else do
    match project, ← locateLake with
    | some project, some lake => pure (some (⟨project, lake⟩ : Prover))
    | _, _ =>
      IO.println "note: no proof checker here (the command `lake`, or the Lean project this \
        program was built from, was not found): claims are evaluated, nothing is proved."
      pure none
  let stem := (System.FilePath.mk file).fileStem.getD "program"
  let mod := "Asteroid_" ++ stem.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let (ok, proved) ← match prover with
    | some p => prove p script mod t
    | none =>
      if !t.claims.isEmpty then
        IO.println s!"not proved: {t.claims.size} claims were only evaluated \
          (no proof checker in this run)"
      pure (true, 0)
  IO.println (s!"claims: {t.good} true, {t.bad} false"
    ++ (if prover.isSome && ok then s!"; {proved} proved" else "")
    ++ (if t.skipped > 0 then s!"; {t.skipped} lines not in the Lean version yet" else ""))
  return if t.bad == 0 && ok && t.skipped == 0 then 0 else 1

end AsteroidLang

open AsteroidLang in
/-- the entry point of the executable `asteroid` -/
def main (args : List String) : IO UInt32 := do
  let flags := ["--no-proof", "--no-lean"]
  let noProof := args.any flags.contains
  match args.filter (!flags.contains ·) with
  | ["version"] => IO.println version; return 0
  | [file] | ["run", file] =>
    try runFile file noProof
    catch e => IO.eprintln s!"asteroid: {e}"; return 2
  | _ => IO.println usage; return 2
