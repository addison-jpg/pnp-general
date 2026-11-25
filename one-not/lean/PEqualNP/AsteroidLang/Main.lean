import Lean.Data.Json
import PEqualNP.AsteroidLang.Emit
import PEqualNP.AsteroidLang.Bench
/-!
# asteroid: the command line

```
asteroid FILE.ath             run a program: evaluate its claims, then have Lean check the proofs
asteroid FILE.ath --no-proof  evaluate only
asteroid --doctor [FILE.ath]  where the project and `lake` were looked for and found
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
  "usage: asteroid FILE.ath [--no-proof]    run a program (--no-proof: evaluate only)\n" ++
  "       asteroid --doctor [FILE.ath]      where it looks for the project and `lake`\n" ++
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

/-- a path as written on the command line or in a program: `\` separates folders on every system,
and a drive letter (`C:/…`) is kept -/
def slashPath (p : String) : System.FilePath :=
  System.FilePath.normalize ⟨p.map fun c => if c == '\\' then '/' else c⟩

/-- a text file as UTF-8, with a byte-order mark dropped and CRLF / CR line ends read as LF -/
def readText (file : System.FilePath) : IO String := do
  let s ← IO.FS.readFile file
  let s := if s.startsWith "\uFEFF" then (s.drop 1).toString else s
  return (s.replace "\r\n" "\n").replace "\r" "\n"

/-- write a text file byte for byte (LF line ends on every system) -/
def writeText (file : System.FilePath) (text : String) : IO Unit :=
  IO.FS.writeBinFile file text.toUTF8

/-- the absolute form of a path, if it exists -/
def real? (p : System.FilePath) : IO (Option System.FilePath) := do
  try return some (← IO.FS.realPath p) catch _ => return none

/-- the first folder, from `dir` upwards, that holds the Lean project of asteroid -/
partial def findProject (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← (dir / "lakefile.toml").pathExists) && (← (dir / "PEqualNP" / "W951").isDir) then
    return some dir
  match dir.parent with
  | some up => if up == dir then return none else findProject up
  | none => return none

/-- where the project is looked for: above the executable (the project it was built from), above
the program file, above the current folder, and in `one-not/lean` below the current folder -/
def projectStarts (file : Option String) : IO (List System.FilePath) := do
  let cwd ← IO.currentDir
  let prog := match file with
    | some f => [((slashPath f).parent.getD ".")]
    | none => []
  return [(← IO.appPath).parent.getD "."] ++ prog ++ [cwd, cwd / "one-not" / "lean"]

/-- the Lean project of asteroid, searched from `projectStarts` -/
def locateProject (file : Option String) : IO (Option System.FilePath) := do
  for start in ← projectStarts file do
    if let some s ← real? start then
      if let some dir ← findProject s then return some dir
  return none

/-- the places `lake` is looked for: every folder on PATH, then where elan installs it
(`~/.elan/bin`, `%USERPROFILE%\.elan\bin`), then the bare name -/
def lakeCandidates : IO (List String) := do
  let exe := if System.Platform.isWindows then "lake.exe" else "lake"
  let mut out := #[]
  for d in System.SearchPath.parse ((← IO.getEnv "PATH").getD "") do
    if !d.toString.isEmpty then out := out.push (d / exe).toString
  for v in ["HOME", "USERPROFILE"] do
    if let some h ← IO.getEnv v then
      if !h.isEmpty then out := out.push (slashPath h / ".elan" / "bin" / exe).toString
  out := out.push "lake"
  return out.toList.eraseDups

/-- the command `lake` and its version line: the first candidate that answers `lake --version`,
asked inside the project (elan's `lake` picks its toolchain from the project's `lean-toolchain`) -/
def locateLake (project : Option System.FilePath) : IO (Option (String × String)) := do
  for cmd in ← lakeCandidates do
    if cmd != "lake" && !(← System.FilePath.pathExists cmd) then continue
    try
      let out ← IO.Process.output { cmd, args := #["--version"], cwd := project }
      if out.exitCode == 0 then return some (cmd, out.stdout.trimAscii.toString)
    catch _ => pure ()
  return none

/-- milliseconds as seconds with one decimal -/
def seconds (ms : Nat) : String :=
  let tenths := (ms + 50) / 100
  s!"{tenths / 10}.{tenths % 10}"

/-- `path` relative to the folder `root`, if it is inside it -/
def relativeTo (root path : System.FilePath) : String :=
  let fwd (p : System.FilePath) := p.toString.map fun c => if c == '\\' then '/' else c
  let prefix_ := fwd root ++ "/"
  let p := fwd path
  if p.startsWith prefix_ then (p.drop prefix_.length).toString else p

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
  /-- the circuits read from files, in order, not announced yet -/
  loads : List Circ := []
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
    match t.loads with
    | C :: rest =>
      IO.println s!"{l.num}: {name} loaded ({C.n} inputs, {C.gates.length} gates)"
      return { t with env := t.env.insert name C, loads := rest }
    | [] => return t
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
      IO.println s!"{l.num}: claim {text}: {if v.value then "TRUE" else "FALSE"} \
        ({e.detail v.env}{note})"
      return { t with verdicts := rest, claims := t.claims ++ claims,
                      good := t.good + (if v.value then 1 else 0),
                      bad := t.bad + (if v.value then 0 else 1) }
  | .unsupported what =>
    let verb := (words what).headD what
    IO.println s!"{l.num}: {verb}: not in the Lean version yet"
    return { t with skipped := t.skipped + 1 }

/-- a circuit of the `.bench` reader as the circuit of the executable -/
def ofBenchCirc (C : SearchCheck.Circ) : Circ :=
  ⟨C.n, C.sets, C.outs, C.gates.map fun g => ⟨g.op, g.a, g.b⟩⟩

/-- read the files a program loads; the result is the program as `run` takes it. `dir` is the
folder of the program file: a relative path is read from there (never from the current folder),
else from the repository folder `root`; an absolute path (`/…`, `C:/…`) as written. -/
def resolve (script : String) (dir root : System.FilePath) (lines : List Line) :
    IO (List Line × List Item × List Circ) := do
  let mut out := #[]
  let mut loads := #[]
  let mut items := #[]
  for l in lines do
    match l.stmt with
    | .circuit name C => items := items.push (.circuit name C); out := out.push l
    | .claim _ _ e _ => items := items.push (.claim l.num e); out := out.push l
    | .load name path =>
      let p := slashPath path
      let file ← do
        if p.isAbsolute then pure p
        else if ← (dir / p).pathExists then pure (dir / p)
        else if ← (root / p).pathExists then pure (root / p) else pure (dir / p)
      unless ← file.pathExists do
        throw <| IO.userError s!"{script}:{l.num}: cannot load {path}: no such file"
      let text ← readText file
      if path.endsWith ".json" then
        match circOfJson text with
        | .ok C =>
          items := items.push (.circuit name C)
          loads := loads.push C
          out := out.push l
        | .error e => throw <| IO.userError s!"{script}:{l.num}: cannot load {path}: {e}"
      else if path.endsWith ".bench" then
        match Bench.read text with
        | .ok C =>
          items := items.push (.circuit name (ofBenchCirc C))
          loads := loads.push (ofBenchCirc C)
          out := out.push l
        | .error e => throw <| IO.userError s!"{path}: {e}"
      else
        throw <| IO.userError s!"{script}:{l.num}: cannot load {path}: not a .bench or .json file"
    | _ => out := out.push l
  return (out.toList, items.toList, loads.toList)

/-- check the claims with Lean; returns whether both modules were accepted and how many proved -/
def prove (p : Prover) (script mod : String) (t : Tally) : IO (Bool × Nat) := do
  let claims := t.claims.toList
  let dir := p.project / "PEqualNP" / "W951"
  writeText (dir / s!"{mod}.lean") (proofModule script mod t.env claims)
  let (ok, ms) ← lakeBuild p.lake p.project mod
  if !ok then
    IO.println s!"NOT PROVED: the proof checker rejected this program's claims ({seconds ms} s)"
    return (false, 0)
  IO.println s!"proved: {claims.length} claims accepted by the proof checker in {seconds ms} s"
  match soundModule mod claims with
  | none => return (true, claims.length)
  | some (text, made) =>
    writeText (dir / s!"{mod}_sound.lean") text
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
  let path := slashPath file
  unless ← path.pathExists do
    IO.eprintln s!"asteroid: {file}: no such file"; return 2
  let project ← locateProject (some file)
  let root := (project.bind (·.parent)).bind (·.parent) |>.getD "."
  let script := relativeTo root (← IO.FS.realPath path)
  let lines ← match parse script (← readText path) with
    | .ok lines => pure lines
    | .error e => IO.eprintln e; return 2
  let (lines, items, loads) ← resolve script (path.parent.getD ".") root lines
  let verdicts ← match run {} items with
    | .ok vs => pure vs
    | .error e => IO.eprintln s!"{script}: {e}"; return 2
  let t ← lines.foldlM step { verdicts, loads }
  let prover ← if noProof || t.claims.isEmpty then pure none else do
    match project, ← locateLake project with
    | some project, some (lake, _) => pure (some (⟨project, lake⟩ : Prover))
    | none, _ =>
      IO.println "note: evaluate only: no Lean project (a folder with lakefile.toml and \
        PEqualNP/W951) above the executable, the program or the current folder \
        (asteroid --doctor shows where it looked)"
      pure none
    | _, none =>
      IO.println "note: evaluate only: the command `lake` was not found on PATH or in \
        ~/.elan/bin (asteroid --doctor shows where it looked)"
      pure none
  let stem := path.fileStem.getD "program"
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
    ++ (if t.skipped > 0 then s!"; {t.skipped} lines skipped (not in the Lean version yet)" else ""))
  return if t.bad == 0 && ok then 0 else 1

/-- `asteroid --doctor`: where the project and `lake` were looked for, what was found, and whether
a run proves or only evaluates -/
def doctor (file : Option String) : IO UInt32 := do
  IO.println version
  IO.println s!"system: {if System.Platform.isWindows then "Windows" else "not Windows"}"
  IO.println s!"executable: {← IO.appPath}"
  IO.println s!"current folder: {← IO.currentDir}"
  if let some f := file then
    IO.println s!"program: {f} ({if ← (slashPath f).pathExists then "found" else "NOT FOUND"})"
  IO.println "project (a folder with lakefile.toml and PEqualNP/W951), searched upwards from:"
  for s in ← projectStarts file do
    let r ← real? s
    let found ← match r with
      | some r => findProject r
      | none => pure none
    IO.println s!"  {r.getD s}: {match found with | some d => s!"found {d}" | none => "nothing"}"
  let project ← locateProject file
  IO.println s!"  -> {match project with | some d => d.toString | none => "NOT FOUND"}"
  let cands ← lakeCandidates
  let present ← cands.filterM fun c => if c == "lake" then pure true else System.FilePath.pathExists c
  IO.println s!"lake, looked for in {cands.length - 1} places (every folder on PATH, ~/.elan/bin, \
    %USERPROFILE%\\.elan\\bin), present in:"
  for c in present do
    IO.println s!"  {if c == "lake" then "lake (the bare name, as the system resolves it)" else c}"
  let lake ← locateLake project
  IO.println s!"  -> {match lake with | some (c, v) => s!"{c}: {v}" | none => "NOT FOUND"}"
  match project, lake with
  | some _, some _ =>
    IO.println "a run will: evaluate the claims, then prove the `by lean` ones with `lake build`"
  | _, _ =>
    IO.println "a run will: evaluate only (nothing is proved; add `lake` to PATH or build \
      asteroid inside the repository)"
  return 0

end AsteroidLang

open AsteroidLang in
/-- the entry point of the executable `asteroid` -/
def main (args : List String) : IO UInt32 := do
  let flags := ["--no-proof", "--no-lean"]
  let noProof := args.any flags.contains
  match args.filter (!flags.contains ·) with
  | ["version"] | ["--version"] => IO.println version; return 0
  | ["--doctor"] | ["doctor"] => doctor none
  | ["--doctor", file] | ["doctor", file] => doctor (some file)
  | [file] | ["run", file] =>
    try runFile file noProof
    catch e => IO.eprintln s!"asteroid: {e}"; return 2
  | _ => IO.println usage; return 2
