import PEqualNP.AsteroidLang.Json
import PEqualNP.AsteroidLang.Eval
/-!
# asteroid: the interactive prompt

`asteroid` with no arguments (or `asteroid repl`): a banner, the prompt `4ST> `, one line at a time
against one persistent set of circuits, as a line of a file (the Python `bin/asteroid` does the same).
Meta commands: `:help`, `:load FILE.ath`, `:save FILE.ath`, `:quit` (Ctrl-D too).

Colours are the plain 16-colour codes of `site/terminal.json` (read at run time, else the built-in
ones), only when stdout is a terminal and `NO_COLOR` is unset. Piped output is plain.

The evaluation of a line is the command line's own (`step`, `resolve` in `Main.lean`); it is passed
in as `exec`, so this file does not depend on `Main`.
-/
namespace AsteroidLang
namespace Repl

/-- the colours: SGR codes -/
structure Palette where
  logo : String := "36"
  logoAlt : String := "34"
  accent : String := "36"
  proved : String := "32"
  refuted : String := "31"
  open_ : String := "33"
  muted : String := "90"

/-- the palette of `site/terminal.json` under `root`, if it can be read; else the built-in one -/
def loadPalette (root : System.FilePath) : IO Palette := do
  try
    let j ← IO.ofExcept (AsteroidLang.Json.parse (← IO.FS.readFile (root / "site" / "terminal.json")))
    let s ← IO.ofExcept (j.field "sgr")
    let g (k d : String) : String := s.strOr k d
    return { logo := g "logo" "36", logoAlt := g "logo_alt" "34", accent := g "accent" "36",
             proved := g "proved" "32", refuted := g "refuted" "31", open_ := g "open" "33",
             muted := g "muted" "90" }
  catch _ => return {}

/-- colour on: stdout is a terminal, `NO_COLOR` unset, `TERM` not `dumb` -/
def colourOn : IO Bool := do
  if (← IO.getEnv "NO_COLOR").isSome then return false
  if (← IO.getEnv "TERM") == some "dumb" then return false
  (← IO.getStdout).isTty

/-- the session: colours, circuits, the lines kept for `:save`, the open circuit block -/
structure Session where
  pal : Palette
  colour : Bool
  env : Env := {}
  /-- lines run so far -/
  ln : Nat := 0
  /-- lines that ran without error -/
  kept : Array String := #[]
  /-- the lines of the circuit block being typed, if one is open -/
  block : Option (Array String) := none

/-- `text` in the colour `code` (plain when colour is off) -/
def Session.paint (s : Session) (code text : String) : String :=
  if s.colour && !text.isEmpty then s!"\x1b[{code}m{text}\x1b[0m" else text

/-- colour the verdict words of one line of output -/
def Session.verdicts (s : Session) (line : String) : String :=
  if !s.colour then line else
  let words : List (String × String) :=
    [("NOT PROVED", s.pal.refuted), ("FALSE", s.pal.refuted), ("rejected", s.pal.refuted),
     ("not proved", s.pal.open_), ("proved", s.pal.proved), ("TRUE", s.pal.proved),
     ("skipped", s.pal.open_), ("not in the Lean version yet", s.pal.open_)]
  let rec go (prev : Char) : Nat → List Char → String → String
    | 0, _, acc => acc
    | _, [], acc => acc
    | fuel + 1, cs@(c :: rest), acc =>
      let hit := if prev.isAlphanum then none else
        words.findSome? fun (w, code) =>
          let wc := w.toList
          if wc.isPrefixOf cs && !((cs.drop wc.length).headD ' ').isAlphanum
          then some (w, code) else none
      match hit with
      | some (w, code) => go (w.toList.getLast?.getD ' ') fuel (cs.drop w.length) (acc ++ s.paint code w)
      | none => go c fuel rest (acc.push c)
  go ' ' (line.length + 1) line.toList ""

/-- frame a block of text with box drawing, in the accent colour -/
def Session.box (s : Session) (text : String) : String :=
  let ls := (text.dropEndWhile (· == '\n')).toString.splitOn "\n"
  if text.trimAscii.isEmpty then "" else
  let w := ls.foldl (fun m l => max m l.length) 0
  let bar := String.ofList (List.replicate (w + 2) '─')
  let side := s.paint s.pal.accent "│"
  let body := ls.map fun l => side ++ " " ++ s.verdicts l ++ String.ofList (List.replicate (w - l.length) ' ') ++ " " ++ side
  "\n".intercalate ([s.paint s.pal.accent ("┌" ++ bar ++ "┐")] ++ body ++ [s.paint s.pal.accent ("└" ++ bar ++ "┘")])

/-- the banner -/
def Session.banner (s : Session) : String :=
  let m := s.paint s.pal.muted
  "\n".intercalate
    [ "  " ++ m ":3" ++ "      " ++ m "=^.^=" ++ "     " ++ m ":)",
      "      " ++ s.paint s.pal.logo "4ST" ++ s.paint s.pal.logoAlt "eroid" ++ "   " ++ m ":D" ++ "   "
        ++ m "an interactive prompt",
      "  " ++ m "^_^" ++ "   " ++ m ":help for help, :quit or Ctrl-D to leave" ++ "   " ++ m ":3" ]

/-- the text of `:help` -/
def helpText : String := "\n".intercalate
  [ "asteroid lines, one at a time; state stays between lines, as in a file:",
    "  let h = load hello.bench      show h      claim gates(h) = base(h)",
    "  circuit NAME N ... end        a circuit typed in (the prompt becomes ...>)",
    "meta commands:",
    "  :help               this text",
    "  :load FILE.ath      run a program's lines here; its names stay",
    "  :save FILE.ath      write this session's lines to a file",
    "  :quit               leave (Ctrl-D too)",
    "proofs (`by lean`) are not run at this prompt: use `asteroid FILE.ath`" ]

/-- what one evaluation of statements does: the circuits in, the circuits out (it prints) -/
abbrev Exec := Env → List Line → IO Env

/-- run the statements of one fed line; the printed text and whether it went through -/
def Session.runLines (s : Session) (exec : Exec) (ls : List Line) : IO (Session × String × Bool) := do
  let red (m : String) := s.paint s.pal.refuted "rejected: " ++ m
  let (out, r) ← IO.FS.withIsolatedStreams (do
    try
      let env ← exec s.env ls
      pure (some env)
    catch e => do IO.println (red (toString e)); pure none)
  match r with
  | some env => return ({ s with env }, out, true)
  | none => return (s, out, false)

/-- feed one raw line: it is a statement, or a line of the open circuit block -/
def Session.feed (s : Session) (exec : Exec) (raw : String) : IO (Session × String) := do
  let line := raw.trimAscii.toString
  let ws := words ((line.splitOn "#").headD "")
  if ws.isEmpty && s.block.isNone then return (s, "")
  let s := { s with ln := s.ln + 1 }
  let relabel (ls : List Line) : List Line := ls.map fun l => { l with num := s.ln }
  let keep (s : Session) (ok : Bool) := if ok then { s with kept := s.kept.push line } else s
  let parsed : Except String (List Line) × Session :=
    match s.block with
    | some b =>
      if ws == ["end"] then
        (parse "repl.ath" ("\n".intercalate (b.push line).toList), { s with block := none })
      else (.ok [], { s with block := some (b.push line) })
    | none =>
      if ws.head? == some "circuit" then (.ok [], { s with block := some #[line] })
      else (parse "repl.ath" line, s)
  match parsed with
  | (.error e, s) =>
    return (keep { s with block := none } false, s.paint s.pal.refuted "rejected: " ++ e ++ "\n")
  | (.ok ls, s) =>
    let (s, out, ok) ← s.runLines exec (relabel ls)
    return (keep s ok, out)

/-- show text in a box -/
def Session.show (s : Session) (text : String) : IO Unit := do
  let b := s.box text
  unless b.isEmpty do IO.println b

/-- a path as typed: from the current folder, else from the repository folder -/
def findFile (root : System.FilePath) (arg : String) : IO (Option System.FilePath) := do
  let p : System.FilePath := ⟨arg.map fun c => if c == '\\' then '/' else c⟩
  if ← p.pathExists then
    if !(← p.isDir) then return some p
  if !p.isAbsolute then
    let q := root / p
    if (← q.pathExists) && !(← q.isDir) then return some q
  return none

/-- one meta command (`:word arg`); `none` means leave -/
def Session.meta (s : Session) (exec : Exec) (root : System.FilePath) (line : String) :
    IO (Option Session) := do
  let body := (line.drop 1).toString
  let word := (body.takeWhile (· != ' ')).toString
  let arg := ((body.dropWhile (· != ' ')).toString).trimAscii.toString
  let red (m : String) := s.paint s.pal.refuted "rejected: " ++ m
  match word with
  | "quit" | "q" | "exit" => return none
  | "help" | "h" | "?" => s.show helpText; return some s
  | "save" =>
    if arg.isEmpty then s.show "usage: :save FILE.ath"; return some s
    try
      IO.FS.writeBinFile ⟨arg.map fun c => if c == '\\' then '/' else c⟩
        ("# saved from the asteroid prompt\n" ++ "\n".intercalate s.kept.toList ++ "\n").toUTF8
      s.show s!"saved {s.kept.size} lines to {arg}"
    catch e => s.show (red (toString e))
    return some s
  | "load" =>
    let some p ← (if arg.isEmpty then pure none else findFile root arg)
      | s.show (red s!"no such file: {if arg.isEmpty then "(none given)" else arg}"); return some s
    let text ← IO.FS.readFile p
    let text := (text.replace "\r\n" "\n").replace "\r" "\n"
    let mut s := s
    let mut outs : Array String := #[]
    for raw in text.splitOn "\n" do
      if (words ((raw.splitOn "#").headD "")).isEmpty then continue
      let (s', out) ← s.feed exec raw
      s := s'
      let out := out.dropEndWhile (· == '\n') |>.toString
      unless out.isEmpty do outs := outs.push out
    s.show (if outs.isEmpty then s!"loaded {arg}" else "\n".intercalate outs.toList)
    return some s
  | "lean" => s.show "proofs are not run at this prompt: use `asteroid FILE.ath`"; return some s
  | _ => s.show (red s!"unknown command :{word}   (:help)"); return some s

/-- the prompt loop; the exit code -/
partial def loop (s : Session) (exec : Exec) (root : System.FilePath) (tty : Bool) : IO UInt32 := do
  let out ← IO.getStdout
  if tty then
    out.putStr (s.paint s.pal.accent (if s.block.isSome then "...> " else "4ST> "))
    out.flush
  let raw ← (← IO.getStdin).getLine
  if raw.isEmpty then
    if tty then IO.println ""
    return 0
  let line := raw.trimAscii.toString
  if line.isEmpty then return ← loop s exec root tty
  if line == "exit" || line == "quit" then return 0
  if line.startsWith ":" && s.block.isNone then
    match ← s.meta exec root line with
    | some s => loop s exec root tty
    | none => return 0
  else
    let (s, text) ← s.feed exec raw
    s.show text
    loop s exec root tty

/-- `asteroid` with no arguments: the prompt. `root` is the repository folder (for
`site/terminal.json` and for `load` paths), `exec` evaluates statements against the circuits. -/
def repl (root : System.FilePath) (exec : Exec) : IO UInt32 := do
  let colour ← colourOn
  let tty ← (← IO.getStdin).isTty
  let s : Session := { pal := ← loadPalette root, colour }
  if tty || (← IO.getEnv "ASTEROID_BANNER").isSome then
    IO.println s.banner
    IO.println ""
  loop s exec root tty

end Repl
end AsteroidLang
