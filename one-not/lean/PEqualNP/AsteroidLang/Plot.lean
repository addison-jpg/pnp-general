import PEqualNP.AsteroidLang.Json
import PEqualNP.AsteroidLang.Eval
/-!
# asteroid: `plot phi NAME [NAME ...] -> FILE.svg`

Draws the expected slack `Φ(p) = Σ_Q p^|Q| (1−p)^(n−|Q|) slack(Q)` of each named circuit on
`[0, 1]` and writes an SVG directly. `Φ` is computed exactly at the 101 points `p = k/100` (an
integer numerator over `100^n`), then written with 12 decimals in the `<desc>` of the file (the
check script `one-not/research/open/native_plot_check.py` reads them there). Slack is that of
`Circ.slackTable` (OR gates). No Mathlib.
-/
namespace AsteroidLang.Plot
open Core

/-- the colours of one drawing -/
structure Colors where
  background : String := "#fafaf7"
  text : String := "#1c1c1a"
  muted : String := "#5f5f5a"
  curves : Array String := #["#005682", "#2e6b3a", "#8a5a00", "#a3352b"]

/-- the light colours of `site/palette.json`, where it exists -/
def loadColors (root : System.FilePath) : IO Colors := do
  let d : Colors := {}
  try
    let j ← IO.ofExcept (AsteroidLang.Json.parse (← IO.FS.readFile (root / "site" / "palette.json")))
    let l ← IO.ofExcept (j.field "light")
    let g (k dflt : String) : String := l.strOr k dflt
    return { background := g "background" d.background, text := g "text" d.text,
             muted := g "muted" d.muted,
             curves := #[g "accent" d.curves[0]!, g "proved" d.curves[1]!,
                         g "open" d.curves[2]!, g "refuted" d.curves[3]!] }
  catch _ => return d

/-- the sums of `slack(Q)` over the cubes `Q` of each size `0 … n` -/
def levelSums (C : Circ) : Array Int := Id.run do
  let mut a := Array.replicate (C.n + 1) (0 : Int)
  let mut q := 0
  for s in C.slackTable do
    let k := (Nat.popCount q)
    a := a.modify k (· + s)
    q := q + 1
  return a
where Nat.popCount (x : Nat) : Nat := Id.run do
  let mut c := 0; let mut y := x
  while y > 0 do
    c := c + y % 2; y := y / 2
  return c

/-- `Φ(k/100) · 100^n`, exactly -/
def phiNum (L : Array Int) (n k : Nat) : Int := Id.run do
  let mut s : Int := 0
  for i in [0:n + 1] do
    s := s + L[i]! * ((k ^ i * (100 - k) ^ (n - i) : Nat) : Int)
  return s

/-- `num / 100^n` as a decimal with 12 places (rounded half away from zero) -/
def decimal12 (num : Int) (n : Nat) : String :=
  let den : Nat := 100 ^ n
  let scale : Nat := 10 ^ 12
  let m : Nat := (num.natAbs * scale * 2 + den) / (2 * den)
  let ip := m / scale
  let fp := toString (m % scale)
  s!"{if num < 0 && m > 0 then "-" else ""}{ip}.{"".pushn '0' (12 - fp.length)}{fp}"

/-- the 101 values of `Φ` of a circuit as 12-place decimals -/
def phiDecimals (C : Circ) : Array String :=
  let L := levelSums C
  (Array.range 101).map fun k => decimal12 (phiNum L C.n k) C.n

/-- a number with two decimals -/
def f2 (x : Float) : String :=
  let r := (x * 100).round
  let neg := r < 0
  let m := (if neg then -r else r).toUInt64.toNat
  let fp := toString (m % 100)
  s!"{if neg then "-" else ""}{m / 100}.{if fp.length < 2 then "0" else ""}{fp}"

/-- escape text for XML -/
def esc (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

/-- the SVG of the curves `(name, n, Φ values)` -/
def svg (cols : Colors) (curves : Array (String × Nat × Array String)) : String := Id.run do
  let W : Float := 720; let H : Float := 440
  let l : Float := 70; let r : Float := W - 30; let t : Float := 50; let b : Float := H - 60
  let vals : Array Float := curves.foldl (init := #[0.0]) fun acc (_, _, ds) =>
    acc ++ ds.map fun d => (d.toInt?.map (fun _ => 0.0)).getD (parseFloat d)
  let hi := vals.foldl max 0.0
  let lo := vals.foldl min 0.0
  let hi' := if hi - lo < 1e-9 then lo + 1.0 else hi
  let pad := (hi' - lo) * 0.08
  let top := hi' + pad
  let bot := if lo < 0 then lo - pad else 0.0
  let X (p : Float) : Float := l + p * (r - l)
  let Y (v : Float) : Float := b - (v - bot) / (top - bot) * (b - t)
  let mut o := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"720\" height=\"440\" \
    viewBox=\"0 0 720 440\" font-family=\"sans-serif\" font-size=\"12\">\n"
  o := o ++ s!"<title>Phi(p) = expected slack</title>\n"
  o := o ++ "<desc>phi at p = 0.00, 0.01 … 1.00, one line per circuit (name, n, values)\n"
  for (nm, n, ds) in curves do
    o := o ++ s!"{esc nm} {n} {" ".intercalate ds.toList}\n"
  o := o ++ "</desc>\n"
  o := o ++ s!"<rect width=\"720\" height=\"440\" fill=\"{cols.background}\"/>\n"
  o := o ++ s!"<text x=\"{f2 l}\" y=\"30\" font-size=\"16\" fill=\"{cols.text}\">\
    Φ(p) = expected slack, p in [0, 1]</text>\n"
  -- grid and axes
  for i in [0:6] do
    let p := i.toFloat / 5
    o := o ++ s!"<line x1=\"{f2 (X p)}\" y1=\"{f2 t}\" x2=\"{f2 (X p)}\" y2=\"{f2 b}\" \
      stroke=\"{cols.muted}\" stroke-opacity=\"0.2\"/>\n"
    o := o ++ s!"<text x=\"{f2 (X p)}\" y=\"{f2 (b + 18)}\" text-anchor=\"middle\" \
      fill=\"{cols.muted}\">{f2 p}</text>\n"
    let v := bot + (top - bot) * p
    o := o ++ s!"<line x1=\"{f2 l}\" y1=\"{f2 (Y v)}\" x2=\"{f2 r}\" y2=\"{f2 (Y v)}\" \
      stroke=\"{cols.muted}\" stroke-opacity=\"0.2\"/>\n"
    o := o ++ s!"<text x=\"{f2 (l - 8)}\" y=\"{f2 (Y v + 4)}\" text-anchor=\"end\" \
      fill=\"{cols.muted}\">{f2 v}</text>\n"
  o := o ++ s!"<rect x=\"{f2 l}\" y=\"{f2 t}\" width=\"{f2 (r - l)}\" height=\"{f2 (b - t)}\" \
    fill=\"none\" stroke=\"{cols.muted}\"/>\n"
  o := o ++ s!"<line x1=\"{f2 l}\" y1=\"{f2 (Y 0)}\" x2=\"{f2 r}\" y2=\"{f2 (Y 0)}\" \
    stroke=\"{cols.text}\" stroke-width=\"1.5\"/>\n"
  o := o ++ s!"<text x=\"{f2 ((l + r) / 2)}\" y=\"{f2 (H - 14)}\" text-anchor=\"middle\" \
    fill=\"{cols.text}\">p</text>\n"
  o := o ++ s!"<text transform=\"translate(18 {f2 ((t + b) / 2)}) rotate(-90)\" \
    text-anchor=\"middle\" fill=\"{cols.text}\">Φ(p)</text>\n"
  -- curves and legend
  let mut idx := 0
  for (nm, n, ds) in curves do
    let col := cols.curves[idx % cols.curves.size]!
    let pts := (ds.toList.zipIdx).map fun (d, k) =>
      s!"{f2 (X (k.toFloat / 100))},{f2 (Y (parseFloat d))}"
    o := o ++ s!"<polyline fill=\"none\" stroke=\"{col}\" stroke-width=\"2.5\" \
      stroke-linejoin=\"round\" points=\"{" ".intercalate pts}\"/>\n"
    let ly := t + 16 + 18 * idx.toFloat
    o := o ++ s!"<line x1=\"{f2 (r - 150)}\" y1=\"{f2 ly}\" x2=\"{f2 (r - 125)}\" y2=\"{f2 ly}\" \
      stroke=\"{col}\" stroke-width=\"2.5\"/>\n"
    o := o ++ s!"<text x=\"{f2 (r - 118)}\" y=\"{f2 (ly + 4)}\" fill=\"{cols.text}\">\
      {esc nm} (n={n})</text>\n"
    idx := idx + 1
  return o ++ "</svg>\n"
where
  /-- a decimal such as `-0.123456789012` as a Float -/
  parseFloat (s : String) : Float :=
    let neg := s.startsWith "-"
    let body := if neg then (s.drop 1).toString else s
    match body.splitOn "." with
    | [a, f] =>
      let v := a.toNat!.toFloat + f.toNat!.toFloat / (10 : Float) ^ f.length.toFloat
      if neg then -v else v
    | _ => 0.0

/-- run one `plot phi NAMES -> FILE` statement (its words joined by spaces). `outPath` turns the
path written in the program into the file to write. Returns the line to print. -/
def runPlot (env : Env) (root : System.FilePath) (outPath : String → System.FilePath)
    (what : String) : IO String := do
  let rest := (what.drop "plot phi ".length).toString
  match rest.splitOn " -> " with
  | [names, file] =>
    let names := (names.splitOn " ").filter (· ≠ "")
    let file := file.trimAscii.toString
    if names.isEmpty then return "plot phi: no circuit named"
    let mut curves := #[]
    for nm in names do
      match env.circ? nm with
      | some C => curves := curves.push (nm, C.n, phiDecimals C)
      | none => return s!"plot phi: {nm}: no circuit of this name"
    let (file, note) :=
      if file.endsWith ".png" then
        ((file.dropEnd 4).toString ++ ".svg", " (asked for .png: this version writes .svg)")
      else (file, "")
    let out := outPath file
    if let some d := out.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile out (svg (← loadColors root) curves).toUTF8
    return s!"wrote {out}{note}"
  | _ => return "plot phi: expected `plot phi NAME [NAME ...] -> FILE.svg`"

end AsteroidLang.Plot
