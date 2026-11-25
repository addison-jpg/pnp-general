"""asteroid extension: frames. A frame ties an idea someone brought to the claim that formalizes it.
  frame "SOURCE" reading "READING" -> CLAIMREF label WORD [reach R] [cost C]
CLAIMREF is a claim line number earlier in the same file, another .ath file (path), or `none`.
The frame is TRUE only if its claim passes in this run. A line claim must have printed TRUE. A file is run
with --no-lean and must exit 0. Otherwise the frame is OPEN and its label is forced to `open`.
A Python claim supports at most `checked-finite`: a stronger WORD is downgraded, and the output says so.
score = reach * chance / cost. reach: integer >= 1 (default 1). cost: thousands of tokens (default 80).
chance: 1.0 if the claim passed, else PRIOR[label]. The weights are choices, not measurements.
Each frame is written to frames.jsonl at the repository root (or $ASTEROID_FRAMES), one line per
(source, reading, claim); a rerun replaces that line, so there are no duplicates."""
import json, os, re, subprocess, sys
import asteroid.asteroid as A

WORDS = ["checked", "checked-finite", "checked-infinite", "paper", "tested", "refuted", "open", "premise"]
STRONGER = {"checked", "checked-infinite"}   # need Lean or a reduction; a Python claim does not give them
PRIOR = {"open": 0.3}                          # chance for a claim that did not pass (its label is forced to open)
REACH, COST = 1, 80                            # 80k tokens: one plain seat, ath_prompts/measure/cost_per_result.md
TIMEOUT = 1800
FILE_CACHE = {}
PAT = re.compile(r'frame "([^"]+)" reading "([^"]+)" -> (\S+) label ([\w-]+)(?: reach (\d+))?(?: cost (\d+(?:\.\d+)?))?')

def frames_path():
    return os.environ.get("ASTEROID_FRAMES") or os.path.join(A.ROOT, "frames.jsonl")

def score(reach, passed, label, cost):
    return reach * (1.0 if passed else PRIOR[label]) / cost

def _run_file(p, where):
    f = A.in_path(p)
    if not os.path.isfile(f): raise SystemExit(f"{where}: no such program: {p}")
    key = os.path.realpath(f)
    if key in FILE_CACHE: return FILE_CACHE[key]
    depth = int(os.environ.get("ASTEROID_FRAME_DEPTH", "0"))
    if depth >= 3: raise SystemExit(f"{where}: frames nest more than 3 files deep (a loop?)")
    env = dict(os.environ, ASTEROID_FRAME_DEPTH=str(depth + 1))
    try:
        r = subprocess.run([sys.executable, "-I", os.path.join(A.ROOT, "asteroid", "asteroid.py"), "--no-lean", f], cwd=A.ROOT,
                           capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=TIMEOUT, env=env)
        out = (r.returncode == 0, f"exit {r.returncode}")
    except subprocess.TimeoutExpired: out = (False, f"timed out after {TIMEOUT} s")
    FILE_CACHE[key] = out
    return out

def write(rec):
    path = frames_path(); key = (rec["source"], rec["reading"], rec["claim"])
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()] if os.path.isfile(path) else []
    old = [r for r in rows if (r["source"], r["reading"], r["claim"]) == key]
    if old and old[0] == rec: return "kept"
    rows = [r for r in rows if (r["source"], r["reading"], r["claim"]) != key] + [rec]
    with open(path, "w", encoding="utf-8") as fh:
        for r in rows: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    return "updated" if old else "written"

def handle(line, api):
    if not line.startswith("frame "): return False
    where = f"{api['script']}:{api['ln']}"
    m = PAT.fullmatch(line)
    if not m: raise SystemExit(f'{where}: frame "SOURCE" reading "READING" -> CLAIMREF label WORD [reach R] [cost C]')
    source, reading, ref, word = m.group(1), m.group(2), m.group(3), m.group(4)
    reach, cost = int(m.group(5) or REACH), float(m.group(6) or COST)
    if word not in WORDS: raise SystemExit(f"{where}: label {word} is not one of {', '.join(WORDS)}")
    if reach < 1 or cost <= 0: raise SystemExit(f"{where}: reach must be >= 1 and cost > 0")
    if ref == "none": passed, why, claim = False, "no claim yet", "none"
    elif ref.isdigit():
        hits = [r for r in api["results"] if r[0] == int(ref)]
        if not hits: raise SystemExit(f"{where}: no claim or check at line {ref} before this frame")
        passed, why = hits[-1][2], f"line {ref} {'TRUE' if hits[-1][2] else 'FALSE'}"
        claim = f"{os.path.relpath(os.path.abspath(api['script']), A.ROOT).replace(os.sep, '/')}:{ref}"
    elif ref.endswith((".ath", ".ast")):
        passed, why = _run_file(ref, where); claim = ref
    else: raise SystemExit(f"{where}: CLAIMREF must be a line number, a .ath file, or none")
    note = ""
    if not passed and word != "open": note = f"; label {word} forced to open"; word = "open"
    elif passed and word in STRONGER: note = f"; label {word} downgraded to checked-finite (the claim is Python only)"; word = "checked-finite"
    status = "TRUE" if passed else "OPEN"
    s = round(score(reach, passed, word, cost), 6)
    rec = {"source": source, "reading": reading, "claim": claim, "label": word, "score": s, "status": status, "reach": reach, "cost": cost}
    w = write(rec)
    A.say(f"{api['ln']}: frame {source[:40]} -> {claim}: {status} ({why}{note}) label {word} score {s:.4g} = {reach} * {1.0 if passed else PRIOR[word]} / {cost:g}; {w} in frames.jsonl")
    return True
