"""cite: the resolver shared by the asteroid verb `cite` (asteroid/ext_cite.py) and the git gate (tools/cite/gate.py).

A citation KEY is `KIND:VALUE` (VALUE may be written in double quotes when it has spaces):

  lit:"TEXT"     a table row of LITERATURE.md that contains TEXT (case-insensitive)
  doi:VALUE      VALUE appears in LITERATURE.md (an outside source must be in the literature index first)
  arxiv:VALUE    VALUE appears in LITERATURE.md (same rule)
  lean:NAME      a Lean declaration (theorem, lemma, def, structure, ...) whose full name is NAME,
                 or whose full name ends with ".NAME" and is the only one that does. An `axiom` is refused.
  file:PATH      a file of this repository (inside the root after symlinks; not under .git)
  commit:HASH    a commit (7 to 40 hex digits) reachable from HEAD
  ath:PATH       an asteroid program in which every claim line is itself cited (checked recursively)
  original       the statement is new here and has no earlier source (an explicit choice, never a default)

A citation is ALIVE when it resolves now, DEAD otherwise. A dead citation is a failure. There is no third state.
Every limit below is hard: past it the citation is DEAD, never assumed fine.
"""
import os, re, subprocess

ROOT = os.path.realpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))

# Limits (choices, in the spirit of asteroid's SPEC.md "Size limits"; change them here and in asteroid/CITE.md).
LIT_MAX_BYTES = 2 * 10**6        # LITERATURE.md is read once per run, at most this many bytes
LEAN_MAX_FILES = 20000           # Lean files indexed per run
LEAN_MAX_BYTES = 2 * 10**6       # bytes read per Lean file
ATH_DEPTH, ATH_FILES = 3, 64     # ath: citations nest at most 3 deep and visit at most 64 programs per run (asteroid's NEST limits)
KEYS_PER_RUN = 4096              # resolutions per run
GIT_TIMEOUT = 60                 # seconds per git call
LEAN_DIRS = ["lean", "one-not/lean", "951/lean"]
KINDS = ("lit", "doi", "arxiv", "lean", "file", "commit", "ath", "original")

KEY_RE = re.compile(r'(lit|doi|arxiv|lean|file|commit|ath):("[^"]*"|[^\s\]\)"`,;]+)|(original)\b')
TOKEN_RE = re.compile(r'cite:((?:lit|doi|arxiv|lean|file|commit|ath):(?:"[^"]*"|[^\s\]\)"`,;]+)|original\b)')
CLAIM_RE = re.compile(r'^\s*(claim!?|check|prove|record)\b')   # .ath lines that state something
CITE_LINE_RE = re.compile(r'^\s*cite\s+(.+)$')

_STATE = {"lit": None, "lean": None, "keys": 0, "ath_seen": set()}

def reset():
    _STATE.update({"lit": None, "lean": None, "keys": 0, "ath_seen": set()})

def parse_keys(text):
    """All KEYs in TEXT, in order, as (kind, value) pairs; `original` has value ''."""
    out = []
    for m in KEY_RE.finditer(text):
        if m.group(3): out.append(("original", ""))
        else: out.append((m.group(1), m.group(2).strip('"')))
    return out

def tokens(text):
    """The KEYs written as `cite:KEY` tokens in a line of Markdown or Lean."""
    return [k for t in TOKEN_RE.findall(text) for k in parse_keys(t)]

def _lit():
    if _STATE["lit"] is None:
        p = os.path.join(ROOT, "LITERATURE.md")
        if not os.path.isfile(p): _STATE["lit"] = ("", []); return _STATE["lit"]
        if os.path.getsize(p) > LIT_MAX_BYTES: _STATE["lit"] = (None, None); return _STATE["lit"]
        text = open(p, encoding="utf-8", errors="replace").read()
        _STATE["lit"] = (text.lower(), [l.lower() for l in text.splitlines() if l.lstrip().startswith("|")])
    return _STATE["lit"]

DECL_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                     r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+([^\s:({\[]+)')
NS_RE = re.compile(r'^\s*(namespace|section)\s*(\S*)')
END_RE = re.compile(r'^\s*end\b\s*(\S*)')

def _lean():
    if _STATE["lean"] is None:
        idx, nfiles, seen = {}, 0, set()
        for d in LEAN_DIRS:
            top = os.path.join(ROOT, d)
            if not os.path.isdir(top): continue
            for dp, dns, fns in os.walk(top):
                dns[:] = [x for x in dns if x not in (".lake", "build", ".git")]
                for fn in fns:
                    if not fn.endswith(".lean"): continue
                    f = os.path.realpath(os.path.join(dp, fn))
                    if f in seen: continue
                    seen.add(f); nfiles += 1
                    if nfiles > LEAN_MAX_FILES: _STATE["lean"] = {"__over__": True}; return _STATE["lean"]
                    stack = []
                    try: text = open(f, encoding="utf-8", errors="replace").read(LEAN_MAX_BYTES)
                    except OSError: continue
                    for line in text.splitlines():
                        if m := NS_RE.match(line): stack.append((m.group(1), m.group(2))); continue
                        if (m := END_RE.match(line)) and stack: stack.pop(); continue
                        if m := DECL_RE.match(line):
                            ns = [n for k, n in stack if k == "namespace" and n]
                            full = ".".join(ns + [m.group(2)]) if not m.group(2).startswith("_root_.") else m.group(2)[7:]
                            idx.setdefault(full, []).append((m.group(1), os.path.relpath(f, ROOT)))
        _STATE["lean"] = idx
    return _STATE["lean"]

def _git(*args):
    return subprocess.run(["git", "-C", ROOT, *args], capture_output=True, text=True, timeout=GIT_TIMEOUT)

def _inside(p):
    f = os.path.realpath(os.path.join(ROOT, p))
    return f if os.path.commonpath([ROOT, f]) == ROOT and not os.path.relpath(f, ROOT).split(os.sep)[0] == ".git" else None

def uncited_claims(path):
    """Line numbers of claim lines in an .ath program that have no `cite` line before the next claim line."""
    lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    out, pending = [], None
    for i, raw in enumerate(lines, 1):
        line = raw.split("#", 1)[0]
        if CLAIM_RE.match(line):
            if pending is not None: out.append(pending)
            pending = i
        elif CITE_LINE_RE.match(line): pending = None
    if pending is not None: out.append(pending)
    return out

def resolve(kind, value, depth=0):
    """(alive, why) for one KEY."""
    _STATE["keys"] += 1
    if _STATE["keys"] > KEYS_PER_RUN: return False, f"more than {KEYS_PER_RUN} citations in one run"
    if kind == "original": return True, "new here (explicit)"
    if kind in ("lit", "doi", "arxiv"):
        text, rows = _lit()
        if text is None: return False, f"LITERATURE.md is over {LIT_MAX_BYTES} bytes"
        v = value.lower()
        if not v: return False, "empty value"
        if kind == "lit":
            hits = [r for r in rows if v in r]
            return (True, f"{len(hits)} row(s) of LITERATURE.md") if hits else (False, "no row of LITERATURE.md contains it")
        return (True, "in LITERATURE.md") if v in text else (False, "not in LITERATURE.md: add the source there first")
    if kind == "lean":
        idx = _lean()
        if idx.get("__over__"): return False, f"more than {LEAN_MAX_FILES} Lean files"
        hits = idx.get(value) or [x for k, v in idx.items() if k.endswith("." + value) for x in v]
        names = {k for k in idx if k == value or k.endswith("." + value)}
        if not hits: return False, "no Lean declaration has this name"
        if len(names) > 1: return False, f"ambiguous: {len(names)} declarations end with it; write the full name"
        if any(k == "axiom" for k, _ in hits): return False, "an axiom is a premise, not a source"
        return True, f"{hits[0][0]} in {hits[0][1]}"
    if kind == "file":
        f = _inside(value)
        return (True, "file exists") if f and os.path.isfile(f) else (False, "no such file in the repository")
    if kind == "commit":
        if not re.fullmatch(r"[0-9a-f]{7,40}", value): return False, "not a hex hash of 7 to 40 digits"
        try:
            if _git("cat-file", "-e", value + "^{commit}").returncode != 0: return False, "no such commit"
            if _git("merge-base", "--is-ancestor", value, "HEAD").returncode != 0: return False, "not reachable from HEAD"
        except subprocess.TimeoutExpired: return False, f"git took over {GIT_TIMEOUT} s"
        return True, "commit reachable from HEAD"
    if kind == "ath":
        f = _inside(value)
        if not (f and os.path.isfile(f) and f.endswith(".ath")): return False, "no such .ath program in the repository"
        if depth >= ATH_DEPTH: return False, f"ath citations nest more than {ATH_DEPTH} deep"
        if f in _STATE["ath_seen"]: return True, "program already checked in this run"
        _STATE["ath_seen"].add(f)
        if len(_STATE["ath_seen"]) > ATH_FILES: return False, f"more than {ATH_FILES} programs visited"
        bad = uncited_claims(f)
        if bad: return False, f"{len(bad)} uncited claim line(s), first at line {bad[0]}"
        for i, raw in enumerate(open(f, encoding="utf-8", errors="replace"), 1):
            if m := CITE_LINE_RE.match(raw.split("#", 1)[0]):
                for k, v in parse_keys(m.group(1)):
                    ok, why = resolve(k, v, depth + 1)
                    if not ok: return False, f"line {i}: {k}:{v} is dead ({why})"
        return True, "every claim of the program is cited and alive"
    return False, f"unknown kind {kind}"
