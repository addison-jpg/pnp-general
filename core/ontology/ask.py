#!/usr/bin/env python3
"""A controlled-English query interface to the repository's recorded results. Read-only. Standard library only.

  python3 -I core/ontology/ask.py show open frames about time
  python3 -I core/ontology/ask.py what connects beauvoir and time
  python3 -I core/ontology/ask.py --model "what do we have that is open about time"

It answers from data. It does not infer, and it never executes anything it is given. The query is matched
against a fixed grammar (GRAMMAR below). A WORD or TAG is compared as data only: it must be one plain word,
it is matched through re.escape, no path is taken from it, and no shell is involved. Every answer line starts
with its label in brackets: checked, checked-finite, checked-infinite, tested, refuted, analogy, open, proposed.

Data, all under ROOT (three dirnames up from this file, or $ASK_ROOT, or the root argument):
  **/findings.jsonl                       board findings (the current ones). Verified by the boards.py rule,
                                          recomputed here relative to ROOT; the second seat is shown
  center/shards/*.jsonl                   center nodes: cells, levels, fingerprints, and findings not on a board
  RESULTS.md                              the rows of the generated results table (verified findings)
  frames.jsonl                            frames (asteroid `frame`): label, TRUE or OPEN
  core/ontology/*.py                      in-between results (asymmetry.py and others), read by their docstring
  core/ontology/tags/tags_culture.json    structure tags on culture works: PROPOSED, UNREVIEWED
  core/ontology/tags/tags_formal.json     structure tags on formal results: PROPOSED, UNREVIEWED

Nothing gets upgraded. An unverified finding prints as not verified. A finding recorded as checked that is not
verified prints as [open]. A row from a tag table always prints as [proposed]; its own label is shown as
"row label" and never moved to the front. A module's label is the label of its board finding if it has one,
else the label its docstring states (and the line says it is not on the board), else [open].

Exit codes: 0 answered, 2 did not understand, 3 the model is missing (--model only).

--model (stage 2): a small local model is asked to write ONE query line in this grammar. The line is then
checked by the same parser. If it does not parse, the interface says so and shows the grammar; it never
guesses. The model never writes answer text. The only file this program ever writes is the model-output
cache core/ontology/.ask_cache.json, and only in --model mode (it is in .gitignore). A plain query writes nothing."""
import ast, difflib, glob, hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MAXQ = 300            # longest query read, in characters
MAXROWS = 12          # rows shown per list; the rest is counted
MAXLEAVES = 400       # findings.jsonl files read at most
MAXREAD = 8 << 20     # bytes read at most from one evidence file
CHECKED = ("checked", "checked-finite", "checked-infinite")
HONEST = CHECKED + ("tested", "refuted", "analogy", "open", "proposed")
BOARD_WORDS = ["checked", "checked-finite", "checked-infinite", "paper", "tested", "refuted", "open", "premise"]   # boards.WORDS
SKIP = {".git", ".lake", "__pycache__", "node_modules", ".venv", "artifacts", ".deps", ".pnp", "dist"}
FILLER = {"the", "a", "an", "please", "kindly", "me", "us"}
WORD_RE = re.compile(r"[\w'-]+")                    # one token of letters, digits, _ ' - only: no shell or path characters
MODEL_NAME = "Qwen/Qwen2.5-0.5B-Instruct"
NOT_MODULES = {"ask.py", "test_ask.py"}

GRAMMAR = """Grammar (case does not matter; the, a, an, please are ignored):
  status
  how many results are verified
  show open frames [about WORD]
  show frames [about WORD]
  show findings [about WORD]           board and center findings, verified or not
  show verified findings [about WORD]
  what is verified about WORD          verified findings and RESULTS.md rows
  what is open about WORD              open frames, unverified findings, open cells and modules
  what connects WORD and WORD          shared tags, shared findings, in-between results
  which results use TAG                formal results, by structure tag (tags are proposed)
  which works use TAG                  culture works, by structure tag (tags are proposed)
  what links CORPUS and PILLAR         tags a culture corpus and a formal pillar share
  list tags | list corpora | list pillars
  what is TAG
  explain WORD                         everything on record whose text mentions WORD"""

EXAMPLES = ["status", "how many results are verified", "show open frames", "show open frames about time", "show frames", "show frames about time",
            "show findings", "show findings about time", "show verified findings", "show verified findings about time",
            "what is verified about time", "what is open about time", "what connects beauvoir and time",
            "which results use exhaustive-check", "which works use branching-tree", "what links beauvoir and physics",
            "list tags", "list corpora", "list pillars", "what is fixed-point", "explain asymmetry"]


def get_root(root=None):
    return os.path.abspath(root or os.environ.get("ASK_ROOT") or DEFAULT_ROOT)


def clean(s, n=80):
    """Make user text safe to echo: printable characters only, short."""
    s = "".join(ch if ch.isprintable() else "?" for ch in str(s))
    return s if len(s) <= n else s[:n] + "..."


def mentions(word, text):
    """word occurs in text at the start of a word (so 'time' finds 'times', not 'sometimes'). word is escaped: plain text only."""
    return bool(word) and re.search(r"(?<!\w)" + re.escape(word), str(text).lower()) is not None


# ---------------------------------------------------------------- parsing

def tokens(q):
    """Lowercased tokens with filler words and trailing ? ! . , removed. None if the query is too long or not text."""
    if not isinstance(q, str) or len(q) > MAXQ: return None
    out = []
    for t in q.lower().split():
        t = t.rstrip("?!.,")
        if t and t not in FILLER: out.append(t)
    return out


def parse(q):
    """Return (kind, args) for a query in the grammar, or None. WORD and TAG tokens must be plain word characters."""
    t = tokens(q)
    if not t: return None
    ok = lambda w: bool(WORD_RE.fullmatch(w))
    n = len(t)
    if t == ["status"]: return ("status", ())
    if n == 5 and t[:3] in (["how", "many", "results"], ["how", "many", "findings"]) and t[3:] == ["are", "verified"]: return ("verified", ())
    for head, kind in ((["show", "open", "frames"], "frames_open"), (["show", "frames"], "frames"),
                       (["show", "verified", "findings"], "findings_verified"), (["show", "findings"], "findings")):
        if t[:len(head)] == head:
            rest = t[len(head):]
            if not rest: return (kind, (None,))
            if len(rest) == 2 and rest[0] == "about" and ok(rest[1]): return (kind, (rest[1],))
            return None
    if n == 5 and t[:2] == ["what", "is"] and t[2] in ("verified", "open") and t[3] == "about" and ok(t[4]): return ("about_" + t[2], (t[4],))
    if n == 5 and t[:2] == ["what", "connects"] and t[3] == "and" and ok(t[2]) and ok(t[4]): return ("connects", (t[2], t[4]))
    if n == 4 and t[:2] == ["which", "results"] and t[2] == "use" and ok(t[3]): return ("results_use", (t[3],))
    if n == 4 and t[:2] == ["which", "works"] and t[2] == "use" and ok(t[3]): return ("works_use", (t[3],))
    if n == 5 and t[:2] == ["what", "links"] and t[3] == "and" and ok(t[2]) and ok(t[4]): return ("links", (t[2], t[4]))
    if n == 2 and t[0] == "list" and t[1] in ("tags", "corpora", "pillars"): return ("list_" + t[1], ())
    if n == 3 and t[:2] == ["what", "is"] and ok(t[2]): return ("what_is", (t[2],))
    if n == 2 and t[0] == "explain" and ok(t[1]): return ("explain", (t[1],))
    return None


# ---------------------------------------------------------------- data (read only)

def _jsonl(path):
    out = []
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            for l in fh:
                l = l.strip()
                if not l: continue
                try: r = json.loads(l)
                except ValueError: continue
                if isinstance(r, dict): out.append(r)
    except OSError: pass
    return out


def _json(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as fh: d = json.load(fh)
        return d if isinstance(d, dict) else None
    except (OSError, ValueError): return None


def _inside(root, rel):
    """A path named in the data (never in a query), kept inside root. None if it leaves root."""
    if not isinstance(rel, str) or not rel or "\x00" in rel: return None
    r = os.path.realpath(root); p = os.path.realpath(os.path.join(r, rel))      # an absolute rel stays absolute
    return p if p == r or p.startswith(r + os.sep) else None


def board_why_not(r, root):
    """boards.verified(r), recomputed with paths relative to root (boards.py uses the working folder). [] means verified.
    test_ask.py checks that the two agree on every finding in the repository."""
    why = []
    if r.get("word") not in BOARD_WORDS: why.append("word")
    for e in r.get("evidence", []) or []:
        path, _, name = str(e).partition("::")
        p = _inside(root, path)
        if not p or not os.path.exists(p): why.append("missing " + path)
        elif name:
            try:
                with open(p, errors="ignore") as fh: body = fh.read(MAXREAD)
            except OSError: body = ""
            if name not in body: why.append(name + " not in " + path)
    if not r.get("evidence"): why.append("no evidence")
    if r.get("word") == "checked":
        if not any(str(e).partition("::")[0].endswith(".lean") for e in r.get("evidence", []) or []): why.append("checked needs a .lean file")
    elif not [b for b in r.get("by", []) or [] if b != r.get("who")]: why.append("needs a second seat in by")
    if r.get("word") in ("checked-finite", "checked-infinite"):
        if not r.get("runner"): why.append(r["word"] + " needs a runner (the exhaustive check, re-runnable)")
    if r.get("word") == "checked-infinite":
        if not r.get("reduction"): why.append("checked-infinite needs a reduction (a proved or cited theorem that the finite check covers all n)")
        else:
            red = str(r["reduction"]); p = _inside(root, red.partition("::")[0])
            if not ((p and os.path.exists(p)) or red.startswith("cite:")): why.append("reduction not found: " + red)
    rt = r.get("retest")
    if isinstance(rt, dict) and not rt.get("ok"): why.append("stale: last retest failed " + str(rt.get("time")))
    return why


def board_findings(root):
    """Every current board finding: each findings.jsonl under root, lines merged by id as boards.load does."""
    out, n = [], 0
    for d, dirs, files in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in SKIP)
        if "findings.jsonl" not in files: continue
        n += 1
        if n > MAXLEAVES: break
        rel = os.path.relpath(d, root)
        last = {}
        for r in _jsonl(os.path.join(d, "findings.jsonl")):
            if "id" not in r: continue
            old = last.get(r["id"], {})
            last[r["id"]] = {**old, **r, "by": sorted(set(old.get("by", []) or []) | set(r.get("by", []) or []))}
        for r in last.values():
            if "statement" not in r: continue
            out.append({"kind": "finding", "src": "board", "id": str(r["id"]), "program": rel, "word": r.get("word"),
                        "text": str(r.get("statement", "")), "who": r.get("who"), "by": r.get("by", []),
                        "runner": r.get("runner"), "evidence": r.get("evidence", []), "why_not": board_why_not(r, root)})
    return out


def results_rows(root):
    """Rows of RESULTS.md: '| label | statement | evidence | recheck |' under '## program'."""
    out, prog = [], None
    try: lines = open(os.path.join(root, "RESULTS.md"), encoding="utf-8", errors="replace").read(MAXREAD).splitlines()
    except OSError: return out
    for i, l in enumerate(lines, 1):
        if l.startswith("## "): prog = l[3:].strip(); continue
        if not prog or not l.startswith("|"): continue
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", l.strip())[1:-1]]
        if len(cells) >= 2 and cells[0] in CHECKED + ("tested", "refuted"):
            out.append({"kind": "result", "label": cells[0], "program": prog, "text": cells[1].replace("\\|", "|"), "line": i})
    return out


def modules(root, findings):
    """In-between results: core/ontology/*.py, read by their docstring (parsed, never run)."""
    out = []
    for p in sorted(glob.glob(os.path.join(root, "core", "ontology", "*.py"))):
        name = os.path.basename(p)
        if name in NOT_MODULES: continue
        try: doc = ast.get_docstring(ast.parse(open(p, encoding="utf-8", errors="replace").read(MAXREAD))) or ""
        except (OSError, SyntaxError, ValueError): continue
        rel = os.path.relpath(p, root).replace(os.sep, "/")
        m = re.search(r"Claim \((checked-infinite|checked-finite|checked|tested|refuted|open)\b", doc)
        runs = lambda f: rel in str(f.get("runner") or "")
        board = [f for f in findings if runs(f) or any(str(e).partition("::")[0] == rel for e in f.get("evidence") or [])]
        board.sort(key=lambda f: (not runs(f), not verified(f), str(f.get("id"))))   # its own runner first, then verified, then id
        out.append({"kind": "module", "file": rel, "doc": doc, "summary": doc.strip().split("\n")[0] if doc.strip() else name,
                    "stated": m.group(1) if m else None, "board": board})
    return out


VERIFIED_WORDS = CHECKED + ("tested", "refuted")   # the words RESULTS.md lists (results.py ORDER)


def verified(f):
    """The repo's rule (boards.py, results.py): an empty why_not list, and a word RESULTS.md lists. A verified tested finding
    stays tested. A missing or malformed why_not is not verified."""
    w = f.get("why_not")
    return f.get("word") in VERIFIED_WORDS and isinstance(w, (list, tuple)) and len(w) == 0


def load(root):
    shards = sorted(glob.glob(os.path.join(root, "center", "shards", "*.jsonl")))
    center = [r for p in shards for r in _jsonl(p)]
    board = board_findings(root)
    seen = {f["id"] for f in board}
    cf = [dict(r, src="center") for r in center if r.get("kind") == "finding" and str(r.get("id")) not in seen]
    findings = sorted(board + cf, key=lambda r: (str(r.get("program")), str(r.get("id"))))
    nodes = [r for r in center if r.get("kind") not in ("finding", "frame")]
    nodes.sort(key=lambda r: (str(r.get("kind")), str(r.get("program")), str(r.get("id"))))
    tdir = os.path.join(root, "core", "ontology", "tags")
    frames = _jsonl(os.path.join(root, "frames.jsonl"))
    for r in frames: r["_check"] = frame_check(root, r, board)
    return {"shards": len(shards), "findings": findings, "nodes": nodes, "results": results_rows(root),
            "modules": modules(root, findings), "frames": frames,
            "culture": _json(os.path.join(tdir, "tags_culture.json")), "formal": _json(os.path.join(tdir, "tags_formal.json"))}


def frame_check(root, r, board):
    """The board finding for a frame's claim. A claim 'FILE.ath:N' whose line N is check "CMD" matches the board
    finding whose runner is CMD. None if there is no such line or finding. The file must stay inside root."""
    m = re.fullmatch(r"([^:\x00]+\.ath):(\d{1,6})", str(r.get("claim") or ""))
    p = m and _inside(root, m.group(1))
    if not p: return None
    try:
        with open(p, encoding="utf-8", errors="replace") as fh: lines = fh.read(MAXREAD).splitlines()
    except OSError: return None
    n = int(m.group(2))
    c = re.fullmatch(r'\s*check\s+"([^"]+)"\s*', lines[n - 1]) if 1 <= n <= len(lines) else None
    if not c: return None
    hits = sorted((f for f in board if str(f.get("runner") or "").strip() == c.group(1).strip()), key=lambda f: (not verified(f), str(f.get("id"))))
    return hits[0] if hits else None


def rows_of(d):
    return [r for r in (d or {}).get("rows", []) if isinstance(r, dict)]


def row_tags(r):
    return [t for t in list(r.get("tags") or []) + list(r.get("new_tags_proposed") or [])]


def group_of(r):
    return str(r.get("corpus") or r.get("pillar") or "?")


# ---------------------------------------------------------------- one line per record, each with its label

def f_label(f):
    w = str(f.get("word") or "open")
    why = "; ".join(str(x) for x in f.get("why_not") or [])
    if verified(f): return w, "verified"
    if w in CHECKED: return "open", f"recorded as {w}, not verified: {clean(why, 120)}"
    if w not in HONEST: return "open", f"recorded as {clean(w, 20)}, not verified" + (f": {clean(why, 120)}" if why else "")
    return w, "not verified" + (f": {clean(why, 120)}" if why else "")


def second_seat(f):
    if "by" not in f and "who" not in f: return "second seat: not recorded"
    others = sorted(set(str(b) for b in f.get("by") or []) - {str(f.get("who"))})
    if others: return "second seat: " + clean(", ".join(others), 60)
    return "second seat: none" + (" (a Lean check needs none)" if f.get("word") == "checked" else "")


def fmt_finding(f):
    lab, note = f_label(f)
    where = "board" if f.get("src") == "board" else "center"
    return f"[{lab}] finding {f.get('program')}/{f.get('id')}: {clean(f.get('text', ''), 150)} ({note}; {second_seat(f)}; {where})"


FRAME_CAP = ("checked", "checked-infinite")   # asteroid/SPEC.md: a frame supports at most checked-finite


def frame_label(w):
    """A recorded frame label, capped as asteroid/SPEC.md caps it. A frame is a reading: never checked."""
    w = str(w or "open")
    return "checked-finite" if w in FRAME_CAP else (w if w in HONEST else "open")


def fmt_frame(r):
    rec = str(r.get("label") or "open")
    lab, notes = frame_label(rec), []
    if r.get("status") != "TRUE": lab = "open"
    elif rec in FRAME_CAP: notes.append(f"recorded as {rec}, capped at checked-finite: a frame is a reading")
    f = r.get("_check")
    if f and lab != "open":
        flab, fnote = f_label(f)
        if not verified(f): lab = "open"; notes.append(f"board finding {f.get('id')} for this check: [{flab}] {fnote}")
        else: notes.append(f"board finding {f.get('id')} for this check is verified")
    return (f"[{lab}] frame {r.get('status')}: {clean(r.get('source', ''), 70)} -> {clean(r.get('reading', ''), 90)} "
            f"(claim {clean(r.get('claim'), 40)}, score {r.get('score')}; as recorded in frames.jsonl"
            + "".join("; " + clean(x, 160) for x in notes) + ")")


def fmt_result(r):
    return f"[{r['label']}] RESULTS.md {r['program']}: {clean(r['text'], 150)} (line {r['line']}; listed as verified)"


def node_label(r):
    w = str(r.get("word") or "")
    return w if r.get("kind") == "level" and w in ("tested", "open") else "open"


def fmt_node(r):
    k = r.get("kind")
    if k == "cell":
        what = f"cell {r.get('state')} on board {clean(r.get('board'), 30)} line {r.get('line')}" + (" (a board decision, not a result)" if r.get("state") == "DECIDED" else "")
    elif k == "level": what = f"level, as center.py records it"
    elif k == "fingerprint": what = "fingerprint (a sequence on record: data, not a claim)"
    else: what = f"{clean(k, 20)} node"
    return f"[{node_label(r)}] center {clean(k, 20)} {r.get('program')}/{r.get('id')}: {clean(r.get('text', ''), 130)} ({what})"


def m_label(m):
    """(label, note). The board finding wins (its own runner first). Off the board the module is open: a stated label is
    only reported in the note, never printed as the bracket label."""
    if m["board"]:
        f = m["board"][0]   # modules() puts the finding whose runner is this module first
        lab, note = f_label(f)
        return lab, f"board finding {f.get('id')}, {note}"
    if m["stated"] in HONEST:   # the author's word is reported, not adopted: off the board it is open
        return "open", f"its docstring states {m['stated']}; not on the board, no second seat, so not verified"
    return "open", "no label stated and no board finding"


def fmt_module(m):
    lab, note = m_label(m)
    return f"[{lab}] module {m['file']}: {clean(m['summary'], 130)} ({note})"


def fmt_row(r, kind):
    tags = ", ".join(t for t in r.get("tags") or []) or "none"
    if r.get("new_tags_proposed"): tags += "; new tag proposed, not adopted: " + ", ".join(r["new_tags_proposed"])
    return (f"[proposed] {kind} {group_of(r)}: {clean(r.get('name', ''), 100)} (row label: {r.get('label_word', 'unlabelled')}; "
            f"tags: {tags}; {clean(r.get('file', ''), 60)})")


def capped(lines, total=None):
    if len(lines) <= MAXROWS: return lines
    return lines[:MAXROWS] + [f"[open] ... and {len(lines) - MAXROWS} more not shown (narrow the query)"]


TAG_NOTE = "[proposed] the tag tables were written by an agent and are unreviewed; a tag is a proposal, not a check"


# ---------------------------------------------------------------- answers

def a_status(D):
    out = []
    if not D["findings"]: out.append("[open] no findings found (no findings.jsonl, no center/shards): no findings to count")
    by = {}
    for f in D["findings"]: by.setdefault(str(f.get("word") or "open"), []).append(f)
    for w in sorted(by):
        n, v = len(by[w]), sum(1 for f in by[w] if verified(f))
        out.append(f"[{w if w in HONEST else 'open'}] {n} findings recorded as {clean(w, 20)}, {v} verified")
    fr = {}
    for r in D["frames"]: fr.setdefault(str(r.get("label") or "open"), []).append(r)
    for w in sorted(fr):
        t = sum(1 for r in fr[w] if r.get("status") == "TRUE")
        out.append(f"[{frame_label(w)}] {len(fr[w])} frames labelled {clean(w, 20)} ({t} TRUE, {len(fr[w]) - t} OPEN)"
                   + (" (capped at checked-finite: a frame is a reading)" if w in FRAME_CAP else ""))
    if not D["frames"]: out.append("[open] no frames.jsonl found: no frames to count")
    rs = {}
    for r in D["results"]: rs[r["label"]] = rs.get(r["label"], 0) + 1
    for w in sorted(rs): out.append(f"[{w}] {rs[w]} RESULTS.md rows labelled {w}")
    nk = {}
    for r in D["nodes"]: nk[str(r.get("kind"))] = nk.get(str(r.get("kind")), 0) + 1
    if nk: out.append("[open] center nodes besides findings and frames: " + ", ".join(f"{n} {clean(k, 20)}" for k, n in sorted(nk.items())))
    if D["modules"]: out.append(f"[open] {len(D['modules'])} modules in core/ontology read by their docstring (each line of theirs carries its own label)")
    c, f = rows_of(D["culture"]), rows_of(D["formal"])
    out.append(f"[proposed] {len(c)} culture rows and {len(f)} formal rows carry structure tags; status: "
               f"{(D['culture'] or D['formal'] or {}).get('status', 'no tag files found')}")
    return out


def a_verified(D):
    fs = D["findings"]
    v = [f for f in fs if verified(f)]
    rest = {}
    for f in fs:
        if not verified(f):
            k = str(f.get("word") or "open") + (" with why_not" if f.get("word") in CHECKED else "")
            rest[k] = rest.get(k, 0) + 1
    if not fs: return ["[open] no findings found: nothing to count"]
    per = {}
    for f in v: per[f["word"]] = per.get(f["word"], 0) + 1
    return ([f"[{w}] {per[w]} verified findings recorded as {w}" for w in VERIFIED_WORDS if w in per]
            + [f"[open] {len(v)} of {len(fs)} results are verified in all (verified = no why_not, and a word RESULTS.md lists); "
               f"{len(fs) - len(v)} are not verified: " + ", ".join(f"{clean(k, 30)} {n}" for k, n in sorted(rest.items()))])


def frame_text(r): return " ".join(str(r.get(k, "")) for k in ("source", "reading", "claim"))


def a_frames(D, openonly, word):
    fr = [r for r in D["frames"] if not openonly or r.get("status") != "TRUE"]
    if word: fr = [r for r in fr if mentions(word, frame_text(r))]
    fr.sort(key=lambda r: (-float(r.get("score") or 0), str(r.get("source"))))
    what = ("open " if openonly else "") + "frames" + (f" about {word}" if word else "")
    if not fr: return [f"[open] no {what} found"]
    return [f"[open] {len(fr)} {what} (highest score first)"] + capped([fmt_frame(r) for r in fr])


def a_findings(D, onlyverified, word):
    fs = [f for f in D["findings"] if (not onlyverified or verified(f)) and (not word or mentions(word, f.get("text", "")))]
    fs.sort(key=lambda f: (not verified(f), str(f.get("program")), str(f.get("id"))))
    what = ("verified " if onlyverified else "") + "findings" + (f" about {word}" if word else "")
    if not fs: return [f"[open] no {what} found"]
    v = sum(1 for f in fs if verified(f))
    return [f"[open] {len(fs)} {what}: {v} verified, {len(fs) - v} not verified (verified ones first; each line has its own label)"] + capped([fmt_finding(f) for f in fs])


def a_about_verified(D, word):
    fs = [f for f in D["findings"] if verified(f) and mentions(word, f.get("text", ""))]
    rs = [r for r in D["results"] if mentions(word, r["text"])]
    if not fs and not rs: return [f"[open] nothing verified mentions {clean(word)} (verified = no why_not, as in RESULTS.md; frames and tags are not counted)"]
    return ([f"[open] {len(fs)} verified findings and {len(rs)} RESULTS.md rows mention {clean(word)} (frames and tags are not counted as verified)"]
            + capped([fmt_finding(f) for f in fs]) + capped([fmt_result(r) for r in rs]))


def a_about_open(D, word):
    fr = sorted([r for r in D["frames"] if r.get("status") != "TRUE" and mentions(word, frame_text(r))], key=lambda r: -float(r.get("score") or 0))
    fs = [f for f in D["findings"] if not verified(f) and mentions(word, f.get("text", ""))]
    ns = [r for r in D["nodes"] if node_label(r) == "open" and r.get("kind") != "fingerprint" and r.get("state") != "DECIDED" and mentions(word, r.get("text", ""))]
    ms = [m for m in D["modules"] if m_label(m)[0] == "open" and mentions(word, m["doc"])]
    rows = [(r, k) for d, k in ((D["culture"], "work"), (D["formal"], "result")) for r in rows_of(d)
            if r.get("label_word") == "open" and mentions(word, " ".join(str(r.get(x) or "") for x in ("name", "reading")))]
    if not (fr or fs or ns or ms or rows): return [f"[open] nothing open on record mentions {clean(word)}"]
    return ([f"[open] about {clean(word)}: {len(fr)} open frames, {len(fs)} unverified findings, {len(ns)} open center nodes, "
             f"{len(ms)} open modules, {len(rows)} tag rows labelled open"]
            + capped([fmt_frame(r) for r in fr]) + capped([fmt_finding(f) for f in fs]) + capped([fmt_node(r) for r in ns])
            + capped([fmt_module(m) for m in ms]) + capped([fmt_row(r, k) for r, k in rows]))


def rows_about(D, word):
    """Tag rows a word points at: its corpus or pillar, a tag of that name, or the row's own text."""
    out = []
    for d, k in ((D["culture"], "work"), (D["formal"], "result")):
        for r in rows_of(d):
            if (group_of(r).lower() == word or word in [x.lower() for x in row_tags(r)]
                    or mentions(word, " ".join(str(r.get(x) or "") for x in ("name", "reading")))): out.append((r, k))
    return out


def a_connects(D, a, b):
    out = []
    ra, rb = rows_about(D, a), rows_about(D, b)
    ta = {t.lower(): t for r, _ in ra for t in row_tags(r)}; tb = {t.lower(): t for r, _ in rb for t in row_tags(r)}
    shared = sorted(set(ta) & set(tb))
    if shared:
        out.append(f"[proposed] shared tags ({len(shared)}): {', '.join(ta[t] for t in shared)} (tags are proposed and unreviewed; a shared tag is not a check)")
        for t in shared[:4]:
            x = [(r, k) for r, k in ra if t in [y.lower() for y in row_tags(r)]][:1]; y = [(r, k) for r, k in rb if t in [z.lower() for z in row_tags(r)]][:1]
            out += [fmt_row(r, k) for r, k in x + y if (r, k)]
        if len(shared) > 4: out.append(f"[open] ... rows for {len(shared) - 4} more shared tags not shown")
    else: out.append(f"[open] no shared tag: {len(ra)} tag rows point at {clean(a)}, {len(rb)} at {clean(b)}")
    both = lambda s: mentions(a, s) and mentions(b, s)
    fs = [f for f in D["findings"] if both(f.get("text", ""))]
    fs.sort(key=lambda f: (not verified(f), str(f.get("id"))))
    rs = [r for r in D["results"] if both(r["text"])]
    fr = [r for r in D["frames"] if both(frame_text(r))]
    ns = [r for r in D["nodes"] if both(r.get("text", ""))]
    ms = [m for m in D["modules"] if both(m["doc"])]
    out.append(f"[open] text that mentions both {clean(a)} and {clean(b)}: {len(fs)} findings, {len(rs)} RESULTS.md rows, {len(fr)} frames, "
               f"{len(ns)} center nodes, {len(ms)} in-between modules (matched as text; nothing inferred)")
    out += capped([fmt_module(m) for m in ms]) + capped([fmt_finding(f) for f in fs]) + capped([fmt_result(r) for r in rs])
    out += capped([fmt_frame(r) for r in fr]) + capped([fmt_node(r) for r in ns])
    return out


def known_tags(D):
    t = {}
    for d in (D["culture"], D["formal"]):
        for r in rows_of(d):
            for x in row_tags(r): t.setdefault(x.lower(), x)
    return t


def unknown_tag(D, tag):
    near = difflib.get_close_matches(tag, list(known_tags(D)), n=3, cutoff=0.6)
    return [f"[open] no tag named {clean(tag)} in the tag tables" + (f"; closest: {', '.join(near)}" if near else "")]


def a_use(D, tag, which):
    d = D["formal" if which == "formal" else "culture"]
    if d is None: return [f"[open] tag file for {which} rows not found"]
    kt = known_tags(D)
    if tag not in kt: return unknown_tag(D, tag)
    rows = [r for r in rows_of(d) if tag in [x.lower() for x in row_tags(r)]]
    kind = "result" if which == "formal" else "work"
    head = f"[proposed] {len(rows)} {kind} rows carry the tag {kt[tag]} (tag proposed, unreviewed)"
    return [head] + capped([fmt_row(r, kind) for r in rows]) if rows else [f"[open] no {which} rows carry the tag {kt[tag]}"]


def a_links(D, corpus, pillar):
    c, f = rows_of(D["culture"]), rows_of(D["formal"])
    corpora = sorted({group_of(r) for r in c}); pillars = sorted({group_of(r) for r in f})
    low = lambda L: {x.lower(): x for x in L}
    if corpus not in low(corpora):
        near = difflib.get_close_matches(corpus, list(low(corpora)), n=3, cutoff=0.6)
        return [f"[open] no culture corpus named {clean(corpus)}; known: {', '.join(corpora) or 'none'}" + (f"; closest: {', '.join(near)}" if near else "")]
    if pillar not in low(pillars):
        near = difflib.get_close_matches(pillar, list(low(pillars)), n=3, cutoff=0.6)
        return [f"[open] no formal pillar named {clean(pillar)}; known: {', '.join(pillars) or 'none'}" + (f"; closest: {', '.join(near)}" if near else "")]
    C, P = low(corpora)[corpus], low(pillars)[pillar]
    cr = [r for r in c if group_of(r) == C]; pr = [r for r in f if group_of(r) == P]
    ct = {t.lower(): t for r in cr for t in row_tags(r)}; pt = {t.lower(): t for r in pr for t in row_tags(r)}
    shared = sorted(set(ct) & set(pt))
    if not shared: return [f"[open] {C} and {P} share no tag in the tag tables (proposed, unreviewed)"]
    out = [f"[proposed] {C} and {P} share {len(shared)} tags: {', '.join(ct[t] for t in shared)} (a shared tag is a proposed link, not a check)"]
    for t in shared:
        a = [r for r in cr if t in [x.lower() for x in row_tags(r)]]; b = [r for r in pr if t in [x.lower() for x in row_tags(r)]]
        out.append(f"[proposed] tag {ct[t]}: {len(a)} {C} rows, {len(b)} {P} rows")
        out += [fmt_row(r, "work") for r in a[:2]] + [fmt_row(r, "result") for r in b[:2]]
        if len(a) > 2 or len(b) > 2: out.append(f"[open] ... {max(0, len(a) - 2) + max(0, len(b) - 2)} more rows under {ct[t]} not shown")
    return out


def a_list(D, what):
    c, f = rows_of(D["culture"]), rows_of(D["formal"])
    if what == "tags":
        cnt = {}
        for kind, rows in (("culture", c), ("formal", f)):
            for r in rows:
                for t in row_tags(r): cnt.setdefault(t, {"culture": 0, "formal": 0})[kind] += 1
        if not cnt: return ["[open] no tag files found"]
        new = {t for r in c + f for t in r.get("new_tags_proposed") or []}
        out = [f"[proposed] {len(cnt)} tags (unreviewed); {len(new)} of them are new tags proposed and not adopted"]
        return out + [f"[proposed] {t}: {n['culture']} culture rows, {n['formal']} formal rows" + (" (new tag, not adopted)" if t in new else "") for t, n in sorted(cnt.items())]
    rows, key = (c, "corpora") if what == "corpora" else (f, "pillars")
    cnt = {}
    for r in rows: cnt[group_of(r)] = cnt.get(group_of(r), 0) + 1
    if not cnt: return [f"[open] no {key} found in the tag files"]
    return [f"[proposed] {len(cnt)} {key} in the tag tables (unreviewed)"] + [f"[proposed] {g}: {n} rows" for g, n in sorted(cnt.items())]


def doc_definition(root, tag):
    """A definition of tag from the ontology docs: a line that starts with the tag followed by ':' or '=' (markdown marks ignored)."""
    for p in sorted(glob.glob(os.path.join(root, "core", "ontology", "*.md"))):
        try: lines = open(p, encoding="utf-8", errors="replace").read(MAXREAD).splitlines()
        except OSError: continue
        for i, l in enumerate(lines, 1):
            s = l.strip().lstrip("-* ").replace("*", "").replace("`", "").strip()
            if re.match(re.escape(tag) + r"\s*[:=]", s.lower()):
                return clean(s, 200), f"{os.path.relpath(p, root)} line {i}"
    return None


def a_what_is(D, root, tag):
    kt = known_tags(D)
    if tag not in kt: return unknown_tag(D, tag)
    name = kt[tag]; out = []
    dd = doc_definition(root, tag)
    if dd: out.append(f"[proposed] {name}: {dd[0]} (from {dd[1]})")
    else:
        for d in (D["culture"], D["formal"]):
            for v in ((d or {}).get("proposed_vocabulary") or {}).get("tags", []):
                if str(v.get("tag", "")).lower() == tag:
                    out.append(f"[proposed] {name}: {clean(v.get('definition'), 200)} (new tag proposed, not adopted)"); break
            if out: break
    if not out: out.append(f"[open] {name}: no definition on record in core/ontology docs; the rows that use it follow")
    c = [r for r in rows_of(D["culture"]) if tag in [x.lower() for x in row_tags(r)]]
    f = [r for r in rows_of(D["formal"]) if tag in [x.lower() for x in row_tags(r)]]
    out.append(f"[proposed] {name} is on {len(c)} culture rows and {len(f)} formal rows (unreviewed)")
    return out + capped([fmt_row(r, "work") for r in c][:6] + [fmt_row(r, "result") for r in f][:6])


def a_explain(D, word):
    fs = [f for f in D["findings"] if mentions(word, f.get("text", ""))]
    fr = [r for r in D["frames"] if mentions(word, frame_text(r))]
    rs = [r for r in D["results"] if mentions(word, r["text"])]
    ns = [r for r in D["nodes"] if mentions(word, r.get("text", ""))]
    ms = [m for m in D["modules"] if mentions(word, m["doc"])]
    rows = [(r, k) for d, k in ((D["culture"], "work"), (D["formal"], "result")) for r in rows_of(d)
            if mentions(word, " ".join(str(r.get(x) or "") for x in ("name", "reading")))]
    if not (fs or fr or rs or ns or ms or rows): return [f"[open] nothing on record mentions {clean(word)}"]
    out = [f"[open] {len(fs)} findings and {len(fr)} frames mention {clean(word)}; also {len(rs)} RESULTS.md rows, {len(ns)} center nodes, "
           f"{len(ms)} modules, {len(rows)} tag rows (matched as text; nothing inferred)"]
    return (out + capped([fmt_finding(f) for f in fs]) + capped([fmt_frame(r) for r in fr]) + capped([fmt_result(r) for r in rs])
            + capped([fmt_node(r) for r in ns]) + capped([fmt_module(m) for m in ms]) + capped([fmt_row(r, k) for r, k in rows]))


def run(kind, args, root):
    D = load(root)
    if kind == "status": return a_status(D)
    if kind == "verified": return a_verified(D)
    if kind in ("frames", "frames_open"): return a_frames(D, kind == "frames_open", args[0])
    if kind in ("findings", "findings_verified"): return a_findings(D, kind == "findings_verified", args[0])
    if kind == "about_verified": return a_about_verified(D, args[0])
    if kind == "about_open": return a_about_open(D, args[0])
    if kind == "connects": return a_connects(D, *args)
    if kind == "results_use": return a_use(D, args[0], "formal")
    if kind == "works_use": return a_use(D, args[0], "culture")
    if kind == "links": return a_links(D, *args)
    if kind.startswith("list_"): return a_list(D, kind[5:])
    if kind == "what_is": return a_what_is(D, root, args[0])
    if kind == "explain": return a_explain(D, args[0])
    raise ValueError(kind)


def suggestions(q, root):
    D = load(root)
    pool = list(EXAMPLES)
    for t in known_tags(D).values(): pool += [f"which results use {t.lower()}", f"which works use {t.lower()}", f"what is {t.lower()}"]
    cs = sorted({group_of(r).lower() for r in rows_of(D["culture"])}); ps = sorted({group_of(r).lower() for r in rows_of(D["formal"])})
    pool += [f"what links {c} and {p}" for c in cs for p in ps]
    t = tokens(q) if isinstance(q, str) else None
    return difflib.get_close_matches(" ".join(t or []), pool, n=1, cutoff=0.5)


def answer(q, root=None):
    """(exit code, text). 0 answered; 2 did not understand. Never writes a file, never runs anything from q."""
    root = get_root(root)
    p = parse(q)
    if p is None:
        near = suggestions(q, root) if isinstance(q, str) and len(q) <= MAXQ else []
        why = " (too long)" if isinstance(q, str) and len(q) > MAXQ else ""
        return 2, "\n".join([f"did not understand: {clean(q)}{why}", GRAMMAR,
                             "closest match: " + near[0] if near else "closest match: none"])
    return 0, "\n".join(run(p[0], p[1], root))


# ---------------------------------------------------------------- stage 2: a model proposes one query line, the parser decides

def build_prompt(root):
    D = load(root)
    cs = sorted({group_of(r).lower() for r in rows_of(D["culture"])}); ps = sorted({group_of(r).lower() for r in rows_of(D["formal"])})
    system = ("You turn a loose question into exactly ONE query line in a fixed grammar. Output only that line: no prose, no quotes, "
              "no explanation. Never answer the question.\n" + GRAMMAR + "\n"
              f"corpora: {', '.join(cs)}\npillars: {', '.join(ps)}\ntags: {', '.join(sorted(known_tags(D)))}\n"
              "Examples:\n"
              "Q: how many of our results are really checked?\nQuery: how many results are verified\n"
              "Q: what frames are still unproved about time?\nQuery: show open frames about time\n"
              "Q: which results are about exhaustive search?\nQuery: which results use exhaustive-check\n"
              "Q: how connected are carseat and math?\nQuery: what links carseat and math\n"
              "Q: what does fixed-point mean?\nQuery: what is fixed-point\n"
              "Q: tell me about asymmetry\nQuery: explain asymmetry\n"
              "Q: what have we actually proved about time?\nQuery: what is verified about time\n"
              "Q: what is still unsettled about language?\nQuery: what is open about language\n"
              "Q: is there anything tying beauvoir to time?\nQuery: what connects beauvoir and time\n"
              "Q: list the findings on routing\nQuery: show findings about routing\n")
    return system


def _python():
    for py in (os.environ.get("ASK_QWEN_PYTHON"), os.environ.get("ASTEROID_QWEN_PYTHON"), os.path.join(DEFAULT_ROOT, ".venv", "bin", "python"), sys.executable):
        if py and os.path.exists(py):
            try:
                if subprocess.run([py, "-c", "import transformers, torch"], capture_output=True, timeout=120).returncode == 0: return py
            except (OSError, subprocess.TimeoutExpired): pass
    return None


class ModelMissing(Exception): pass


def model_generate(system, user, model=MODEL_NAME):
    """Ask the local model once (greedy, chat template, 40 new tokens). Raises ModelMissing with a plain reason. Tests replace this."""
    py = _python()
    if not py: raise ModelMissing("no python with transformers and torch (set ASK_QWEN_PYTHON)")
    env = dict(os.environ, HF_HUB_OFFLINE="1")
    job = json.dumps({"model": model, "system": system, "user": user})
    try: r = subprocess.run([py, "-I", os.path.abspath(__file__), "--worker"], input=job, capture_output=True, text=True, env=env, timeout=900)
    except subprocess.TimeoutExpired: raise ModelMissing("the model timed out after 900 s")
    if r.returncode != 0: raise ModelMissing(f"the model did not run (exit {r.returncode}): " + (r.stderr.strip().splitlines() or ["no message"])[-1][:200])
    return r.stdout


def _worker():
    job = json.loads(sys.stdin.read())
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    torch.manual_seed(0); torch.set_num_threads(max(1, (os.cpu_count() or 2) // 2))
    tok = AutoTokenizer.from_pretrained(job["model"]); m = AutoModelForCausalLM.from_pretrained(job["model"], torch_dtype=torch.float32).eval()
    text = tok.apply_chat_template([{"role": "system", "content": job["system"]}, {"role": "user", "content": job["user"]}], tokenize=False, add_generation_prompt=True)
    ids = tok(text, return_tensors="pt")
    with torch.no_grad(): out = m.generate(**ids, max_new_tokens=40, do_sample=False)
    sys.stdout.write(tok.decode(out[0][ids["input_ids"].shape[1]:], skip_special_tokens=True))


def cache_path():
    return os.environ.get("ASK_CACHE") or os.path.join(HERE, ".ask_cache.json")


def first_line(text):
    for l in str(text).splitlines():
        l = re.sub(r"^\s*(?:Query:|A:)\s*", "", l.strip().strip("`")).strip()
        if l: return l
    return ""


def propose(question, root=None, generator=None, cache=None):
    """Ask the generator for one query line. Returns the raw first line. The generator may raise ModelMissing.
    cache: a path to a JSON cache keyed by prompt hash, or None for no cache (the only file this module ever writes)."""
    root = get_root(root)
    system = build_prompt(root); user = "Q: " + question
    key = hashlib.sha256(json.dumps([MODEL_NAME, system, user]).encode("utf-8")).hexdigest()
    c = {}
    if cache:
        try: c = json.load(open(cache, encoding="utf-8"))
        except (OSError, ValueError): c = {}
        if not isinstance(c, dict): c = {}
        if key in c: return first_line(c[key])
    raw = (generator or model_generate)(system, user)
    if cache:
        c[key] = raw
        try:
            tmp = cache + ".tmp"
            with open(tmp, "w", encoding="utf-8") as fh: json.dump(c, fh, indent=1, sort_keys=True)
            os.replace(tmp, cache)
        except OSError: pass
    return first_line(raw)


def answer_model(question, root=None, generator=None, cache=None):
    """(exit code, text). The model's line is validated by parse(); only a parsed line is answered, from data."""
    root = get_root(root)
    if not isinstance(question, str) or not question.strip() or len(question) > MAXQ:
        return 2, "\n".join(["did not understand: the question is empty or longer than %d characters" % MAXQ, GRAMMAR])
    try: line = propose(question, root, generator, cache)
    except ModelMissing as e:
        return 3, f"[open] the model is not available: {clean(e, 200)}\nnothing was asked; use a plain query instead (see --help)"
    p = parse(line)
    if p is None:
        return 2, "\n".join([f"[proposed] model proposed: {clean(line, 120)}",
                             "[open] that line is not in the grammar, so it was not run; the interface does not guess", GRAMMAR])
    canon = " ".join(tokens(line))
    return 0, "\n".join([f"[proposed] model proposed: {canon} (a proposal; the parser accepted it, the answer below comes from data)"] + run(p[0], p[1], root))


def main(argv):
    if argv[:1] == ["--worker"]: return _worker() or 0
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__.split("\n\n")[0] + "\n\n" + GRAMMAR + "\n  --model \"loose question\"   a local model proposes one line above; the parser decides"); return 0 if argv else 2
    if argv[0] == "--model":
        code, text = answer_model(" ".join(argv[1:]), cache=cache_path())
    else:
        code, text = answer(" ".join(argv))
    print(text); return code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
