#!/usr/bin/env python3
"""A controlled-English query interface to the repository's recorded results. Read-only. Standard library only.

  python3 -I core/ontology/ask.py show open frames about time
  python3 -I core/ontology/ask.py --model "what do we have that is open about time"

It answers from data. It does not infer, and it never executes anything it is given. The query is matched
against a fixed grammar (GRAMMAR below); a WORD or TAG is compared as data only (no regex is built from it,
no path is taken from it, no shell is involved). Every answer line starts with its label in brackets:
checked, checked-finite, tested, refuted, analogy, open, proposed (or the recorded word of a finding).

Data, all under ROOT (three dirnames up from this file, or $ASK_ROOT, or the root argument):
  center/shards/*.jsonl                   findings with their recorded word; verified = a checked word and no why_not
  frames.jsonl                            frames (asteroid `frame`): label, TRUE or OPEN
  core/ontology/tags/tags_culture.json    structure tags on culture works: PROPOSED, UNREVIEWED
  core/ontology/tags/tags_formal.json     structure tags on formal results: PROPOSED, UNREVIEWED

A row from a tag table always prints as [proposed]: the tag is a proposal. The row's own label is shown
beside it as "row label", and is never promoted to the line's label.

Exit codes: 0 answered, 2 did not understand, 3 the model is missing (--model only).

--model (stage 2): a small local model is asked to write ONE query line in this grammar. The line is then
checked by the same parser. If it does not parse, the interface says so and shows the grammar; it never
guesses. The model never writes answer text. The only file this program ever writes is the model-output
cache core/ontology/.ask_cache.json, and only in --model mode (it is in .gitignore). A plain query writes nothing."""
import difflib, glob, hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MAXQ = 300            # longest query read, in characters
MAXROWS = 12          # rows shown per list; the rest is counted
CHECKED = ("checked", "checked-finite", "checked-infinite")
FILLER = {"the", "a", "an", "please", "kindly", "me", "us"}
WORD_RE = re.compile(r"[\w'-]+")                    # one token of letters, digits, _ ' - only: no shell or path characters
MODEL_NAME = "Qwen/Qwen2.5-0.5B-Instruct"

GRAMMAR = """Grammar (case does not matter; the, a, an, please are ignored):
  status
  how many results are verified
  show open frames [about WORD]
  show frames [about WORD]
  which results use TAG          formal results, by structure tag (tags are proposed)
  which works use TAG            culture works, by structure tag (tags are proposed)
  what links CORPUS and PILLAR   tags a culture corpus and a formal pillar share
  list tags | list corpora | list pillars
  what is TAG
  explain WORD                   findings and frames whose text mentions WORD"""

EXAMPLES = ["status", "how many results are verified", "show open frames", "show frames about time",
            "which results use exhaustive-check", "which works use branching-tree", "what links beauvoir and physics",
            "list tags", "list corpora", "list pillars", "what is fixed-point", "explain asymmetry"]


def get_root(root=None):
    return os.path.abspath(root or os.environ.get("ASK_ROOT") or DEFAULT_ROOT)


def clean(s, n=80):
    """Make user text safe to echo: printable characters only, short."""
    s = "".join(ch if ch.isprintable() else "?" for ch in str(s))
    return s if len(s) <= n else s[:n] + "..."


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
    for head, kind in ((["show", "open", "frames"], "frames_open"), (["show", "frames"], "frames")):
        if t[:len(head)] == head:
            rest = t[len(head):]
            if not rest: return (kind, (None,))
            if len(rest) == 2 and rest[0] == "about" and ok(rest[1]): return (kind, (rest[1],))
            return None
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


def verified(f):
    return f.get("word") in CHECKED and not f.get("why_not")


def load(root):
    shards = sorted(glob.glob(os.path.join(root, "center", "shards", "*.jsonl")))
    findings = [r for p in shards for r in _jsonl(p) if r.get("kind") == "finding"]
    findings.sort(key=lambda r: (str(r.get("program")), str(r.get("id"))))
    tdir = os.path.join(root, "core", "ontology", "tags")
    return {"shards": len(shards), "findings": findings, "frames": _jsonl(os.path.join(root, "frames.jsonl")),
            "culture": _json(os.path.join(tdir, "tags_culture.json")), "formal": _json(os.path.join(tdir, "tags_formal.json"))}


def rows_of(d):
    return [r for r in (d or {}).get("rows", []) if isinstance(r, dict)]


def row_tags(r):
    return [t for t in list(r.get("tags") or []) + list(r.get("new_tags_proposed") or [])]


def group_of(r):
    return str(r.get("corpus") or r.get("pillar") or "?")


# ---------------------------------------------------------------- one line per record, each with its label

def f_label(f):
    w = str(f.get("word") or "open")
    if w in CHECKED and f.get("why_not"): return "open", f"recorded as {w}, not verified: it has a why_not"
    if verified(f): return w, "verified"
    return w, "not verified"


def fmt_finding(f):
    lab, note = f_label(f)
    return f"[{lab}] finding {f.get('program')}/{f.get('id')}: {clean(f.get('text', ''), 150)} ({note})"


def fmt_frame(r):
    return (f"[{r.get('label', 'open')}] frame {r.get('status')}: {clean(r.get('source', ''), 70)} -> {clean(r.get('reading', ''), 90)} "
            f"(claim {clean(r.get('claim'), 40)}, score {r.get('score')})")


def fmt_row(r, kind):
    tags = ", ".join(t for t in r.get("tags") or []) or "none"
    if r.get("new_tags_proposed"): tags += "; new tag proposed, not adopted: " + ", ".join(r["new_tags_proposed"])
    return (f"[proposed] {kind} {group_of(r)}: {clean(r.get('name', ''), 100)} (row label: {r.get('label_word', 'unlabelled')}; "
            f"tags: {tags}; {clean(r.get('file', ''), 60)})")


def capped(lines, total=None):
    total = len(lines) if total is None else total
    if len(lines) <= MAXROWS: return lines
    return lines[:MAXROWS] + [f"[open] ... and {len(lines) - MAXROWS} more not shown (narrow the query)"]


TAG_NOTE = "[proposed] the tag tables were written by an agent and are unreviewed; a tag is a proposal, not a check"


# ---------------------------------------------------------------- answers

def a_status(D):
    out = []
    if not D["shards"]: out.append("[open] no center/shards found: no findings to count")
    by = {}
    for f in D["findings"]: by.setdefault(str(f.get("word") or "open"), []).append(f)
    for w in sorted(by):
        n, v = len(by[w]), sum(1 for f in by[w] if verified(f))
        out.append(f"[{w}] {n} findings recorded as {w}, {v} verified")
    fr = {}
    for r in D["frames"]: fr.setdefault(str(r.get("label") or "open"), []).append(r)
    for w in sorted(fr):
        t = sum(1 for r in fr[w] if r.get("status") == "TRUE")
        out.append(f"[{w}] {len(fr[w])} frames labelled {w} ({t} TRUE, {len(fr[w]) - t} OPEN)")
    if not D["frames"]: out.append("[open] no frames.jsonl found: no frames to count")
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
    return [f"[checked] {len(v)} of {len(fs)} results are verified (a checked word and no why_not)",
            f"[open] {len(fs) - len(v)} are not verified: " + ", ".join(f"{k} {n}" for k, n in sorted(rest.items()))]


def a_frames(D, openonly, word):
    fr = [r for r in D["frames"] if not openonly or r.get("status") != "TRUE"]
    if word: fr = [r for r in fr if word in " ".join(str(r.get(k, "")) for k in ("source", "reading", "claim")).lower()]
    fr.sort(key=lambda r: (-float(r.get("score") or 0), str(r.get("source"))))
    what = ("open " if openonly else "") + "frames" + (f" about {word}" if word else "")
    if not fr: return [f"[open] no {what} found"]
    return [f"[open] {len(fr)} {what} (highest score first)"] + capped([fmt_frame(r) for r in fr])


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
        out += [fmt_row(r, "work") for r in a[:3]] + [fmt_row(r, "result") for r in b[:3]]
        if len(a) > 3 or len(b) > 3: out.append(f"[open] ... {max(0, len(a) - 3) + max(0, len(b) - 3)} more rows under {ct[t]} not shown")
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
        try: lines = open(p, encoding="utf-8", errors="replace").read().splitlines()
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
    return out + capped([fmt_row(r, "work") for r in c][:6] + [fmt_row(r, "result") for r in f][:6], None)


def a_explain(D, word):
    fs = [f for f in D["findings"] if word in str(f.get("text", "")).lower()]
    fr = [r for r in D["frames"] if word in " ".join(str(r.get(k, "")) for k in ("source", "reading")).lower()]
    if not fs and not fr: return [f"[open] no finding or frame mentions {clean(word)}"]
    out = [f"[open] {len(fs)} findings and {len(fr)} frames mention {clean(word)} (matched as plain text; nothing inferred)"]
    return out + capped([fmt_finding(f) for f in fs]) + capped([fmt_frame(r) for r in fr])


def run(kind, args, root):
    D = load(root)
    if kind == "status": return a_status(D)
    if kind == "verified": return a_verified(D)
    if kind in ("frames", "frames_open"): return a_frames(D, kind == "frames_open", args[0])
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
              "Q: tell me about asymmetry\nQuery: explain asymmetry\n")
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
