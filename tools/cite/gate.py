"""The citation gate: refuses added claims that cite nothing, and citations that are dead.

  python3 -I tools/cite/gate.py --staged          what `git commit` is about to record (the pre-commit hook)
  python3 -I tools/cite/gate.py --range A..B      the commits A..B (CI: the pushed range)
  python3 -I tools/cite/gate.py --all             audit: every claim of the tree (old ones too); prints counts

What counts as a claim (only lines ADDED in the diff are forced; --all reports every line):
  .ath     a line starting with claim, claim!, check, prove or record. It needs a `cite KEY ...` line
           below it, before the next claim line.
  .md      a line with a result tag: [PROVED] [TESTED ...] [DATA] [DEAD] [LEAN] [REFUTED] [CHECKED].
           It needs a `cite:KEY` token on the same line.
  .lean    a `theorem` or `lemma` declaration. It needs a `cite:KEY` token on its line, in the
           8 lines above it (its docstring or comment), or in the first 40 lines of the file (covers the whole file).
Every `cite:KEY` token and every `cite` line on an added line must be ALIVE (tools/cite/cite.py).

Limits (hard; past one the gate FAILS, it never passes by default): at most 200000 added lines and
4000 changed files per run, plus the resolver's limits. Exit 0: all forced claims cited and alive. Exit 1 otherwise.
"""
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cite as C

MAX_ADDED, MAX_FILES = 200000, 4000
MD_TAG = re.compile(r'\[(PROVED|TESTED[^\]]*|DATA|DEAD|LEAN|REFUTED|CHECKED)\]')
LEAN_DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+\S')
LEAN_WINDOW = 8
LEAN_HEADER = 40
SKIP = ("LITERATURE.md", "NAMES.md")     # the index itself, and a generated file

def git(*args, check=True):
    r = subprocess.run(["git", "-C", C.ROOT, *args], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=C.GIT_TIMEOUT)
    if check and r.returncode != 0: raise SystemExit(f"gate: git {' '.join(args)} failed: {r.stderr.strip()[:200]}")
    return r.stdout

def added_lines(diff_args):
    """{path: set of added line numbers in the new version}."""
    out, path, ln = {}, None, 0
    for line in git("diff", "--no-color", "-U0", "--diff-filter=AM", *diff_args).splitlines():
        if line.startswith("+++ "):
            path = line[6:] if line.startswith("+++ b/") else None
        elif line.startswith("@@") and path:
            m = re.search(r'\+(\d+)(?:,(\d+))?', line); ln = int(m.group(1))
        elif line.startswith("+") and not line.startswith("+++") and path:
            out.setdefault(path, set()).add(ln); ln += 1
    return out

def content(rev, path):
    if rev == "WORKTREE": return open(os.path.join(C.ROOT, path), encoding="utf-8", errors="replace").read()
    return git("show", f"{rev}:{path}")

def check_file(path, text, lines, report):
    """lines: added line numbers to force, or None for all. Appends (path, ln, why) failures to report."""
    rows = text.splitlines()
    want = (lambda i: True) if lines is None else (lambda i: i in lines)
    if path.endswith(".ath"):
        uncited = set()
        pending = None
        for i, raw in enumerate(rows, 1):
            body = raw.split("#", 1)[0]
            if C.CLAIM_RE.match(body):
                if pending is not None: uncited.add(pending)
                pending = i
            elif m := C.CITE_LINE_RE.match(body):
                pending = None
                if want(i):
                    keys = C.parse_keys(m.group(1))
                    if not keys: report.append((path, i, "cite line with no KEY"))
                    for k, v in keys:
                        ok, why = C.resolve(k, v)
                        if not ok: report.append((path, i, f"dead citation {k}:{v} ({why})"))
        if pending is not None: uncited.add(pending)
        for i in sorted(uncited):
            if want(i): report.append((path, i, "claim with no cite line below it"))
        return
    if path.endswith(".md"):
        if os.path.basename(path) in SKIP: return
        for i, raw in enumerate(rows, 1):
            if not want(i): continue
            toks = C.tokens(raw)
            if MD_TAG.search(raw) and not toks: report.append((path, i, "result tag with no cite:KEY on the line"))
            for k, v in toks:
                ok, why = C.resolve(k, v)
                if not ok: report.append((path, i, f"dead citation {k}:{v} ({why})"))
        return
    if path.endswith(".lean"):
        header = any(C.tokens(w) for w in rows[:LEAN_HEADER])   # one cite in the module header covers every theorem of the file
        for i, raw in enumerate(rows, 1):
            if not want(i): continue
            for k, v in C.tokens(raw):
                ok, why = C.resolve(k, v)
                if not ok: report.append((path, i, f"dead citation {k}:{v} ({why})"))
            if LEAN_DECL.match(raw):
                window = rows[max(0, i - 1 - LEAN_WINDOW):i]
                if not header and not any(C.tokens(w) for w in window): report.append((path, i, f"theorem with no cite:KEY on its line or the {LEAN_WINDOW} lines above"))

def main(argv):
    report = []
    if argv[:1] == ["--all"]:
        files = [f for f in git("ls-files").splitlines() if f.endswith((".ath", ".md", ".lean"))]
        for f in files:
            try: check_file(f, content("WORKTREE", f), None, report)
            except (OSError, UnicodeError): pass
        by = {}
        for p, i, why in report: by[why.split(" (")[0].split(":")[0]] = by.get(why.split(" (")[0].split(":")[0], 0) + 1
        print(f"gate --all: {len(files)} files, {len(report)} uncited or dead claim lines (old lines are not forced; this is an audit)")
        for k, n in sorted(by.items(), key=lambda x: -x[1]): print(f"  {n:6d}  {k}")
        return 0
    if argv[:1] == ["--staged"]: diff_args, rev = ["--cached"], ""
    elif argv[:1] == ["--range"] and len(argv) == 2:
        a, b = argv[1].split("..", 1)
        if not a or set(a) == {"0"}: a = git("hash-object", "-t", "tree", "/dev/null").strip()   # first push: diff against the empty tree
        diff_args, rev = [a, b], b
    else:
        print(__doc__); return 2
    added = added_lines(diff_args)
    if len(added) > MAX_FILES: print(f"gate: FAIL: {len(added)} changed files (limit {MAX_FILES}); split the change"); return 1
    if sum(len(v) for v in added.values()) > MAX_ADDED: print(f"gate: FAIL: more than {MAX_ADDED} added lines; split the change"); return 1
    for path, lines in sorted(added.items()):
        if not path.endswith((".ath", ".md", ".lean")): continue
        check_file(path, content(rev, path) if rev else git("show", f":{path}"), lines, report)
    for p, i, why in report: print(f"{p}:{i}: {why}")
    n = sum(1 for p in added if p.endswith((".ath", ".md", ".lean")))
    print(f"gate: {'FAIL' if report else 'PASS'}: {n} files checked, {len(report)} problem(s)" + ("" if not report else
          "\n  fix: add `cite KEY` below each .ath claim, or a `cite:KEY` token on the tagged line / above the theorem."
          "\n  KEY = lit:\"TEXT\" | doi:X | arxiv:X | lean:NAME | file:PATH | commit:HASH | ath:PATH | original   (asteroid/CITE.md)"))
    return 1 if report else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
