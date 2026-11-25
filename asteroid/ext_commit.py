"""asteroid extension: commit. At the end of a run, git commit exactly the files this run wrote.
  commit ["MESSAGE"] [push]
It acts after all claims and records. If a claim is FALSE or the run fails, it commits nothing.
It stages only the findings.jsonl files records were added to, the frames file if a frame changed it,
and boards/TREE.md and boards/tree.json if boards.build ran. Never `git add -A`.
Author and committer: asteroid <asteroid@users.noreply.github.com>, set for this command only.
`push` runs `git push origin HEAD:main` after a commit. A failed push leaves the commit in place.
See asteroid/COMMIT.md."""
import os, re, subprocess, sys
import asteroid.asteroid as A

NAME, EMAIL = "asteroid", "asteroid@users.noreply.github.com"
PUSH_TIMEOUT = 120
PAT = re.compile(r'commit(?: "([^"]+)")?( push)?')
STATE = {"want": None, "records": [], "before": {}, "after": {}, "build": False, "frames": set(), "failed": False, "done": False, "script": None}

def _install():
    """Wrap the writers once, so this module learns exactly which files the run wrote."""
    import boards
    if getattr(boards.add, "_commit", False): return
    add, build = boards.add, boards.build
    def add2(d, who, serves, word, statement, *a, **k):
        f = _rel(os.path.join(d, "findings.jsonl"))
        if f not in STATE["before"]: STATE["before"][f] = _read(f)
        r = add(d, who, serves, word, statement, *a, **k); STATE["records"].append((d, word, statement))
        STATE["after"][f] = _read(f); return r
    def build2(*a, **k):
        r = build(*a, **k); STATE["build"] = True; return r
    add2._commit = True; boards.add, boards.build = add2, build2
    try:
        from asteroid import ext_frame as Fr
        w = Fr.write
        def write2(rec):
            r = w(rec)
            if r != "kept": STATE["frames"].add(Fr.frames_path())
            return r
        Fr.write = write2
    except ImportError: pass
_install()

def _git(args, **k):
    env = dict(os.environ, GIT_AUTHOR_NAME=NAME, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_NAME=NAME, GIT_COMMITTER_EMAIL=EMAIL)
    return subprocess.run(["git", "-c", f"user.name={NAME}", "-c", f"user.email={EMAIL}"] + args, cwd=A.ROOT,
                          capture_output=True, text=True, encoding="utf-8", errors="replace", env=env, **k)

def _rel(p):
    return os.path.relpath(os.path.abspath(os.path.join(A.ROOT, p)), A.ROOT).replace(os.sep, "/")

def _read(rel):
    try:
        with open(os.path.join(A.ROOT, rel), "rb") as f: return f.read()
    except FileNotFoundError: return b""

def _head(rel):
    r = subprocess.run(["git", "show", f"HEAD:{rel}"], cwd=A.ROOT, capture_output=True)
    return r.stdout if r.returncode == 0 else b""

def message(prog, results, records, msg=None):
    good = [r for r in results if r[2]]
    lines = [msg or f"asteroid: {prog}: {len(good)} claims true", ""]
    lines += [f"TRUE {r[1]}" for r in good]
    lines += [f"record {d} {w} {s[:80]}" for d, w, s in records]
    return "\n".join(lines + ["", f"Run-by: bin/asteroid {prog}"])

def finish(mod, say):
    """Called once, when the run prints its final `claims:` line."""
    S = STATE; S["done"] = True
    msg, push = S["want"]
    if S["failed"] or any(not r[2] for r in mod.results):
        say("commit skipped: a claim failed"); return
    if _git(["rev-parse", "-q", "--verify", "MERGE_HEAD"]).returncode == 0:
        say("commit refused: a merge is in progress"); return
    if _git(["symbolic-ref", "-q", "HEAD"]).returncode != 0:
        say("commit refused: HEAD is detached"); return
    for f in S["before"]:
        if S["before"][f] != _head(f):
            say(f"commit refused: {f} had changes not yet committed before this run"); return
        if _read(f) != S["after"].get(f):
            say(f"commit refused: {f} changed after this run wrote it"); return
    paths = [_rel(os.path.join(d, "findings.jsonl")) for d, _, _ in S["records"]]
    paths += [_rel(p) for p in sorted(S["frames"])]
    if S["build"]: paths += ["boards/TREE.md", "boards/tree.json"]
    paths = [p for p in dict.fromkeys(paths) if os.path.exists(os.path.join(A.ROOT, p))]
    for p in paths:
        r = _git(["add", "--", p])
        if r.returncode: say(f"commit failed: git add {p}: {r.stderr.strip()}"); return
    if not paths or _git(["diff", "--cached", "--quiet", "HEAD", "--"] + paths).returncode == 0:
        say("commit skipped: nothing new"); return
    prog = _rel(S["script"])
    r = _git(["commit", "--only", "-m", message(prog, mod.results, S["records"], msg), "--"] + paths)
    if r.returncode: say(f"commit failed: {(r.stderr or r.stdout).strip()}"); return
    h = _git(["rev-parse", "--short", "HEAD"]).stdout.strip()
    say(f"committed {h}: {', '.join(paths)}")
    if push:
        try: r = _git(["push", "origin", "HEAD:main"], timeout=PUSH_TIMEOUT)
        except subprocess.TimeoutExpired: say(f"push failed: timed out after {PUSH_TIMEOUT} s; the commit stays"); return
        say("pushed to origin main" if r.returncode == 0 else f"push failed: {r.stderr.strip()}; the commit stays")

def handle(line, api):
    if not (line == "commit" or line.startswith("commit ")): return False
    m = PAT.fullmatch(line)
    if not m: raise SystemExit(f'{api["script"]}:{api["ln"]}: commit ["MESSAGE"] [push]')
    if STATE["want"] is not None: raise SystemExit(f'{api["script"]}:{api["ln"]}: only one commit line per program')
    STATE["want"] = (m.group(1), bool(m.group(2))); STATE["script"] = api["script"]
    # the running module may be __main__ (asteroid.py run as a script), not asteroid.asteroid
    mod = next((x for x in list(sys.modules.values()) if getattr(x, "API", None) is api), A)
    say = mod.say
    def say2(text=""):
        t = str(text)
        if t.startswith("NOT PROVED"): STATE["failed"] = True
        say(text)
        if t.startswith("claims: ") and not STATE["done"]: finish(mod, say)
    mod.say = say2
    say(f'{api["ln"]}: commit at the end of the run' + (" and push" if m.group(2) else ""))
    return True
