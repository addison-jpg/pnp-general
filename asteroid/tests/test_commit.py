"""Test of asteroid/ext_commit.py in a TEMPORARY git repository (never the real one).
Run from the repository root:  python3 -I asteroid/tests/test_commit.py      (exit 1 on any FAIL)"""
import glob, os, shutil, subprocess, sys, tempfile
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASE = os.environ.get("ASTEROID_COMMIT_TEST_DIR") or "/tmp/claude-0/-home-user/c7c2895f-eb04-517d-b538-6d0d59d567a9/scratchpad/commit-test"
os.makedirs(BASE, exist_ok=True)
fails = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

def git(t, *a): return subprocess.run(["git", *a], cwd=t, capture_output=True, text=True).stdout.strip()

def make():
    t = tempfile.mkdtemp(prefix="asteroid_commit_", dir=BASE)
    os.makedirs(os.path.join(t, "asteroid")); os.makedirs(os.path.join(t, "one-not/tools"))
    for f in glob.glob(os.path.join(REPO, "asteroid", "*.py")): shutil.copy(f, os.path.join(t, "asteroid"))
    shutil.copy(os.path.join(REPO, "boards.py"), t)
    shutil.copytree(os.path.join(REPO, "one-not/tools/search"), os.path.join(t, "one-not/tools/search"),
                    ignore=shutil.ignore_patterns("__pycache__", "*.json*"))
    for f in glob.glob(os.path.join(REPO, "one-not/tools/search/*.py")): shutil.copy(f, os.path.join(t, "one-not/tools/search"))
    os.makedirs(os.path.join(t, "boards")); os.makedirs(os.path.join(t, "notes"))
    open(os.path.join(t, "notes/findings.jsonl"), "w").close()
    open(os.path.join(t, "other.txt"), "w").write("a\n")
    open(os.path.join(t, ".gitignore"), "w").write("__pycache__/\n")
    for c in (["init", "-q", "-b", "main"], ["add", "-A"],
              ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "init"]): git(t, *c)
    open(os.path.join(t, "other.txt"), "a").write("unrelated change\n")
    return t

def run(t, prog):
    p = os.path.join(t, "p.ath"); open(p, "w").write(prog)
    env = {k: v for k, v in os.environ.items() if not k.startswith(("ASTEROID_", "GIT_"))}
    env["PYTHONPATH"] = t
    r = subprocess.run([sys.executable, "-X", "utf8", os.path.join(t, "asteroid", "__main__.py"), "--no-lean", p],
                       cwd=t, capture_output=True, text=True, env=env, timeout=600)
    return r.stdout + r.stderr

GOOD = 'seq s = [1, 2, 3, 4, 5]\nclaim s = [1, 2, 3]\nrecord notes notes tested "s starts 1 2 3"\ncommit\n'
t = make()
try:
    out = run(t, GOOD); print(out.strip())
    head = git(t, "rev-parse", "HEAD~1") and git(t, "log", "-1", "--format=%an <%ae>|%cn <%ce>")
    files = git(t, "show", "--name-only", "--format=", "HEAD").split("\n")
    body = git(t, "log", "-1", "--format=%B")
    want("a passing program commits", "committed " in out and head)
    want("the commit holds the findings file", "notes/findings.jsonl" in files)
    want("the commit holds nothing but the findings file and the boards", set(files) <= {"notes/findings.jsonl", "boards/TREE.md", "boards/tree.json"})
    want("the unrelated change stays unstaged", "other.txt" in git(t, "diff", "--name-only") and "other.txt" not in git(t, "diff", "--cached", "--name-only"))
    want("author and committer are asteroid", head == "asteroid <asteroid@users.noreply.github.com>|asteroid <asteroid@users.noreply.github.com>")
    want("message names the program and counts the claims", body.startswith("asteroid: p.ath: 1 claims true"))
    want("message lists the claim and the record", "TRUE s = [1, 2, 3]" in body and "record notes tested s starts 1 2 3" in body)
    want("message has the trailer", "Run-by: bin/asteroid p.ath" in body)
    want("repo config is untouched", git(t, "config", "--local", "user.name") == "")

    n = git(t, "rev-list", "--count", "HEAD")
    out = run(t, GOOD); print(out.strip())
    want("nothing new: no commit", "commit skipped: nothing new" in out and git(t, "rev-list", "--count", "HEAD") == n)

    out = run(t, 'seq s = [1, 2, 3]\nclaim s = [1, 2, 4]\nrecord notes notes tested "never"\ncommit\n'); print(out.strip())
    want("a FALSE claim: no commit", "commit skipped: a claim failed" in out and git(t, "rev-list", "--count", "HEAD") == n)

    out = run(t, 'seq s = [1, 2, 3]\nclaim s = [1, 2]\nrecord notes notes tested "custom"\ncommit "my message"\n')
    want("MESSAGE replaces the first line", git(t, "log", "-1", "--format=%s") == "my message")

    git(t, "checkout", "-q", "--detach")
    out = run(t, 'seq s = [1, 2, 3]\nclaim s = [1, 2]\nrecord notes notes tested "detached"\ncommit\n')
    want("detached HEAD: refused", "commit refused: HEAD is detached" in out)
finally:
    shutil.rmtree(t, ignore_errors=True)

P = 'seq s = [1, 2, 3]\nclaim s = [1, 2]\nrecord notes notes tested "%s"\ncommit%s\n'
t = make()
try:
    n = git(t, "rev-list", "--count", "HEAD")
    open(os.path.join(t, "notes/findings.jsonl"), "a").write('{"id": "zz-other", "who": "someone", "serves": "notes", "word": "tested", "statement": "not from this run", "evidence": [], "by": []}\n')
    out = run(t, P % ("dirty", "")); print(out.strip())
    want("findings file already changed: refused", "commit refused: notes/findings.jsonl had changes" in out and git(t, "rev-list", "--count", "HEAD") == n)
    git(t, "checkout", "-q", "--", "notes/findings.jsonl")

    git(t, "stash", "-q"); git(t, "checkout", "-q", "-b", "side"); open(os.path.join(t, "m.txt"), "w").write("side\n")
    git(t, "add", "m.txt"); git(t, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "side")
    git(t, "checkout", "-q", "main"); open(os.path.join(t, "m.txt"), "w").write("main\n")
    git(t, "add", "m.txt"); git(t, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "main")
    git(t, "merge", "side")
    n = git(t, "rev-list", "--count", "HEAD")
    out = run(t, P % ("merge", ""))
    want("merge in progress: refused", "commit refused: a merge is in progress" in out and git(t, "rev-list", "--count", "HEAD") == n)
    git(t, "merge", "--abort"); git(t, "checkout", "-q", "--", ".")

    bare = t + "_remote.git"
    subprocess.run(["git", "init", "-q", "--bare", bare], capture_output=True)
    git(t, "remote", "add", "origin", bare)
    out = run(t, P % ("pushed", " push")); print(out.strip())
    want("push sends the commit to origin main", "pushed to origin main" in out
         and git(bare, "rev-parse", "main") == git(t, "rev-parse", "HEAD"))
finally:
    shutil.rmtree(bare if "bare" in dir() else t + "_none", ignore_errors=True)
    shutil.rmtree(t, ignore_errors=True)
print("FAIL" if fails else "PASS"); sys.exit(1 if fails else 0)
