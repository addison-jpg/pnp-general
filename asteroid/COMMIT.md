# commit

    commit ["MESSAGE"] [push]

A program may end with a `commit` line. It acts at the end of the run, after all claims and records.

- If a claim is FALSE, or the run would exit nonzero, nothing is committed. The run prints `commit skipped: a claim failed`.
- The commit holds only the files this run wrote: each `findings.jsonl` a record was added to, `frames.jsonl` (or `$ASTEROID_FRAMES`) if a frame changed it, and `boards/TREE.md` and `boards/tree.json` if the boards were rebuilt. Each is staged by name. Other changes stay out.
- If none of them changed, the run prints `commit skipped: nothing new`.
- The author and committer are `asteroid <asteroid@users.noreply.github.com>`. This is set for the one command. Git config is not changed.
- The message: `asteroid: PROGRAM: N claims true` (or MESSAGE), a blank line, one line per true claim, one line per record (dir, word, first 80 characters), and the trailer `Run-by: bin/asteroid PROGRAM`.
- With `push`, a successful commit is pushed with `git push origin HEAD:main` (timeout 120 s). If the push fails, the error is printed and the commit stays.
- The commit is refused during a merge or on a detached HEAD.

Code: `asteroid/ext_commit.py`. Test: `python3 -I asteroid/tests/test_commit.py` (it uses a temporary git repository).
