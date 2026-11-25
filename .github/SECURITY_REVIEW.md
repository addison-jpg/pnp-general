# GitHub workflow review (defensive, 2026-11-25)

Scope: this repository's `.github/workflows/*.yml` only. Method: read the triggers, permissions, input use, secret use and action pins, and grep for the known risky patterns. Each finding cites the file and line. Labels: checked (grep and reading of the file, reproduced here), open (needs a decision).

## What is in good shape (checked)

- **No `pull_request_target`.** Fork pull requests run without repository secrets.
- **Default permissions are read-only.** Write access is granted only where needed: `exe.yml` (the publish job, commits `dist/`) and `compute.yml` (the job that writes results).
- **No untrusted event text in shell steps.** No `github.event.issue`, `comment`, `pull_request` or `head_commit` values are interpolated into a `run:` block.
- **Dispatch inputs go through environment variables, not shell text.** `compute.yml` and `compute-job.yml` pass `inputs.spec` and friends via `env:`.
- **The Discord webhook is never printed.** `discord.yml` reads it from the environment, and its messages report only the shape of the value (checked, lines 12 to 42).

## Findings to decide

1. **Actions are pinned to tags, not commit SHAs** (open). All 28 `uses:` lines are `actions/checkout@v4`, `download-artifact@v4`, `upload-artifact@v4` and `setup-python@v5`. These are GitHub's own actions, but a tag can move. Pinning to a full commit SHA stops a silent change. Recommendation: pin, and keep the tag in a comment.
2. **A workflow writes to the repository** (open, by design). `exe.yml` commits built binaries to `dist/` with `contents: write`, and `compute.yml` writes results. Both run on `workflow_dispatch` or `push`. The write is narrow and the job is isolated. Recommendation: keep it, and make sure no job with write access runs untrusted code from a branch that a fork can change.
3. **The secret handling depends on the run context** (open). The webhook is available only to the Discord workflow, which runs on `push` to this repository. Forks do not get it. Recommendation: keep it that way, and rotate the webhook if it was ever pasted in chat (the earlier webhook URLs shared in chat should count as exposed).

## Not checked here

- The repository's branch protection and secret scopes, which are settings on GitHub, not in these files.
- Any Cloudflare Worker secrets, which live outside this repository.

This review is a reading of the files. It makes no claim about GitHub's own systems.
