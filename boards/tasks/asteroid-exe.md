# Task: asteroid-exe

- **Serves:** asteroid on the front page of the repository (owner, 2026-11-25: ".exe should be on the board ... it should live on the front page of the entire github").
- **Statement:** A double-clickable `asteroid.exe` for Windows (no Python or Lean install needed), with ONE direct download link at the top of the root README.md.
- **Done when:** a stranger on Windows clicks the link on the front page, gets `asteroid.exe`, and `asteroid.exe hello.ath` runs (evaluate at least; say plainly in the README whether `by lean` proving works from the .exe).
- **How (pick one, write DECIDED):** (a) build the pure-Lean `asteroid` executable on a `windows-latest` GitHub Actions runner (`lake build asteroid`, see asteroid/NATIVE.md); (b) bundle the Python front end with PyInstaller on the runner. Prefer (a) if it builds; (b) is the fallback.
- **Where the file lives:** the QUIET rule at the top of BOARD.md forbids releases and tags until Addison says ready. So until then the workflow commits the built file to `dist/windows/asteroid.exe` on main (or a CI artifact if the file is too large for git, > 50 MB), and the README links the raw file. When Addison says ready, switch to a GitHub Release with `releases/latest/download/asteroid.exe`.
- **Seats:** OPEN, asking for one Sonnet seat (Actions + packaging). Smallest agent that can do it. Nobody asks the owner.

## Lines (TAKEN / DECIDED only)
- TAKEN (main, 2026-11-25): already seated: main's asteroid-UI Sonnet (interactive prompt, then the window, then the exe). DECIDED (b) PyInstaller: the Lean binary is 122 MiB, over GitHub's 100 MB file limit. Path: Addison asked for the repo root, next to asteroid/: `asteroid.exe` at the root, not dist/windows/. Workflow is workflow_dispatch only, commits via github-actions[bot] with [skip ci]; no release or tag (QUIET).
