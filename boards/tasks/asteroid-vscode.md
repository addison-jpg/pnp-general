# Task: asteroid-vscode

- **Serves:** beginners editing .ath files (Addison, 2026-11-25: GitHub will not list asteroid as a language soon; Linguist needs ~200 repos using the extension).
- **Statement:** A VS Code extension in editors/vscode/: language id `asteroid`, extension `.ath`, a TextMate grammar (keywords from asteroid/SPEC.md: circuit, end, set, claim, by lean, let, load, show, plot, hunt, record, forall cubes, ...; comments `#`; numbers; strings; `->`), language configuration (comment toggling, brackets), the 4STeroid logo as the extension icon (PNG from site/logo-*.svg), and a README.
- **Done when:** `npx @vscode/vsce package` produces editors/vscode/asteroid-*.vsix (commit the .vsix if < 1 MB), every .ath file in the repo tokenizes without unmatched scopes (test with vscode-tmgrammar-test or a small script), and the root README says in one line how to install it (Extensions → … → Install from VSIX).
- **Not now:** publishing to the VS Code Marketplace or Open VSX (outward: QUIET rule; Addison publishes).
- **Seats:** coord's Sonnet seat (below).

## Lines (TAKEN / DECIDED only)
- TAKEN (coord Sonnet seat, 2026-11-25): editors/vscode/ extension.
- DECIDED (coord Sonnet seat, 2026-11-25): built, tested (20 files, 0 problems), packaged (13 KB .vsix, committed), root README line added. Not published.
- DECIDED (coord Sonnet seat, 2026-11-25): published by Addison to the VS Code Marketplace via web upload, publisher ID `asteroid` (package.json changed to match), item `asteroid.asteroid` v0.1.0. Icon cropped to 4ST. README now points at the Marketplace.
