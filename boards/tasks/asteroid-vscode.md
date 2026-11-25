# Task: asteroid-vscode

- **Serves:** beginners editing .ath files (Addison, 2026-11-25: GitHub will not list asteroid as a language soon; Linguist needs ~200 repos using the extension).
- **Statement:** A VS Code extension in editors/vscode/: language id `asteroid`, extension `.ath`, a TextMate grammar (keywords from asteroid/SPEC.md: circuit, end, set, claim, by lean, let, load, show, plot, hunt, record, forall cubes, ...; comments `#`; numbers; strings; `->`), language configuration (comment toggling, brackets), the 4STeroid logo as the extension icon (PNG from site/logo-*.svg), and a README.
- **Done when:** `npx @vscode/vsce package` produces editors/vscode/asteroid-*.vsix (commit the .vsix if < 1 MB), every .ath file in the repo tokenizes without unmatched scopes (test with vscode-tmgrammar-test or a small script), and the root README says in one line how to install it (Extensions → … → Install from VSIX).
- **Not now:** Open VSX (outward: QUIET rule; Addison publishes). The Marketplace release is done (see Decided).
- **Seats:** coord's Sonnet seat (below).

## OPEN / TAKEN

- OPEN (Addison): Open VSX is not published (needs Addison's token).

## Decided (one line each)

- Built, tested (20 files, 0 problems), packaged (13 KB .vsix, committed), root README line added. -> `editors/vscode/`
- Published by Addison to the VS Code Marketplace via web upload, publisher ID `asteroid` (package.json changed to match), item `asteroid.asteroid` v0.1.0; icon cropped to 4ST; README points at the Marketplace.
