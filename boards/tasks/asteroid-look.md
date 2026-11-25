# Task: asteroid-look

- **Serves:** the asteroid website and terminal output.
- **Source:** owner, 2026-11-24: one pre-existing format; no Python at all; a clean open-source project with a website and a command line; "I dont want it to look ugly and vibecoded".
- **Statement:** A colour scheme chosen by the owner: a small page with a colour picker per role (background, surface, text, muted, accent, proved, refuted, open, code) and a live preview of the site header and of terminal output; it exports hex values to `site/palette.json` and CSS variables.
- **Done when:** the owner can open the picker, choose, and the chosen values are in the repository.
- **Seats:** coord, with small agents.

## Lines (TAKEN / DECIDED only)

- 22:41 coord TAKEN: one Sonnet agent builds site/palette.html + site/palette.json; owner picks.
- 22:43 coord [DATA] picker at site/palette.html (one self-contained file; start values in site/palette.json, read by other work). Owner opens it by downloading the file and double-clicking, or from a clone: open site/palette.html. Choose colours, then 'copy as JSON' and paste it into site/palette.json, or send the URL (the hash holds the choice). Start values pass WCAG 4.5 on every checked pair; nothing is picked for the owner. Built by a Sonnet agent, Playwright-checked from file://.
- 00:15 qg-d2 [DATA] picker published as a private page for the owner (claude.ai artifact, link given in chat); owner picks, qg-d2 commits the JSON to site/palette.json.
- 00:38 qg-d2 [DECIDED] (owner: "basic and raw and not very HD downstream of the logo"; picker deferred): site/terminal.json = 16-colour ANSI codes from the logo (4ST teal -> cyan 36, eroid blue -> blue 34; proved 32, refuted 31, open 33, muted 90); site/palette.json accent = logo colours (light #005682, 7.57:1; dark #19B3B3, 7.15:1). The picker stays for later.
