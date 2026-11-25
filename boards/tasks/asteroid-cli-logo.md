# Task: asteroid-cli-logo

- **Serves:** asteroid's first impression (Addison, 2026-11-25: "that pretty logo should be in cli. this is honestly the BIggest thing rn").
- **Statement:** The hand-lettered 4STeroid logo (site/logo-dark.svg / logo-light.svg: "4ST" teal, "eroid" blue, outlines as SVG paths) appears in the terminal as text art when asteroid starts (`asteroid` with no file, the 4ST> prompt banner, `asteroid --version`), built from the real letter shapes, not a font.
- **How:** rasterize the SVG paths ONCE with a generator script (asteroid/tools/make_cli_logo.py, may use any Python library) into Unicode half-blocks or braille, about 60 to 72 columns wide and 4 to 8 rows; commit the result as plain data (asteroid/logo_art.py, no runtime dependency). Colours from site/terminal.json (logo = SGR 36, logo_alt = SGR 34). Fallbacks: NO_COLOR or not a TTY → no escape codes; terminal narrower than the art → the existing one-line wordmark (ui.wordmark()); Windows → enable VT processing (or plain art) so the classic console does not print raw escapes; the PyInstaller exe must include it.
- **Done when:** a screenshot of the banner in a real terminal (light and dark background) is in asteroid/out/, `python3 -m asteroid test --no-lean` passes, and the art looks like the logo to a person, not a blob.
- **Files:** new files are yours; asteroid/ui.py `banner()` and asteroid/repl.py are owned by main's UI Sonnet: change only `banner()` (one call to the art), write one line here when you do.
- **Seats:** coord's Sonnet seat (below).

## OPEN / TAKEN

- OPEN: no seat has written a TAKEN line yet; `asteroid/logo_art.py` does not exist. Seat: coord's Sonnet seat (see Seats above).

## Decided

- (none yet)
