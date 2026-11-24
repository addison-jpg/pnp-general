The logo colour is the `logo` role in site/palette.json; replace it with the owner's chosen value when they send it.

The asteroid logo is the wordmark `4ST3RO1D`, in the typing quirk of Terezi Pyrope (Homestuck): all capitals, 4/3/1 for A/E/I, in teal.
Font stack: "Courier New", Courier, "Liberation Mono", "Nimbus Mono PS", monospace; bold (700), letter-spacing 0.02em. No other decoration.
Colour: `logo` in site/palette.json (light `#008282`, dark `#19B3B3`); nothing else holds it.
Files: site/logo.svg (follows the colour scheme), site/logo-light.svg, site/logo-dark.svg (fixed fill).
Regenerate after editing the value: `python3 asteroid/tools/make_logo.py`
The README files use the light/dark `<picture>` switch of GitHub.
The logo is the only place this style is used; body text, docs and terminal output stay as they are.
