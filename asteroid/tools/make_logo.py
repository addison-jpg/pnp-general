#!/usr/bin/env python3
"""Regenerate site/logo.svg, site/logo-light.svg, site/logo-dark.svg from the
`logo` role in site/palette.json. Usage: python3 asteroid/tools/make_logo.py"""
import json
import math
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
SITE = ROOT / "site"
WORD = "4ST3RO1D"  # Terezi quirk: capitals, A->4, E->3, I->1
FONT = '"Courier New", Courier, "Liberation Mono", "Nimbus Mono PS", monospace'
SIZE, SPACING, PAD = 40, 0.02, 8


def build(style: str) -> str:
    adv = SIZE * (0.6 + SPACING)  # monospace advance plus letter-spacing
    w = math.ceil(len(WORD) * adv) + 2 * PAD
    h = math.ceil(SIZE * 0.8) + 2 * PAD
    y = PAD + round(SIZE * 0.7)
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}" '
        f'role="img" aria-label="{WORD}">\n'
        f"<title>{WORD}</title>\n<style>\n{style}\n</style>\n"
        f'<text x="{PAD}" y="{y}" font-family=\'{FONT}\' font-size="{SIZE}" '
        f'font-weight="700" letter-spacing="{SPACING}em">{WORD}</text>\n</svg>\n'
    )


def main() -> None:
    pal = json.loads((SITE / "palette.json").read_text())
    light, dark = pal["light"]["logo"], pal["dark"]["logo"]
    (SITE / "logo.svg").write_text(build(
        f"text {{ fill: {light}; }}\n@media (prefers-color-scheme: dark) {{ text {{ fill: {dark}; }} }}"))
    (SITE / "logo-light.svg").write_text(build(f"text {{ fill: {light}; }}"))
    (SITE / "logo-dark.svg").write_text(build(f"text {{ fill: {dark}; }}"))
    print(f"logo: light {light}, dark {dark}")


if __name__ == "__main__":
    main()
