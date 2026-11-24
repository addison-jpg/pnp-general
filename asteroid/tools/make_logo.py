#!/usr/bin/env python3
"""Regenerate the asteroid logo SVGs.

The letters are drawn as outlines from the fan-made fonts credited in site/LOGO.md, so no font has to be
installed to see the logo and no font file is shipped in this repository. Colours come from the `logo`
role (Terezi wordmark) and the `logo_alt` role (Vriska wordmark) in site/palette.json.

Usage: python3 asteroid/tools/make_logo.py --terezi PATH.ttf [--vriska PATH.otf]   (needs: pip install fonttools)
"""
import argparse
import json
import pathlib

from fontTools.pens.boundsPen import BoundsPen
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.ttLib import TTFont

ROOT = pathlib.Path(__file__).resolve().parents[2]
SITE = ROOT / "site"
HEIGHT = 48  # rendered height in px of the cap height, plus padding


def outline(font_path: str, word: str) -> tuple[str, tuple[float, float, float, float]]:
    """Path data for `word` set in the font, y pointing down, and its bounding box."""
    f = TTFont(font_path)
    gs, cmap, hmtx = f.getGlyphSet(), f.getBestCmap(), f["hmtx"]
    missing = [c for c in word if ord(c) not in cmap]
    if missing:
        raise SystemExit(f"{font_path} has no glyph for {missing}")
    svg, bounds, x = SVGPathPen(gs), BoundsPen(gs), 0
    for ch in word:
        g = cmap[ord(ch)]
        t = (1, 0, 0, -1, x, 0)  # flip y: font units point up, SVG points down
        gs[g].draw(TransformPen(svg, t))
        gs[g].draw(TransformPen(bounds, t))
        x += hmtx[g][0]
    return svg.getCommands(), bounds.bounds


def build(d: str, box, word: str, style: str) -> str:
    x0, y0, x1, y1 = box
    pad = 0.08 * (y1 - y0)
    vb = (x0 - pad, y0 - pad, x1 - x0 + 2 * pad, y1 - y0 + 2 * pad)
    w = round(HEIGHT * vb[2] / vb[3])
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{vb[0]:.0f} {vb[1]:.0f} {vb[2]:.0f} {vb[3]:.0f}" '
            f'width="{w}" height="{HEIGHT}" role="img" aria-label="{word}">\n<title>{word}</title>\n'
            f"<style>\n{style}\n</style>\n<path d=\"{d}\"/>\n</svg>\n")


def write(stem: str, d: str, box, word: str, light: str, dark: str) -> None:
    (SITE / f"{stem}.svg").write_text(build(d, box, word,
        f"path {{ fill: {light}; }}\n@media (prefers-color-scheme: dark) {{ path {{ fill: {dark}; }} }}"))
    (SITE / f"{stem}-light.svg").write_text(build(d, box, word, f"path {{ fill: {light}; }}"))
    (SITE / f"{stem}-dark.svg").write_text(build(d, box, word, f"path {{ fill: {dark}; }}"))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--terezi", required=True)
    ap.add_argument("--vriska")
    a = ap.parse_args()
    pal = json.loads((SITE / "palette.json").read_text())
    d, box = outline(a.terezi, "4ST3RO1D")  # Terezi's quirk: capitals, A->4, E->3, I->1
    write("logo", d, box, "4ST3RO1D", pal["light"]["logo"], pal["dark"]["logo"])
    print("logo: 4ST3RO1D,", pal["light"]["logo"], pal["dark"]["logo"])
    if a.vriska:
        d, box = outline(a.vriska, "asteroid")  # the Vriska font has letters only, no digits
        lt, dk = pal["light"].get("logo_alt", "#005682"), pal["dark"].get("logo_alt", "#3D9BD6")
        write("logo-vriska", d, box, "asteroid", lt, dk)
        print("logo-vriska: asteroid,", lt, dk)


if __name__ == "__main__":
    main()
