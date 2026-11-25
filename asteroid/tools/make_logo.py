#!/usr/bin/env python3
"""Regenerate the asteroid logo SVGs.

The letters are drawn as outlines from the fan-made fonts credited in asteroid/site/LOGO.md, so no font has to be
installed to see the logo and no font file is shipped in this repository. Colours come from the `logo`
role (the Terezi half, \"4ST\") and the `logo_alt` role (the Vriska half, \"eroid\") in asteroid/site/palette.json.

Usage: python3 asteroid/tools/make_logo.py --terezi PATH.ttf --vriska PATH.otf   (needs: pip install fonttools)
"""
import argparse
import json
import pathlib

from fontTools.pens.boundsPen import BoundsPen
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.ttLib import TTFont

ROOT = pathlib.Path(__file__).resolve().parents[2]
SITE = ROOT / "asteroid" / "site"
HEIGHT = 48  # rendered height in px of the cap height, plus padding


def outline(font_path: str, word: str, scale: float = 1.0, x0: float = 0.0) -> tuple[str, tuple[float, float, float, float]]:
    """Path data for `word` set in the font at `scale` from x = x0, y pointing down, and its bounding box."""
    f = TTFont(font_path)
    scale = scale * 1000 / f["head"].unitsPerEm
    gs, cmap, hmtx = f.getGlyphSet(), f.getBestCmap(), f["hmtx"]
    missing = [c for c in word if ord(c) not in cmap]
    if missing:
        raise SystemExit(f"{font_path} has no glyph for {missing}")
    svg, bounds, x = SVGPathPen(gs), BoundsPen(gs), x0
    for ch in word:
        g = cmap[ord(ch)]
        t = (scale, 0, 0, -scale, x, 0)  # flip y: font units point up, SVG points down
        gs[g].draw(TransformPen(svg, t))
        gs[g].draw(TransformPen(bounds, t))
        x += hmtx[g][0] * scale
    return svg.getCommands(), bounds.bounds


def svg(parts, box, label: str, style: str) -> str:
    """parts: list of (css class, path data)."""
    x0, y0, x1, y1 = box
    pad = 0.08 * (y1 - y0)
    vb = (x0 - pad, y0 - pad, x1 - x0 + 2 * pad, y1 - y0 + 2 * pad)
    w = round(HEIGHT * vb[2] / vb[3])
    paths = "".join(f'<path class="{c}" d="{d}"/>\n' for c, d in parts)
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{vb[0]:.0f} {vb[1]:.0f} {vb[2]:.0f} {vb[3]:.0f}" '
            f'width="{w}" height="{HEIGHT}" role="img" aria-label="{label}">\n<title>{label}</title>\n'
            f"<style>\n{style}\n</style>\n{paths}</svg>\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--terezi", required=True)
    ap.add_argument("--vriska", required=True)
    a = ap.parse_args()
    pal = json.loads((SITE / "palette.json").read_text())
    # "4ST" in Terezi's hand and quirk (capitals, A -> 4), "eroid" in Vriska's hand.
    d1, b1 = outline(a.terezi, "4ST")
    _, probe = outline(a.vriska, "eroid")
    k = (b1[3] - b1[1]) / (probe[3] - probe[1])  # same overall height for both halves
    gap = 0.10 * (b1[3] - b1[1])
    d2, b2 = outline(a.vriska, "eroid", scale=k, x0=b1[2] + gap - probe[0] * k)
    box = (min(b1[0], b2[0]), min(b1[1], b2[1]), max(b1[2], b2[2]), max(b1[3], b2[3]))
    parts, label = [("t", d1), ("v", d2)], "4STeroid (asteroid)"
    tl, td = pal["light"]["logo"], pal["dark"]["logo"]
    vl, vd = pal["light"]["logo_alt"], pal["dark"]["logo_alt"]
    (SITE / "logo.svg").write_text(svg(parts, box, label,
        f".t {{ fill: {tl}; }} .v {{ fill: {vl}; }}\n@media (prefers-color-scheme: dark) {{ .t {{ fill: {td}; }} .v {{ fill: {vd}; }} }}"))
    (SITE / "logo-light.svg").write_text(svg(parts, box, label, f".t {{ fill: {tl}; }} .v {{ fill: {vl}; }}"))
    (SITE / "logo-dark.svg").write_text(svg(parts, box, label, f".t {{ fill: {td}; }} .v {{ fill: {vd}; }}"))
    print(f"logo: 4ST (Terezi) {tl}/{td}, eroid (Vriska) {vl}/{vd}")


if __name__ == "__main__":
    main()
