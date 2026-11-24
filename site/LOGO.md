# The asteroid logo

The logo is the word `4ST3RO1D`: capitals with A, E and I written as 4, 3 and 1, the typing style of Terezi Pyrope. An alternate mark, `asteroid` in Vriska Serket's hand, is in `logo-vriska*.svg`. This is the only place these styles are used; text, documentation and terminal output keep their ordinary fonts.

The letters are drawn as outlines (`<path>`), so nobody needs a font installed to see them, and no font file is shipped in this repository.

Colours: the `logo` role (main mark) and the `logo_alt` role (Vriska mark) in `palette.json`, light and dark. To change them, edit those values and run:

    python3 asteroid/tools/make_logo.py --terezi PATH/terezzzzzzz.ttf --vriska PATH/Arachnidsgrip1.otf

## Credit

- Lettering of the main mark: the font **terezzzzzzz**, a fan-made handwriting font in the style of Terezi Pyrope, made with MyScriptFont.com (FontForge, 20 August 2013). Designer not named in the font.
- Lettering of the alternate mark: the font **Arachnidsgrip1**, a fan-made handwriting font in the style of Vriska Serket, made with Calligraphr (2 September 2021). Designer not named in the font.
- Terezi Pyrope and Vriska Serket are characters of *Homestuck* by Andrew Hussie.

If you made either font and want a different credit, a link, or the logo removed, open an issue.
