"""Colours and the framed box for asteroid's terminal output. Standard library only.
Colour is on only when stdout is a terminal and NO_COLOR is unset; `--no-color` turns it off. Piped output stays plain."""
import os, re, sys, random

CYAN = (0x19, 0xB3, 0xB3); BLUE = (0x3D, 0x9B, 0xD6)
GREEN = (0x7F, 0xBF, 0x8A); RED = (0xE5, 0x8A, 0x80); YELLOW = (0xD9, 0xA6, 0x50); GREY = (0x6E, 0x6D, 0x68)
ENABLED = False
_ANSI = re.compile(r"\x1b\[[0-9;]*m")

def enable_windows_ansi():
    if os.name != "nt": return
    os.system("")                                   # makes cmd, PowerShell and Windows Terminal read ANSI escapes
    try:
        import ctypes; k = ctypes.windll.kernel32; h = k.GetStdHandle(-11); m = ctypes.c_uint32()
        if k.GetConsoleMode(h, ctypes.byref(m)): k.SetConsoleMode(h, m.value | 0x0004)
    except Exception: pass

def setup(no_color=False, stream=None):
    """Decide once, at start-up, whether to use colour."""
    global ENABLED
    stream = stream or sys.stdout
    ENABLED = bool(not no_color and "NO_COLOR" not in os.environ and getattr(stream, "isatty", lambda: False)()
                   and os.environ.get("TERM") != "dumb")
    if ENABLED: enable_windows_ansi()
    return ENABLED

def rgb(c, text): return f"\x1b[38;2;{c[0]};{c[1]};{c[2]}m{text}\x1b[0m" if ENABLED else text
def cyan(t): return rgb(CYAN, t)
def dim(t): return rgb(GREY, t)
def visible(t): return _ANSI.sub("", t)

_VERDICTS = [
    (re.compile(r"\b(NOT PROVED|FALSE|rejected)\b"), RED),
    (re.compile(r"\b(proved|TRUE|demo OK)\b"), GREEN),
    (re.compile(r"\b(skipped|line skipped|not proved)\b"), YELLOW)]
def paint(text):
    """Colour the verdict words in a line of output. Plain text when colour is off."""
    if not ENABLED or "\x1b" in text: return text
    for rx, c in _VERDICTS: text = rx.sub(lambda m: rgb(c, m.group(1)), text)
    return text

def noisy_gradient(text, seed=4):
    """'eroid': a gradient from cyan to blue with a little per-letter noise, truecolor."""
    if not ENABLED: return text
    r = random.Random(seed); out = []
    for i, ch in enumerate(text):
        t = i / max(1, len(text) - 1)
        c = tuple(max(0, min(255, int(CYAN[k] + (BLUE[k] - CYAN[k]) * t + r.randint(-18, 18)))) for k in range(3))
        out.append(rgb(c, ch))
    return "".join(out)

def wordmark(): return cyan("4ST") + noisy_gradient("eroid")

def banner(version=""):
    faces = [":3", ":)", "=^.^=", ":D", "^_^"]
    r = random.Random(7)
    top = "  " + dim(faces[0]) + "      " + dim(faces[2]) + "     " + dim(faces[1])
    mid = "      " + wordmark() + "   " + dim(faces[3]) + "   " + dim("an interactive prompt")
    bot = "  " + dim(faces[4]) + "   " + dim(":help for help, :quit or Ctrl-D to leave") + "   " + dim(faces[0])
    return "\n".join([top, mid, bot])

def box(text, title=""):
    """Frame a block of text with Unicode box drawing."""
    lines = text.rstrip("\n").split("\n") if text.strip() else []
    if not lines: return ""
    w = max(len(visible(l)) for l in lines + [title])
    t = f" {title} " if title else ""
    top = "┌" + t + "─" * (w + 2 - len(t)) + "┐"; bot = "└" + "─" * (w + 2) + "┘"
    side = rgb(CYAN, "│")
    return "\n".join([rgb(CYAN, top)] + [side + " " + l + " " * (w - len(visible(l))) + " " + side for l in lines] + [rgb(CYAN, bot)])
