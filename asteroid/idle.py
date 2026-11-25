"""`bin/asteroid idle`: a window for asteroid, in the spirit of Python's IDLE.
Built on tkinter and on idlelib, the code IDLE itself is made of: `idlelib.colorizer.ColorDelegator` (syntax colouring, subclassed here
with asteroid's verbs) attached to a `tk.Text` by `idlelib.percolator.Percolator`. A plot a program writes is shown with `tkinter.PhotoImage`.
Standard library only. If tkinter is missing: one line saying how to get it, exit code 2."""
import os, re, sys, io, json, contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
DARK = {"background": "#141413", "surface": "#1d1d1b", "text": "#ecebe6", "muted": "#a19f97", "accent": "#8db4dc",
        "proved": "#7fbf8a", "refuted": "#e58a80", "open": "#d9a650", "codeBackground": "#0f0f0e", "codeText": "#e6e5e0",
        "logo": "#19B3B3", "logo_alt": "#3D9BD6"}
def palette():
    """The dark colours of site/palette.json (the built-in copy is used when that file is not beside the code, as in the Windows .exe)."""
    for p in (os.path.join(os.path.dirname(HERE), "site", "palette.json"), os.path.join(HERE, "palette.json")):
        try: return {**DARK, **json.load(open(p, encoding="utf-8"))["dark"]}
        except Exception: pass
    return dict(DARK)

VERBS = ["let", "load", "show", "claim", "claim!", "by", "lean", "plot", "phi", "circuit", "end", "set", "save", "conjecture", "hunt", "record",
         "forall", "cubes", "prove", "not", "and", "or"]
VERDICTS = [(re.compile(r"\b(NOT PROVED|FALSE|rejected|cannot parse)\b"), "bad"), (re.compile(r"\b(proved|TRUE|OK)\b"), "good"),
            (re.compile(r"(line skipped|not proved)"), "warn")]

def run_text(text, path, lean=False):
    """Run a program's text in this process from a clean slate; return (printed text, exit code)."""
    import asteroid.asteroid as A
    os.makedirs(os.path.join(A.ROOT, "asteroid", "out"), exist_ok=True)
    A.reset(); A.NO_LEAN = not (lean and A.lake())
    if not path:
        path = os.path.join(A.ROOT, "asteroid", "out", "_window.ath")
    open(path, "w", encoding="utf-8", newline="\n").write(text)
    buf = io.StringIO(); rc = 1
    with contextlib.redirect_stdout(buf):
        try: rc = A.run(os.path.relpath(path, A.ROOT) if os.path.commonpath([A.ROOT, os.path.abspath(path)]) == A.ROOT else path)
        except SystemExit as e: print("rejected: " + str(e.code)); rc = 1
        except Exception as e: print(f"rejected: {type(e).__name__}: {e}"); rc = 1
    return buf.getvalue(), rc

def selftest():
    """Headless: run hello.ath with the proof checker off. Used by the Windows .exe build to see the bundle is whole."""
    import asteroid.asteroid as A
    hello = os.path.join(A.ROOT, "hello.ath")
    out, rc = run_text(open(hello, encoding="utf-8").read(), None)
    print(out.rstrip().splitlines()[-1] if out.strip() else "(no output)")
    print("selftest " + ("ok" if rc == 0 else "FAILED")); return 0 if rc == 0 else 1

def main(argv=()):
    if "--selftest" in argv: return selftest()
    try:
        import tkinter as tk
        from tkinter import filedialog, messagebox
        from idlelib.colorizer import ColorDelegator
        from idlelib.percolator import Percolator
    except ImportError:
        print("asteroid idle needs tkinter. Windows: it ships with python.org Python (re-run the installer, tick tcl/tk). Debian/Ubuntu: sudo apt install python3-tk idle; macOS: use python.org Python.")
        return 2
    P = palette()
    import asteroid.asteroid as A

    class Colors(ColorDelegator):
        """IDLE's own colorizer, with asteroid's verbs instead of Python's keywords."""
        def __init__(self):
            super().__init__()
            self.prog = re.compile(r"(?P<COMMENT>#[^\n]*)|(?P<KEYWORD>(?<![\w])(?:" + "|".join(re.escape(v) for v in VERBS).replace(r"claim\!", r"claim!?") + r")(?![\w]))"
                                   r"|(?P<STRING>\"[^\"\n]*\"|'[^'\n]*')|(?P<BUILTIN>(?<![\w])-?\d+(?![\w]))|(?P<SYNC>\n)", re.S)
            self.idprog = re.compile(r"(?!x)x")
        def LoadTagDefs(self):
            super().LoadTagDefs()
            self.tagdefs = {"COMMENT": {"foreground": P["muted"], "background": P["codeBackground"]},
                            "KEYWORD": {"foreground": P["logo"], "background": P["codeBackground"]},
                            "STRING": {"foreground": P["open"], "background": P["codeBackground"]},
                            "BUILTIN": {"foreground": P["logo_alt"], "background": P["codeBackground"]},
                            "DEFINITION": {"foreground": P["accent"], "background": P["codeBackground"]},
                            "SYNC": {"background": P["codeBackground"]}, "TODO": {"background": P["codeBackground"]},
                            "ERROR": {"background": P["refuted"]}, "hit": {"background": P["accent"]}, "STRING3": {}}

    root = tk.Tk(); root.title("asteroid idle"); root.configure(bg=P["background"]); root.geometry("1100x700")
    font = ("Consolas" if os.name == "nt" else "Menlo" if sys.platform == "darwin" else "DejaVu Sans Mono", 11)
    state = {"path": None, "img": None}

    # wordmark: "4ST" in cyan, "eroid" fading from cyan to blue, one tag per letter
    head = tk.Text(root, height=1, bd=0, bg=P["background"], highlightthickness=0, font=(font[0], 22, "bold"), cursor="arrow")
    head.pack(fill="x", padx=12, pady=(8, 0))
    head.insert("end", "4ST", "c0")
    head.tag_configure("c0", foreground=P["logo"])
    a, b = [int(P["logo"][i:i + 2], 16) for i in (1, 3, 5)], [int(P["logo_alt"][i:i + 2], 16) for i in (1, 3, 5)]
    for i, ch in enumerate("eroid"):
        t = i / 4; col = "#%02x%02x%02x" % tuple(int(a[k] + (b[k] - a[k]) * t) for k in range(3))
        head.tag_configure(f"g{i}", foreground=col); head.insert("end", ch, f"g{i}")
    head.insert("end", "   :3   =^.^=   :)", "faint"); head.tag_configure("faint", foreground=P["muted"], font=(font[0], 11))
    head.configure(state="disabled")

    bar = tk.Frame(root, bg=P["background"]); bar.pack(fill="x", padx=12, pady=6)
    lean = tk.BooleanVar(value=False)
    def btn(text, cmd, primary=False):
        w = tk.Button(bar, text=text, command=cmd, relief="flat", bd=0, padx=10, pady=3, bg=P["logo"] if primary else P["surface"],
                      fg=P["background"] if primary else P["text"], activebackground=P["logo_alt"], activeforeground=P["background"])
        w.pack(side="left", padx=(0, 6)); return w

    pan = tk.PanedWindow(root, orient="horizontal", bg=P["background"], sashwidth=5, bd=0); pan.pack(fill="both", expand=True, padx=12, pady=(0, 10))
    edit = tk.Text(pan, undo=True, wrap="none", bg=P["codeBackground"], fg=P["codeText"], insertbackground=P["logo"], font=font, bd=0, padx=8, pady=6, highlightthickness=0,
                   selectbackground=P["logo_alt"], tabs=("1c",))
    right = tk.PanedWindow(pan, orient="vertical", bg=P["background"], sashwidth=5, bd=0)
    out = tk.Text(right, state="disabled", wrap="word", bg=P["codeBackground"], fg=P["codeText"], font=font, bd=0, padx=8, pady=6, height=14, highlightthickness=0)
    prev = tk.Label(right, bg=P["surface"], fg=P["muted"], text="a plot appears here after a `plot` line runs", bd=0)
    right.add(out, stretch="always"); right.add(prev, stretch="always"); pan.add(edit, stretch="always"); pan.add(right, stretch="always")
    for tag, key in (("good", "proved"), ("bad", "refuted"), ("warn", "open")): out.tag_configure(tag, foreground=P[key])
    Percolator(edit).insertfilter(Colors())

    def set_out(text):
        out.configure(state="normal"); out.delete("1.0", "end"); out.insert("end", text)
        for rx, tag in VERDICTS:
            for m in rx.finditer(text):
                out.tag_add(tag, f"1.0+{m.start()}c", f"1.0+{m.end()}c")
        out.configure(state="disabled"); out.see("end")
    def show_plot(text):
        pngs = re.findall(r"wrote (.+\.png)\s*$", text, re.M)
        if not pngs: return
        try:
            img = tk.PhotoImage(file=pngs[-1].strip())
            k = max(1, -(-img.width() // max(200, prev.winfo_width())), -(-img.height() // max(150, prev.winfo_height())))
            if k > 1: img = img.subsample(k)
            state["img"] = img; prev.configure(image=img, text="")
        except Exception as e: prev.configure(image="", text=f"cannot show {pngs[-1]}: {e}")
    def title(): root.title("asteroid idle" + (" - " + os.path.basename(state["path"]) if state["path"] else ""))
    def open_(_=None):
        p = filedialog.askopenfilename(filetypes=[("asteroid", "*.ath"), ("all", "*.*")], initialdir=os.path.join(A.ROOT, "asteroid", "examples"))
        if p: edit.delete("1.0", "end"); edit.insert("1.0", open(p, encoding="utf-8").read()); state["path"] = p; title()
    def save_as(_=None):
        p = filedialog.asksaveasfilename(defaultextension=".ath", filetypes=[("asteroid", "*.ath")])
        if p: state["path"] = p; save(); title()
    def save(_=None):
        if not state["path"]: return save_as()
        open(state["path"], "w", encoding="utf-8", newline="\n").write(edit.get("1.0", "end-1c") + "\n")
    def run(_=None):
        set_out("running...\n"); root.update_idletasks()
        text, rc = run_text(edit.get("1.0", "end-1c") + "\n", state["path"], lean.get())
        set_out(text + ("\n(exit code %d)" % rc if rc else "")); show_plot(text)
    btn("Open", open_); btn("Save", save); btn("Run  (F5)", run, True)
    tk.Checkbutton(bar, text="Lean", variable=lean, bg=P["background"], fg=P["muted"], selectcolor=P["surface"], activebackground=P["background"],
                   activeforeground=P["text"]).pack(side="left")
    root.bind("<F5>", run); root.bind("<Control-o>", open_); root.bind("<Control-s>", save)
    try: edit.insert("1.0", open(os.path.join(A.ROOT, "hello.ath"), encoding="utf-8").read())
    except OSError: edit.insert("1.0", "# type asteroid lines here, then press F5\n")
    edit.focus_set()
    if "--autorun" in argv: root.after(300, run)     # for a screenshot: run the buffer once, as soon as the window is up
    root.mainloop(); return 0
