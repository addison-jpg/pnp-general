"""The interactive prompt: `bin/asteroid` with no arguments (or `bin/asteroid repl`).
Built on the standard library's `cmd.Cmd` (readline history and line editing where the platform has readline).
Each line is run by the interpreter's own `exec_line`, against one persistent environment, exactly as a line of a file."""
import cmd, io, os, sys, contextlib
from asteroid import ui
import asteroid.asteroid as A

HELP = """asteroid lines, one at a time; state stays between lines, as in a file:
  let h = load hello.bench      show h      claim gates(h) = base(h)      plot phi h -> h.png
  circuit NAME N ... end        a circuit typed in (the prompt becomes ...>)
meta commands:
  :help               this text
  :load FILE.ath      run a program's lines here; its names stay
  :lean on|off        send `by lean` claims to the proof checker (default off: fast)
  :save FILE.ath      write this session's lines to a file
  :quit               leave (Ctrl-D too)"""

class Prompt(cmd.Cmd):
    use_rawinput = True
    def __init__(self, lean=False, stdin=None, stdout=None):
        super().__init__(stdin=stdin, stdout=stdout)
        self.st = A.Session(); self.ln = 0; self.lines = []; self.lean = lean and bool(A.lake()); self.interactive = stdin is None and sys.stdin.isatty()
        A.PROG_DIR = A.CALLER_DIR
        self.hist = os.path.join(A.ROOT, "asteroid", "out", ".repl_history")
        self._set_prompt()
    def _set_prompt(self): self.prompt = ui.cyan("...> " if self.st.block else "4ST> ") if self.interactive else ""
    # --- readline history, where the platform has it
    def preloop(self):
        try:
            import readline; readline.read_history_file(self.hist)
        except Exception: pass
    def postloop(self):
        try:
            import readline; os.makedirs(os.path.dirname(self.hist), exist_ok=True); readline.set_history_length(500); readline.write_history_file(self.hist)
        except Exception: pass
    def emptyline(self): pass
    def show(self, text):
        box = ui.box(text)
        if box: print(box, file=self.stdout)
    def run_line(self, line, keep=True):
        """Run one asteroid line; return the text it printed. Errors are shown, not raised."""
        self.ln += 1; buf = io.StringIO(); ok = True
        with contextlib.redirect_stdout(buf):
            try: A.exec_line(self.st, line, self.ln, "repl.ath")
            except SystemExit as e: print(ui.rgb(ui.RED, "rejected: ") + str(e.code if e.code is not None else "")); ok = False
            except KeyError as e: print(ui.rgb(ui.RED, "rejected: ") + f"no such name {e}"); ok = False
            except Exception as e: print(ui.rgb(ui.RED, "rejected: ") + f"{type(e).__name__}: {e}"); ok = False
            if ok and self.lean and A.lean_claims and "by lean" in line and not self.st.block: self.prove()
        if ok and keep: self.lines.append(line)
        return buf.getvalue()
    def prove(self):
        L = A.build_lean("repl.ath")
        if L: A.say(f"proved: {len(L['theorems'])} claims accepted by the proof checker in {L['seconds']} s" if L["ok"] else "NOT PROVED: the proof checker rejected these claims")
    def default(self, line):
        line = line.strip()
        if line.startswith(":"): return self.meta(line)
        if line in ("exit", "quit"): return True
        self.show(self.run_line(line)); self._set_prompt()
    def meta(self, line):
        word, _, arg = line[1:].partition(" "); arg = arg.strip()
        if word in ("quit", "q", "exit"): return True
        if word in ("help", "h", "?"): self.show(HELP)
        elif word == "lean":
            if arg == "on":
                if A.lake(): self.lean = True; self.show("lean on: `by lean` claims go to the proof checker (slow)")
                else: self.show("lean stays off: `lake` (Lean) is not installed here")
            elif arg == "off": self.lean = False; self.show("lean off: claims are evaluated in Python only")
            else: self.show("lean is " + ("on" if self.lean else "off") + "   (:lean on | :lean off)")
        elif word == "save":
            if not arg: self.show("usage: :save FILE.ath"); return
            p = os.path.join(A.CALLER_DIR, arg)
            try: open(p, "w", encoding="utf-8", newline="\n").write("# saved from the asteroid prompt\n" + "\n".join(self.lines) + "\n"); self.show(f"saved {len(self.lines)} lines to {p}")
            except OSError as e: self.show(ui.rgb(ui.RED, "rejected: ") + str(e))
        elif word == "load":
            p = A.in_path(arg) if arg else ""
            if not arg or not os.path.isfile(p): self.show(ui.rgb(ui.RED, "rejected: ") + f"no such file: {arg or '(none given)'}"); return
            out = []
            for raw in open(p, encoding="utf-8"):
                if raw.split("#", 1)[0].strip(): out.append(self.run_line(raw.rstrip("\n")).rstrip("\n"))
            self.show("\n".join(x for x in out if x) or f"loaded {arg}")
        else: self.show(ui.rgb(ui.RED, "rejected: ") + f"unknown command :{word}   (:help)")
        self._set_prompt()
    def do_EOF(self, line):
        if self.interactive: print(file=self.stdout)
        return True
    def precmd(self, line): return line
    def parseline(self, line): return (None, None, line)      # every line goes to `default`

def main(lean=False):
    p = Prompt(lean=lean)
    if p.interactive or os.environ.get("ASTEROID_BANNER"):
        print(ui.banner()); print()
    try: p.cmdloop(intro=None)
    except KeyboardInterrupt: print()
    return 0
