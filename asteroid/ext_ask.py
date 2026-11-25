"""asteroid extension: ask. Put a question to the repository's recorded results, in controlled English.
  ask "QUESTION"
QUESTION is one line of the grammar in core/ontology/ASK.md (for example ask "show open frames about time").
The answer is printed from data by core/ontology/ask.py; every answer line carries its label.
An ask line is NOT a claim: it never appears in the claims line, never writes a record or a frame, never changes
the exit code, and never writes any file. A question the grammar does not parse prints "did not understand"
and the grammar, and the program goes on. The question is data: nothing in it is run, and a `#` in it starts
a comment as everywhere in asteroid (so it cuts the question short). See asteroid/ASK.md."""
import importlib.util, os, re, sys
import asteroid.asteroid as A

PAT = re.compile(r'ask "([^"]*)"')
_ASK = []

def _ask():
    """core/ontology/ask.py, loaded by path with no bytecode written (a question must write no file in the repo)."""
    if not _ASK:
        path = os.path.join(A.ROOT, "core", "ontology", "ask.py")
        old = sys.dont_write_bytecode; sys.dont_write_bytecode = True
        try:
            spec = importlib.util.spec_from_file_location("ontology_ask", path)
            mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        finally: sys.dont_write_bytecode = old
        _ASK.append(mod)
    return _ASK[0]

def handle(line, api):
    if line != "ask" and not line.startswith("ask "): return False
    where = f"{api['script']}:{api['ln']}"
    m = PAT.fullmatch(line)
    if not m: raise SystemExit(f'{where}: ask "QUESTION"')
    code, text = _ask().answer(m.group(1))
    A.say(f'{api["ln"]}: ask "{m.group(1)[:80]}" (a question, not a claim)')
    for l in text.splitlines(): A.say("   " + l)
    return True
