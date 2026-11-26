"""asteroid extension: citations. A claim lives as long as its citation does.
  cite KEY [KEY ...]
KEY is KIND:VALUE with KIND one of lit, doi, arxiv, lean, file, commit, ath, or the word `original`
(grammar, meaning and limits: asteroid/CITE.md; resolver: tools/cite/cite.py).
A cite line attaches to the nearest claim, check, prove or record line above it.
Each KEY is resolved when the line is read. An ALIVE key prints and changes nothing else.
A DEAD key counts as a FALSE claim: the run exits 1, no record is written and `commit` is skipped.
A program with an uncited claim still runs; the git gate (tools/cite/gate.py) is what refuses it."""
import os, sys
import asteroid.asteroid as A

sys.path.insert(0, os.path.join(A.ROOT, "tools", "cite"))
import cite as C

def handle(line, api):
    if not (line == "cite" or line.startswith("cite ")): return False
    where = f"{api['script']}:{api['ln']}"
    keys = C.parse_keys(line[4:])
    if not keys: raise SystemExit(f"{where}: cite KEY [KEY ...] with KEY = KIND:VALUE ({', '.join(C.KINDS[:-1])}) or original")
    if not api["results"]: raise SystemExit(f"{where}: cite needs a claim or check above it")
    target = api["results"][-1][0]
    for kind, value in keys:
        ok, why = C.resolve(kind, value)
        k = kind if kind == "original" else f"{kind}:{value}"
        A.say(f"{api['ln']}: cite {k} for line {target}: {'ALIVE' if ok else 'DEAD'} ({why})")
        if not ok: api["results"].append((api["ln"], f"cite {k}", False, False))
    return True
