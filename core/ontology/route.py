#!/usr/bin/env python3
"""Route a question to the tiny exact checks underneath it. Read-only. Standard library only.

  python3 -I core/ontology/route.py what is verified about neuron
  python3 -I core/ontology/route.py explain asymmetry

A question is parsed by the same grammar as ask.py (core/ontology/ask.py). This program does not answer it.
It says (1) which recorded source answers that form of question, and (2) which rechecks already recorded in
RESULTS.md mention the WORD or TAG, each shown with its label, so the smallest exact check can be picked.
It NEVER runs a check: a recheck is printed as text, and only if it is a plain `python3 -I path/to/file.py`
(anything else is shown as "not a plain command"). The cost shown is the script's length in lines, a proxy and
not a measured time; a cost this program has not measured is not claimed. Order: exact checks first
(checked, checked-finite), then tested, then refuted; within a label, shorter scripts first.
A recheck mentioning a word does not answer the question: it is where a person or ask.py can look.
Exit codes: 0 routed, 2 did not understand (same grammar as ask.py)."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ask

SOURCE = {  # form of question -> (what answers it, what kind of reading that is)
    "status": ("center/shards and boards", "recorded counts"),
    "verified": ("RESULTS.md", "recorded counts"),
    "frames_open": ("frames.jsonl", "recorded frames"), "frames": ("frames.jsonl", "recorded frames"),
    "findings": ("**/findings.jsonl", "recorded findings"), "findings_verified": ("**/findings.jsonl", "recorded findings"),
    "about_verified": ("findings and RESULTS.md", "recorded results"), "about_open": ("frames, findings, center cells", "recorded gaps"),
    "connects": ("tag tables and findings", "proposed links (tags are unreviewed)"),
    "results_use": ("core/ontology/tags/tags_formal.json", "proposed tags"), "works_use": ("core/ontology/tags/tags_culture.json", "proposed tags"),
    "links": ("tag tables", "proposed links"), "list_tags": ("tag tables", "proposed tags"), "list_corpora": ("tag tables", "proposed tags"),
    "list_pillars": ("tag tables", "proposed tags"), "what_is": ("core/ontology/SCHEMA.md and tag tables", "definitions"),
    "explain": ("everything on record that mentions the word", "recorded text"),
}
ROW = re.compile(r"^\| (checked-finite|checked|tested|refuted) \| (.*) \| (`[^|]*`(?:, `[^|]*`)*) \| (.*?) \|$")
PLAIN = re.compile(r"^`python3 -I ([\w./-]+\.py)`$")
ORDER = {"checked": 0, "checked-finite": 0, "tested": 1, "refuted": 2}

def words_of(args): return [a for a in args if a]

def rechecks(root, words):
    path = os.path.join(root, "RESULTS.md")
    out, seen = [], set()
    if not os.path.isfile(path): return out
    for line in open(path, encoding="utf-8", errors="replace"):
        m = ROW.match(line.rstrip("\n"))
        if not m: continue
        label, stmt, _ev, rc = m.groups()
        if not rc.strip() or not any(ask.mentions(w, stmt) for w in words): continue
        pm = PLAIN.match(rc.strip())
        if pm:
            rel = pm.group(1); full = os.path.join(root, rel)
            inside = os.path.realpath(full).startswith(os.path.realpath(root) + os.sep) and os.path.isfile(full)
            cost = sum(1 for _ in open(full, encoding="utf-8", errors="replace")) if inside else None
            key = rel
        else:
            rel, cost, key = None, None, rc.strip()
        out.append((ORDER[label], cost if cost is not None else 10 ** 9, label, rel, rc.strip(), ask.clean(stmt, 90), key, cost))
    best = []
    for r in sorted(out, key=lambda r: r[:2] + (r[5],)):   # best label first, so a duplicate keeps its strongest label
        if r[6] in seen: continue
        seen.add(r[6]); best.append(r)
    return best

def route(q, root=None):
    root = ask.get_root(root); p = ask.parse(q)
    if p is None: return None
    kind, args = p; src, what = SOURCE.get(kind, ("recorded data", "recorded data"))
    lines = [f"[open] route: '{kind}' is answered from {src} ({what}); nothing is run here"]
    ws = words_of(args)
    if not ws:
        lines.append("[open] no WORD in this question, so no recheck is matched"); return lines
    rc = rechecks(root, ws)
    if not rc: lines.append(f"[open] no recorded recheck in RESULTS.md mentions {', '.join(ask.clean(w) for w in ws)}")
    for _o, _sortcost, label, rel, raw, stmt, _key, cost in rc[:ask.MAXROWS]:
        if rel is None: cmd = f"not a plain command: {ask.clean(raw, 70)}"
        elif cost is None: cmd = f"python3 -I {ask.clean(rel, 70)}  (path is outside the repository or missing; not opened)"
        else: cmd = f"python3 -I {rel}  (script is {cost} lines; a proxy for cost, not a measured time)"
        lines.append(f"[{label}] recheck: {cmd} -- {stmt}")
    if len(rc) > ask.MAXROWS: lines.append(f"[open] ... and {len(rc) - ask.MAXROWS} more rechecks")
    return lines

def main(argv):
    q = " ".join(argv)
    out = route(q)
    if out is None:
        print(f"did not understand: {ask.clean(q)}"); print(ask.GRAMMAR); return 2
    print("\n".join(out)); return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
