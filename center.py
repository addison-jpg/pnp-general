#!/usr/bin/env python3
"""The centre of the ball: one store of records, and every view generated outward from it.

The board lives here. Hand-written boards are inputs only until they are retired; everything a seat
should read is a generated view. Three ways the centre grows, all supported:

  1. richer records   every record carries the same core fields plus optional ones (runner, axes, bound,
                      pair, persistence, provenance); a view shows what it needs and ignores the rest.
  2. more records     records are sharded by program into center/shards/<program>.jsonl (sorted,
                      deterministic, so two builds of the same inputs give the same bytes).
  3. more dimensions  a new record kind is one entry in KINDS (a reader function); nothing else changes.

Radius (credence, in [0, 1]) is computed, never typed: 0 = settled by Lean (checked) or by a refutation
confirmed by a second seat; otherwise it shrinks with each independent seat and each passing retest, and
grows with a failed retest. It is a bookkeeping choice, not a theorem.

  python3 -I center.py          rebuild center/shards/*.jsonl, center/state.json, center/VIEW.md
  python3 -I center.py queue    list the open frames (frames.jsonl, asteroid `frame`) by score, highest first
  python3 -I center.py ask TEXT print the open cells and records whose text contains TEXT (a seat's one query)

Standard library only. It reuses boards.py's loader and its verification rule, so the two never disagree."""
import json, os, re, sys, glob, hashlib, importlib.util, collections

SCHEMA = 1   # 1. every record carries "schema"; readers reject a newer schema than they know
ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)
_spec = importlib.util.spec_from_file_location("boards", os.path.join(ROOT, "boards.py"))
boards = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(boards)

def program(path):
    p = path.lower()
    for key, name in [("philosoph", "philosophy"), ("quantumgravity", "quantum-gravity"), ("methods", "methods"),
                      ("lateral", "lateral"), ("worlds", "worlds"), ("asteroid", "asteroid"), ("compute", "compute"),
                      ("refuter", "circuits"), ("flagship", "circuits"), ("one-not", "circuits"), ("open-one", "circuits"),
                      ("open-many", "circuits"), ("open-qg", "quantum-gravity"), ("qg-", "quantum-gravity"),
                      ("hypercomplex", "worlds"), ("model-in", "compute"), ("git-compute", "compute"),
                      ("ath-prompt", "prompt-method"), ("ath_prompt", "prompt-method"), ("brain", "brain"), ("ontology", "ontology"), ("privacy", "privacy"), ("compbio", "compbio")]:
        if key in p: return name
    return "other"

def radius(rec):
    w = rec.get("word")
    if w in ("checked", "checked-finite", "checked-infinite") and not rec.get("why_not"): return 0.0
    seats = len(set(rec.get("by", [])) | {rec.get("who")})
    ok = sum(1 for t in rec.get("retests", []) if t.get("ok"))
    bad = sum(1 for t in rec.get("retests", []) if not t.get("ok"))
    if w == "refuted" and seats >= 2 and not rec.get("why_not"): return 0.0
    base = {"tested": 0.5, "refuted": 0.4, "paper": 0.7, "premise": 0.8, "open": 1.0, "checked": 0.3}.get(w, 1.0)
    r = base / (1 + 0.5 * (seats - 1) + 0.25 * ok) + 0.2 * bad
    return round(min(1.0, r), 3)

def read_findings():
    out = []
    for d in boards.leaves():
        raw = [json.loads(l) for l in open(os.path.join(d, "findings.jsonl")) if l.strip()]
        retests = collections.defaultdict(list)
        for r in raw:
            if "retest" in r: retests[r["id"]].append(r["retest"])
        for r in boards.load(d):
            if "statement" not in r: continue
            why = boards.verified(r)
            rec = {"kind": "finding", "id": r["id"], "program": program(d), "dir": d, "word": r.get("word"),
                   "text": r.get("statement", ""), "who": r.get("who"), "by": r.get("by", []),
                   "evidence": r.get("evidence", []), "runner": r.get("runner"), "why_not": why,
                   "retests": retests.get(r["id"], []), "provenance": [e.split("::")[0] for e in r.get("evidence", [])]}
            rec["radius"] = radius(rec); rec["schema"] = SCHEMA; out.append(rec)
    return out

CELL = re.compile(r"^\s*-\s+(?:\d{4}-\d\d-\d\d\s+)?(?:[A-Z]\w*\s+\((?:Opus|Sonnet|Fable)[^)]*\)\s+)?"
                  r"(OPEN|TAKEN|STOPPED|DECIDED|RE-AIMED|DONE)\b(.*)$")

def read_cells():
    out = []
    for f in sorted(glob.glob("boards/tasks/*.md")) + ["BOARD.md"]:
        board = os.path.splitext(os.path.basename(f))[0]
        for n, line in enumerate(open(f, encoding="utf-8"), 1):
            m = CELL.match(line)
            if not m: continue
            state, rest = m.group(1), m.group(2).strip(" :")
            kind = (re.search(r"\((Fable|Opus|Sonnet)[^)]*\)", line) or [None, None])[1]
            target = (re.search(r"->\s*`?([^`\s]+)", line) or [None, None])[1]
            text = re.sub(r"\s+", " ", rest)[:400]
            cid = hashlib.sha256(f"{board}:{text[:120]}".encode()).hexdigest()[:8]
            rec = {"kind": "cell", "id": cid, "program": program(board), "board": board, "line": n,
                   "state": {"DONE": "DECIDED", "RE-AIMED": "OPEN"}.get(state, state), "seat": kind, "text": text,
                   "target": target, "radius": 0.0 if state in ("DECIDED", "DONE") else 1.0}
            rec["schema"] = SCHEMA; out.append(rec)
    return out

def read_fingerprints():
    out = []
    for f in sorted(glob.glob("**/fingerprints.json", recursive=True)):
        if "/.lake/" in f or f.startswith("center/"): continue
        for e in json.load(open(f)):
            out.append({"kind": "fingerprint", "id": hashlib.sha256((f + e["name"]).encode()).hexdigest()[:8],
                        "program": program(f) if program(f) != "other" else os.path.dirname(f).replace("/", "-"), "text": e["name"],
                        "seq": e["seq"], "runner": e.get("runner"), "radius": 0.5, "state": "DATA", "schema": SCHEMA})
    return out

def _forms(seq):
    yield "as is", seq
    yield "first differences", [b - a for a, b in zip(seq, seq[1:])]
    ps, t = [], 0
    for x in seq: t += x; ps.append(t)
    yield "partial sums", ps
    yield "plus 1", [x + 1 for x in seq]

def _common(a, b, need=5):
    for i in range(len(a)):
        for j in range(len(b)):
            k = 0
            while i + k < len(a) and j + k < len(b) and a[i + k] == b[j + k]: k += 1
            if k >= need and len(set(a[i:i + k])) >= 4: return k
    return 0

def matches(recs):
    """Cross-program sequence matches. Proposals only: a shared sequence is often coincidence."""
    fps = [r for r in recs if r["kind"] == "fingerprint"]; out = []
    for x in range(len(fps)):
        for y in range(x + 1, len(fps)):
            a, b = fps[x], fps[y]
            if a["program"] == b["program"]: continue
            for na, sa in _forms(a["seq"]):
                for nb, sb in _forms(b["seq"]):
                    k = _common(sa, sb)
                    if k: out.append({"a": a["text"], "b": b["text"], "form_a": na, "form_b": nb, "terms": k, "status": "proposed"})
    return out

def read_levels():
    """One record per level.json: an ontology level (a parallel on the lantern) with its infinite families."""
    out = []
    for f in sorted(glob.glob("**/level.json", recursive=True)):
        if "/.lake/" in f or f.startswith("center/"): continue
        e = json.load(open(f, encoding="utf-8"))
        still_open = any(x.get("handled_by") in ("open", "impossible") for x in e.get("infinity", []))
        rec = {"kind": "level", "id": hashlib.sha256(f.encode()).hexdigest()[:8],
               "program": program(f) if program(f) != "other" else e.get("ladder", "other"),
               "word": "open" if still_open else "tested", "text": e.get("name", f), "who": None, "by": [], "retests": []}
        rec["radius"] = radius(rec); rec["schema"] = SCHEMA; out.append(rec)
    return out

def read_frames():
    """One record per line of frames.jsonl, written by the asteroid `frame` statement (asteroid/ext_frame.py)."""
    f = os.environ.get("ASTEROID_FRAMES") or "frames.jsonl"
    if not os.path.isfile(f): return []
    out = []
    for l in open(f, encoding="utf-8"):
        if not l.strip(): continue
        e = json.loads(l)
        rec = {"kind": "frame", "id": hashlib.sha256(f"{e['source']}|{e['reading']}|{e['claim']}".encode()).hexdigest()[:8],
               "program": program(e["claim"]) if program(e["claim"]) != "other" else program(e["source"]),
               "source": e["source"], "reading": e["reading"], "claim": e["claim"], "label": e["label"], "score": e["score"],
               "status": e["status"], "state": e["status"], "word": e["label"], "text": f"{e['source']}: {e['reading']}",
               "who": None, "by": [], "retests": []}
        rec["radius"] = radius(rec); rec["schema"] = SCHEMA; out.append(rec)
    return out

def queue():
    """Open frames, highest score first."""
    return sorted((r for r in read_frames() if r["status"] == "OPEN"), key=lambda r: (-r["score"], r["id"]))

KINDS = {"finding": read_findings, "cell": read_cells, "fingerprint": read_fingerprints, "level": read_levels, "frame": read_frames}   # 3. a new dimension is one more entry here

def build():
    recs = [r for reader in KINDS.values() for r in reader()]
    os.makedirs("center/shards", exist_ok=True)
    for f in glob.glob("center/shards/*.jsonl"): os.remove(f)
    by_prog = collections.defaultdict(list)
    for r in recs: by_prog[r["program"]].append(r)
    for p, rs in by_prog.items():
        rs.sort(key=lambda r: (r["kind"], r["id"]))
        with open(f"center/shards/{p}.jsonl", "w") as fh:
            for r in rs: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    summary = {}
    for p, rs in sorted(by_prog.items()):
        f = [r for r in rs if r["kind"] == "finding" and not r["why_not"]]
        c = [r for r in rs if r["kind"] == "cell"]
        summary[p] = {"findings": dict(collections.Counter(r["word"] for r in f)),
                      "cells": dict(collections.Counter(r["state"] for r in c)),
                      "mean_radius_findings": round(sum(r["radius"] for r in f) / len(f), 3) if f else None}
    json.dump(summary, open("center/state.json", "w"), indent=1, sort_keys=True)
    out = ["# The centre (generated by `python3 -I center.py`; do not edit)", "",
           "Records live in `center/shards/<program>.jsonl`. Radius 0 = settled (Lean, or a refutation confirmed by a second seat); "
           "1 = open. Hand-written boards are inputs until retired; this is what a seat reads.", ""]
    for p, s in sorted(summary.items()):
        out.append(f"## {p}")
        out.append("findings (verified): " + (", ".join(f"{v} {k}" for k, v in sorted(s["findings"].items())) or "none")
                   + f" · mean radius {s['mean_radius_findings']}")
        out.append("cells: " + (", ".join(f"{v} {k}" for k, v in sorted(s["cells"].items())) or "none"))
        opens = [r for r in by_prog[p] if r["kind"] == "cell" and r["state"] == "OPEN"]
        for r in opens[:12]:
            out.append(f"- OPEN [{r['seat'] or '?'}] {r['text'][:160]}" + (f" → `{r['target']}`" if r['target'] else "") + f"  ({r['board']}:{r['line']})")
        if len(opens) > 12: out.append(f"- … {len(opens) - 12} more in the shard")
        out.append("")
    ms = matches(recs)
    out += ["## Sequence matches across programs (proposals only; a seat decides join / analogy / rhyme)", ""]
    out += [f"- {m['a']} [{m['form_a']}] ~ {m['b']} [{m['form_b']}], {m['terms']} terms" for m in ms] or ["- none yet"]
    out.append("")
    open("center/VIEW.md", "w").write("\n".join(out))
    os.makedirs("center/views", exist_ok=True)   # outer edge: one generated view per program
    for p, rs in by_prog.items():
        v = [f"# {p} (generated by center.py; do not edit)", ""]
        for kind, title in [("finding", "Findings"), ("cell", "Cells"), ("fingerprint", "Fingerprints"), ("frame", "Frames")]:
            sel = [r for r in rs if r["kind"] == kind]
            if not sel: continue
            v.append(f"## {title}")
            for r in sorted(sel, key=lambda r: (r["radius"], r["id"])):
                tag = r.get("word") or r.get("state")
                extra = f" seq {r['seq'][:8]}" if kind == "fingerprint" else ""
                v.append(f"- [{tag}, r={r['radius']}] {r['text'][:200]}{extra}")
            v.append("")
        open(f"center/views/{p.replace('/', '_')}.md", "w").write("\n".join(v))
    return recs, summary

def check_outer():
    """Outer-edge sync: every file path an outer surface cites must exist. Reports drift; changes nothing."""
    import re as _re
    surfaces = ["README.md", "BOARD.md", "AGENTS.md"] + sorted(glob.glob("worlds/*.md") + glob.glob("*/README.md") + glob.glob("*/BASE.md") + glob.glob("boards/tasks/*.md"))
    pat = _re.compile(r"`([A-Za-z0-9_./\-]+\.(?:lean|py|md|ath|bench|json|jsonl|yml|png|svg))(?:::[A-Za-z0-9_.']+)?`")
    bad = []
    for f in surfaces:
        if not os.path.exists(f) or f == "worlds/SPHERE_LIT.md": continue   # SPHERE_LIT lists Mathlib file names, not repo paths
        for n, line in enumerate(open(f, encoding="utf-8"), 1):
            if any(t in line for t in ("Mathlib", "OPEN", "->", "→", "...", "planned", "not started")): continue   # targets still to be written, Mathlib names, elisions
            for m in pat.finditer(line):
                p = m.group(1)
                if p.startswith(("http", "~", "/")) or "*" in p: continue
                base = os.path.dirname(f)
                if not (os.path.exists(p) or os.path.exists(os.path.join(base, p)) or glob.glob("**/" + p, recursive=True)):
                    bad.append((f, n, p))
    return bad

if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        bad = check_outer()
        for f, n, p in bad: print(f"{f}:{n}: cites missing {p}")
        print(f"{len(bad)} stale outer references"); sys.exit(1 if bad else 0)
    if sys.argv[1:2] == ["queue"]:   # open frames by score; reads frames.jsonl only, builds nothing
        q = queue()
        for r in q: print(f"{r['score']:<10.4g} {r['claim']:24} {r['source'][:60]}  |  {r['reading'][:80]}")
        print(f"{len(q)} open frames"); sys.exit(0)
    if sys.argv[1:2] == ["test"]:   # 2. determinism: two builds of the same inputs give identical bytes
        import hashlib as _h
        def digest():
            h = _h.sha256()
            for f in sorted(glob.glob("center/shards/*.jsonl")) + ["center/VIEW.md", "center/state.json"]:
                h.update(open(f, "rb").read())
            return h.hexdigest()
        build(); d1 = digest(); build(); d2 = digest()
        assert d1 == d2, "centre is not deterministic"
        assert all(json.loads(l).get("schema") == SCHEMA for f in glob.glob("center/shards/*.jsonl") for l in open(f)), "a record without schema"
        print("determinism and schema checks passed", d1[:12]); sys.exit(0)
    if sys.argv[1:2] == ["snapshot"]:   # 3. manifest of the current store: hashes of every shard and view (no copies)
        import hashlib as _h, time as _t
        man = {f: _h.sha256(open(f, "rb").read()).hexdigest() for f in sorted(glob.glob("center/shards/*.jsonl")) + ["center/VIEW.md", "center/state.json"]}
        os.makedirs("center/snapshots", exist_ok=True)
        name = _t.strftime("center/snapshots/%Y%m%dT%H%M%SZ.json", _t.gmtime())
        json.dump({"schema": SCHEMA, "files": man}, open(name, "w"), indent=1, sort_keys=True)
        print("snapshot manifest", name, len(man), "files"); sys.exit(0)
    if sys.argv[1:2] == ["selftest"]:
        a = {"kind": "fingerprint", "program": "x", "text": "A", "seq": [1, 3, 7, 15, 31, 63, 127]}
        b = {"kind": "fingerprint", "program": "y", "text": "B", "seq": [9, 1, 3, 7, 15, 31, 63, 99]}
        c = {"kind": "fingerprint", "program": "z", "text": "C", "seq": [1, 1, 2, 4, 9, 21, 51, 127, 323]}
        m = matches([a, b, c])
        assert any(x["a"] == "A" and x["b"] == "B" for x in m), "planted match not found"
        assert not any("C" in (x["a"], x["b"]) for x in m), "false match on an unrelated sequence"
        print("matcher selftest passed"); sys.exit(0)
    recs, summary = build()
    if sys.argv[1:2] == ["ask"]:
        q = " ".join(sys.argv[2:]).lower()
        for r in recs:
            if q in r["text"].lower() and (r["kind"] == "finding" or r["state"] == "OPEN"):
                print(f"{r['kind']:8} {r.get('word') or r.get('state'):8} r={r['radius']:<5} {r['program']:16} {r['text'][:150]}")
    else:
        print(f"{len(recs)} records in {len(summary)} shards → center/VIEW.md")
