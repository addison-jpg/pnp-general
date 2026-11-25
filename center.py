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
  python3 -I center.py ask TEXT print the open cells and records whose text contains TEXT (a seat's one query)

Standard library only. It reuses boards.py's loader and its verification rule, so the two never disagree."""
import json, os, re, sys, glob, hashlib, importlib.util, collections

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
                      ("ath-prompt", "prompt-method"), ("ath_prompt", "prompt-method")]:
        if key in p: return name
    return "other"

def radius(rec):
    w = rec.get("word")
    if w == "checked" and not rec.get("why_not"): return 0.0
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
            rec["radius"] = radius(rec); out.append(rec)
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
            out.append(rec)
    return out

KINDS = {"finding": read_findings, "cell": read_cells}   # 3. a new dimension is one more entry here

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
    open("center/VIEW.md", "w").write("\n".join(out))
    return recs, summary

if __name__ == "__main__":
    recs, summary = build()
    if sys.argv[1:2] == ["ask"]:
        q = " ".join(sys.argv[2:]).lower()
        for r in recs:
            if q in r["text"].lower() and (r["kind"] == "finding" or r["state"] == "OPEN"):
                print(f"{r['kind']:8} {r.get('word') or r.get('state'):8} r={r['radius']:<5} {r['program']:16} {r['text'][:150]}")
    else:
        print(f"{len(recs)} records in {len(summary)} shards → center/VIEW.md")
