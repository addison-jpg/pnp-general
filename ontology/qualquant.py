"""Generalized qual-quant: which kinds of frame close? Standard library only, exact fractions.

Reads frames.jsonl (every frames*.ath writes there). Each frame gets one type:
- structure: the reading names a finite mathematical object or relation that a program can enumerate.
- effect: the reading claims a measured effect of an intervention (needs runs, data, or a model).
- contested: the reading is a question of interpretation (meaning, history of ideas, metaphysics)
  that no finite check decides.
Rules, in order, applied by code to the fields (reading and source):
  1. hand overrides below, each with its reason;
  2. effect if the reading has a word from EFFECT;
  3. contested if the claim is none and the reading has a word from CONTESTED;
  4. structure otherwise.
Closed means status TRUE (a passing check); open means status OPEN.
The qual-quant frame itself is left out, so it does not count itself.
"""
import json, os, sys
from fractions import Fraction as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EFFECT = ("succeed", "fewer corrections", "cut duplicates")
CONTESTED = ("contested", "song means", "which measure", "history-of-ideas", "fixed idea", "reading")
HAND = {  # substring of source -> (type, reason)
    "Stirner": ("contested", "a history-of-ideas claim; needs sources read, not a computation"),
    "lineage of 1, 2": ("structure", "a DAG of re-recordings is a finite object; it is open for want of dated edges, not of a method"),
    ".ath mirrors ~ATH": ("structure", "halting under size limits is a property of the program; open only because no check is written"),
    "the meteor": ("structure", "a transport map between two finite rule sets; open because the map is not written"),
}

def classify(r):
    for k, (t, why) in HAND.items():
        if k in r["source"]: return t, "hand: " + why
    rd = r["reading"]
    if any(w in rd for w in EFFECT): return "effect", "rule 2"
    if r["claim"] == "none" and any(w in rd for w in CONTESTED): return "contested", "rule 3"
    return "structure", "rule 4"

def main():
    rows = [json.loads(l) for l in open(os.path.join(ROOT, "frames.jsonl"), encoding="utf-8")]
    rows = [r for r in rows if "qual-quant" not in r["source"]]
    by = {"structure": [], "effect": [], "contested": []}
    for r in rows:
        t, why = classify(r); by[t].append((r, why))
    ok = sum(len(v) for v in by.values()) == len(rows)
    rate = {}
    print(f"n = {len(rows)} frames (small; the rates below describe this repo, not a law)")
    for t, v in by.items():
        closed = sum(r["status"] == "TRUE" for r, _ in v)
        rate[t] = F(closed, len(v)) if v else None
        print(f"\n{t}: {closed} closed of {len(v)} = {rate[t]}")
        for r, why in v:
            print(f"  [{r['status']:4}] {r['source'][:70]}  ({why})")
    s, c = rate["structure"], rate["contested"]
    ok &= s is not None and c is not None and s > c
    print(f"\nrule (measured): structure closes at {s}, contested at {c}, effect at {rate['effect']}")
    print("PASS" if ok else "FAIL")
    return ok

if __name__ == "__main__":
    sys.exit(0 if main() else 1)
