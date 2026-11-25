#!/usr/bin/env python3
"""Anti-fascist formalization: two exact finite checks and one crude keyword detector.

Part A (checked-finite). Beauvoir reading: refusal of reciprocity. On every Kripke frame on 2..4 worlds and every
class C of worlds where each c in C reaches every world and no world other than c reaches c, the B axiom
p -> []<>p fails at every c in C (some valuation). Exhaustive, nothing sampled.
Part B (checked-finite). Deleuze-Guattari reading: a single critical centre. On every labelled graph on 3..6
vertices: a connected graph has a vertex whose removal leaves only isolated points, with every edge critical,
exactly when it is the star. Counted exactly.
Part C (tested, crude). A keyword detector over the feature names of Eco (1995) and Stanley (2018), paraphrased.
It flags text for a person to review. It is never a verdict on a person or a group. Measured on a small
synthetic labelled set written here; then run on center/shards/*.jsonl and workshop/compute/monqwensor/proposals.json.
Run: python3 -I philosophy/antifascism.py   (last line is JSON)
"""
import itertools, json, re, glob, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def b_fails_at(n, R, c):
    # B fails at c iff some w with cRw has no way back to c (take p = {c}).
    return any((c, w) in R and (w, c) not in R for w in range(n))

def part_a():
    frames = classes = 0
    for n in range(2, 5):
        pairs = [(a, b) for a in range(n) for b in range(n)]
        for mask in range(1 << len(pairs)):
            R = {p for k, p in enumerate(pairs) if mask >> k & 1}
            dom = [c for c in range(n) if all((c, w) in R for w in range(n))
                   and not any((w, c) in R for w in range(n) if w != c)]
            frames += 1
            for size in range(1, len(dom) + 1):
                for C in itertools.combinations(dom, size):
                    classes += 1
                    assert all(b_fails_at(n, R, c) for c in C), "part A fails"
    return frames, classes

def connected(n, adj, skip=-1):
    vs = [v for v in range(n) if v != skip]
    if not vs: return True
    seen, todo = {vs[0]}, [vs[0]]
    while todo:
        v = todo.pop()
        for w in adj[v]:
            if w != skip and w not in seen: seen.add(w); todo.append(w)
    return len(seen) == len(vs)

def part_b():
    stars = 0
    for n in range(3, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            E = [p for k, p in enumerate(pairs) if mask >> k & 1]
            adj = {v: set() for v in range(n)}
            for a, b in E: adj[a].add(b); adj[b].add(a)
            if not connected(n, adj): continue
            centre = any(len(adj[v]) == n - 1 and len(E) == n - 1 for v in range(n))
            def crit(e):
                a, b = e; adj[a].discard(b); adj[b].discard(a)
                r = not connected(n, adj); adj[a].add(b); adj[b].add(a); return r
            # removing v leaves only isolated points: every edge touches v
            shatter = any(all(v in e for e in E) for v in range(n)) and all(crit(e) for e in E)
            assert shatter == centre, "part B fails"
            stars += centre
    return stars  # n stars per n: 3+4+5+6

# Part C: marker sets, written openly. Feature names paraphrased; patterns are ours.
MARKERS = {
    "cult of tradition / mythic past": [r"\bglorious past\b", r"\brestore (our|the) (true )?greatness\b", r"\bpure origins?\b"],
    "rejection of modernity / anti-intellectualism": [r"\bintellectuals? (are|is) (the )?(enem|traitor|poison)", r"\bthinking is weakness\b"],
    "disagreement as treason": [r"\bdissent(ers)? (is|are) treason\b", r"\btraitors? (within|among us)\b"],
    "fear of difference / us vs them": [r"\bgroup x (is|are) (vermin|a disease|an infestation|subhuman)\b", r"\bthey are not (really )?(people|human)\b"],
    "obsession with a plot": [r"\bsecret plot\b", r"\b(they|group x) secretly control\b", r"\bhidden cabal\b"],
    "enemy both too strong and too weak": [r"\bweak and degenerate\b.*\bcontrol everything\b"],
    "life as permanent war / violence": [r"\bmust be (purged|eliminated|cleansed)\b", r"\bdrive them out by force\b"],
    "cult of the leader / one will": [r"\bthe leader alone (speaks|knows)\b", r"\bone people,? one leader\b"],
    "victimhood / sexual anxiety (Stanley)": [r"\bthey are replacing us\b", r"\bprotect our women from\b"],
    "law and order against a named group (Stanley)": [r"\bgroup x (is|are) (inherently )?criminal\b"],
}
COMPILED = {f: [re.compile(p, re.I) for p in ps] for f, ps in MARKERS.items()}

def score(text):
    return {f: sum(bool(p.search(text)) for p in ps) for f, ps in COMPILED.items() if any(p.search(text) for p in ps)}

LABELLED = [  # (synthetic sentence, 1 = flag-worthy). No real quotes, no real groups.
    ("Group X are vermin and must be purged from the town.", 1),
    ("Dissenters are treason and the leader alone knows the way.", 1),
    ("A secret plot by group X controls the banks.", 1),
    ("They are replacing us, and we must restore our true greatness.", 1),
    ("Group X are inherently criminal and they are not really people.", 1),
    ("Traitors within must be eliminated before the vote.", 1),
    ("A hidden cabal decides every election.", 1),
    ("Intellectuals are the enemy of the nation.", 1),
    ("They are weak and degenerate, yet they control everything.", 1),
    ("Our tradition says group X is a disease on the land.", 1),
    ("The committee met to discuss the library budget.", 0),
    ("Historians study the past to understand propaganda.", 0),
    ("The novel describes a secret garden behind the school.", 0),
    ("Group X won the regional chess tournament.", 0),
    ("We disagree about tax policy and will debate it on Friday.", 0),
    ("The leader of the hiking club planned the route.", 0),
    ("This essay explains how a plot works in a detective story.", 0),
    ("Weeds must be eliminated from the garden in spring.", 0),
    ("The museum restored the painting to its original colours.", 0),
    ("Researchers compared reciprocity in two small frames.", 0),
]

def part_c():
    tp = fp = fn = tn = 0; misses = []
    for s, y in LABELLED:
        f = bool(score(s))
        tp += f and y; fp += f and not y; fn += (not f) and y; tn += (not f) and not y
        if f != bool(y): misses.append(s)
    return dict(tp=tp, fp=fp, fn=fn, tn=tn, precision=tp / max(1, tp + fp), recall=tp / max(1, tp + fn),
                fpr=fp / max(1, fp + tn), misses=misses)

def strings(o):
    if isinstance(o, str): yield o
    elif isinstance(o, dict):
        for v in o.values(): yield from strings(v)
    elif isinstance(o, list):
        for v in o: yield from strings(v)

def part_d():
    recs = flagged = 0; hits = []
    for path in sorted(glob.glob(os.path.join(ROOT, "center/shards/*.jsonl"))):
        for line in open(path, encoding="utf-8"):
            line = line.strip()
            if not line: continue
            try: r = json.loads(line)
            except ValueError: continue
            recs += 1; s = score(" ".join(strings(r)))
            if s: flagged += 1; hits.append((os.path.basename(path), r.get("id"), s))
    p = os.path.join(ROOT, "workshop/compute/monqwensor/proposals.json")
    prop = json.load(open(p, encoding="utf-8")); ps = list(strings(prop))
    pflag = [t[:80] for t in ps if score(t)]
    return recs, flagged, hits, len(ps), pflag

def main():
    fa, ca = part_a(); sb = part_b(); c = part_c(); recs, fl, hits, np_, pf = part_d()
    print(f"A Beauvoir: {fa} frames on 2..4 worlds, {ca} dominating classes; B fails at every member. checked-finite")
    print(f"B rhizome: single shattering centre with every edge critical iff star; {sb} stars on 3..6 vertices. checked-finite")
    print(f"C detector (tested, crude, flags for human review only): TP {c['tp']} FP {c['fp']} FN {c['fn']} TN {c['tn']}; "
          f"precision {c['precision']:.2f} recall {c['recall']:.2f} false-positive rate {c['fpr']:.2f}; misses {c['misses']}")
    print(f"D corpus: {fl} of {recs} center records flagged; {len(pf)} of {np_} proposal strings flagged")
    for h in hits: print("  flag (for a person to judge):", h)
    for t in pf: print("  proposal flag:", t)
    print("parts A and B exhaustive; part C measured (tested, not checked)"); print("PASS")
    print(json.dumps({"ok": True, "frames_a": fa, "classes_a": ca, "stars_b": sb, "precision": c["precision"],
                      "recall": c["recall"], "fpr": c["fpr"], "records": recs, "flagged": fl,
                      "proposal_strings": np_, "proposal_flagged": len(pf)}))

if __name__ == "__main__":
    main()
