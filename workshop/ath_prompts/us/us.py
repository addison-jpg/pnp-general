#!/usr/bin/env python3
"""Look at us: asks (Addison's jobs) and seats (agent sizes) as a two-sided matching, on recorded data only. Analogy.
Data: the seat table in ath_prompt_method.md (Sonnet and Opus rows; the one Fable row is not a haiku/sonnet/opus
seat and is left out) and the C3 Haiku run (measure/trial/CLAUDE_HAIKU.md: 84 asks, about 65k tokens each, tested).
Preferences, from the data and nothing else:
 ask -> seat: a seat is acceptable to an ask only if the data records that seat on that ask; ranked by best recorded
   result (checked > checked lemmas > tested > obstacle), then by lower mean recorded tokens.
 seat -> ask: the asks it closed first (same result order), then lower mean recorded tokens. Capacity: the number of
   asks the data records for that seat. Blocking: check.py's `wants`, imported, on both sides.
Beauvoir condition: a frame whose worlds are asks, recorded runs, and one 'record' world (a finding or a written
follow-up line). ask -> its runs; run -> record when its result is a finding or the data records a follow-up line.
[]<>T is evaluated at every ask with beauvoir.py's own successor function (imported; its exhaustive check must pass).
Models recorded cost and results only. Run: python3 -I workshop/ath_prompts/us/us.py"""
import contextlib, importlib.util, io, json, os
H = os.path.dirname(os.path.abspath(__file__)); R = os.path.join(H, "..", "..", "..")
def load(p):
    s = importlib.util.spec_from_file_location(os.path.basename(p)[:-3], os.path.join(R, p)); m = importlib.util.module_from_spec(s)
    with contextlib.redirect_stdout(io.StringIO()): s.loader.exec_module(m)
    return m
L, B = load("culture/love/check.py"), load("core/ontology/beauvoir.py")
GRADE = {"checked": 3, "checked lemmas": 2, "tested": 1, "obstacle": 0}
# (run, seat, ask, tokens, result, follow-up line recorded in these files)
RUNS = [("A6", "sonnet", "one Lean lemma", 99716, "checked", 0), ("A8", "sonnet", "one Lean lemma", 84399, "checked", 0),
        ("A9", "sonnet", "two Lean lemmas", 91567, "checked", 0), ("A12", "sonnet", "two Lean lemmas", 89475, "checked", 0),
        ("A11", "sonnet", "one Lean conditional", 92533, "checked", 0), ("B8", "sonnet", "one Lean reduction", 86424, "checked", 0),
        ("A4", "opus", "open attack", 204309, "checked lemmas", 0), ("B5", "opus", "open attack", 211345, "checked lemmas", 0),
        ("A7", "opus", "one paper attempt", 149698, "obstacle", 0), ("A10", "opus", "one paper attempt", 146304, "obstacle", 0),
        ("C3", "haiku", "register trial (84 asks)", 65000, "tested", 1)]   # about 65k per ask; follow-up: "A harder set ... is needed"
def match(runs):
    """the recorded assignment, capacities, acceptable lists and blocking pairs for a list of runs"""
    asks = sorted({r[2] for r in runs}); rec = {}
    for _, s, a, t, res, _ in runs: rec.setdefault((a, s), []).append((GRADE[res], t))
    score = {p: (-max(g for g, _ in v), sum(t for _, t in v) / len(v)) for p, v in rec.items()}   # smaller is better
    acc = {a: sorted((s for s in SEATS if (a, s) in rec), key=lambda s: score[(a, s)]) for a in asks}
    assign = {a: next(r[1] for r in runs if r[2] == a) for a in asks}   # the seat each ask was first given
    cap = {s: sum(1 for a in asks if assign[a] == s) for s in SEATS}
    ra = [[acc[a].index(s) if s in acc[a] else 99 for s in SEATS] for a in asks]
    rb = [sorted(range(len(asks)), key=lambda i: score.get((asks[i], s), (9, 0))) for s in SEATS]
    rb = [[r.index(i) for i in range(len(asks))] for r in rb]
    held = {j: [i for i, a in enumerate(asks) if assign[a] == s] for j, s in enumerate(SEATS)}
    block = [(asks[i], s) for i, a in enumerate(asks) for j, s in enumerate(SEATS) if s in acc[a] and s != assign[a]
             and L.wants(ra, i, j, [SEATS.index(assign[a])], 1) and L.wants(rb, j, i, held[j], max(cap[s], 1))]
    return asks, assign, cap, acc, block
SEATS = ["haiku", "sonnet", "opus"]
asks, assign, cap, acc, block = match(RUNS)
# power check, not data: had a haiku seat recorded one checked Lean lemma at 60k tokens, that pair would block
assert match(RUNS + [("X", "haiku", "one Lean lemma", 60000, "checked", 0)])[4] == [("one Lean lemma", "haiku")]
W = asks + [r[0] for r in RUNS] + ["record"]; ix = {w: i for i, w in enumerate(W)}
Rel = {(ix[a], ix[r]) for r, _, a, *_ in RUNS} | {(ix[r], ix["record"]) for r, _, _, _, res, f in RUNS if GRADE[res] >= 1 or f}
B.R, B.n = Rel, len(W)                                       # beauvoir.py's succ reads its module's R and n
truth = {a: all(B.succ(v) for v in B.succ(ix[a])) for a in asks}   # []<>T at the ask: every reached run goes on
dead = [W[v] for a in asks for v in B.succ(ix[a]) if not B.succ(v)]
assert B.ok, "beauvoir.py's own check failed"
print(f"asks {len(asks)}, seats {SEATS}, capacity {cap}, longest acceptable list {max(map(len, acc.values()))}")
print(f"recorded assignment: {assign}\nblocking pairs: {block or 'none'} -> {'stable' if not block else 'not stable'}")
print(f"Beauvoir []<>T at each ask: {truth}\ndead ends (obstacle, no follow-up line in these files): {dead}")
fp = [{"name": "us: asks, seats, recorded runs", "seq": [len(asks), len(SEATS), len(RUNS)]},
      {"name": "us: longest acceptable seat list of an ask", "seq": [max(map(len, acc.values()))]},
      {"name": "us: blocking pairs of the recorded assignment", "seq": [len(block)]},
      {"name": "us: asks where the Beauvoir condition fails", "seq": [sum(not v for v in truth.values())]},
      {"name": "us: dead-end runs", "seq": [len(dead)]}]
for e in fp: e["runner"] = "python3 -I workshop/ath_prompts/us/us.py"
with open(os.path.join(H, "us_fingerprints.json"), "w", encoding="utf-8") as f: f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
print("PASS")
