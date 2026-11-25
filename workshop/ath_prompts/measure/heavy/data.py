"""Inputs for the heavy instrument.

B1: Addison's 10 typed prompts (verbatim, from workshop/ath_prompts/research-seat.md) against the formal rewrites of
the first measurement (workshop/ath_prompts/measure/measure.py, FORMAL), plus the preferences block.

INTERCHANGE: five statements that exist in this repository as English, as an asteroid (.ath) claim and as a
Lean statement. Every string is copied from the file named next to it (Lean: the statement up to `:=`).
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "..", "research-seat.md")
MEASURE = os.path.join(HERE, "..", "measure.py")


def b1_pairs():
    txt = open(SRC, encoding="utf-8").read()
    prefs = "\n\n".join(l[2:] for l in txt.split("## Prompts, in order")[0].splitlines() if l.startswith("> "))
    items = {}
    for l in txt.split("## Prompts, in order")[1].split("## Counts")[0].splitlines():
        m = re.match(r'^- (?:2026-11-25 )?(\d\d:\d\d) > (.*)$', l)
        if m: items[m.group(1)] = m.group(2)
    # the formal rewrites are read out of measure.py without importing it (it loads a model at import)
    src = open(MEASURE, encoding="utf-8").read()
    ns = {}
    exec(src[src.index("FORMAL = {"):src.index("def parse")], ns)
    F, FP = ns["FORMAL"], ns["FORMAL_PREFS"]
    assert set(items) == set(F)
    return [(k, items[k], F[k]) for k in items], ("prefs", prefs, FP)


# (id, English, .ath, Lean). Sources:
#  or_n   English: README.md "What is proved" (several NOT gates); .ath: asteroid/demo.ath; Lean: Or4ManyNot.lean or_needs_gates
#  one_not English: asteroid/programs/theorem.ath line 2 (the Statement comment); .ath: same file, `conjecture theorem`;
#          Lean: one-not/lean/PEqualNP/W951/LiftBound.lean OneNotBound
#  correct / hyps / slack  English: README.md hello.ath comments; .ath: README.md hello.ath; Lean: one-not/lean/PEqualNP/W951/Asteroid_hello.lean
INTERCHANGE = [
    ("or_n",
     "The OR of n inputs needs n − 1 AND/OR gates with any number of NOT gates",
     "claim gates(demo) = base(demo)",
     "theorem or_needs_gates (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)\n"
     "    (hor : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i, x i = true)) :\n"
     "    n ≤ C.gates.countP counted + 1"),
    ("one_not",
     "a correct circuit with at most one NOT gate has gates(c) >= base(c) = sum over sets of (|S| - 1).",
     "conjecture theorem: gates(c) >= base(c)",
     "def OneNotBound : Prop :=\n"
     "  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) →\n"
     "    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →\n"
     "    ∀ (gates : List Gate) (out : Fin m → ℕ),\n"
     "    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧\n"
     "      g.inputs.length ≤ 2) →\n"
     "    AtMostOneNot gates →\n"
     "    (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) →\n"
     "    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length"),
    ("correct",
     "it computes both ORs on all 16 inputs",
     "claim correct(hello) by lean",
     "theorem hello_claim0 : correctB hello = true"),
    ("hyps",
     "the theorem's side conditions hold",
     "claim hyps(hello) by lean",
     "theorem hello_claim1 : hypsB hello = true"),
    ("slack",
     "the count behind the theorem, at every cube",
     "claim forall cubes slack(hello) >= 0 by lean",
     "theorem hello_claim2 : slackNonnegAll hello = true"),
]
