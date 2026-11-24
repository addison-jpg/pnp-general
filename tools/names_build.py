#!/usr/bin/env python3
"""Builds NAMES.json (one flat tree: name -> {parent, kind, code, means}) and NAMES.md from it.
Bottom up: a leaf (witness, Lean theorem, dead route) points to its parent concept, up to the root.
Run from the repo root: python3 -I tools/names_build.py"""
import json, re, sys
ROOT = "one NOT gate saves nothing on Boolean sums"
N = {}
def add(name, parent, kind, code="", means=""):
    assert name not in N, name
    N[name] = {"parent": parent, "kind": kind, "code": code, "means": means}

add(ROOT, None, "statement", "951, L-meta-951",
    "sets of size >= 2 that pairwise share at most one point; a circuit of AND and OR gates and one NOT gate computes the OR of every set; then number of gates >= monotone optimum")

# ---- level 1: the five parts
O="objects"; F="facts of a minimal counterexample"; C="the count"; S="the point step"; G="the certificate game"; D="dead ends"; W="witness circuits"; L="checked in Lean"
add(O, ROOT, "part", "", "the things every statement is about")
add(F, ROOT, "part", "R1 to R7, MinCERed", "what a counterexample with the fewest gates must satisfy")
add(C, ROOT, "part", "MU", "some named family of gates has at least monotone-optimum members; this implies the statement")
add(S, ROOT, "part", "STEP, GainF2, GainOne", "prove the count one input at a time: setting some input to 1 removes at least cost-of-the-point gates from the family")
add(G, ROOT, "part", "U-game, Theorem G", "a pairwise test on the lifted outputs; when it is won the statement is checked in Lean")
add(D, ROOT, "part", "DEAD_ENDS.md", "refuted or exhausted routes, in seven families")
add(W, ROOT, "part", "951/data/witnesses", "correct circuits that refute a route; none refutes the statement")
add(L, ROOT, "part", "951/lean/PEqualNP/W951", "statements the Lean checker accepted")

# ---- objects
for name, code, means in [
 ("set system", "S_w", "the sets; any two share at most one point"),
 ("demand of a set", "d_w", "size of the set minus 1"),
 ("monotone optimum", "base", "sum of the demands; the exact gate count without a NOT gate (Wegener, Mehlhorn)"),
 ("NOT gate", "N", "the single NOT gate"),
 ("NOT input", "h", "the wire the NOT gate reads; a monotone function of the inputs"),
 ("face with the NOT gate set to 0", "C_0", "monotone circuit; never above the real circuit"),
 ("face with the NOT gate set to 1", "C_1", "monotone circuit; never below the real circuit"),
 ("world 0", "U, {h = 1}", "inputs where the NOT gate outputs 0"),
 ("world 1", "D, {h = 0}", "inputs where the NOT gate outputs 1"),
 ("cube", "Q, x_Q = 1", "the inputs with every point of Q set to 1"),
 ("alive set", "", "a set that does not meet Q"),
 ("monotone optimum of a cube", "base(Q), baseDQ", "sum of the demands of the alive sets"),
 ("local cube", "CubeLocal", "on the cube the NOT input is one input or constant"),
 ("non-local cube", "", "on the cube the NOT input depends on at least two inputs"),
 ("zero point of a set", "z, Z", "an input that is 0 on the whole set"),
 ("top zero point of a set", "top_w", "0 on the set, 1 everywhere else"),
 ("atom", "e_u, Z + e_u", "a zero point of a set with one point of the set switched on"),
 ("heavy point", "", "a point v with NOT input = 1 at Q + e_v"),
 ("cost of a point", "cost(v)", "sum of the demands of the alive sets through the point"),
 ("gain of a point", "gain(v)", "number of family gates that leave the family when the point is set to 1"),
 ("real merge set", "M_z(w)", "the OR gates that join two blocks of a set in a union-find run at a zero point; always demand-many (merge count lemma, Lemma M)"),
 ("pure class in world 0", "I0", "a class of a set read at a zero point in world 0"),
 ("pure class in world 1", "I1", "a class of a set read at a zero point in world 1"),
 ("lifted circuit", "lift, y", "the NOT gate replaced by a fresh input y; a monotone circuit for a partial function"),
 ("lifted class", "", "a class of a set read in the lifted circuit; need not sit above the zero point"),
 ("set of type A", "type A", "meaning not re-derived here: see CanonClass.lean and research-typeA-increment.md"),
 ("set of type B", "type B", "meaning not re-derived here: see fable-global-price.md"),
 ("output in two-world normal form", "DD, DD-normal", "the output equals (set OR) AND h on one face and (set OR) OR h on the other"),
]: add(name, O, "object", code, means)

# ---- facts
for name, code, means, st in [
 ("minimal counterexample", "MinCE", "a correct circuit with fewer gates than the monotone optimum and the fewest gates among such", "definition"),
 ("no constant gate", "R1, no_const", "", "checked"),
 ("no two gates compute the same function", "R2, no_dup", "", "checked"),
 ("no gate computes an input", "R3, no_var", "", "checked"),
 ("every gate is read", "R4, live", "", "checked"),
 ("the NOT gate is essential", "R5', not_used", "both faces are incorrect", "checked"),
 ("observability", "R+, observable", "a constant put on any nonempty set of readers of a wire makes the circuit incorrect", "checked"),
 ("no gate-saving rewiring", "R6, no_rewire", "no gate input can be moved to another wire so that the circuit stays correct and a gate goes unread", "paper; Lean local to another session"),
 ("private NOT cone", "R7", "meaning not re-derived here: see 951/FINDINGS_2026-11-24.md", "reported"),
]: add(name, F, "fact", code, (means+" " if means else "")+"["+st+"]")

# ---- the count: families and targets
for name, code, means in [
 ("one-face witness gates", "F1, UC", "OR gates that are 0 at a zero point of an alive set and 1 at two of its atoms, in one face"),
 ("real-witness gates", "F2", "the same with the real circuit in place of a face"),
 ("repaired one-face witness gates", "F3", "one-face witness gates with an extra condition on face 1 atoms"),
 ("cone-restricted one-face witness gates", "F4", "one-face witness gates inside the cone of the output of the witnessing set"),
 ("cone-restricted real-witness gates", "F5", "real-witness gates inside the cone of the output of the witnessing set"),
 ("disjoint representatives over real merge sets", "MergeSDR", "one real merge set per set, pairwise disjoint"),
 ("disjoint representatives over pure classes", "PureSDR", "one pure class per set, pairwise disjoint"),
 ("disjoint representatives over lifted classes", "LiftSDR", "one lifted class per set, pairwise disjoint"),
 ("lifted count", "MUL", "the union of lifted classes has at least monotone-optimum gates"),
 ("fractional merge matching", "MergeFrac, FracMatch", "weights on zero points with load at most 1 on every gate"),
 ("price inequality", "MergePrice", "for every price on gates, the cheapest classes together cost at most all gates"),
]: add(name, C, "target", code, means)

# ---- the step
for name, code, means in [
 ("point step for real-witness gates", "F2 STEP, GainF2", "some point has gain >= cost; false for all correct circuits, open among circuits with no gate-saving rewiring"),
 ("point step for one-face witness gates", "GainOne, LIGHT-COUNT, HEAVY-COUNT", "the same for one-face witness gates; refuted"),
 ("point deletion", "x_v := 0", "induction that sets a point to 0; refuted"),
 ("mixed induction", "", "set a point to 0 at some cubes and to 1 at others; not refuted, two circuits tested"),
 ("gate elimination step", "GE, ElimStep", "setting a point to 1 and simplifying removes at least cost-many gates; the inductive form of the statement"),
]: add(name, S, "target", code, means)

# ---- the game
for name, code, means in [
 ("lifted test system", "LTS", "a zero point and atoms chosen for a set in the lifted circuit"),
 ("pair certificate", "LTSCert", "for two sets: at most one atom of one system is not below the zero point of the other"),
 ("certificate game won", "U-game won", "every set has a system and every pair has a pair certificate in one direction"),
 ("certificate game theorem", "Theorem G, liftSDR_of_ugame", "game won => disjoint representatives over lifted classes => the statement; no minimality [checked]"),
 ("exact reach of value arguments", "Proposition S", "an argument reading only gate values at test points stops exactly at the game [paper]"),
 ("no mixing of worlds", "Theorem D", "with two-world normal outputs and sets of size >= 3 a winning choice stays in one world [paper]"),
 ("one colouring per merge gate", "Lemma T", "a merge gate splits every set it serves by one colouring; forbids odd cycles of 2-point traces only [paper]"),
 ("lost game", "open part (X)", "OPEN: circuits whose lifted outputs lose the game; smallest: sets {0,1,2}, {0,3,4}, NOT input x1 OR x3"),
]: add(name, G, "target", code, means)

# ---- Lean leaves
for name, parent, means in [
 ("no_minCE", ROOT, "the one unproved declaration under L-meta-951"),
 ("no_minCE_of_ugame", "certificate game theorem", "UGame.lean"),
 ("ugame_of_G1 / ugame_of_G0 / ugame_of_allHeavy / ugame_of_typeB", "certificate game won", "four cases where the game is always won"),
 ("no_minCE_of_gainF2_or_cubeLocal", "point step for real-witness gates", "CubeF2.lean:353: local cube or point step at every cube => the statement"),
 ("muF2_of_notVar", "local cube", "NotVarF2: the statement when the NOT gate reads an input"),
 ("small3_bound", L, "the statement when every set has at most 3 points"),
 ("bound_of_noDD", L, "TwoWorld.lean: the bound when no output is in two-world normal form"),
 ("partial_bound", L, "PartialBound.lean"),
 ("merge_run", "real merge set", "MergeRun.lean: the merge count lemma"),
 ("canon_size / canon_disjoint / canon_cross", "pure class in world 1", "CanonClass.lean"),
 ("lAvoid", "disjoint representatives over real merge sets", "Augment.lean"),
]: add(name, parent, "lean", name, means)

# ---- dead-end families (rows stay in 951/DEAD_ENDS.md)
fam = [
 ("class chosen without looking at the other sets", "A", "disjoint representatives over pure classes"),
 ("rule fixing the world of a set", "B", "world 0"),
 ("counting over pure classes for all correct circuits", "C", "disjoint representatives over pure classes"),
 ("counting over real merge sets without minimality", "D", "disjoint representatives over real merge sets"),
 ("induction one input at a time for all correct circuits", "E", S),
 ("local or memoryless argument", "F", "gate elimination step"),
 ("method from outside circuits", "G", ROOT),
]
for name, code, hits in fam:
    add(name, D, "dead family", "family "+code, "kills: "+hits+"; rows in 951/DEAD_ENDS.md section "+code)

# ---- witnesses (leaf -> the dead family it feeds)
for name, code, parent, means in [
 ("Fano formula with an unused NOT gate", "FANO-FORMULA, fano_formula.json", fam[4][0], "17 gates; kills point deletion"),
 ("Pappus configuration with junk gates", "PAPPUS-JUNK, pappus_junk_gain.json", fam[4][0], "n = 9, 66 gates; kills the point step for one-face witness gates"),
 ("twin balanced OR trees with leaf junk", "TWIN-TREE, twin_tree_f2step.json", fam[4][0], "n = 14, 28 gates; kills the point step for real-witness gates; every cube is local"),
 ("twin trees with the NOT gate read", "TWIN-TREE-N, twin_tree_N_f2step.json", fam[4][0], "30 gates; the NOT gate reads one input"),
 ("matched twin trees with a 14-input NOT input", "MATCH-C, nonlocal/match_c_k7.json", fam[4][0], "n = 16, 55 gates; kills the step at a non-local cube under R1 to R5' and R+; has a gate-saving rewiring; certificate game won"),
 ("two two-world sets sharing one merge gate", "cxMU_dd, cxMU_clean2, cxMU_clean2_DD", fam[2][0], "n = 7, 36 gates; pure classes cover 5 < 6; loses the certificate game"),
 ("Pasch configuration with a doubly served class", "tri_all_5593.json", fam[2][0], "kills the looseness lemma"),
 ("two 4-sets with junk", "cx44_1_junk.json", fam[2][0], "loses the certificate game"),
 ("Pasch configuration, 14 gates, heavy point", "pasch_s14_heavy_atmostone.json", fam[1][0], "kills 'at most one world-0 set through a heavy point'"),
 ("five-input circuit where only a light point works", "ess_rand_clean_744.json", fam[1][0], "n = 5, 9 gates; violates no fact of a minimal counterexample that scaffold tested"),
 ("star of four pairs with a threshold NOT input", "STAR4, star4.json; STAR4b, star4b_threshold.json", fam[3][0], "real merge sets cover 2 < 3 (threshold crossing)"),
 ("selector path", "selector path", fam[3][0], "kills bounded augmenting for all correct circuits"),
 ("three 4-sets in a triangle", "cxT2", fam[0][0], "n = 9; no gate-saving rewiring found in 1,679 tries; loses the certificate game; the hard core named by cTAHG"),
 ("inner-product junk design", "cxr", fam[3][0], "kills 'later merge gates of different sets are disjoint'"),
 ("adversary against the two-point menu", "ADV3", fam[0][0], "load 1.2"),
 ("adversary against the general world laws", "ADV4", fam[1][0], ""),
 ("junk circuit where a light point fails", "JUNK, junk.json", fam[4][0], ""),
 ("five-input gap for seen gates", "see_gap_n5.json", fam[4][0], "meaning not re-derived here"),
]: add(name, parent, "witness", code, means)

for k, v in N.items():
    assert v["parent"] is None or v["parent"] in N, (k, v["parent"])
json.dump(N, open("NAMES.json", "w"), indent=1, ensure_ascii=False)

kids = {}
for k, v in N.items(): kids.setdefault(v["parent"], []).append(k)
out = ["# Names", "", "Generated from `NAMES.json` by `tools/names_build.py`; edit the script, not this file.",
       "One flat tree: every name has one parent. Read bottom up: a witness or a Lean theorem is a leaf,",
       "its parent is the concept it serves, up to the root statement. `code` is the old short form.", ""]
def walk(k, d):
    v = N[k]
    out.append("  " * d + f"- **{k}**" + (f" (`{v['code']}`)" if v["code"] and v["code"] != k else "") + f" · {v['kind']}" + (f": {v['means']}" if v["means"] else ""))
    for c in kids.get(k, []): walk(c, d + 1)
walk(ROOT, 0)
open("NAMES.md", "w").write("\n".join(out) + "\n")

# coverage: which code-like tokens of the key documents have no name yet
codes = " ".join(v["code"] + " " + k for k, v in N.items())
docs = ["951/DEAD_ENDS.md", "COLLATION_2026-11-24.md", "951/FINDINGS_2026-11-24.md"]
tok = {}
for d in docs:
    for t in re.findall(r"\b(?:cx[A-Za-z0-9_]+|[A-Z][A-Za-z]*[0-9][A-Za-z0-9']*|[A-Z]{2,}(?:-[A-Z0-9]+)+|[A-Z][a-z]+[A-Z][A-Za-z0-9]*)\b", open(d).read()):
        tok[t] = tok.get(t, 0) + 1
miss = sorted(((c, t) for t, c in tok.items() if t not in codes), reverse=True)
print(len(N), "names;", len(tok) - len(miss), "of", len(tok), "code tokens of", len(docs), "documents named")
print("unnamed, most used:", " ".join(f"{t}({c})" for c, t in miss[:40]))
