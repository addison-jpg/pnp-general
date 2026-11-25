#!/usr/bin/env python3
"""Tests for route.py on a fixture ROOT. Script; exit 1 on any FAIL. Run: python3 -I core/ontology/test_route.py"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROUTE = os.path.join(HERE, "route.py")
fails = 0
def want(name, ok, extra=""):
    global fails
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else f"\n   {extra[-600:]}")); fails += not ok
def run(q, root):
    r = subprocess.run([sys.executable, "-I", ROUTE, *q.split()], capture_output=True, text=True, env=dict(os.environ, ASK_ROOT=root))
    return r.returncode, r.stdout
def snap(d): return sorted((p, os.path.getsize(os.path.join(dp, p)), os.path.getmtime(os.path.join(dp, p))) for dp, _, fs in os.walk(d) for p in fs)

with tempfile.TemporaryDirectory() as fx:
    os.makedirs(os.path.join(fx, "a")); os.makedirs(os.path.join(fx, "b"))
    open(os.path.join(fx, "a", "small.py"), "w").write("print('PASS')\n")
    open(os.path.join(fx, "b", "big.py"), "w").write("x = 1\n" * 50)
    open(os.path.join(fx, "RESULTS.md"), "w").write("\n".join([
        "| label | statement | evidence | recheck |", "|---|---|---|---|",
        "| tested | a sampled time fact | `b/big.py` | `python3 -I b/big.py` |",
        "| checked-finite | a long exact time fact | `b/big.py` | `python3 -I b/big.py` |",
        "| checked-finite | a short exact time fact | `a/small.py` | `python3 -I a/small.py` |",
        "| checked | a Lean time fact | `x.lean` |  |",
        "| refuted | a refuted time claim; rm -rf / | `a/small.py` | `python3 a/small.py; rm -rf /` |",
        "| checked-finite | a time path escape | `a/small.py` | `python3 -I ../../etc/passwd.py` |",
        "| checked-finite | an unrelated fact about trees | `a/small.py` | `python3 -I a/small.py` |", ""]))
    before = snap(fx)
    c, o = run("what is verified about time", fx)
    want("routes a known form, exit 0", c == 0 and "route: 'about_verified'" in o, o)
    want("exact checks come first, the shorter script first", o.find("a/small.py") < o.find("b/big.py") < o.find("[refuted]"), o)
    want("the same script is listed once (first label kept: checked-finite before tested)", o.count("python3 -I b/big.py") == 1 and "[checked-finite] recheck: python3 -I b/big.py" in o, o)
    want("cost is a line count, said to be a proxy", "script is 1 lines; a proxy for cost" in o and "script is 50 lines" in o, o)
    want("a row with no recheck is not listed", "Lean time fact" not in o, o)
    want("a command that is not plain is shown as text, not as a command", "not a plain command: `python3 a/small.py; rm -rf /`" in o, o)
    want("a path outside ROOT has no cost and is not opened", "../../etc/passwd.py  (path is outside the repository or missing; not opened)" in o and "1000000000" not in o, o)
    want("a row whose statement does not mention the word is left out", "trees" not in o, o)
    c, o = run("status", fx)
    want("no WORD: says no recheck is matched", c == 0 and "no WORD in this question" in o, o)
    c, o = run("explain dragons", fx)
    want("no match: says so, exit 0", c == 0 and "no recorded recheck in RESULTS.md mentions dragons" in o, o)
    c, o = run("gibberish words here", fx)
    want("unparseable: did not understand, grammar, exit 2", c == 2 and "did not understand" in o and "Grammar" in o, o)
    c, o = run("explain $(touch " + fx + "/pwned)", fx)
    want("a shell word is refused and nothing runs", c == 2 and not os.path.exists(os.path.join(fx, "pwned")), o)
    c, o = run("x " * 400, fx)
    want("very long input is refused", c == 2, o)
    want("no file in ROOT changed", snap(fx) == before)
print("\nall passed" if not fails else f"\n{fails} FAILED"); sys.exit(1 if fails else 0)
