#!/usr/bin/env python3
"""Anti-~ATH: adversarial programs against asteroid's stated guarantees.

~ATH loops until a death. asteroid says the opposite of itself: every claim halts by a size limit, a program
cannot run anything but a repository check, and a record or frame cannot claim more than its claims support.
This script writes adversarial .ath programs into a scratch directory and runs each through
`bin/asteroid --no-lean` with an outer timeout. Three families:
  1 halting     huge formulas, maximal Kripke sets, long lines, loops of frame files and of checks.
                Pass: the run ends within the outer timeout, with a refusal or FALSE, and no Python traceback.
  2 no escape   check / seq run with shell syntax, other interpreters, paths outside the repository, symlinks.
                Each attack would create a marker file in the scratch directory. Pass: no marker.
  3 no removal  records and frames stronger than their claims, records with no claim, duplicates,
                ASTEROID_FRAMES aimed at a findings file. Pass: refusal or downgrade, and no change to any
                findings.jsonl or frames.jsonl of the repository (hashed before and after).
Every attack is harmless if it succeeded: it writes only inside the scratch directory, never deletes, never uses
the network. Child runs use the scratch directory as their working directory.
This is a test, not a proof: halting in general is undecidable. It tests asteroid's stated guarantees only.
Run: python3 -I asteroid/tests/test_anti_ath.py   (ANTI_ATH_DIR picks the scratch directory). Exit 1 on FAIL."""
import concurrent.futures, os, shutil, signal, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.path.join(ROOT, "bin", "asteroid")
OUTER = 120                     # seconds; past this the run counts as a hang
SCR = os.environ.get("ANTI_ATH_DIR") or tempfile.mkdtemp(prefix="anti-ath-")
SCR = os.path.join(os.path.abspath(SCR), "run-%d" % os.getpid())
os.makedirs(SCR)
FAILS, PASSES = [], []

def want(name, ok, info=""):
    (PASSES if ok else FAILS).append(name)
    if not ok: print("FAIL " + name + ("  |  " + info if info else ""))

def snapshot():
    """The lines of every findings.jsonl and frames.jsonl in the repository."""
    out = {}
    for d, dirs, files in os.walk(ROOT):
        dirs[:] = [x for x in dirs if x not in (".git", ".lake", "node_modules", "__pycache__", ".venv")]
        for f in files:
            if f in ("findings.jsonl", "frames.jsonl"):
                p = os.path.join(d, f); out[os.path.relpath(p, ROOT)] = set(open(p, "rb").read().decode("utf-8", "replace").splitlines())
    return out

def write(rel, text):
    p = os.path.join(SCR, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8", newline="") as fh: fh.write(text)
    return p

def run(prog, env_extra=None):
    """Run one program; returns (rc, output, seconds, timed_out)."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("ASTEROID_")}
    env["ASTEROID_FRAMES"] = os.path.join(SCR, "frames_test.jsonl")
    env.update(env_extra or {})
    t0 = time.time()
    p = subprocess.Popen(["sh", BIN, "--no-lean", "--no-color", prog], cwd=SCR, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
    try: out, _ = p.communicate(timeout=OUTER); hung = False
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, _ = p.communicate(); hung = True
    return p.returncode, out.decode("utf-8", "replace"), round(time.time() - t0, 1), hung

def rel_from_root(p): return os.path.relpath(p, ROOT)

# ---------------------------------------------------------------- family 1: halting
def halting_cases():
    C = {}
    F = lambda e, s="[1]": f'seq s = {s}\nclaim formula s = "{e}"\n'
    for e in ["1000000!", "(10**6)!!", "C(1000000, 500000)", "(2**100000)**100000", "2**100000**2", "(n*10**5)!",
              "sum(i, 1, 1000000, sum(j, 1, 1000000, 1))", "sum(i, 1, 10**12, 0)", "sum(i, 1, 1000000, 10**99999)",
              "sum(i, 1, 1000000, (2**99999)**10 // (2**99999)**5)", "sum(i, 1, 1000000, 30000!)",
              "sum(i, 1, 1000000, C(100000, 50000))", "sum(i, 1, 1000000, (10**99999 + i) * (10**99999 + i))",
              "(" * 5000 + "1" + ")" * 5000, "-" * 20000 + "1", "2**" * 5000 + "2", "1+" * 100000 + "1",
              "sum(a,1,9,sum(b,1,9,sum(c,1,9,sum(d,1,9,sum(e,1,9,sum(f,1,9,sum(g,1,9,sum(h,1,9,n!!))))))))"]:
        C["formula " + e[:40]] = F(e)
    C["formula on 10 terms of (n*10^5)!"] = F("(n*100000)!", "[" + ", ".join(["1"] * 10) + "]")
    C["30 claims at the step limit"] = "seq s = [1]\n" + 'claim formula s = "sum(i, 1, 1000000, 10**99999)"\n' * 30
    C["30 claims of long division"] = "seq s = [1]\n" + 'claim formula s = "sum(i, 1, 1000000, (3**60000)**10 // (3**60000))"\n' * 30
    big = "[" + ", ".join(str(i) for i in range(10**6)) + "]"
    C["seq literal of 10^6 terms, partial sums"] = f"seq a = {big}\nseq b = {big}\nclaim a matches b partial\nclaim a = {big}\n"
    C["seq literal with a 10^5-digit term"] = "seq a = [" + "9" * 100000 + "]\nclaim a = [1]\n"
    C["seq literal of 10^6 spaces"] = "seq a = [1" + " " * 10**6 + "]\nclaim a = [1]\n"
    C["kripke all 4 any, 3 atoms"] = 'kripke K = all 4 any\nclaim valid K "p | q | r | ~p"\n'
    C["kripke all 4 any, 1 atom, 400 negations"] = 'kripke K = all 4 any\nclaim valid K "' + "~~" * 200 + '(p | ~p)"\n'
    C["kripke 40 valid claims at the limit"] = 'kripke K = all 4 any\n' + 'claim valid K "[]p -> [][]p | ~[]p"\n' * 40
    C["kripke defines on all 4 any, big formula"] = 'kripke K = all 4 any\nclaim defines K "' + "[]" * 300 + 'p -> p" reflexive\n'
    C["kripke 5000 nested boxes"] = 'kripke K = all 2 any\nclaim valid K "' + "[]" * 5000 + 'p"\n'
    C["kripke 3000 nested parentheses"] = 'kripke K = all 2 any\nclaim valid K "' + "(" * 3000 + "p" + ")" * 3000 + '"\n'
    C["kripke 12 worlds, 4 atoms"] = 'kripke K = worlds 12 rel [' + ", ".join(f"({i},{j})" for i in range(12) for j in range(12)) + ']\nclaim valid K "p | q | r | s"\n'
    C["kripke all 5"] = 'kripke K = all 5 any\nclaim valid K "p | ~p"\n'
    C["kripke all 12"] = 'kripke K = all 12 any\nclaim valid K "p | ~p"\n'
    C["very long claim line of spaces"] = "claim x" + " " * 300000 + "y\n"
    C["very long claim ending in by lean"] = "seq s = [1]\nclaim s = [1]" + " " * 300000 + "by lean\n"
    C["very long frame line"] = 'seq s = [1]\nclaim s = [1]\nframe "' + "a " * 200000 + '" reading "' + "b " * 200000 + '" -> 2 label open\n'
    C["very long record line"] = 'record ' + os.path.join(SCR, "rec", "long") + ' x tested "' + "c " * 300000 + '"\n'
    C["very long kripke rel"] = "kripke K = worlds 3 rel [" + "(0,1), " * 200000 + "(1,2)]\n"
    C["very long cannot-parse line"] = "frame " + '"' * 300000 + "\n"
    C["prob huge dist"] = "dist D = {" + ", ".join(f"x{i}: 1/100000" for i in range(100000)) + "}\nclaim expect D = 1\n"
    C["prob product of 1000 x 1000 x 1000"] = "dist D = {" + ", ".join(f"{i}: 1/1000" for i in range(1000)) + "}\ndist E = D * D\ndist G = E * D\nclaim expect G = 1\n"
    C["prob probability with 10^5 digits"] = "dist D = {a: " + "1" * 100000 + "/" + "1" * 100000 + "}\n"
    C["prob product of big dists"] = "dist D = {" + ", ".join(f"{i}: 1/2000" for i in range(2000)) + "}\ndist E = D * D\ndist G = E * D\nclaim expect G = 1\n"
    return C

def frame_file_cases():
    """Loops and fans of frame files, and loops of checks that run asteroid on themselves."""
    C = {}
    claim = "seq s = [1]\nclaim s = [1]\n"
    write("loop/a.ath", claim + 'frame "a" reading "a" -> b.ath label open\n')
    write("loop/b.ath", claim + 'frame "b" reading "b" -> a.ath label open\n')
    C["frame files a -> b -> a"] = os.path.join(SCR, "loop/a.ath")
    write("self/s.ath", claim + 'frame "s" reading "s" -> s.ath label open\n')
    C["frame file -> itself"] = os.path.join(SCR, "self/s.ath")
    for i in range(8): write(f"chain/c{i}.ath", claim + f'frame "c" reading "c{i}" -> c{i + 1}.ath label open\n')
    write("chain/c8.ath", claim)
    C["frame files nested 8 deep"] = os.path.join(SCR, "chain/c0.ath")
    k = 12
    for i in range(k): write(f"fan/f{i}.ath", claim + "".join(f'frame "f" reading "f{i}-{j}" -> f{j}.ath label open\n' for j in range(k)))
    C["frame fan: 12 files, each -> all 12"] = os.path.join(SCR, "fan/f0.ath")
    me = os.path.join(SCR, "chk/self.ath")
    write("chk/self.ath", claim + f'check "python3 -I asteroid/asteroid.py --no-lean {me}"\n')
    C["check runs asteroid on itself"] = me
    fan = os.path.join(SCR, "chk/fan.ath")
    write("chk/fan.ath", claim + f'check "python3 -I asteroid/asteroid.py --no-lean {fan}"\n' * 10)
    C["10 checks, each runs asteroid on itself"] = fan
    sq = os.path.join(SCR, "chk/seq.ath")
    write("chk/seq.ath", claim + f'seq t = run "python3 -I asteroid/asteroid.py --no-lean {sq}"\n')
    C["seq run of asteroid on itself"] = sq
    return C

def halting_ok(rc, out, hung):
    if hung: return False, "outer timeout: a hang"
    if "Traceback" in out: return False, "a Python traceback, not a clean refusal"
    return True, ""

# ---------------------------------------------------------------- family 2: no escape
def escape_cases():
    C = []
    evil = write("esc/evil.py", "import sys\nopen(sys.argv[1] if len(sys.argv) > 1 else __file__ + '.marker', 'w').write('x')\nprint('PASS')\n")
    os.symlink(evil, os.path.join(SCR, "esc", "link.py"))
    os.symlink(ROOT, os.path.join(SCR, "esc", "repo"))
    ok_check = "python3 -I asteroid/tests/test_prob.py"
    for i, tpl in enumerate([
        "{ok}; touch {M}", "{ok} && touch {M}", "{ok} | touch {M}", "{ok} $(touch {M})", "{ok} `touch {M}`",
        "{ok} || touch {M}", "{ok} > {M}", "touch {M}", "sh -c 'touch {M}'", "bash -c \\x22touch {M}\\x22",
        "python3 -c 'open(\\x27{M}\\x27,\\x27w\\x27)'", "python3 -I -c 'open(\\x27{M}\\x27,\\x27w\\x27)'",
        "python3 -I -c x.py", "python3 -I -m zipfile -c {M} asteroid/SPEC.md", "python3 -I -mzipfile.py -c {M} asteroid/SPEC.md",
        "python3 {evil} {M}", "python3 -I {evil} {M}", "python3 -I {rel_evil} {M}", "python3 -I asteroid/../{rel_evil} {M}",
        "python3 -I {link} {M}", "python3 -I {repo_evil} {M}", "python3 -O -I {evil} {M}", "python3 -I -X dev {evil} {M}",
        "env python3 -I {evil} {M}", "X=1 python3 -I {evil} {M}", "PYTHONSTARTUP={evil} python3 -I asteroid/tests/test_prob.py",
        "env PYTHONPATH={esc} python3 -I asteroid/tests/test_prob.py", "/usr/bin/python3 -I {evil} {M}", "python -I {evil} {M}",
        "python3 -I /bin/sh.py -c touch", "python3 -I ~/../../{evil_noslash} {M}", "python3 -I {ok_script} {M} ; touch {M}",
        "python3 -I esc/evil.py {M}", "python3 -I ./{rel_evil} {M}"]):
        C.append(("check/" + tpl[:30], tpl, i))
    out = []
    for name, tpl, i in C:
        for verb in ("check", "seq"):
            M = os.path.join(SCR, "esc", f"marker_{verb}_{i}")
            cmd = tpl.format(ok=ok_check, M=M, evil=evil, rel_evil=rel_from_root(evil), link=os.path.join(SCR, "esc", "link.py"),
                             repo_evil=os.path.join(SCR, "esc", "repo", rel_from_root(evil)), esc=os.path.join(SCR, "esc"),
                             evil_noslash=evil.lstrip("/"), ok_script="asteroid/tests/test_prob.py")
            cmd = cmd.replace("\\x22", '"').replace("\\x27", "'")
            line = f'check "{cmd}"' if verb == "check" else f'seq t = run "{cmd}"'
            out.append((f"{verb}: {tpl[:50]}", f"seq s = [1]\nclaim s = [1]\n{line}\n", M))
    # newline injection: the line ends, the rest is a new (unparsable) line; \r is a line end too
    for j, sep in enumerate(["\n", "\r", "\r\n", "\x0b", "\x0c", "\x1c", " "]):
        M = os.path.join(SCR, "esc", f"marker_nl_{j}")
        out.append((f"newline injection {j}", f'check "python3 -I asteroid/tests/test_prob.py{sep}touch {M}"\ncheck "touch {M}{sep}"\n', M))
    return out

# ---------------------------------------------------------------- family 3: checks cannot be removed
def removal_cases():
    """(name, program, scratch findings file that must stay absent or hold `n` lines, n, env, extra test)"""
    C = []
    T = "seq s = [1, 2, 6]\nclaim formula s = \"n!\"\n"
    Fz = "seq s = [1, 2, 6]\nclaim formula s = \"n\"\n"
    def rec(case, word, body, n=0, stmt=None, env=None, check=None):
        d = os.path.join(SCR, "rec", case)
        C.append((f"record: {case}", body + f'record {d} x {word} "{stmt or "anti-ath " + case}"\n', os.path.join(d, "findings.jsonl"), n, env, check))
    rec("after a FALSE claim", "checked-finite", Fz)
    rec("after TRUE then FALSE", "tested", T + Fz)
    rec("checked from a Python claim", "checked", T)
    rec("checked by lean from a Python claim", "checked", T + 'claim s = [1, 2, 6] by lean\n')
    rec("checked-infinite from a Python claim", "checked-infinite", T)
    rec("no claim at all", "checked-finite", "seq s = [1, 2, 6]\n")
    rec("no claim, only a frame", "tested", 'frame "x" reading "y" -> none label checked\n')
    rec("unknown word", "proved", T)
    rec("word with a dash trick", "checked-", T)
    rec("FALSE claim, then a frame claiming it", "checked-finite", Fz + 'frame "x" reading "y" -> 2 label checked\n')
    rec("failed check", "checked-finite", 'seq s = [1]\nclaim s = [1]\ncheck "python3 -I asteroid/SPEC.md.py"\n')
    rec("not of a false claim", "checked-finite", "seq s = [1]\nclaim not s = [2]\nclaim s = [2]\n")
    # control: a supported record is written once; a duplicate in the same run and a rerun add nothing
    d = os.path.join(SCR, "rec", "duplicate"); os.makedirs(d, exist_ok=True)
    dup = T + f'record {d} x tested "anti-ath duplicate"\n' * 3
    C.append(("record: duplicate x3 (control: exactly 1 line)", dup, os.path.join(d, "findings.jsonl"), 1, None, None))
    C.append(("record: duplicate rerun (still exactly 1 line)", dup, os.path.join(d, "findings.jsonl"), 1, None, None))
    # frames: labels stronger than the claim, written to a scratch frames file
    fr = os.path.join(SCR, "frames_test.jsonl")
    for lab in ("checked", "checked-infinite"):
        C.append((f"frame: label {lab} on a Python claim is downgraded", T + f'frame "anti-ath {lab}" reading "r" -> 2 label {lab}\n', None, 0, None,
                  ("label", fr, f"anti-ath {lab}", "checked-finite")))
    C.append(("frame: label checked on a FALSE claim is forced open", Fz + 'frame "anti-ath false" reading "r" -> 2 label checked\n', None, 0, None,
              ("label", fr, "anti-ath false", "open")))
    C.append(("frame: label checked with no claim is forced open", 'frame "anti-ath none" reading "r" -> none label checked\n', None, 0, None,
              ("label", fr, "anti-ath none", "open")))
    write("fr/bad.ath", Fz)
    C.append(("frame: label checked on a failing file is forced open", f'frame "anti-ath file" reading "r" -> {os.path.join(SCR, "fr/bad.ath")} label checked\n',
              None, 0, None, ("label", fr, "anti-ath file", "open")))
    C.append(("frame: a line that is not a claim is refused", 'seq s = [1]\nframe "anti-ath seq" reading "r" -> 1 label checked\n', None, 0, None,
              ("absent", fr, "anti-ath seq", None)))
    C.append(("frame: a later line is refused", 'frame "anti-ath later" reading "r" -> 2 label checked\nseq s = [1]\nclaim s = [1]\n', None, 0, None,
              ("absent", fr, "anti-ath later", None)))
    # ASTEROID_FRAMES aimed at findings files or non-jsonl files: refused before anything is written
    real = os.path.join(ROOT, "asteroid", "findings.jsonl")
    fake = os.path.join(SCR, "fx", "findings.jsonl"); os.makedirs(os.path.dirname(fake), exist_ok=True)
    if os.path.isfile(real): shutil.copyfile(real, fake)
    for name, target in [("a copy of a findings.jsonl", fake), ("a new findings.jsonl", os.path.join(SCR, "fx2", "findings.jsonl")),
                         ("findings.jsonl through ..", os.path.join(SCR, "fx", "..", "fx3", "findings.jsonl")),
                         ("a non-jsonl file", os.path.join(SCR, "fx4", "notes.md"))]:
        C.append((f"ASTEROID_FRAMES at {name}", T + 'frame "anti-ath env" reading "r" -> 2 label tested\n', None, 0, {"ASTEROID_FRAMES": target},
                  ("unchanged", target, open(target, "rb").read() if os.path.isfile(target) else None, None)))
    return C

def removal_ok(case, rc, out, hung):
    name, prog, ffile, n, env, extra = case
    if hung: return False, "outer timeout"
    if ffile is not None:
        lines = [l for l in open(ffile, encoding="utf-8") if l.strip()] if os.path.isfile(ffile) else []
        if len(lines) != n: return False, f"{len(lines)} record lines, want {n}"
    if extra:
        kind, path, key, val = extra
        import json
        rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()] if os.path.isfile(path) and kind != "unchanged" else []
        mine = [r for r in rows if r.get("source") == key]
        if kind == "label" and not (mine and all(r["label"] == val for r in mine)): return False, f"frame label {[r['label'] for r in mine]}, want {val}"
        if kind == "absent" and mine: return False, "frame was written"
        if kind == "unchanged":
            now = open(path, "rb").read() if os.path.isfile(path) else None
            if now != key: return False, "the ASTEROID_FRAMES target changed"
            if rc == 0: return False, "the run did not refuse"
    return True, ""

def main():
    before = snapshot()
    print(f"anti-ath: scratch {SCR}")
    jobs = []
    for name, text in halting_cases().items():
        jobs.append(("halting", name, write(f"h/{len(jobs)}.ath", text), None))
    for name, path in frame_file_cases().items():
        jobs.append(("halting", name, path, None))
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(4) as ex:
        res = list(ex.map(lambda j: (j, run(j[2], j[3])), jobs))
    slow = 0
    for (fam, name, path, _), (rc, out, secs, hung) in res:
        ok, why = halting_ok(rc, out, hung); slow = max(slow, secs)
        want(f"halting: {name} ({secs} s)", ok, why + " | " + out.strip().splitlines()[-1][:160] if out.strip() else why)
    print(f"family 1 (halting): {len(res)} programs, slowest {slow} s (outer limit {OUTER} s)")
    esc = escape_cases()
    with concurrent.futures.ThreadPoolExecutor(4) as ex:
        res = list(ex.map(lambda c: (c, run(write(f"e/{abs(hash(c[0] + c[1])) % 10**9}.ath", c[1]))), esc))
    for (name, prog, M), (rc, out, secs, hung) in res:
        want(f"escape: {name}", not os.path.exists(M) and not hung, "marker file appeared" if os.path.exists(M) else "outer timeout")
    # writers of records are refused by name, without running them (boards.py add would write a finding)
    sys.path.insert(0, ROOT)
    os.environ.setdefault("PYTHONPATH", ROOT)
    import asteroid.ext_finite as XF
    for cmd in ["python3 -I boards.py add " + os.path.join(SCR, "w") + " w s checked x y", "python3 -I center.py",
                "python3 -I ./boards.py retest", "python3 -I one-not/../boards.py confirm x y", "python3 -I one-not/tools/tensor/dag.py"]:
        try: XF._cmd(cmd, "anti"); refused = False
        except SystemExit: refused = True
        want(f"escape: a check may not run {cmd.split()[2]}", refused)
    good = XF._cmd("python3 -I asteroid/tests/test_prob.py", "anti")
    want("escape control: a repository check is accepted", good[1] == "asteroid/tests/test_prob.py")
    print(f"family 2 (no escape): {len(res) + 6} attacks")
    rem = removal_cases()
    n3 = 0
    for case in rem:                 # in order: the duplicate rerun depends on the first run
        rc, out, secs, hung = run(write(f"r/{n3}.ath", case[1]), case[4]); n3 += 1
        ok, why = removal_ok(case, rc, out, hung)
        want(case[0], ok, why + " | " + (out.strip().splitlines() or [""])[-1][:160])
    ctl = run(write("ctl/true.ath", 'seq s = [1, 2, 6]\nclaim formula s = "n!"\ncheck "python3 -I asteroid/tests/test_prob.py"\n'))
    want("control: a true program still passes", ctl[0] == 0, ctl[1][-300:])
    after = snapshot()
    changed = sorted(k for k in set(before) | set(after) if before.get(k) != after.get(k))
    ours = [k for k in changed if any("anti-ath" in l or SCR in l for l in after.get(k, set()) - before.get(k, set()))]
    want("no new line from this test in any repository findings.jsonl or frames.jsonl", not ours, ", ".join(ours))
    if changed and not ours: print("note: changed meanwhile by another process (no line from this test): " + ", ".join(changed))
    print(f"family 3 (no removal): {n3} programs; repository record files compared: {len(before)}")
    print(f"anti-ath: {len(PASSES)} passed, {len(FAILS)} failed, {time.time() - t0:.0f} s")
    print("This tests asteroid's stated guarantees only. Halting in general is undecidable.")
    print("FAIL" if FAILS else "PASS")
    return 1 if FAILS else 0

if __name__ == "__main__": sys.exit(main())
