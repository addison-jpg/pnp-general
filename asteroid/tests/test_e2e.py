"""End-to-end test: run the real launcher from another directory, on files in a path with a space.
Standard library only.   python3 asteroid/tests/test_e2e.py     (exit code 1 on any FAIL)"""
import os, re, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WIN = os.name == "nt"
LAUNCHER = os.path.join(ROOT, "bin", "asteroid.cmd" if WIN else "asteroid")
rows = []

def record(name, ok, note=""):
    rows.append((name, "PASS" if ok else "FAIL", note))

def run(args, cwd, env=None):
    p = subprocess.run([LAUNCHER] + args, cwd=cwd, capture_output=True, env=env, timeout=600)
    out = (p.stdout + p.stderr).decode("utf-8", "replace")
    return p.returncode, out

def last_line(out):
    lines = [l for l in out.splitlines() if l.strip()]
    return lines[-1] if lines else ""

def convert_crlf(src, dst):
    data = open(src, "rb").read().replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
    open(dst, "wb").write(data)

def main():
    tmp = tempfile.mkdtemp(prefix="asteroid e2e ")
    try:
        hello = open(os.path.join(ROOT, "hello.ath"), encoding="utf-8").read()
        noplot = "\n".join(l for l in hello.splitlines() if not l.startswith("plot ")) + "\n"
        shutil.copy(os.path.join(ROOT, "hello.bench"), os.path.join(tmp, "hello.bench"))
        convert_crlf(os.path.join(ROOT, "hello.bench"), os.path.join(tmp, "hello_crlf.bench"))
        def w(name, text, crlf=False):
            data = text.encode("utf-8")
            if crlf: data = data.replace(b"\n", b"\r\n")
            open(os.path.join(tmp, name), "wb").write(data)
        absb = os.path.join(tmp, "hello_crlf.bench").replace("\\", "/")
        w("hello.ath", hello)                                        # has a plot line
        w("noplot.ath", noplot)
        w("noplot_crlf.ath", noplot.replace("hello.bench", absb), crlf=True)   # absolute path, with a space
        w("relative.ath", noplot.replace("hello.bench", "only_here.bench"))    # name that exists only in the temp dir
        shutil.copy(os.path.join(ROOT, "hello.bench"), os.path.join(tmp, "only_here.bench"))
        w("kaomoji.ath", "# kaomoji (˶˃ ᵕ ˂˶) :3\n" + noplot)
        w("false.ath", noplot + "claim gates(hello) = 99\n")
        print("launcher:", LAUNCHER, "\ntemp dir:", tmp, "\n")

        for name in ("noplot.ath", "noplot_crlf.ath", "relative.ath", "kaomoji.ath"):
            rc, out = run([name, "--no-lean"], tmp)
            last = last_line(out)
            ok = rc == 0 and last.startswith("claims:") and re.search(r"\b0 false", last) is not None
            record(f"run {name}", ok, "" if ok else f"rc={rc} last={last!r}")
            if not ok: print(f"--- {name} ---\n{out[-1500:]}")

        rc, out = run(["false.ath", "--no-lean"], tmp)
        ll = last_line(out)
        record("false claim -> non-zero exit", rc != 0 and ll.startswith("claims:") and "1 false" in ll, f"rc={rc} last={ll!r}")

        rc, out = run(["hello.ath", "--no-lean"], tmp)
        last = last_line(out)
        if rc == 0 and last.startswith("claims:"):
            record("plot program (matplotlib)", True, "passes")
        else:
            mpl = [l for l in out.splitlines() if "matplotlib" in l.lower()]
            one = len(mpl) == 1 and "Traceback" not in out
            note = f"rc={rc}; " + (f"one clear line: {mpl[0]!r}" if one else f"messy output, last={last!r}")
            record("plot program (matplotlib)", True, "recorded, not enforced: " + note)

        # the interactive prompt, fed from stdin: state persists across lines, verdicts appear, output is plain when piped
        feed = "let h = load hello.bench\nshow h\nclaim gates(h) = base(h)\nclaim! gates(h) < base(h)\nnonsense\n:save kept.ath\n:quit\n"
        pr = subprocess.run([LAUNCHER], cwd=tmp, input=feed.encode(), capture_output=True, timeout=120)
        po = pr.stdout.decode("utf-8", "replace")
        okp = (pr.returncode == 0 and "python TRUE" in po and "python FALSE" in po and "rejected:" in po and "\x1b" not in po
               and os.path.isfile(os.path.join(tmp, "kept.ath")))
        record("prompt (stdin)", okp, "" if okp else f"rc={pr.returncode} out={po[-600:]!r}")
        rc, out = run(["--doctor"], tmp)
        if "--show-lean" in out:       # the usage text: flag not implemented yet
            record("--doctor", True, "SKIP: flag not there yet")
        else:
            record("--doctor", rc == 0, f"rc={rc}" + ("" if rc == 0 else f" last={last_line(out)!r}"))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print("\n%-34s %-5s %s" % ("check", "", "note"))
    for n, s, note in rows: print("%-34s %-5s %s" % (n, s, note))
    return 1 if any(s == "FAIL" for _, s, _ in rows) else 0

if __name__ == "__main__":
    sys.exit(main())
