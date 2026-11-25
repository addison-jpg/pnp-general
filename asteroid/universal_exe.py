"""Entry point of the one-file `asteroid` (dist/linux/asteroid, dist/windows/asteroid.exe), built with PyInstaller
from packaging/universal/asteroid.spec. It runs the same `main` as `python3 -m asteroid`.

Two things a plain Python run gets for free, done here by hand:
  1. The repository. The code is inside the binary; the data (.bench files, findings, frames.jsonl, one-not/lean)
     is in the repository. It is searched upwards from the program's folder, the current folder and the binary's
     folder (a folder holding asteroid/asteroid.py and one-not/tools/search/core.py). Found: it is passed on in
     ASTEROID_ROOT. Not found: the files packed into the binary stand in, and nothing can be proved.
  2. `sys.executable`. The interpreter runs child programs as `sys.executable -I [-X utf8] FILE.py ARGS` (frame,
     check, hunt, test) and asks `sys.executable -c CODE`. Here sys.executable is this binary, so those forms are
     read below and run with the Python inside it."""
import os, runpy, sys

PY_FLAGS = {"-I", "-P", "-E", "-s", "-S", "-B", "-u", "-O", "-OO", "-q"}

def _python(argv):
    """`[-I] [-X opt] (-c CODE | FILE.py) ARGS`, as python3 would read it. None if argv is not that form."""
    i = 0
    while i < len(argv) and (argv[i] in PY_FLAGS or argv[i] == "-X"):
        i += 2 if argv[i] == "-X" else 1
    if i >= len(argv) or (i == 0 and argv[0] != "-c"): return None   # an asteroid command line never starts with these
    import asteroid                                    # this package wins over a folder of the same name on the path
    if argv[i] == "-c" and i + 1 < len(argv):
        sys.argv = ["-c"] + argv[i + 2:]
        try: exec(compile(argv[i + 1], "<string>", "exec"), {"__name__": "__main__"}); return 0
        except SystemExit as e: return 0 if e.code is None else e.code
    if argv[i].endswith(".py") and os.path.isfile(argv[i]):
        sys.argv = argv[i:]
        if not {"-I", "-P"} & set(argv[:i]):          # as python3: -I and -P keep the script's folder off the path
            sys.path.insert(0, os.path.dirname(os.path.abspath(argv[i])))
        try: runpy.run_path(argv[i], run_name="__main__"); return 0
        except SystemExit as e: return 0 if e.code is None else e.code
    return None

def _repo(argv):
    def ok(d): return os.path.isfile(os.path.join(d, "asteroid", "asteroid.py")) and os.path.isfile(os.path.join(d, "one-not", "tools", "search", "core.py"))
    starts = [os.path.dirname(os.path.abspath(a)) for a in argv if a.endswith((".ath", ".ast"))]
    starts += [os.getcwd(), os.path.dirname(os.path.abspath(sys.executable))]
    for d in starts:
        while True:
            if ok(d): return d
            up = os.path.dirname(d)
            if up == d: break
            d = up
    return None

if __name__ == "__main__":
    argv = sys.argv[1:]
    code = _python(argv)
    if code is not None: sys.exit(code)
    if getattr(sys, "frozen", False) and not os.environ.get("ASTEROID_ROOT"):
        r = _repo(argv)
        if r: os.environ["ASTEROID_ROOT"] = r
    from asteroid.asteroid import main
    sys.exit(main(argv))
