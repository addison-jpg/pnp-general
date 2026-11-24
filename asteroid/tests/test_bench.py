"""The two `.bench` readers agree: asteroid/ext_bench.py (Python) and AsteroidLang/Bench.lean (Lean).

For every `.bench` file of the repository (hello.bench and the witness circuits) and for a list of
malformed files, both readers are run and must give the same circuit (n, sets, gates, outs) or the same
error message. For a converted witness file the circuit must also equal the JSON file next to it, and the
file must be exactly what the writer prints. Needs Lean (`lake`).
Run from the repository root:  python3 -I asteroid/tests/test_bench.py"""
import sys, os, json, glob, subprocess, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "asteroid"))
import ext_bench as B

MALFORMED = [
    "INPUT(a)\nINPUT(b)\nOUTPUT(z)\nz = NAND(a, b)\n",                  # operator not accepted
    "INPUT(a)\nOUTPUT(z)\nz = AND(a, a, a)\n",                          # three operands
    "INPUT(a)\nOUTPUT(z)\nz = OR(a, y)\ny = NOT(z)\n",                  # cycle
    "INPUT(a)\nOUTPUT(z)\nz = OR(a, q)\n",                              # undefined signal
    "INPUT(a)\n#@ and a = a\n",                                         # unknown directive
    "INPUT(a)\nz = XOR(a, a) # c\n#@ or\n",                             # malformed directive
    "INPUT(a-b)\n", "INPUT(a)\nz = NOT(a\n", "INPUT(a)\nz = = NOT(a)\n",  # syntax
    "INPUT(a)\nOUTPUT(z)\n", "INPUT(a)\nINPUT(a)\n", "INPUT(a)\nz = NOT(a)\nz = NOT(a)\n",
    "INPUT(a)\nINPUT(b)\nOUTPUT(z)\nOUTPUT(a)\n#@ or z = a b\nz = OR(a, b)\n",   # an output without a directive
    # not errors: out of order, BUFF, lower case, CR, trailing comment; digits as names, an output that is an input
    "input(a)\n  INPUT ( b )\r\n\noutput(z)   # the only output\nz = and(n, w)\nw = BUFF(o)\nn = NOT(a)\no = OR(a, b)",
    "INPUT(1)\nOUTPUT(1)\n#@ or 1 = 1\n",
]


def python_line(path):
    src = open(path, newline="").read(); op = {"and": 0, "or": 1, "not": 2}
    try: c = B.read(src)
    except B.BenchError as e: return "ERR " + e.msg, None
    gs = ",".join(f"[{op[g[0]]},{g[1]},{g[2] if len(g) > 2 else g[1]}]" for g in c["gates"])
    nl = B.parse(src); canonical = B.print_netlist(nl) == src and B.parse(B.print_netlist(nl)) == nl
    return f"OK n={c['n']} sets={json.dumps(c['sets'])} outs={json.dumps(c['outs'])} gates=[{gs}]\tcanonical={'true' if canonical else 'false'}", c


def main():
    files = [os.path.join(ROOT, "hello.bench")] + sorted(glob.glob(os.path.join(ROOT, "one-not/data/witnesses/**/*.bench"), recursive=True)) + sorted(glob.glob(os.path.join(ROOT, "one-not/data/beyond_one_not/*.bench")))
    with tempfile.TemporaryDirectory() as d:
        bad = []
        for i, s in enumerate(MALFORMED):
            bad.append(os.path.join(d, f"case{i:02d}.bench")); open(bad[-1], "w", newline="").write(s)
        local = "/home/user/pequalnp-proofs/tools/bin"
        env = dict(os.environ, PATH=(local + ":" if os.path.isdir(local) else "") + os.environ["PATH"])
        r = subprocess.run(["lake", "env", "lean", "--run", os.path.join(ROOT, "asteroid/tests/bench_dump.lean")] + files + bad,
                           cwd=os.path.join(ROOT, "one-not/lean"), env=env, capture_output=True, text=True)
        lean = dict(l.split("\t", 1) for l in r.stdout.splitlines() if "\t" in l)
        if r.returncode != 0 or len(lean) != len(files) + len(bad): print(r.stdout[-800:], r.stderr[-800:]); return 1
        differ = with_json = errors = 0
        for f in files + bad:
            py, c = python_line(f); same = py == lean[f]; j = os.path.splitext(f)[0] + ".json"
            if c is None: errors += 1
            if f in files and (c is None or not py.endswith("canonical=true")): same = False
            if same and os.path.exists(j):
                dj = json.load(open(j)); same = c == {k: dj[k] for k in ("n", "sets", "gates", "outs")}; with_json += 1
            if not same: differ += 1; print(f"DIFFER {f}\n  lean:   {lean[f][:200]}\n  python: {py[:200]}")
    print(f"{len(files)} repository files ({with_json} equal to their JSON circuit, all in the writer's layout), {len(bad)} test files ({errors} of them errors): "
          + ("the two readers agree on all" if not differ else f"{differ} DIFFER"))
    return 1 if differ else 0


if __name__ == "__main__": sys.exit(main())
