"""Convert a circuit file (.json or .bench) to an .ath circuit file: one `circuit NAME N ... end` block.

    python3 -I asteroid/to_ath.py FILE...            writes FILE.circ.ath next to each (wire numbering kept exactly:
                                                    inputs by number, gate k named g<k>, so gate k is wire n + k)
    python3 -I asteroid/to_ath.py --check FILE...    round trip: the old loader's circuit == circ_of_ath(new file), exactly

The .ath file is read by `let NAME = load FILE.ath` (asteroid.py circ_of_ath; native AsteroidLang/Main.lean resolve).
"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import asteroid as A          # circ_of_ath
import ext_bench as EB        # the .bench reader


def load_old(f):
    if f.endswith(".json"):
        d = json.load(open(f, encoding="utf-8"))
        d = d.get("circuit", d)
        return {k: d[k] for k in ("n", "sets", "gates", "outs")}
    c = EB.read(open(f, encoding="utf-8").read())      # the loader's own reader (ext_bench.handle uses read)
    return {k: c[k] for k in ("n", "sets", "gates", "outs")}


def name_of(f):
    s = re.sub(r"[^A-Za-z0-9_]", "_", os.path.splitext(os.path.basename(f))[0])
    return "c_" + s


def to_ath(c, name, origin):
    n = c["n"]
    w = lambda i: str(i) if i < n else f"g{i - n}"
    out = [f"# {origin}: converted by asteroid/to_ath.py; inputs 0..{n - 1}, gate k = g<k> = wire {n} + k",
           f"circuit {name} {n}"]
    for k, g in enumerate(c["gates"]):
        out.append(f"g{k} = not {w(g[1])}" if g[0] == "not" else f"g{k} = {g[0]} {w(g[1])} {w(g[2])}")
    for S, o in zip(c["sets"], c["outs"]):
        out.append("set " + " ".join(str(u) for u in S) + f" -> {w(o)}")
    out.append("end")
    return "\n".join(out) + "\n"


def norm(c):
    return {"n": c["n"], "sets": [list(S) for S in c["sets"]], "outs": list(c["outs"]),
            "gates": [[g[0], g[1]] if g[0] == "not" else [g[0], g[1], g[2]] for g in c["gates"]]}


if __name__ == "__main__":
    args = sys.argv[1:]
    check = "--check" in args
    files = [a for a in args if not a.startswith("--")]
    bad = 0
    for f in files:
        old = load_old(f)
        target = os.path.splitext(f)[0] + ".circ.ath"   # .circ.ath: never collides with a program FILE.ath
        if not check:
            open(target, "w", encoding="utf-8", newline="\n").write(to_ath(old, name_of(f), os.path.basename(f)))
        new = A.circ_of_ath(open(target, encoding="utf-8").read(), target)
        same = norm(old) == norm(new)
        bad += not same
        print(("SAME " if same else "DIFF ") + f"{f} -> {target} (n {old['n']}, {len(old['gates'])} gates, {len(old['sets'])} sets)")
    sys.exit(1 if bad else 0)
