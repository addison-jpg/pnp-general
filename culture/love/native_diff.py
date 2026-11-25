#!/usr/bin/env python3
"""Differential: the Rust crate native/ against the Python reference fingerprints, n <= 3. Any mismatch fails.
--new: only after the differential passes, run the new results (n=3 stable polytope on all profiles, n=4 at k=1
by symmetry) and write native_fingerprints.json. Build output goes to $CARGO_TARGET_DIR (default: a temp dir).
Run: python3 -I culture/love/native_diff.py [--new]"""
import importlib.util, json, os, re, subprocess, sys, tempfile
H = os.path.dirname(os.path.abspath(__file__)); T = os.environ.get("CARGO_TARGET_DIR") or os.path.join(tempfile.gettempdir(), "love-native-target")
subprocess.run(["cargo", "build", "--release", "-q", "-j", "2", "--manifest-path", os.path.join(H, "native", "Cargo.toml")], check=True, env=dict(os.environ, CARGO_TARGET_DIR=T))
run = lambda mode: [json.loads(l) for l in subprocess.run([os.path.join(T, "release", "love-native"), mode], check=True, capture_output=True, text=True).stdout.splitlines() if l.startswith("{")]
py = {e["name"]: e["seq"] for f in ("fingerprints", "paths_fingerprints", "field_fingerprints") for e in json.load(open(os.path.join(H, f + ".json")))}
out = subprocess.run([sys.executable, "-I", os.path.join(H, "check.py")], check=True, capture_output=True, text=True).stdout
tot = re.findall(r"^n=([1-3]) .*total stable: k1=(\d+) k2=(\d+)", out, re.M)
for k in (1, 2): py[f"native extra: stable matchings summed over profiles k={k}, n=1..3"] = [int(t[k]) for t in tot]
rs = run("diff"); bad = [e["name"] for e in rs if py.get(e["name"]) != e["seq"]]
for e in rs: print(f"{'ok  ' if e['name'] not in bad else 'FAIL'} {e['name']}: Python {py.get(e['name'])} Rust {e['seq']}")
miss = [n for n in py if "doubly stochastic" not in n and n not in {e["name"] for e in rs}]
assert not bad and not miss and len(rs) == 21, f"differential failed: {bad} missing {miss}"
if "--new" in sys.argv:
    new = run("new"); ex = next(e["example"] for e in new if "example" in e)
    sp = importlib.util.spec_from_file_location("love_check", os.path.join(H, "check.py")); L = importlib.util.module_from_spec(sp); sp.loader.exec_module(L)
    ra, rb = L.ranks(ex["pa"]), L.ranks(ex["pb"]); L.validate(4, ex["pa"], ex["pb"])
    assert sum(L.stable(4, 1, ra, rb, m) for m in L.matchings(4, 1)) == ex["stable"], "Python reference disagrees on the n=4 example"
    print(f"Python reference: the n=4 example has {ex['stable']} stable matchings: {ex}")
    fp = [dict(e, runner="python3 -I culture/love/native_diff.py --new") for e in new if "seq" in e and "seconds" not in e["name"]]
    for e in new: print(e)
    with open(os.path.join(H, "native_fingerprints.json"), "w", encoding="utf-8") as f: f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
print("PASS")
