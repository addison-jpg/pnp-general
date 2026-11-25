"""Score every B1 text and every INTERCHANGE form under one model; write data/<label>.json (raw numbers, small).

  nice -n 19 python run.py --label 0.5B --hf <path to Qwen2.5-0.5B-Instruct> [--dtype float32] [--threads 2]
  nice -n 19 python run.py --label 7B-q4 --gguf <path to qwen2.5-7b-instruct-q4_k_m.gguf>

Runs on a GPU unchanged (HFModel picks cuda when torch sees one). Weights are never in the repository.
"""
import argparse, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from data import b1_pairs, INTERCHANGE

ap = argparse.ArgumentParser()
ap.add_argument("--label", required=True)
ap.add_argument("--hf"); ap.add_argument("--gguf")
ap.add_argument("--dtype", default="float32"); ap.add_argument("--threads", type=int, default=2)
a = ap.parse_args()

if a.hf:
    from instrument import HFModel
    M = HFModel(a.hf, dtype=a.dtype, threads=a.threads); lens = True
else:
    from instrument import GGUFModel
    M = GGUFModel(a.gguf, threads=a.threads); lens = False

pairs, prefs = b1_pairs()
out = {"label": a.label, "n_layers": M.n_layers, "dtype": a.dtype if a.hf else "gguf", "b1": [], "prefs": None, "interchange": []}
t0 = time.time()
for pid, inf, frm in pairs:
    out["b1"].append({"id": pid, "inf": inf, "frm": frm, "r_inf": M.score(inf, lens), "r_frm": M.score(frm, lens)})
    print(a.label, pid, f"{time.time() - t0:.0f}s", flush=True)
out["prefs"] = {"id": "prefs", "inf": prefs[1], "frm": prefs[2], "r_inf": M.score(prefs[1], False), "r_frm": M.score(prefs[2], False)}
for sid, en, ath, lean in INTERCHANGE:
    out["interchange"].append({"id": sid, "forms": {k: {"text": t, "r": M.score(t, False)} for k, t in (("english", en), ("ath", ath), ("lean", lean))}})
out["seconds"] = time.time() - t0
d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data"); os.makedirs(d, exist_ok=True)
json.dump(out, open(os.path.join(d, f"{a.label}.json"), "w"), ensure_ascii=False)
print("done", a.label, f"{out['seconds']:.0f}s")
