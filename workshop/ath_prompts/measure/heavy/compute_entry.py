"""git-compute entry for the heavy instrument (spec: workshop/compute/specs/heavy_qwen_7b.json).

On a runner:  python3 -I compute_entry.py --label 7B-q4 --gguf-repo REPO --gguf-pattern GLOB --shard i --of N --out PATH
  downloads the weights INSIDE the runner (never committed), scores items j with j % N == i, writes JSON lines to PATH
  and also prints each line to the job log prefixed `HEAVYJSON ` (artifacts cannot be fetched from the cloud container).
Locally:      python3 compute_entry.py --assemble LOG [LOG ...]   rebuilds data/<label>.json from the job logs.
Items: the 10 B1 pairs, the preferences block, the 5 interchange statements (16 items).
"""
import argparse, glob, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from data import b1_pairs, INTERCHANGE


def items():
    pairs, prefs = b1_pairs()
    out = [("b1", i, p) for i, p in enumerate(pairs)] + [("prefs", 0, prefs)]
    return out + [("interchange", i, s) for i, s in enumerate(INTERCHANGE)]


def score_item(M, kind, it):
    if kind == "b1" or kind == "prefs":
        pid, inf, frm = it
        lens = kind == "b1"
        return {"id": pid, "inf": inf, "frm": frm, "r_inf": M.score(inf, lens), "r_frm": M.score(frm, lens)}
    sid, en, ath, lean = it
    return {"id": sid, "forms": {k: {"text": t, "r": M.score(t, False)} for k, t in (("english", en), ("ath", ath), ("lean", lean))}}


def assemble(logs):
    recs = []
    for p in logs:
        for line in open(p, encoding="utf-8", errors="replace"):
            k = line.find("HEAVYJSON ")
            if k >= 0: recs.append(json.loads(line[k + 10:]))
    lab = recs[0]["label"]
    out = {"label": lab, "n_layers": recs[0]["n_layers"], "dtype": recs[0]["dtype"], "b1": [None] * 10, "prefs": None,
           "interchange": [None] * len(INTERCHANGE), "seconds": 0.0, "where": "git-compute (GitHub runner, 4 vCPU, 16 GB, no GPU)"}
    seen = set()
    for r in recs:
        if (r["kind"], r["idx"]) in seen: continue
        seen.add((r["kind"], r["idx"])); out["seconds"] += r["seconds"]
        if r["kind"] == "prefs": out["prefs"] = r["rec"]
        else: out[r["kind"]][r["idx"]] = r["rec"]
    assert all(out["b1"]) and out["prefs"] and all(out["interchange"]), "missing items"
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    json.dump(out, open(os.path.join(HERE, "data", f"{lab}.json"), "w"), ensure_ascii=False)
    print("assembled", lab, len(seen), "items")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--assemble", nargs="+")
    ap.add_argument("--label"); ap.add_argument("--hf-repo"); ap.add_argument("--dtype", default="float32")
    ap.add_argument("--gguf-repo"); ap.add_argument("--gguf-pattern")
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--shard", type=int, default=0); ap.add_argument("--of", type=int, default=1); ap.add_argument("--out")
    a = ap.parse_args()
    if a.assemble: return assemble(a.assemble)
    from huggingface_hub import snapshot_download
    wdir = os.path.join(os.environ.get("RUNNER_TEMP", "/tmp"), "weights")
    if a.gguf_repo:
        snapshot_download(a.gguf_repo, allow_patterns=[a.gguf_pattern], local_dir=wdir)
        first = sorted(glob.glob(os.path.join(wdir, a.gguf_pattern)))[0]
        from instrument import GGUFModel
        M = GGUFModel(first, threads=a.threads); dtype = "gguf"
    else:
        snapshot_download(a.hf_repo, local_dir=wdir, allow_patterns=["*.json", "*.safetensors", "*.txt", "merges.txt", "vocab.json"])
        from instrument import HFModel
        M = HFModel(wdir, dtype=a.dtype, threads=a.threads); dtype = a.dtype
    f = open(a.out, "w", encoding="utf-8")
    for j, (kind, idx, it) in enumerate(items()):
        if j % a.of != a.shard: continue
        t0 = time.time(); rec = score_item(M, kind, it)
        line = json.dumps({"label": a.label, "n_layers": M.n_layers, "dtype": dtype, "kind": kind, "idx": idx,
                           "seconds": time.time() - t0, "rec": rec}, ensure_ascii=False)
        f.write(line + "\n"); f.flush()
        print("HEAVYJSON " + line, flush=True)
    f.close()


if __name__ == "__main__":
    main()
