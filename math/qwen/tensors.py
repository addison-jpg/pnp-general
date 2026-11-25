#!/usr/bin/env python3
"""Qwen2.5 tensors, read from the safetensors headers: exact counts, no weights are loaded. Standard library only.

For each model directory given (default: none, so the script says NOT CHECKED), read config.json and every
*.safetensors header (an 8-byte length, then JSON: name, dtype, shape, offsets). Print tensors, parameters
(the exact product of the shapes), dtypes and file size. The weights are never stored in the repository.
Run: python3 -I math/qwen/tensors.py DIR [DIR ...]   (last line is JSON)
"""
import glob, json, math, os, struct, sys, time

def header(path):
    with open(path, "rb") as f:
        n = struct.unpack("<Q", f.read(8))[0]
        return json.loads(f.read(n))

def summarize(d):
    cfg = json.load(open(os.path.join(d, "config.json")))
    tensors = params = 0; dtypes = set()
    files = sorted(glob.glob(os.path.join(d, "*.safetensors")))
    for p in files:
        for k, v in header(p).items():
            if k == "__metadata__": continue
            tensors += 1; params += math.prod(v["shape"]); dtypes.add(v["dtype"])
    size = sum(os.path.getsize(p) for p in files)
    return {"model": os.path.basename(os.path.normpath(d)), "layers": cfg["num_hidden_layers"], "hidden": cfg["hidden_size"],
            "vocab": cfg["vocab_size"], "tensors": tensors, "params": params, "dtypes": sorted(dtypes), "bytes": size, "files": len(files)}

def main(dirs):
    t0 = time.time()
    if not dirs:
        print("NOT CHECKED: no model directory given. Pass the directories of the Qwen2.5 weights and rerun.")
        print(json.dumps({"states": 0, "seconds": 0, "checked": False})); return 0
    rows = [summarize(d) for d in dirs]
    for r in rows:
        print(f"{r['model']}: {r['layers']} layers, hidden {r['hidden']}, vocab {r['vocab']}, {r['tensors']} tensors, "
              f"{r['params']:,} parameters ({r['params']/1e9:.3f}B), {','.join(r['dtypes'])}, {r['bytes']/1e9:.2f} GB in {r['files']} file(s)")
    print("PASS")
    print(json.dumps({"states": sum(r["tensors"] for r in rows), "seconds": round(time.time() - t0, 3), "models": rows}))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
