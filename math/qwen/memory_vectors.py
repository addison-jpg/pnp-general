#!/usr/bin/env python3
"""Map the memory's own vocabulary (program names and record labels) onto Qwen2.5-0.5B input-embedding vectors.
Static input embeddings: one fixed vector per single token, read by seek from the local weights (no full load).
A name that is not a single token is recorded as absent, never guessed. Reading (analogy): the vector is a token
embedding, not a meaning. Standard library only.
Run: python3 -I math/qwen/memory_vectors.py MODEL_DIR   (last line is JSON). Without a model dir: NOT CHECKED.
"""
import json, math, os, struct, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
WORDS = ["checked", "checked-finite", "tested", "refuted", "open", "paper", "frame", "claim", "record", "shard", "program"]

def main(model_dir):
    t0 = time.time()
    if not model_dir:
        print("NOT CHECKED: no model directory given."); print(json.dumps({"checked": False})); return 0
    st = os.path.join(model_dir, "model.safetensors")
    n = struct.unpack("<Q", open(st, "rb").read(8))[0]
    header = json.loads(open(st, "rb").read(8 + n)[8:])
    e = header["model.embed_tokens.weight"]; vocab_n, hidden = e["shape"]
    start = 8 + n + e["data_offsets"][0]
    vocab = json.load(open(os.path.join(model_dir, "vocab.json"), encoding="utf-8"))
    programs = sorted(f[:-4] for f in os.listdir(ROOT) if f.endswith(".ath"))
    names = programs + WORDS
    out = {}
    with open(st, "rb") as f:
        for name in names:
            key = name if name in vocab else ("Ġ" + name if ("Ġ" + name) in vocab else None)
            if key is None: out[name] = None; continue
            tid = vocab[key]; assert 0 <= tid < vocab_n
            f.seek(start + tid * hidden * 2)
            vec = [struct.unpack("<f", struct.pack("<I", x << 16))[0] for x in struct.unpack("<%dH" % hidden, f.read(hidden * 2))]
            assert len(vec) == hidden and all(math.isfinite(v) for v in vec)
            out[name] = {"token_id": tid, "vector": [round(v, 6) for v in vec]}
    found = sum(1 for v in out.values() if v)
    json.dump({"model": "Qwen2.5-0.5B-Instruct", "kind": "static input embeddings (not meanings)", "hidden": hidden,
               "rows": out}, open(os.path.join(ROOT, "workshop", "route", "memory_vectors.json"), "w", encoding="utf-8"), indent=1)
    print(f"{found} of {len(names)} memory names are single tokens; absent: {[k for k, v in out.items() if not v]}")
    print("PASS")
    print(json.dumps({"states": found, "seconds": round(time.time() - t0, 3), "hidden": hidden, "found": found, "names": len(names)}))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else ""))
