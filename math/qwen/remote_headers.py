#!/usr/bin/env python3
"""Exact tensor and parameter counts of a Qwen2.5 model, read from Hugging Face safetensors headers by byte range.
No weights are downloaded or stored. Requests are paced (a short burst, then a pause). Standard library only.
Asserts the counts it reads against the stated expected values, so a check line fails if they change.
Run: python3 -I math/qwen/remote_headers.py   (last line is JSON)
"""
import json, math, struct, sys, time, urllib.request

BASE = "https://huggingface.co/Qwen/Qwen2.5-7B-Instruct/resolve/main/"
EXPECT = {"shards": 4, "tensors": 339, "params": 7615616512}

def get(name, rng=None):
    req = urllib.request.Request(BASE + name, headers={"Range": rng} if rng else {})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()

def main():
    t0 = time.time()
    idx = json.loads(get("model.safetensors.index.json"))
    shards = sorted(set(idx["weight_map"].values()))
    tensors = params = 0
    for s in shards:
        n = struct.unpack("<Q", get(s, "bytes=0-7"))[0]
        header = json.loads(get(s, f"bytes=8-{7 + n}"))
        for k, v in header.items():
            if k == "__metadata__": continue
            tensors += 1; params += math.prod(v["shape"])
        time.sleep(3)  # pause between shards
    assert len(shards) == EXPECT["shards"], f"shards {len(shards)}"
    assert tensors == EXPECT["tensors"], f"tensors {tensors}"
    assert params == EXPECT["params"], f"params {params}"
    print(f"Qwen2.5-7B-Instruct: {len(shards)} shards, {tensors} tensors, {params:,} parameters ({params/1e9:.3f}B)")
    print("PASS")
    print(json.dumps({"states": tensors, "seconds": round(time.time() - t0, 2), "shards": len(shards), "tensors": tensors, "params": params}))

if __name__ == "__main__":
    sys.exit(main())
