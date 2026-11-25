#!/usr/bin/env python3
"""Route only the needed bytes of Qwen2.5-7B-Instruct into the memory vocabulary. Standard library only.
The n-partite route: memory name -> token id (vocab) -> one embedding row -> one byte range of one shard.
Nothing else is downloaded: the index, the header, the vocabulary file, then one row per memory name, paced.
Checked: each row has `hidden` finite values; each name found is a single token; the header's shape is 152064 rows.
Output: workshop/route/memory_vectors_7b.json. Reading (analogy): input embeddings, not meanings.
Run: python3 -I math/qwen/memory_vectors_7b.py   (last line is JSON)
"""
import json, math, os, struct, sys, time, urllib.request
BASE = "https://huggingface.co/Qwen/Qwen2.5-7B-Instruct/resolve/main/"
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORDS = ["checked", "checked-finite", "tested", "refuted", "open", "paper", "frame", "claim", "record", "shard", "program"]

def get(name, rng=None):
    req = urllib.request.Request(BASE + name, headers={"Range": rng} if rng else {})
    with urllib.request.urlopen(req, timeout=60) as r: return r.read()

def main():
    t0 = time.time()
    idx = json.loads(get("model.safetensors.index.json"))
    shard = idx["weight_map"]["model.embed_tokens.weight"]
    n = struct.unpack("<Q", get(shard, "bytes=0-7"))[0]
    header = json.loads(get(shard, f"bytes=8-{7 + n}"))
    e = header["model.embed_tokens.weight"]; vocab_n, hidden = e["shape"]
    assert e["dtype"] == "BF16" and vocab_n == 152064, (e["dtype"], vocab_n)
    base = 8 + n + e["data_offsets"][0]
    vocab = json.loads(get("vocab.json"))
    time.sleep(2)
    programs = sorted(f[:-4] for f in os.listdir(ROOT) if f.endswith(".ath"))
    out = {}
    for name in programs + WORDS:
        key = name if name in vocab else ("Ġ" + name if ("Ġ" + name) in vocab else None)
        if key is None: out[name] = None; continue
        tid = vocab[key]; assert 0 <= tid < vocab_n
        lo = base + tid * hidden * 2
        row = get(shard, f"bytes={lo}-{lo + hidden * 2 - 1}")
        vec = [struct.unpack("<f", struct.pack("<I", x << 16))[0] for x in struct.unpack("<%dH" % hidden, row)]
        assert len(vec) == hidden and all(math.isfinite(v) for v in vec)
        out[name] = {"token_id": tid, "vector": [round(v, 6) for v in vec]}
        time.sleep(0.5)  # paced: one small range at a time
    found = sum(1 for v in out.values() if v)
    json.dump({"model": "Qwen2.5-7B-Instruct", "kind": "static input embeddings (not meanings)", "hidden": hidden,
               "rows": out}, open(os.path.join(ROOT, "workshop", "route", "memory_vectors_7b.json"), "w", encoding="utf-8"), indent=1)
    print(f"{found} of {len(out)} memory names routed to 7B rows; bytes fetched: {found * hidden * 2} (rows) plus index, header, vocab")
    print("PASS")
    print(json.dumps({"states": found, "seconds": round(time.time() - t0, 2), "hidden": hidden, "found": found, "names": len(out)}))

if __name__ == "__main__":
    main()
