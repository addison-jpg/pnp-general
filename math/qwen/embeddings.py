#!/usr/bin/env python3
"""One centralized store of Qwen2.5 input-embedding vectors for the repository's own terms. Standard library only.

Reads the embed_tokens tensor of a Qwen2.5 safetensors file: BF16, shape (vocab, hidden), rows read by seek
(no full load). A term becomes a row only if it is a SINGLE token in the model's vocabulary (exact match, with the
byte-level space marker). Output: math/qwen/semantic_rows.json, with the model's header hash and the shape.

These are STATIC INPUT embeddings: one vector per token, the same whatever the context. They are not contextual
meanings, and they are not the semantics of the model. A reading that they carry meaning is analogy.
Checked exactly: each vector has `hidden` finite values; each term found is single-token; the file's header hash
is recorded so the store can be re-verified against the same weights.
Run: python3 -I math/qwen/embeddings.py MODEL_DIR   (last line is JSON). Without a model dir: NOT CHECKED.
"""
import hashlib, json, math, os, struct, sys, time

TERMS = ["asteroid", "claim", "check", "frame", "record", "proof", "queer", "camp", "love", "mirror", "cone", "disk",
         "hub", "base", "rhizome", "tree", "ontology", "semantics", "field", "tensor"]
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "semantic_rows.json")

def bf16_to_f32(u16):
    return struct.unpack("<f", struct.pack("<I", u16 << 16))[0]

def main(model_dir):
    t0 = time.time()
    if not model_dir:
        print("NOT CHECKED: no model directory. Pass the directory holding model.safetensors and vocab.json.")
        print(json.dumps({"checked": False, "states": 0})); return 0
    st = os.path.join(model_dir, "model.safetensors")
    raw_head = open(st, "rb").read(8)
    n = struct.unpack("<Q", raw_head)[0]
    head_bytes = open(st, "rb").read(8 + n)
    header = json.loads(head_bytes[8:])
    e = header["model.embed_tokens.weight"]
    assert e["dtype"] == "BF16", e["dtype"]
    vocab_n, hidden = e["shape"]
    start = 8 + n + e["data_offsets"][0]
    vocab = json.load(open(os.path.join(model_dir, "vocab.json"), encoding="utf-8"))
    rows = {}
    with open(st, "rb") as f:
        for term in TERMS:
            for key in (term, "Ġ" + term):          # byte-level BPE: a leading space is the marker Ġ
                if key in vocab:
                    tid = vocab[key]
                    assert 0 <= tid < vocab_n
                    f.seek(start + tid * hidden * 2)
                    vec = [bf16_to_f32(x) for x in struct.unpack("<%dH" % hidden, f.read(hidden * 2))]
                    assert len(vec) == hidden and all(math.isfinite(v) for v in vec)
                    rows[key] = {"token_id": tid, "vector": [round(v, 6) for v in vec]}
                    break
            else:
                rows[term] = None                   # not a single token: recorded as absent, not guessed
    out = {"model_header_sha256": hashlib.sha256(head_bytes).hexdigest(), "hidden": hidden, "vocab": vocab_n,
           "kind": "static input embeddings (not contextual meanings)", "rows": rows}
    json.dump(out, open(OUT, "w", encoding="utf-8"), indent=1)
    found = sum(1 for v in rows.values() if v); absent = [k for k, v in rows.items() if not v]
    print(f"{found} of {len(TERMS)} terms are single tokens; {hidden}-dimensional vectors; absent: {absent}")
    print("PASS")
    print(json.dumps({"states": found, "seconds": round(time.time() - t0, 3), "hidden": hidden, "found": found, "absent": absent}))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else ""))
