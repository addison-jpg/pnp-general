#!/usr/bin/env python3
"""MONQWENSOR, first version: link centre records by a local model's internal representation.

Every record in center/shards/*.jsonl is passed through a local Qwen model; its vector is the mean of the last hidden
layer over the text's tokens, normalised onto the unit sphere (for Qwen2.5-1.5B, d = 1536, so the sphere is S^1535).
Two records from different programs are proposed as linked when their vectors are close (cosine similarity).
Proposals only: closeness in the model's internal space is a hint, never a result. A proposal becomes a finding only
after a check.

Run (offline, CPU): VENV/bin/python compute/monqwensor/embed.py [--model Qwen/Qwen2.5-1.5B-Instruct] [--top 25]
Writes compute/monqwensor/proposals.json and prints the top cross-program pairs and where the known join ranks.
"""
import argparse, glob, json, os, re, time
os.environ.setdefault("HF_HUB_OFFLINE", "1")
import torch
from transformers import AutoModel, AutoTokenizer

KNOWN = ("segmental-growth histories", "rooted binary phylogenetic trees")   # the join already checked exactly

BOILER = re.compile(r"`[^`]*`|\S+\.(lean|py|md|json|jsonl|ath|bench)\S*|\([^)]*(provenance|Fable|Opus|Sonnet|main|seat)[^)]*\)|"
                    r"\b(checked|checked-finite|tested|refuted|open|paper|premise|standard axioms|propext|Classical\.choice|Quot\.sound|"
                    r"Lean|lean|builds?|sorry|axioms?|findings?|supersedes|seat|confirmed|TAKEN|DECIDED|OPEN)\b|[0-9a-f]{8}", re.I)

def clean(t):
    """Keep the mathematical statement: drop code spans, file paths, provenance, labels and ids."""
    return re.sub(r"\s+", " ", BOILER.sub(" ", t)).strip(" .,:;-")

def records():
    out = []
    for f in sorted(glob.glob("center/shards/*.jsonl")):
        for line in open(f, encoding="utf-8"):
            r = json.loads(line)
            t = (r.get("text") or "").strip()
            if "MONQWENSOR" in t or ("growth" in t and "phylogenetic" in t): continue   # records that state the answer: excluded from the test
            c = clean(t)
            if len(c) >= 20: out.append({"id": r["id"], "kind": r["kind"], "program": r.get("program", "other"), "text": t[:600], "clean": c[:600]})
    return out

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--model", default="Qwen/Qwen2.5-1.5B-Instruct"); ap.add_argument("--top", type=int, default=25)
    a = ap.parse_args(); t0 = time.time(); torch.set_num_threads(os.cpu_count() or 4)
    tok = AutoTokenizer.from_pretrained(a.model); model = AutoModel.from_pretrained(a.model, torch_dtype=torch.float32).eval()
    recs = records(); vecs = []
    with torch.no_grad():
        for i in range(0, len(recs), 8):
            b = tok([r["clean"] for r in recs[i:i + 8]], return_tensors="pt", padding=True, truncation=True, max_length=192)
            h = model(**b).last_hidden_state; m = b["attention_mask"].unsqueeze(-1).float()
            vecs.append(torch.nn.functional.normalize((h * m).sum(1) / m.sum(1), dim=-1))
    V = torch.cat(vecs); S = V @ V.T
    # centre the similarities: subtract each record's mean similarity, so generic "everything looks alike" is removed
    S = S - S.mean(1, keepdim=True) / 2 - S.mean(0, keepdim=True) / 2
    pairs = []
    n = len(recs)
    for i in range(n):
        for j in range(i + 1, n):
            if recs[i]["program"] != recs[j]["program"]: pairs.append((float(S[i, j]), i, j))
    pairs.sort(reverse=True)
    def known(i, j): return {KNOWN[0] in recs[i]["text"] or KNOWN[0] in recs[j]["text"], KNOWN[1] in recs[i]["text"] or KNOWN[1] in recs[j]["text"]} == {True} and (KNOWN[0] in recs[i]["text"]) != (KNOWN[0] in recs[j]["text"])
    rank = next((k + 1 for k, (_, i, j) in enumerate(pairs) if known(i, j)), None)
    out = [{"score": round(s, 4), "a": recs[i]["program"] + ": " + recs[i]["text"][:140], "b": recs[j]["program"] + ": " + recs[j]["text"][:140], "status": "proposed"} for s, i, j in pairs[:a.top]]
    json.dump({"model": a.model, "dim": V.shape[1], "records": n, "cross_pairs": len(pairs), "known_join_rank": rank, "top": out}, open("compute/monqwensor/proposals.json", "w"), indent=1, ensure_ascii=False)
    for p in out[:12]: print(f"{p['score']:+.3f}  {p['a'][:90]}\n        {p['b'][:90]}")
    print(f"records {n}, dim {V.shape[1]}, cross-program pairs {len(pairs)}, known join rank {rank}, seconds {round(time.time()-t0,1)}")

if __name__ == "__main__":
    main()
