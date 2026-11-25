#!/usr/bin/env python3
"""Match a term to its nearest recorded terms without an exact copy (after Steinmetz and Gini: opening-book clusters
match a position without an exact match; abstracts read via OpenAlex, the dissertation itself was not reachable).
Exact cosine similarity over the stored static embeddings (math/qwen/semantic_rows.json). Standard library only.

Checked: cosine is symmetric; each term's nearest other term is well defined (no ties at the top); a term is its
own best match at cosine 1. Output: each term's two nearest recorded terms. Reading (analogy): nearness in the
embedding is nearness of input tokens, not of meaning.
Run: python3 -I math/qwen/nearest.py   (last line is JSON)
"""
import json, math, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
def main():
    t0 = time.time()
    store = json.load(open(os.path.join(HERE, "semantic_rows.json"), encoding="utf-8"))["rows"]
    names = sorted(k for k, v in store.items() if v)
    vecs = {k: store[k]["vector"] for k in names}
    def norm(v): return math.sqrt(sum(x * x for x in v))
    def cos(a, b): return sum(x * y for x, y in zip(a, b)) / (norm(a) * norm(b))
    sim = {(a, b): cos(vecs[a], vecs[b]) for a in names for b in names}
    for a in names:
        assert abs(sim[(a, a)] - 1) < 1e-9, "a term is its own match"
        for b in names: assert abs(sim[(a, b)] - sim[(b, a)]) < 1e-12, "cosine is symmetric"
    ties = 0
    for a in names:
        others = sorted(((sim[(a, b)], b) for b in names if b != a), reverse=True)
        if len(others) > 1 and abs(others[0][0] - others[1][0]) < 1e-12: ties += 1
    assert ties == 0, "no ties at the top"
    rows = {}
    for a in names:
        best = sorted(((sim[(a, b)], b) for b in names if b != a), reverse=True)[:2]
        rows[a] = [(b, round(s, 4)) for s, b in best]
        print(f"{a}: " + ", ".join(f"{b} ({s:.3f})" for s, b in best))
    print("PASS")
    print(json.dumps({"states": len(names) ** 2, "seconds": round(time.time() - t0, 3), "terms": len(names), "ties": ties}))

if __name__ == "__main__":
    main()
