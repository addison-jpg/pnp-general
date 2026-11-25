#!/usr/bin/env python3
"""Attack (b) on C2 (informal asks carry more information per token). Standard library only. No model calls.
1. From the stored Qwen per-token bits (heavy/data/*.json): recompute bits/char after
   (i) dropping the first token's bits, (ii) dropping the two shortest prompts, (iii) removing the bits and
   characters of misspelled and slang words, (iv) leaving out each prompt in turn.
2. A model with no tokenizer: an interpolated character 5-gram trained on Python's own docs
   (pydoc_data.topics), scored on both registers, as written and lowercased.
3. Total bits for the same instruction (information, as opposed to surprisal).
Run: python3 -I workshop/ath_prompts/attack/c2_density.py"""
import json, math, os, re
from collections import defaultdict
H = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "measure", "heavy", "data")
SIZES = ["0.5B", "1.5B", "3B", "7B-q4"]
# words a reader would call misspelled or slang (chosen by this seat by reading the 10 prompts)
NOISE = {"acquanted", "quetly", "prrfectly", "than", "shouldnt", "pls", "u", "rlly", "cus", "bruh", "ass", "umm", "ok", "also also"}

def sign_p(pos, n):
    k = min(pos, n - pos); return min(1.0, 2 * sum(math.comb(n, j) for j in range(k + 1)) / 2 ** n)

def spans(text, r):
    """char span of each token: tokens are byte-level BPE with G-dot for a space."""
    out, i = [], 0
    for t in r["tokens"]:
        s = t.replace("Ġ", " ").replace("Ċ", "\n")
        j = text.find(s, i) if s else i
        if j != i: return None  # non-ASCII byte tokens: give up on this text
        out.append((i, i + len(s))); i += len(s)
    return out if i == len(text) else None

def noise_mask(text):
    m = [False] * len(text)
    for w in NOISE:
        for mt in re.finditer(r"(?<![A-Za-z])" + re.escape(w) + r"(?![A-Za-z])", text):
            for k in range(mt.start(), mt.end()): m[k] = True
    return m

def bpc(pairs, side, drop_first=0, drop_noise=False):
    bits = chars = 0
    for p in pairs:
        text, r = p[side], p["r_" + side]
        b = r["bits"][drop_first:]
        if drop_noise and side == "inf":
            sp = spans(text, r); m = noise_mask(text)
            assert sp is not None, p["id"]
            keep = [k for k, (a, z) in enumerate(sp) if k >= drop_first and not any(m[a:z])]
            b = [r["bits"][k] for k in keep]; c = sum(sp[k][1] - sp[k][0] for k in keep)
        else:
            c = len(text)
        bits += sum(b); chars += c
    return bits / chars

print("== 0. C1 length without the Qwen tokenizer: characters and whitespace words per pair ==")
b1 = json.load(open(os.path.join(H, "0.5B.json")))["b1"]
for unit, f in (("tokens(Qwen)", lambda p, side: len(p["r_" + side]["bits"])), ("chars", lambda p, side: len(p[side])), ("words", lambda p, side: len(p[side].split()))):
    d = [f(p, "inf") - f(p, "frm") for p in b1]; nz = [x for x in d if x]
    rest = [p for p in b1 if p["id"] != "05:12"]
    print(f"{unit} | informal shorter {sum(x < 0 for x in d)}/10, ties {d.count(0)}, sign p={sign_p(sum(x < 0 for x in nz), len(nz)):.4f}"
          f" | pooled {sum(f(p, 'inf') for p in b1)} vs {sum(f(p, 'frm') for p in b1)} | without 05:12 {sum(f(p, 'inf') for p in rest)} vs {sum(f(p, 'frm') for p in rest)}")
print("== 1. Qwen bits/char, informal vs formal (pooled over prompts) ==")
for s in SIZES:
    b1 = json.load(open(os.path.join(H, s + ".json")))["b1"]
    long_ = [p for p in b1 if len(p["inf"]) >= 30]
    per = [(sum(p["r_inf"]["bits"]) / len(p["inf"])) - (sum(p["r_frm"]["bits"]) / len(p["frm"])) for p in b1]
    row = {"as stored": (bpc(b1, "inf"), bpc(b1, "frm")),
           "first token dropped": (bpc(b1, "inf", 1), bpc(b1, "frm", 1)),
           "prompts >= 30 chars (8)": (bpc(long_, "inf"), bpc(long_, "frm")),
           "misspelled/slang words removed": (bpc(b1, "inf", 0, True), bpc(b1, "frm"))}
    for k, (i, f) in row.items(): print(f"{s} | {k} | {i:.3f} | {f:.3f} | gap {i - f:+.3f}")
    loo = [bpc([q for q in b1 if q is not p], "inf") - bpc([q for q in b1 if q is not p], "frm") for p in b1]
    tot = [sum(p["r_inf"]["bits"]) - sum(p["r_frm"]["bits"]) for p in b1]
    print(f"{s} | leave-one-out gap min {min(loo):+.3f} max {max(loo):+.3f} | per-prompt informal higher {sum(d > 0 for d in per)}/10"
          f" | total bits informal more in {sum(t > 0 for t in tot)}/10, mean {sum(tot) / 10:+.1f} bits/prompt")

print("== 2. character 5-gram (no tokenizer), trained on pydoc_data.topics ==")
import pydoc_data.topics as T
corpus = "\n".join(T.topics.values())
N = 5
def train(text):
    c = [defaultdict(lambda: defaultdict(int)) for _ in range(N)]
    for i in range(len(text)):
        for n in range(N):
            if i - n >= 0: c[n][text[i - n:i]][text[i]] += 1
    return c
V = 256
def prob(c, h, ch):
    p = 1.0 / V  # Witten-Bell interpolation from order 0 up
    for n in range(N):
        if n > len(h): break
        ctx = h[len(h) - n:] if n else ""
        d = c[n].get(ctx)
        if not d: continue
        tot = sum(d.values()); typ = len(d); lam = tot / (tot + typ)
        p = lam * d.get(ch, 0) / tot + (1 - lam) * p
    return p
def text_bits(c, t): return sum(-math.log2(prob(c, t[:i], t[i])) for i in range(len(t)))
for lower in (False, True):
    c = train(corpus.lower() if lower else corpus)
    b1 = json.load(open(os.path.join(H, "0.5B.json")))["b1"]
    I = [p["inf"].lower() if lower else p["inf"] for p in b1]; F = [p["frm"].lower() if lower else p["frm"] for p in b1]
    bi = [text_bits(c, t) for t in I]; bf = [text_bits(c, t) for t in F]
    per = [a / len(x) - b / len(y) for a, b, x, y in zip(bi, bf, I, F)]
    pos = sum(d > 0 for d in per)
    print(f"{'lowercased' if lower else 'as written'} | informal {sum(bi) / sum(map(len, I)):.3f} | formal {sum(bf) / sum(map(len, F)):.3f} bits/char"
          f" | informal higher in {pos}/10, sign p={sign_p(pos, 10):.4f} | total bits informal {sum(bi):.0f} vs formal {sum(bf):.0f}")
print("PASS")
