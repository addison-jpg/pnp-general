"""Statistics layer over raw per-token log-probabilities. Pure Python + numpy (scipy optional).

Units: bits (log base 2). Rates per character and per whitespace word are tokenizer-independent;
per-token rates mostly measure the tokenizer.
"""
import math, random
import numpy as np


def words(text):
    return len(text.split())


def summarize(text, r):
    """Per-text numbers from one scored text r (instrument.score output)."""
    b = sum(r["bits"]); n = len(r["bits"])
    return {"tokens": n, "chars": len(text), "words": words(text), "bits": b,
            "bits_per_token": b / n, "bits_per_char": b / len(text), "bits_per_word": b / words(text),
            "ent_per_token": sum(r["ent"]) / n,
            # surprisal minus entropy: > 0 means the text is more surprising than the model expected to be
            "excess_per_token": (b - sum(r["ent"])) / n}


def pooled(rows, num, den):
    return sum(r[num] for r in rows) / sum(r[den] for r in rows)


def bootstrap_ratio_diff(A, B, num, den, n_boot=10000, seed=0):
    """Paired bootstrap over items of pooled(A) - pooled(B). Returns (point, lo95, hi95)."""
    rng = random.Random(seed); k = len(A)
    point = pooled(A, num, den) - pooled(B, num, den)
    ds = []
    for _ in range(n_boot):
        idx = [rng.randrange(k) for _ in range(k)]
        a = [A[i] for i in idx]; b = [B[i] for i in idx]
        ds.append(pooled(a, num, den) - pooled(b, num, den))
    ds.sort()
    return point, ds[int(0.025 * n_boot)], ds[int(0.975 * n_boot) - 1]


def wilcoxon_exact(d):
    """Exact two-sided Wilcoxon signed-rank p-value (zeros dropped, average ranks for ties)."""
    d = [x for x in d if x != 0]; n = len(d)
    if n == 0: return 1.0
    absd = sorted((abs(x), i) for i, x in enumerate(d))
    ranks = [0.0] * n; i = 0
    while i < n:
        j = i
        while j + 1 < n and absd[j + 1][0] == absd[i][0]: j += 1
        for k in range(i, j + 1): ranks[absd[k][1]] = (i + j) / 2 + 1
        i = j + 1
    wplus = sum(r for r, x in zip(ranks, d) if x > 0)
    # exact null distribution over all 2^n sign assignments (n <= 20 here)
    from itertools import product
    tot = sum(ranks); cnt = 0; ext = 0
    obs = abs(wplus - tot / 2)
    for s in product((0, 1), repeat=n):
        w = sum(r for r, si in zip(ranks, s) if si)
        cnt += 1; ext += abs(w - tot / 2) >= obs - 1e-12
    return ext / cnt


def sign_test(d):
    d = [x for x in d if x != 0]; n = len(d); k = sum(1 for x in d if x > 0)
    m = min(k, n - k)
    p = sum(math.comb(n, i) for i in range(0, m + 1)) / 2 ** n * 2
    return min(1.0, p), k, n


def paired(A, B, key):
    """Per-item differences A-B of one per-text rate: mean, bootstrap CI of the mean, Wilcoxon p, sign count."""
    d = [a[key] - b[key] for a, b in zip(A, B)]
    rng = random.Random(1); k = len(d)
    bs = sorted(sum(d[rng.randrange(k)] for _ in range(k)) / k for _ in range(10000))
    p_s, pos, n = sign_test(d)
    return {"mean": sum(d) / k, "lo": bs[250], "hi": bs[9749], "wilcoxon_p": wilcoxon_exact(d), "pos": pos, "n": n}


def direction(lo, hi):
    return "+" if lo > 0 else ("-" if hi < 0 else "0")


def verdict(per_size, want="+"):
    """per_size: list of (size_label, point, lo, hi) in increasing size; want: the sign the claim predicts.
    Returns one of:
    'holds at every size'  - the CI excludes 0 in the claimed direction at every size run;
    'fails at every size (opposite direction)' - the CI excludes 0 against the claim at every size;
    'reverses'             - CIs exclude 0 with opposite signs at two sizes;
    'shrinks with size (small-model artefact)' - CI excludes 0 at the smallest size, includes 0 at the largest,
                             with a smaller point estimate at the largest;
    'grows with size'      - the mirror case; else 'not resolved (CI includes 0)'."""
    dirs = [direction(lo, hi) for _, _, lo, hi in per_size]
    if "+" in dirs and "-" in dirs: return "reverses"
    if all(x == want for x in dirs): return "holds at every size"
    if all(x == dirs[0] != "0" for x in dirs): return "fails at every size (opposite direction)"
    p0, pN = per_size[0][1], per_size[-1][1]
    if dirs[0] != "0" and dirs[-1] == "0" and abs(pN) < abs(p0): return "shrinks with size (small-model artefact)"
    if dirs[0] == "0" and dirs[-1] != "0": return "grows with size"
    return "not resolved (CI includes 0)"


def spearman(x, y):
    rx = np.argsort(np.argsort(x)); ry = np.argsort(np.argsort(y))
    return float(np.corrcoef(rx, ry)[0, 1])


# ---- logit lens summaries ----

def settle_layers(r, top_k_bits=None):
    """Per token: the first layer (1-based) from which the lens top-1 is the actual token at every later layer,
    or None if it is not top-1 at the final layer. Returned with the total layer count."""
    L = len(r["lens_top1"]); T = len(r["bits"]); out = []
    for t in range(T):
        if not r["lens_top1"][-1][t]: out.append(None); continue
        l = L
        while l - 1 >= 1 and r["lens_top1"][l - 2][t]: l -= 1
        out.append(l)
    return out, L


def half_info_layer(r):
    """Per token: first layer at which the lens surprisal has fallen at least halfway (in bits) from the
    first-layer surprisal to the final surprisal, and stays there. Defined for every token."""
    LB = r["lens_bits"]; L = len(LB); out = []
    for t in range(len(r["bits"])):
        s0, sL = LB[0][t], LB[-1][t]
        if s0 <= sL: out.append(1); continue
        thr = (s0 + sL) / 2; l = L
        while l - 1 >= 1 and LB[l - 2][t] <= thr: l -= 1
        out.append(l)
    return out, L
