"""Plot Phi(p) = E_p[slack(Q)] for witness circuits (README: the remaining sorry is 0 <= Phi(0) for a minimal counterexample).
Run from the repo root:  python3 -I one-not/tools/search/plot_phi.py OUT.png [FILE.json ...]   (needs matplotlib, numpy)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import continuous as C
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
out = sys.argv[1]; W = "one-not/data/witnesses/"
files = sys.argv[2:] or [W + "twin_tree_f2step.json", W + "nonlocal/match_c_k7.json", W + "pappus_junk_gain.json",
                         W + "fano_formula.json", W + "cxMU_dd.json", W + "nonlocal/general_count_below_base_min.json"]
ps = [i / 200 for i in range(201)]
fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
for f in files:
    c = C.load(f); n = c["n"]
    any_gate = "general_count" in f
    sl = C.slack_table(c, 0, any_gate=any_gate); m = C.level_means(sl, n)
    lab = os.path.basename(f).replace(".json", "") + f" (n={n})"
    ax[0].plot(ps, [C.bern_eval(m, p) for p in ps], label=lab)
    ax[1].plot(range(n + 1), m, marker="o", ms=3, label=lab)
ax[0].axhline(0, color="k", lw=0.8); ax[1].axhline(0, color="k", lw=0.8)
ax[0].set_xlabel("p = probability that a point is set to 1"); ax[0].set_ylabel("Phi(p) = expected slack")
ax[0].set_title("Phi(p): the sorry is 0 <= Phi(0) for a minimal counterexample")
ax[1].set_xlabel("number of points set to 1"); ax[1].set_ylabel("mean slack at that level"); ax[1].set_title("Level means of slack")
ax[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(out, dpi=160); print("wrote", out)
