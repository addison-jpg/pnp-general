"""The structure of the project, as one picture: who decides, where work flows, how results come back up."""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

INK, DIM, LINE = "#1f2328", "#57606a", "#8c959f"
COL = {"you": "#008282", "coord": "#3D9BD6", "board": "#6e40c9", "seat": "#bf8700",
       "check": "#1a7f37", "compute": "#cf222e", "out": "#008282"}

fig, ax = plt.subplots(figsize=(16, 10.5), dpi=150)
ax.set_xlim(0, 160); ax.set_ylim(0, 105); ax.axis("off")
fig.patch.set_facecolor("white")

def box(x, y, w, h, title, body, kind):
    c = COL[kind]
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.4,rounding_size=1.5",
                                fc=c + "14", ec=c, lw=1.8))
    ax.text(x + w / 2, y + h - 2.4, title, ha="center", va="top", fontsize=11.5, weight="bold", color=c)
    ax.text(x + w / 2, y + h - 6.6, body, ha="center", va="top", fontsize=8.6, color=INK, linespacing=1.35)
    return (x, y, w, h)

def arrow(a, b, label="", side=(0, 0), color=LINE, style="-|>", rad=0.0, ls="-"):
    ax.add_patch(FancyArrowPatch(a, b, arrowstyle=style, mutation_scale=14, color=color, lw=1.4,
                                 connectionstyle=f"arc3,rad={rad}", linestyle=ls))
    if label:
        mx, my = (a[0] + b[0]) / 2 + side[0], (a[1] + b[1]) / 2 + side[1]
        ax.text(mx, my, label, fontsize=8, color=DIM, ha="center", va="center",
                bbox=dict(fc="white", ec="none", pad=0.6))

ax.text(80, 103, "How the project is organised", ha="center", fontsize=16, weight="bold", color=INK)
ax.text(80, 99.6, "Decisions flow down (left to right) · results flow back up (bottom arrows) · nothing counts until it is checked or tested",
        ha="center", fontsize=9.5, color=DIM)

# Row 1: people and coordinators
you = box(4, 78, 24, 16, "Addison", "chooses problems,\napproves cards,\nsets the rules", "you")
co = box(36, 78, 30, 16, "Coordinators", "main (this chat), coord,\nwarden (spend), research:\nturn asks into cards", "coord")
bd = box(74, 72, 40, 22, "BOARD.md  (the top)",
         "rules: unify first · Fable for design ·\nquiet until ready · state at full strength\ncards: FLAGSHIP (payment Hall) ·\nMETHODS · LATERAL · WORLDS MAP · COMPUTE",
         "board")
tk = box(122, 72, 34, 22, "Task boards", "boards/tasks/*.md\none per card, each with\nOPEN → TAKEN → DECIDED\nlines (a seat = one line)", "board")

arrow((28, 86), (36, 86), "asks")
arrow((66, 86), (74, 86), "cards")
arrow((114, 83), (122, 83), "links")

# Row 2: seats
sf = box(4, 40, 46, 24, "Seats (agents)",
         "Fable · design, formalisation, proof\nOpus · one hard attempt\nSonnet · retrieval, sweeps, plumbing\n\nrule: one narrow line each;\nsub-lemmas go back as OPEN lines", "seat")
arrow((126, 72), (40, 64.5), "a seat takes one OPEN line", side=(30, 1.6), rad=0.0)
arrow((22, 64), (22, 78), "reports", side=(-5, 0), color=COL["seat"], ls="--")

# Row 2: the two ways a claim gets backed
ln = box(58, 40, 40, 24, "Lean  (checked)",
         "theorem in a .lean file\nkernel accepts it, standard axioms\nonly checker of 'checked'\nverifier also runs on GitHub", "check")
tn = box(106, 40, 50, 24, "Compute  (tested)",
         "tensor backend: one array op per gate\ngit-compute: up to 20 GitHub runners\n+ shared cache · job DAG ·\nrefuter seeds feed the next search", "compute")
arrow((50, 55), (58, 55), "proves")
arrow((48, 63.5), (108, 63.5), "searches / refutes", side=(0, 1.0), rad=-0.12)

# Row 3: findings and the tree
fd = box(30, 8, 50, 22, "findings.jsonl  (next to the evidence)",
         "one record per result: word\n(checked · tested · refuted) + evidence path\n+ optional runner (re-check in one command)\ntested needs a second seat", "check")
tr = box(90, 8, 40, 22, "boards.py → TREE.md",
         "verified findings propagate up\nthe directory tree; counts split\nby program; `retest` re-runs\nrunners and marks stale ones", "board")
rd = box(138, 8, 20, 22, "README", "what is proved,\nwhat is open,\nhow to check it", "out")

arrow((78, 40), (58, 30), "records", side=(4, 1))
arrow((140, 40), (72, 30), "records", side=(14, -2), rad=-0.05)
arrow((80, 19), (90, 19))
arrow((130, 19), (138, 19))
arrow((110, 30), (100, 72), "state rolls up", side=(-8, 0), color=COL["board"], ls="--", rad=-0.15)

# legend: flagship target as the spine
ax.text(4, 2.5, "Current spine:  PaymentHall ⇒ BottomPay ⇒ … ⇒ no_minCE  (every arrow checked; PaymentHall itself open)",
        fontsize=9.2, color=COL["you"], weight="bold")

fig.savefig("/home/user/pnp-general/site/structure.png", bbox_inches="tight", facecolor="white")
print("ok")
