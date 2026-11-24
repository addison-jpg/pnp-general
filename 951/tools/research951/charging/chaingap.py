"""Layer-cake test of the concave dual  Σ_w min_z π(M_z(w)) <= π(G).
For π = Σ_t 1_{A_t} (nested A_1 ⊇ A_2 ⊇ ...), m_w(π) = min_M Σ_t |M ∩ A_t| >= Σ_t F_w(A_t), F_w(A) = min_M |M ∩ A|.
0/1 prices suffice for a family iff equality holds for all chains (one M optimal at every level).
We search 2- and 3-level chains built from the merge sets themselves and report the largest per-family gap and the
largest gap of the SUM (which is what a 0/1 proof would lose)."""
import sys, json, itertools, random
from mzmatroid import merge_set
random.seed(3)
tot_fam = 0; gap_fam = 0; worst = []
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    fams = []
    for S in sets:
        Sm = sum(1 << u for u in S)
        fams.append(sorted({merge_set(n, gates, S, z) for z in range(1 << n) if not z & Sm}, key=sorted))
    allM = [M for F in fams for M in F]
    G = range(len(gates))
    def m(F, pi): return min(sum(pi[g] for g in M) for M in F)
    def Fw(F, A): return min(len(M & A) for M in F)
    best = (0, None)
    cands = []
    for M1, M2 in itertools.product(allM, repeat=2):
        cands.append([M1 | M2, M1])            # chain A1 ⊇ A2
    for _ in range(400):
        k = random.randint(2, 3); ms = random.sample(allM, min(len(allM), k))
        U = set(); chain = []
        for M in ms: U |= M; chain.append(frozenset(U))
        cands.append(list(reversed(chain)))
    for chain in cands:
        chain = [frozenset(A) for A in chain]
        pi = [sum(1 for A in chain if g in A) for g in G]
        gsum = sum(m(F, pi) - sum(Fw(F, A) for A in chain) for F in fams)
        if gsum > best[0]: best = (gsum, [sorted(A) for A in chain])
    fam_gaps = []
    for F in fams:
        tot_fam += 1; g = 0
        for chain in cands[:2000]:
            chain = [frozenset(A) for A in chain]
            pi = [sum(1 for A in chain if gg in A) for gg in G]
            g = max(g, m(F, pi) - sum(Fw(F, A) for A in chain))
        gap_fam += g > 0; fam_gaps.append(g)
    print(f.split('/')[-1], '| per-family max layer-cake gap', fam_gaps, '| sum gap', best[0], best[1] if best[0] else '')
print('families with a positive layer-cake gap:', gap_fam, 'of', tot_fam)
