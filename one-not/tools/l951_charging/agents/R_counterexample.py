# Explicit counterexample to LEMMA R as stated in MATH_FINDINGS.md (removed >= Σ_hit(|S|-1) + 2), and to its
# +0 form (removed >= Σ_hit(|S|-1)).  NOT a counterexample to L-meta-951 (size 12 >= base 7).
# System: n=8, S=(0,1,2,3,4,5), T=(5,6,7); |S ∩ T| = 1.  NOT reads h = x0, single minterm M={0}; S is hit, T unhit.
# Trick: junk gate w18 = OR(x1..x5) AND x6 reads S's top internal gate and feeds T's output, so S's 4 internal
# gates stay live after x0=1.  Run from the repo root:  python3 tools/l951_charging/agents/R_counterexample.py
import sys
sys.argv = ['x']
exec(open('tools/l951_charging/agents/restr951.py').read().split('\nt0=time.time()')[0])
n = 8; sets = [(0, 1, 2, 3, 4, 5), (5, 6, 7)]
gates = [('or', 1, 2),    # w8
         ('or', 8, 3),    # w9
         ('or', 9, 4),    # w10
         ('or', 10, 5),   # w11 = x1|..|x5   (top internal gate of S)
         ('or', 11, 0),   # w12 = OR(S)
         ('or', 5, 6),    # w13
         ('or', 13, 7),   # w14 = OR(T)
         ('not', 0, 0),   # w15 = NOT x0     (p = 7)
         ('and', 15, 6),  # w16 = ~x0 & x6
         ('or', 14, 16),  # w17 = OR(T)      (NOT is in T's output cone)
         ('and', 11, 6),  # w18 = junk <= x6
         ('or', 17, 18)]  # w19 = OR(T)
outs = [12, 19]; p = 7; s = len(gates); base = sum(len(S) - 1 for S in sets)
for x in range(1 << n):
    w = wires(n, gates, x)
    assert all(w[o] == int(any(x >> v & 1 for v in S)) for S, o in zip(sets, outs)), x
cone = set(); st = [outs[1]]
while st:
    w = st.pop()
    if w >= n and w not in cone: cone.add(w); st += [gates[w - n][1], gates[w - n][2]]
assert n + p in cone
live = restrict_count(n, gates, outs, p, [0], [1])
removed = s - live; hit = len(sets[0]) - 1
print(f'correct on all {1 << n} inputs; NOT in cone of o_T; size={s} base={base} (base+{s - base})')
print(f'M={{0}}: live={live} removed={removed} Σ_hit(|S|-1)={hit}  ->  removed - Σ_hit = {removed - hit}  (R needs >= 2, +0 form needs >= 0)')
