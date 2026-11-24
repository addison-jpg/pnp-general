# The AVERAGE over chains (all orders of the points) of the partial sums of gain - cost.  Serves README items L5, L6, C3.
# By the chain sum (L5) the partial sum after i points of a chain is slack(empty) - slack(Q_i), so the average over all orders is
#   A(i) = slack(empty) - mean over |D| = i of slack(D)      (exact, as a fraction; no sampling).
# Question tested: is A(i) >= 0 at every prefix length i?  Also the Cesaro mean of the A(i) (the L6 form) and the least i with A(i) >= 0.
# Run from the repo root: python3 -I one-not/tools/kill_tests/c3_avg.py [files...]
import sys, os, json, glob
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L, c3_allq as A
files = sys.argv[1:] or sorted(glob.glob('one-not/data/witnesses/*.json') + glob.glob('one-not/data/witnesses/nonlocal/*.json'))
print('| circuit | n | slack(empty) | A(1), A(2), ... (rounded) | prefix lengths with A(i) < 0 | least i >= 1 with A(i) >= 0 | Cesaro mean of A(1..n) |'); print('|---|---|---|---|---|---|---|')
neg = tot = 0
for f in files:
    d = json.load(open(f))
    if d['n'] > 16: continue
    c = L.mk(d.get('name', f), d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
    if c is None: continue
    n = d['n']; cnt, base, _ = A.slack_table(c); s = [0] * (n + 1); m = [0] * (n + 1)
    for Q in range(1 << n):
        k = bin(Q).count('1'); s[k] += cnt[Q] - base[Q]; m[k] += 1
    s0 = cnt[0] - base[0]; Av = [s0 - Fraction(s[i], m[i]) for i in range(n + 1)]
    assert Av[n] == s0
    bad = [i for i in range(1, n + 1) if Av[i] < 0]; tot += 1; neg += bool(bad)
    print('|', os.path.basename(f), '|', n, '|', s0, '|', ' '.join('%.2f' % float(x) for x in Av[1:]), '|', bad, '|', min(i for i in range(1, n + 1) if Av[i] >= 0), '|', '%.2f' % float(sum(Av[1:]) / n), '|')
print('circuits with some negative averaged prefix: %d of %d' % (neg, tot))
