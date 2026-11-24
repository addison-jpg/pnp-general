# gc3.py (scaffold, desktop Coord 12:48 task (a)): for gate triples K, S(K) = sum_w min_z |M_z(w) ∩ K| (real merge sets, all real
# zero points z of w). Report max S(K)/3 and any K with S(K) > 3. All triples if C(#merge-gates,3) <= CAP, else CAP random.
#   python3 gc3.py IN.jsonl K R OUT.jsonl [CAP]
import sys, json, random, itertools
D = '/tmp/claude-0/-home-user/dbc7162d-d362-5361-8133-bb93548aca7c/scratchpad/f15'
sys.path.insert(0, D)
from mfrac import tables, merges
inp, K, R, outp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]; CAP = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
out = open(outp, 'w')
for i, line in enumerate(open(inp)):
    if i % K != R: continue
    d = json.loads(line); c = d.get('circuit', d); c = {k: c[k] for k in ('n', 'sets', 'gates', 'outs')}
    if c['n'] > 13: continue
    T = tables(c); Ms = merges(c, T)
    fam = [sorted({sum(1 << g for g in M) for M in m.values()}) for m in Ms]
    G = sorted({g for m in Ms for M in m.values() for g in M})
    rng = random.Random(i)
    trip = list(itertools.combinations(G, 3)) if len(G) < 40 and len(G) * (len(G)-1) * (len(G)-2) // 6 <= CAP else [tuple(rng.sample(G, 3)) for _ in range(CAP)]
    best = 0; bestK = None; over = 0
    for t in trip:
        km = (1 << t[0]) | (1 << t[1]) | (1 << t[2])
        s = sum(min(bin(M & km).count('1') for M in f) for f in fam if f)
        if s > best: best, bestK = s, t
        if s > 3: over += 1
    out.write(json.dumps({'src': d.get('src', d.get('name', i)), 'max_S': best, 'K': bestK, 'over': over, 'triples': len(trip)} | ({'circuit': c} if over else {})) + '\n')
