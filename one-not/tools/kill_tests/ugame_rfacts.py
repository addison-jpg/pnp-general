"""U-game (won/lost) against the local MinCE facts R1-R5', R+ (f2_rplus_all.check) on every correct one-NOT circuit given.
(cTAHG, 2026-11-24)  python3 -I one-not/tools/kill_tests/ugame_rfacts.py FILE_OR_DIR ..."""
import sys, json, os
import numpy as np
sys.path.insert(0, 'tools/kill_tests'); sys.path.insert(0, 'tools')
import ugame, f2_rplus_all as RP
from w951 import Circuit
seen = set(); rows = []
for p in sys.argv[1:]:
    files = []
    if os.path.isdir(p):
        for root, _, fs in os.walk(p):
            files += [os.path.join(root, f) for f in sorted(fs) if f.endswith(('.json', '.jsonl'))]
    else:
        files = [p]
    for f in files:
        lines = open(f).read().splitlines() if f.endswith('.jsonl') else [open(f).read()]
        for i, l in enumerate(lines):
            try:
                c = Circuit.from_dict(json.loads(l))
            except Exception:
                continue
            if len(c.nots) != 1 or c.n > 12 or not c.is_correct():
                continue
            d = dict(n=c.n, sets=[list(S) for S in c.sets], gates=[list(g) for g in c.gates], outs=list(c.outs))
            key = json.dumps(d)
            if key in seen: continue
            seen.add(key)
            n = d['n']; N = n + 1; PP = 1 << N; I2 = np.arange(PP, dtype=np.int64)
            L = [((I2 >> k) & 1).astype(bool) for k in range(n)]; y = ((I2 >> n) & 1).astype(bool)
            for g in d['gates']:
                if g[0] == 'not': L.append(y.copy())
                elif g[0] == 'and': L.append(L[g[1]] & L[g[2]])
                else: L.append(L[g[1]] | L[g[2]])
            won = ugame.solve(N, d['sets'], [L[o].astype(np.int8).tolist() for o in d['outs']]) is not None
            try:
                r = RP.check(d, verbose=False)[0]
            except Exception as e:
                r = {'err': repr(e)[:80]}
            clean = r.get('Rplus') == 0 and all(r.get(k) for k in ('R1', 'R2', 'R3', 'R4', 'R5'))
            rows.append((f.split('/')[-1] + ':%d' % i, n, len(d['gates']), won, clean, r))
won = sum(1 for r in rows if r[3]); clean = [r for r in rows if r[4]]
print('circuits', len(rows), 'U-game won', won, 'R-clean', len(clean), 'R-clean and LOST', sum(1 for r in clean if not r[3]))
for r in rows:
    if not r[3]: print('LOST', r[0], 'n', r[1], 's', r[2], 'Rclean', r[4], {k: v for k, v in r[5].items() if k != 'skipped'})
