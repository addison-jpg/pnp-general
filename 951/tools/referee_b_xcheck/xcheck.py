"""Independent cross-check of referee_b support survey, built on tools/w951 + own max-flow (no referee code).
Usage: python3 xcheck.py  (run from anywhere). Writes results.json / results.txt next to itself."""
import sys, os, json, glob, ast
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = '/home/user/pnp-general/951'
sys.path.insert(0, ROOT + '/tools')
from w951 import Circuit, systems
from w951.circuit import z_of
from collections import deque

def maxflow_ok(demand, support):
    """Dinic-free simple augmenting-path bipartite b-matching: sets w (cap demand) -> gates (cap 1)."""
    gates = {}
    ws = [w for w in demand if demand[w] > 0]
    tot = sum(demand[w] for w in ws)
    # node ids: 's', ('w',w), ('g',g), 't'; residual capacities in dict
    cap = {}; adj = {}
    def add(a, b, c):
        cap[(a, b)] = c; cap.setdefault((b, a), 0)
        adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    for w in ws:
        add('s', ('w', w), demand[w])
        for g in support[w]:
            add(('w', w), ('g', g), 1); add(('g', g), 't', 1)
    flow = 0
    while flow < tot and 't' in adj:
        prev = {'s': None}; q = deque(['s'])
        while q and 't' not in prev:
            a = q.popleft()
            for b in adj[a]:
                if b not in prev and cap[(a, b)] > 0:
                    prev[b] = a; q.append(b)
        if 't' not in prev: break
        b = 't'
        while prev[b] is not None:
            a = prev[b]; cap[(a, b)] -= 1; cap[(b, a)] += 1; b = a
        flow += 1
    return flow >= tot

def analyse(c):
    n = c.n
    if sum(1 for g in c.gates if g[0] == 'not') != 1: return None
    if not any(len(S) >= 4 for S in c.sets): return None
    if not c.is_correct(): return {'skip': 'incorrect'}
    M, err = {}, None
    for w, S in enumerate(c.sets):
        z = z_of(n, S)
        atoms = {u: z | (1 << u) for u in S}
        good, wz, B = systems.system(c, S, z, atoms)
        try:
            Mw, _ = systems.merges(c, S, B)
        except AssertionError as e:
            err = (w, 'assert', repr(e)[:50]); Mw = None
        M[w] = Mw
    if err: return {'merge_error': err}
    big = [w for w, S in enumerate(c.sets) if len(S) >= 4]
    dem = {w: max(0, len(M[w]) - 2) for w in big}
    first2 = set()
    for w in M: first2 |= set(M[w][:2])
    cones = {w: {x for x in c.cone(c.outs[w]) if x >= n} for w in big}
    sup = {'A': {w: set(M[w][2:]) for w in big}, 'B': {w: set(M[w]) for w in big},
           'C': cones, 'D': {w: cones[w] - first2 for w in big}}
    r = {'demand': sum(dem.values())}
    for k in 'ABCD': r[k] = maxflow_ok(dem, sup[k])
    return r

def items():
    # hand-built: same file list as referee's output
    for line in open(ROOT + '/tools/referee_b/data/survey_handbuilt.txt'):
        p = line.split(' ')[0]
        d = json.load(open(ROOT + '/' + p))
        d = d[0] if isinstance(d, list) else d
        yield p, 0, Circuit.from_dict(d.get('circuit', d))
    # corpora: every circuit in ess,tri,q,climb with a |S|>=4 set (own selection)
    for d in ['ess', 'tri', 'q', 'climb']:
        for f in sorted(glob.glob('/home/user/corpora/%s/*.jsonl' % d)):
            for k, line in enumerate(open(f)):
                line = line.strip()
                if not line: continue
                try: j = json.loads(line)
                except Exception: continue
                if isinstance(j, dict) and 'circuit' in j: j = j['circuit']
                if not isinstance(j, dict) or 'gates' not in j or 'sets' not in j: continue
                if not any(len(S) >= 4 for S in j['sets']): continue
                yield 'corpora/%s/%s' % (d, os.path.basename(f)), k, Circuit.from_dict(j)

if __name__ == '__main__':
    res = {}
    for p, k, c in items():
        try: r = analyse(c)
        except Exception as e: r = {'skip': repr(e)[:80]}
        if r: res['%s#%d' % (p, k)] = r
    json.dump(res, open(HERE + '/results.json', 'w'), indent=0)
    # compare with referee
    ref = {}
    for fn in ['survey_handbuilt.txt', 'survey_corpora.txt']:
        for line in open(ROOT + '/tools/referee_b/data/' + fn):
            p, k, rest = line.split(' ', 2)
            ref['%s#%s' % (p, k)] = ast.literal_eval(rest.strip())
    hb = lambda key: not key.startswith('corpora/')
    for name, sel in [('hand', hb), ('corp', lambda k: not hb(k))]:
        ks = [k for k in res if sel(k) and 'A' in res[k]]
        print(name, len(ks), {x: sum(res[k][x] for k in ks) for x in 'ABCD'})
    print('skips/errors:', {k: v for k, v in res.items() if 'A' not in v})
    print('only mine:', [k for k in res if 'A' in res[k] and k not in ref][:20])
    print('only ref:', [k for k in ref if k not in res or 'A' not in res[k]][:20])
    dis = [(k, {x: (res[k][x], ref[k][x]) for x in 'ABCD' if res[k][x] != ref[k][x]} | ({'demand': (res[k]['demand'], ref[k]['demand'])} if res[k]['demand'] != ref[k]['demand'] else {}))
           for k in ref if k in res and 'A' in res[k] and (any(res[k][x] != ref[k][x] for x in 'ABCD') or res[k]['demand'] != ref[k]['demand'])]
    print('disagreements:', dis)
    print('B fails:', [k for k in res if 'A' in res[k] and not res[k]['B']])
