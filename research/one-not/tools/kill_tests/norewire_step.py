"""Task boards/tasks/rewire-read-not (cTAHG): keep the correct one-NOT circuits with every gate read (R4), the NOT gate
read, and NO gate-saving rewiring (MinCE.no_rewire, R6); on those, test the one-point F2 STEP at every cube with
positive base (f2_nonlocal_check.analyse).  A step failure on such a circuit is a witness for the board.
Run from research/one-not/:  python3 -I research/tools/kill_tests/norewire_step.py FILE_OR_DIR ...   (json, jsonl, {"circuit": ...} lines)"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2_nonlocal_check as FC

def tables(d):
    n = d['n']; P = 1 << n; idx = np.arange(P, dtype=np.int64)
    W = [((idx >> i) & 1).astype(bool) for i in range(n)]
    for g in d['gates']:
        if g[0] == 'not': W.append(~W[g[1]])
        elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
        else: W.append(W[g[1]] | W[g[2]])
    return W

def correct(d, W=None):
    W = W or tables(d); n = d['n']
    for o, R in zip(d['outs'], d['sets']):
        t = np.zeros(1 << n, bool)
        for u in R: t |= W[u]
        if not (W[o] == t).all(): return False
    return True

def live(d, G=None):
    G = G or d['gates']; n = d['n']; L = set(); st = list(d['outs'])
    while st:
        x = st.pop()
        if x < n or x in L: continue
        L.add(x); st += G[x - n][1:]
    return L

def gate_saving_rewire(d):
    """first rewire (gate wire r, input pos, new wire f) that keeps every output correct and leaves a gate unread"""
    n = d['n']; G = d['gates']
    for k, g in enumerate(G):
        r = n + k
        desc = {r}
        for kk in range(k + 1, len(G)):
            if any(j in desc for j in G[kk][1:]): desc.add(n + kk)
        for pos in range(1, len(g)):
            for f in range(n + k):                      # earlier wires: no reordering needed
                if f in desc or f == g[pos]: continue
                G2 = [list(x) for x in G]; G2[k][pos] = f
                d2 = dict(d, gates=G2)
                if len(live(d2, G2)) < len(G) and correct(d2):
                    return (r, pos, f)
    return None

def load(paths):
    for p in paths:
        files = []
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                files += [os.path.join(root, f) for f in sorted(fs) if f.endswith(('.json', '.jsonl'))]
        else:
            files = [p]
        for f in files:
            txt = open(f).read()
            try:
                whole = json.loads(txt)
                items = whole if isinstance(whole, list) else [whole]
            except ValueError:
                items = [json.loads(l) for l in txt.splitlines() if l.strip().startswith('{')]
            for i, d in enumerate(items):
                if isinstance(d, dict) and 'circuit' in d: d = d['circuit']
                if isinstance(d, dict) and 'gates' in d and 'sets' in d and 'outs' in d:
                    yield '%s:%d' % (f, i), dict(n=d['n'], sets=d['sets'], gates=[list(g) for g in d['gates']], outs=d['outs'])

if __name__ == '__main__':
    seen = set(); tot = kept = fails = 0
    for name, d in load(sys.argv[1:]):
        key = json.dumps(d)
        if key in seen: continue
        seen.add(key)
        if sum(g[0] == 'not' for g in d['gates']) != 1 or d['n'] > 13: continue
        try:
            if not correct(d): continue
        except Exception:
            continue
        tot += 1
        L = live(d)
        Nw = [d['n'] + k for k, g in enumerate(d['gates']) if g[0] == 'not'][0]
        if len(L) != len(d['gates']) or Nw not in L: continue
        if gate_saving_rewire(d) is not None: continue
        kept += 1
        r = FC.analyse(dict(d, name=name), verbose=False)['F2']
        bad = r['step_fail'] > 0
        fails += bad
        print(json.dumps(dict(name=name, n=d['n'], s=len(d['gates']), base=r['base_empty'], F2=r['F_empty'],
                              step_fail=r['step_fail'], step_fail_nonlocal=r['step_fail_nonlocal'],
                              nonlocal_cubes=r['nonlocal_cubes'], count_fail=r['count_fail'])), flush=True)
    print('SUMMARY correct one-NOT', tot, 'kept (R4, NOT read, no gate-saving rewire)', kept, 'with an F2 step failure', fails,
          file=sys.stderr)
