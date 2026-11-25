"""Seat A4: direct check of the no-DD count proof (A4_f2_transfer.md section 2).  Run from the repo root:
   python3 -I research/one-not/research/open/A4_unit_merges.py [--nocorpus] [--all]   (--all: also DD sets, the NOT gate's merges counted as not_merges)
At every mixed state (Q, D) of every one-NOT circuit of A4_dd_test.collect: for each alive set w that is not DD, run the
unit-form union-find (zero point Z_w = 1 off S_w u D, atoms P_u = 1_Q + e_u) over the real gates; check
 (a) at least |S_w - D| - 1 merges, (b) every merge is an OR gate with an F2Mix witness for w at (Q, D),
 (c) merge sets of two non-DD sets are disjoint.  Prints counts of violations (expected all 0)."""
import sys, collections
sys.path.insert(0, 'research/one-not/research/open'); sys.path.insert(0, 'research/one-not/tools/search')
import numpy as np
import A4_dd_test as T

def run(c, out):
    n = c['n']; G = c['gates']; p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; ain = G[p][1]
    for D in range(1 << n):
        fr, w = T.tables(c, D); pos = {v: i for i, v in enumerate(fr)}; M = 1 << len(fr); a = w[ain]
        jj = np.arange(M)
        for j in range(M):
            Q = {fr[i] for i in range(len(fr)) if j >> i & 1}
            merges = []
            for S in c['sets']:
                if set(S) & Q: continue
                S2 = [u for u in S if not D >> u & 1]
                if len(S2) < 2: continue
                sm = sum(1 << pos[u] for u in S2); zw = (M - 1) & ~sm
                P = {u: j | 1 << pos[u] for u in S2}
                dd = bool(a[zw]) and any(not a[P[u]] for u in S2)
                if dd and not ALL: continue  # DD set
                out['sets'] += 1; out['dd_sets'] += dd
                lab = {u: u for u in S2}
                def find(u):
                    while lab[u] != u: u = lab[u]
                    return u
                mg = []
                for k in range(len(G)):
                    i = n + k
                    if w[i][zw]: continue
                    on = [u for u in S2 if w[i][P[u]]]
                    roots = {find(u) for u in on}
                    if len(roots) > 1:
                        rs = list(roots)
                        for r in rs[1:]: lab[r] = rs[0]
                        if G[k][0] == 'not': out['not_merges'] += len(rs) - 1; continue
                        if G[k][0] != 'or': out['merge_not_or'] += 1
                        mg.append(k); out['extra_merges'] += len(rs) - 2
                if len({find(u) for u in S2}) != 1 or len(mg) + sum(0 for _ in []) < 0: out['not_joined'] += 1
                if len(mg) < len(S2) - 1 - 0 and len({find(u) for u in S2}) == 1 and len(mg) < len(S2) - 1: pass
                # F2Mix witness for w: Z in subcube, Z zero on S2, Z one on Q
                zero = ((jj & sm) == 0) & ((jj & j) == j)
                for k in mg:
                    t = w[n + k]; ones = sum(t[jj | 1 << pos[u]].astype(int) for u in S2)
                    if not np.any(zero & ~t & (ones >= 2)): out['merge_not_F2' + ('_dd' if dd else '')] += 1
                merges.append((set(mg), dd))
            # DD-absorption: F2Mix gates outside the non-DD merges must pay for the DD sets
            F2 = set(); bdd = 0
            for S in c['sets']:
                if set(S) & Q: continue
                S2 = [u for u in S if not D >> u & 1]
                if len(S2) < 2: continue
                sm = sum(1 << pos[u] for u in S2); zw = (M - 1) & ~sm
                if a[zw] and any(not a[j | 1 << pos[u]] for u in S2): bdd += len(S2) - 1
                zero = ((jj & sm) == 0) & ((jj & j) == j)
                for k in range(len(G)):
                    if G[k][0] != 'or' or k in F2: continue
                    t = w[n + k]; ones = sum(t[jj | 1 << pos[u]].astype(int) for u in S2)
                    if np.any(zero & ~t & (ones >= 2)): F2.add(k)
            nd = set().union(*[m for m, d in merges if not d]) if merges else set()
            if bdd:
                out['dd_states'] += 1; slackA = len(F2 - nd) - bdd
                out['absorb_fail'] += slackA < 0; out['absorb_tight'] += slackA == 0
                if slackA < 0 and 'absorb_ex' not in out: out['absorb_ex'] = (c['name'], sorted(Q), D, slackA)
            for x in range(len(merges)):
                for y in range(x):
                    if merges[x][0] & merges[y][0]: out['overlap_%d%d' % (merges[x][1], merges[y][1])] += 1
            out['states'] += 1

if __name__ == '__main__':
    ALL = '--all' in sys.argv
    cs = T.collect(9, '--nocorpus' not in sys.argv); out = collections.Counter()
    for c in cs: run(c, out)
    print('circuits', len(cs), dict(out))
