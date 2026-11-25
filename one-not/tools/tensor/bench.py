"""Benchmark: tensor backend against the existing scripts' core loops, on the same circuits.  From the repo root:
    python3 -I one-not/tools/tensor/bench.py [speed|maxn]
speed: (a) A5_transfer_t1 / continuous 'mixed' inner loop: slack_table(c, R, parts=True) for every R;  (b) slack at every cube;
       (c) the DD-state test at the head of A14_bottom_hall.analyse / A7 check_state, at every one of the 3^n states.
maxn : largest n whose tables / cube slack / mixed statistics run here (time and peak RSS)."""
import os, sys, time, resource
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'search'))
import numpy as np
import bits, corpus, core, continuous as C
from test_tensor import dd_slow

def tm(f, *a, **k):
    t = time.perf_counter(); r = f(*a, **k); return time.perf_counter() - t, r

def speed():
    cs = [c for c in corpus.collect(9) if core.nots(c) <= 1 and 6 <= c['n'] <= 9 and any(g[0] == 'or' for g in c['gates'])]
    print('| circuit | n | gates | A5 loop (slack_table over all R) s | tensor mixed_slack s | speed-up | tensor mixed_stats s | speed-up | cube slack: old s | new s | speed-up | DD head (3^n states): old s | new s | speed-up |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    T = np.zeros(8)
    for c in cs:
        n = c['n']; bits.mixed_slack(c, rs=[0])     # warm the constant tables
        t1, _ = tm(lambda: [C.slack_table(c, R, parts=True) for R in range(1 << n)])
        t2, _ = tm(bits.mixed_slack, c); t2s, _ = tm(bits.mixed_stats, c)
        t3, _ = tm(lambda: [C.slack_table(c, 0, parts=True) for _ in range(50)]); t3 /= 50
        t4, _ = tm(lambda: [bits.slack_cubes(c, parts=True) for _ in range(50)]); t4 /= 50
        if core.nots(c) == 1 and n <= 8:
            t5, _ = tm(dd_slow, c); t6, _ = tm(bits.dd_states, c)
        else: t5 = t6 = float('nan')
        T += [t1, t2, t3, t4, 0 if t5 != t5 else t5, 0 if t6 != t6 else t6, t2s, 0]
        print('| %s | %d | %d | %.3f | %.4f | %.0fx | %.4f | %.0fx | %.4f | %.5f | %.1fx | %.2f | %.4f | %s |' % (c['name'].split('/')[-1], n, len(c['gates']), t1, t2, t1 / t2, t2s, t1 / t2s, t3, t4, t3 / t4, t5, t6, ('%.0fx' % (t5 / t6)) if t5 == t5 else 'n/a'))
    print('| TOTAL | | | %.2f | %.3f | %.0fx | %.3f | %.0fx | %.3f | %.4f | %.1fx | %.1f | %.3f | %.0fx |' % (T[0], T[1], T[0] / T[1], T[6], T[0] / T[6], T[2], T[3], T[2] / T[3], T[4], T[5], T[4] / T[5]))

def big():
    print('| circuit | n | gates | slack at all cubes: continuous.slack_table s | tensor s | speed-up | tensor tables s |')
    print('|---|---|---|---|---|---|---|')
    cs = {c['name'].split('/')[-1].split(':')[0]: c for c in corpus.collect(24)}
    for nm in ['twin_tree_or2.json', 'match_c_k7.json', 'twin_tree_k5_c3.json']:
        c = cs[nm]; n = c['n']; t1, a = tm(C.slack_table, c, 0, False, True); t2, b = tm(bits.slack_cubes, c, False, True); t3, _ = tm(bits.tables, c)
        assert (a[0] == b[0]).all() and (a[1] == b[1]).all()
        print('| %s | %d | %d | %.2f | %.3f | %.0fx | %.3f |' % (nm, n, len(c['gates']), t1, t2, t1 / t2, t3), flush=True)

def synth(n):
    """Boolean sums of the n cyclic triples {i, i+1, i+2}: 2 OR gates per set, 2n gates in all (no NOT gate)."""
    sets = [[i, (i + 1) % n, (i + 2) % n] for i in range(n)]; G = []; outs = []
    for S in sets:
        G.append(['or', S[0], S[1]]); G.append(['or', n + len(G) - 1, S[2]]); outs.append(n + len(G) - 1)
    return {'n': n, 'sets': sets, 'gates': G, 'outs': outs}

def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024

def maxn():
    """Run each step in a fresh process (clean peak RSS).  Usage: bench.py maxn [N ...] runs the cube slack and the tables at those n."""
    import subprocess
    for n in [int(x) for x in sys.argv[2:]] or [20, 22, 24, 26, 27]:
        r = subprocess.run([sys.executable, '-I', __file__, 'one', str(n)], capture_output=True, text=True); print(r.stdout.strip() or r.stderr.strip()[-200:], flush=True)

def one():
    n = int(sys.argv[2]); c = synth(n)
    t1, T = tm(bits.tables, c); r1 = rss(); del T
    t2, s = tm(bits.slack_cubes, c); print('synthetic n=%d (%d gates): tables %.2f s; cube slack %.2f s (slack(empty) = %d), peak RSS %.0f MB' % (n, len(c['gates']), t1, t2, s[0], rss()))

def mixed_n():
    for nm in ['twin_tree_or2.json', 'match_c_k7.json']:
        c = {x['name'].split('/')[-1].split(':')[0]: x for x in corpus.collect(24)}[nm]
        t, st = tm(bits.mixed_stats, c); print('%s n=%d (%d gates): mixed_stats over %d states %.1f s, peak RSS %.0f MB, min slack %d' % (nm, c['n'], len(c['gates']), st['states'], t, rss(), st['min_slack']), flush=True)

if __name__ == '__main__':
    {'speed': speed, 'big': big, 'maxn': maxn, 'one': one, 'mixed_n': mixed_n}[sys.argv[1] if len(sys.argv) > 1 else 'speed']()
