"""front-612 support-B harness: numerics for no_minCE angles 2 (merge-tree charging) and 3 (potentials).

Imports research/tools/w951 from a coord-951 checkout (W951_TOOLS, default /home/user/c951/tools); nothing copied.
Corpora (corpora/): fixh16_clean.jsonl (data-fixh16), w9/*.json (front-match work/notes951/w9),
w951 test instances (coord-951 research/tools/w951/tests/instances), and the f15 HARD4 circuit (scaffold-951).

For every correct one-NOT circuit and every set w with |S_w| >= 4, the canonical system is z = z_{S_w}
(all ones off S_w), atoms z + e_u (rule R*). If it is Good, systems.merges gives the union-find merge
gates M_w (|S_w| - 1 of them, in gate order). The 3rd+ merges are M_w[2:].

A candidate rule is a function rule(c, prof) -> (ok: bool, info) where prof is the per-set profile
computed here. run_rule reports the failures sorted by (s, n, W), smallest first.
Usage: python3 harness.py [baseline]"""
import glob, json, os, sys
sys.path.insert(0, os.environ.get('W951_TOOLS', '/home/user/c951/tools'))
from w951 import Circuit, load, systems

HERE = os.path.dirname(os.path.abspath(__file__))

def hard4_circuit():
    g = [('or', 0, 4), ('not', 4), ('or', 1, 6), ('or', 5, 6), ('or', 1, 7), ('or', 2, 8),
         ('or', 2, 10), ('or', 0, 12), ('and', 11, 13), ('or', 3, 14)]
    return Circuit.from_dict({'n': 6, 'sets': [[0, 1, 2, 3], [0, 4, 5]], 'gates': [list(x) for x in g], 'outs': [15, 9]})

def corpora():
    out = []
    for i, line in enumerate(open(os.path.join(HERE, 'corpora/fixh16_clean.jsonl'))):
        d = json.loads(line); d = d.get('c', d)
        out.append((f'fixh16:{i}', Circuit.from_dict(d)))
    for f in sorted(glob.glob(os.path.join(HERE, 'corpora/w9/*.json'))):
        try:
            for j, c in enumerate(load(f)):
                out.append((f'w9:{os.path.basename(f)}:{j}', c))
        except Exception as e:
            print('skip', f, type(e).__name__, e, file=sys.stderr)
    tdir = os.path.join(os.environ.get('W951_TOOLS', '/home/user/c951/tools'), 'w951/tests/instances')
    for f in sorted(glob.glob(os.path.join(tdir, '*.json'))):
        try:
            for j, c in enumerate(load(f)):
                out.append((f'inst:{os.path.basename(f)}:{j}', c))
        except Exception as e:
            print('skip', f, type(e).__name__, e, file=sys.stderr)
    for f in sorted(glob.glob(os.path.join(HERE, 'corpora/dc/*/*.jsonl'))):
        tag = os.path.relpath(f, os.path.join(HERE, 'corpora/dc'))
        for j, line in enumerate(open(f)):
            try:
                d = json.loads(line); d = d.get('c', d)
                if not isinstance(d, dict) or 'gates' not in d:
                    continue
                out.append((f'dc:{tag}:{j}', Circuit.from_dict(d)))
            except Exception as e:
                print('skip', tag, j, type(e).__name__, file=sys.stderr); break
    out.append(('f15:HARD4', hard4_circuit()))
    return out

def profile(c):
    """Per set w with |S_w| >= 4: dict(w, S, good, merges, cnt, third) or None if the merge run fails."""
    prof = []
    for w, S in enumerate(c.sets):
        if len(S) < 4:
            continue
        z = ((1 << c.n) - 1) & ~sum(1 << u for u in S)
        atoms = {u: z | (1 << u) for u in S}
        good, wz, B = systems.system(c, S, z, atoms)
        try:
            M, cnt = systems.merges(c, S, B)
        except AssertionError as e:
            prof.append(dict(w=w, S=S, good=good, merges=None, err=str(e)))
            continue
        prof.append(dict(w=w, S=S, good=good, merges=M, cnt=cnt, third=M[2:], hard=bool(wz[c.h_wire]) if c.h_wire is not None else None))
    return prof

def run_rule(rule, items, name):
    fails, n = [], 0
    for tag, c in items:
        prof = profile(c)
        if not prof:
            continue
        n += 1
        ok, info = rule(c, prof)
        if not ok:
            fails.append((c.s, c.n, c.W, tag, info))
    fails.sort(key=lambda t: t[:3])
    print(f'[{name}] tested {n} circuits with a |S|>=4 set: {len(fails)} failures')
    for f in fails[:5]:
        print('   ', f)
    return n, fails

# ---- baseline checks (not candidates; facts about the corpora) ----
def third_disjoint(c, prof):
    """B1: the 3rd+ merge gates of different |S|>=4 sets are pairwise disjoint."""
    seen = {}
    for p in prof:
        for g in p.get('third') or []:
            if g in seen:
                return False, dict(gate=g, sets=(seen[g], p['w']))
            seen[g] = p['w']
    return True, None

def third_not_free(c, prof):
    """B2: every 3rd+ merge gate of a Good canonical system lies in that set's output cone."""
    for p in prof:
        if not p['good'] or not p.get('third'):
            continue
        cone = set(c.cone(c.outs[p['w']]))
        bad = [g for g in p['third'] if g not in cone]
        if bad:
            return False, dict(w=p['w'], gates=bad)
    return True, None

if __name__ == '__main__':
    items = corpora()
    big = [t for t, c in items if c.n > 20]
    ok = [(t, c) for t, c in items if c.n <= 20 and len(c.nots) == 1 and c.is_correct()]
    print(f'corpora: {len(items)} circuits loaded, {len(big)} skipped (n > 20), {len(ok)} correct with one NOT')
    stats = dict(sets4=0, good=0, err=0, hard=0, third=0)
    for t, c in ok:
        for p in profile(c):
            stats['sets4'] += 1; stats['good'] += p['good']; stats['err'] += p['merges'] is None
            stats['hard'] += bool(p.get('hard')); stats['third'] += len(p.get('third') or [])
    print('profile:', stats)
    run_rule(third_disjoint, ok, 'B1 3rd+ merges disjoint across sets')
    run_rule(third_not_free, ok, 'B2 3rd+ merges inside own cone (Good systems)')
