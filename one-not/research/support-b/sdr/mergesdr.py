"""F1 (fable_worlds.md): MergeSDR on the full corpus. For every correct one-NOT circuit with >= 2 sets:
does a choice of zero points z_w exist with M_{z_w}(w) pairwise disjoint? (backtracking over the distinct merge
sets of each set, sets ordered by menu size). Also F1' = the same inside the two-world menu {0, top_w}.
A circuit with no disjoint choice is a MergeSDR counterexample (MergeFrac may still hold: then run the LP).
Merge sets: w951 systems.system + systems.merges, atoms z + e_u, all 2^(n-|S|) zero points.
Usage: python3 mergesdr.py OUT.jsonl  (corpora via ../supportB harness: set FRONT612_HARNESS to its dir)"""
import itertools, json, os, sys
from multiprocessing import Pool
sys.path.insert(0, os.environ.get('W951_TOOLS', '/home/user/c951/tools'))
sys.path.insert(0, os.environ.get('FRONT612_HARNESS', '/home/user/pequalnp-proofs/research/front/no_minCE/supportB'))
from w951 import Circuit, systems

def menu(c, w, only=None):
    S = c.sets[w]; rest = [v for v in range(c.n) if v not in S]; out = set()
    pts = only if only is not None else (sum(1 << v for v, b in zip(rest, bits) if b) for bits in itertools.product((0, 1), repeat=len(rest)))
    for z in pts:
        g, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
        out.add(frozenset(systems.merges(c, S, B)[0]))
    return out

def sdr(menus):
    order = sorted(range(len(menus)), key=lambda w: len(menus[w]))
    ms = [sorted(menus[w], key=len) for w in order]
    def bt(i, used):
        if i == len(ms): return True
        return any(bt(i + 1, used | M) for M in ms[i] if not (M & used))
    return bt(0, frozenset())

def job(item):
    tag, d = item
    try:
        c = Circuit.from_dict(d)
        if len(c.sets) < 2 or len(c.nots) != 1 or c.n - min(len(S) for S in c.sets) > 14 or not c.is_correct():
            return None
        full = [menu(c, w) for w in range(len(c.sets))]
        two = [menu(c, w, [0, ((1 << c.n) - 1) & ~sum(1 << u for u in S)]) for w, S in enumerate(c.sets)]
        return dict(tag=tag, n=c.n, s=c.s, m=len(c.sets), maxS=max(len(S) for S in c.sets), ess=c.is_essential(),
                    sdr=sdr(full), sdr2=sdr(two))
    except Exception as e:
        return dict(tag=tag, err=f'{type(e).__name__}: {e}')

if __name__ == '__main__':
    import harness as H
    seen, items = set(), []
    for t, c in H.corpora():
        k = json.dumps(c.to_dict(), sort_keys=True)
        if k in seen: continue
        seen.add(k); items.append((t, c.to_dict()))
    print(f'{len(items)} distinct circuits', flush=True)
    out = open(sys.argv[1], 'w'); stats = dict(tested=0, sdr_fail=0, sdr2_fail=0, err=0)
    with Pool(4) as P:
        for i, r in enumerate(P.imap_unordered(job, items, chunksize=8)):
            if r is None: continue
            if 'err' in r: stats['err'] += 1; out.write(json.dumps(r) + '\n'); continue
            stats['tested'] += 1; stats['sdr_fail'] += not r['sdr']; stats['sdr2_fail'] += not r['sdr2']
            if not r['sdr'] or not r['sdr2']: out.write(json.dumps(r) + '\n'); out.flush()
            if not r['sdr']: print('!!! MergeSDR FAILS:', r, flush=True)
            if stats['tested'] % 2000 == 0: print(stats, flush=True)
    print('FINAL', stats, flush=True)
