"""A3: search for a counterexample to MixedStep on irreducible one-NOT circuits (no gate-saving rewiring, NOT gate read),
with more inputs / sets than earlier runs, and count the states of negative slack.
Run from repo root:  python3 -I one-not/research/open/A3_mixed_search.py SECONDS SEED [NMAX=10] [out.jsonl]
Evaluation 1: continuous.mixed_margin (numpy).  Evaluation 2 (independent, naive bit-parallel): asteroid.ext_mixed.direct_mixedstep,
run on every circuit with n <= 6 and on every candidate counterexample.  mixed_margin >= 1 means MixedStep fails."""
import sys, os, json, time, random, copy
sys.path[:0] = ['one-not/tools/search', '.']
import numpy as np
from core import nots, correct, prune, reduce, faces_incorrect, tables
import core, continuous as C, hunt as H, irreducible as I
from conjectures import is_irreducible_read_not

def extend(c, rng):
    """more inputs / sets, still correct: add k new points and 1-2 new sets (mixing old and new points) read by fresh OR trees."""
    c = copy.deepcopy(c); n = c['n']; k = rng.choice([1, 2, 3]); n2 = n + k
    sh = lambda x: x if x < n else x + k
    G = [[g[0]] + [sh(a) for a in g[1:]] for g in c['gates']]; outs = [sh(o) for o in c['outs']]; sets = [list(S) for S in c['sets']]
    for _ in range(rng.choice([1, 1, 2])):
        S = sorted(set(rng.sample(range(n2), rng.choice([2, 3, 4]))) | {rng.randrange(n, n2)})
        if len(S) < 2: continue
        cur = S[0]
        for u in S[1:]: G.append(['or', cur, n2 + len(G)] if False else ['or', cur, u]); cur = n2 + len(G) - 1
        sets.append(S); outs.append(cur)
    return {"n": n2, "sets": sets, "gates": G, "outs": outs}

def junk2(c, rng, steps, mx):
    cur = copy.deepcopy(c)
    for _ in range(steps):
        new = (H.rewrite if rng.random() < 0.5 else H.mutate)(cur, rng, mx)
        if len(new['gates']) <= 40 and nots(new) <= mx and correct(new): cur = new
    return cur

def state_stats(c):
    """(margin m, #states, #base>0, #negative slack, min slack) over all 3^n mixed states."""
    n = c['n']; ns = pos = neg = 0; mn = 10 ** 9
    for R in range(1 << n):
        cnt, base = C.slack_table(c, R, parts=True); sl = cnt - base
        ns += len(sl); pos += int((base > 0).sum()); neg += int((sl < 0).sum()); mn = min(mn, int(sl.min()))
    m, k = C.mixed_margin(c)
    return m, ns, pos, neg, mn

def main():
    secs = float(sys.argv[1]); seed = int(sys.argv[2]); nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    outp = sys.argv[4] if len(sys.argv) > 4 else f'one-not/research/open/A3_found_seed{seed}.jsonl'
    MAXNOT = int(os.environ.get('MAXNOT', '1'))   # 1 = the one-NOT region; 2 = outside the theorem, to reach states of negative slack
    rng = random.Random(seed); starts = I.load_starts(9)
    starts += [(nm + ' ortree', H.or_tree(c['n'], c['sets'])) for nm, c in starts]
    t0 = time.time(); seen = set(); T = dict(runs=0, irr=0, tested=0, states=0, pos=0, neg=0, minsl=10 ** 9, worst=-10 ** 9, direct=0, fails=0)
    hist = {}
    with open(outp, 'w') as f:
        while time.time() - t0 < secs:
            nm, c = rng.choice(starts)
            for _ in range(rng.choice([0, 1, 1, 2])):
                if c['n'] + 3 <= nmax: c = extend(c, rng)
            if c['n'] > nmax: continue
            c = junk2(c, rng, rng.choice([0, 3, 8, 20]), MAXNOT)
            if not 1 <= nots(c) <= MAXNOT: continue
            r = reduce(c, rng, keep_not=rng.random() < 0.7); T['runs'] += 1
            if r['n'] > nmax or not (is_irreducible_read_not(r) and faces_incorrect(r) if MAXNOT == 1 else (1 <= nots(r) <= MAXNOT and core.all_read(r) and core.gate_saving_rewire(r) is None)): continue
            T['irr'] += 1; kk = I.key(r)
            if kk in seen: continue
            seen.add(kk)
            m, ns, pos, neg, mn = state_stats(r)
            T['tested'] += 1; T['states'] += ns; T['pos'] += pos; T['neg'] += neg; T['minsl'] = min(T['minsl'], mn); T['worst'] = max(T['worst'], m)
            hist[r['n']] = hist.get(r['n'], 0) + 1
            if r['n'] <= 7:
                from asteroid.ext_mixed import direct_mixedstep
                ok, _, _ = direct_mixedstep({"n": r['n'], "sets": r['sets'], "gates": r['gates'], "outs": r['outs']}); T['direct'] += 1
                assert ok == (m <= 0), ("evaluations disagree", r)
            if m >= 1:
                T['fails'] += 1; f.write(json.dumps(dict(r, margin=m)) + '\n'); f.flush(); print('CANDIDATE', json.dumps(r))
            elif T['tested'] <= 3 or T['tested'] % 20 == 0:
                f.write(json.dumps(dict(r, margin=m, states=ns, neg=neg)) + '\n')
    print(json.dumps(dict(T, seed=seed, nmax=nmax, secs=round(time.time() - t0), by_n=hist)))
if __name__ == "__main__": main()
