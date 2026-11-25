"""Generator of irreducible circuits with a read NOT gate (README L2 MinCE.no_rewire; board rewire-read-not).
Start: witness files (n <= 9, one NOT gate) and random junk (rewrite/mutate of hunt.py on witnesses and OR trees), then `reduce` with
RANDOM order of rewirings; mode A = plain random order, mode B = keep_not (reject rewirings that make the NOT gate unread).
Keep: correct, exactly one NOT, every gate read, no gate-saving rewiring, both faces (NOT -> 0, NOT -> 1) incorrect.
Then run predicate "C2 one-point step under no-rewire" on each. Run from the repo root:
  python3 -I research/one-not/tools/search/irreducible.py GEN_SECONDS [seed] [out.jsonl]   (output default: found/irreducible_seed<seed>.jsonl)"""
import sys, os, json, time, random, glob, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
from conjectures import step_under_no_rewire, is_irreducible_read_not
from hunt import mutate, rewrite, or_tree

EXTRA = ['research/one-not/data/fano_sat66.json', 'research/one-not/tools/w951/tests/instances', 'research/one-not/front/work/notes951/w9/fc']

def _items(p):
    for f in ([p] if os.path.isfile(p) else sorted(glob.glob(p + '/**/*.json', recursive=True))):
        try: whole = json.load(open(f))
        except ValueError: continue
        for i, d in enumerate(whole if isinstance(whole, list) else [whole]):
            if isinstance(d, dict) and 'circuit' in d: d = d['circuit']
            if isinstance(d, dict) and all(k in d for k in ('n', 'sets', 'gates', 'outs')):
                yield f"{os.path.basename(f)}:{i}", {"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']}

def load_starts(maxn=9):
    """Witness files plus the circuits the earlier norewire scripts used (fano_sat66, w951 test instances, cxT2 (fc)); one NOT gate, correct."""
    out = []
    for p in ['research/one-not/data/witnesses'] + EXTRA:
        for nm, c in _items(p):
            if c['n'] <= maxn and nots(c) == 1 and correct(c): out.append((nm, c))
    return out

def junk(c, rng, steps):
    cur = copy.deepcopy(c)
    for _ in range(steps):
        new = (rewrite if rng.random() < 0.5 else mutate)(cur, rng, 1)
        if len(new['gates']) <= 40 and nots(new) <= 1 and correct(new): cur = new
    return cur

def key(c): return json.dumps([c['n'], c['sets'], c['gates'], c['outs']])

def main():
    secs = float(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    outp = sys.argv[3] if len(sys.argv) > 3 else f'research/one-not/tools/search/found/irreducible_seed{seed}.jsonl'
    rng = random.Random(seed); starts = load_starts()
    starts += [(nm + ' ortree', or_tree(c['n'], c['sets'])) for nm, c in starts]
    t0 = time.time(); found = {}; runs = 0; stat = {'A': [0, 0, 0], 'B': [0, 0, 0]}   # runs, kept NOT read & irreducible, faces ok
    while time.time() - t0 < secs:
        nm, c = rng.choice(starts); mode = 'A' if rng.random() < 0.3 else 'B'
        c = junk(c, rng, rng.choice([0, 0, 3, 8, 20]))
        if nots(c) != 1: continue
        r = reduce(c, rng, keep_not=(mode == 'B')); runs += 1; stat[mode][0] += 1
        if not is_irreducible_read_not(r): continue
        stat[mode][1] += 1
        if not faces_incorrect(r): continue
        stat[mode][2] += 1
        found.setdefault(key(r), (nm, mode, r))
    t1 = time.time(); fails = 0; res = []
    os.makedirs(os.path.dirname(outp) or '.', exist_ok=True)
    with open(outp, 'w') as f:
        for k, (nm, mode, r) in found.items():
            m, det = step_under_no_rewire(r, 9)
            if m < 0: fails += 1
            f.write(json.dumps(dict(r, source=nm, mode=mode, step_margin=m, step_detail=det)) + '\n')
    print(f"seed {seed}: {runs} reductions in {t1 - t0:.0f}s; mode A (random) [runs, irreducible+NOT read, +faces incorrect] {stat['A']}; mode B (keep NOT) {stat['B']}; "
          f"distinct circuits {len(found)}; one-point step run on all in {time.time() - t1:.0f}s; step failures (margin < 0): {fails}; saved {outp}")
if __name__ == "__main__": main()
