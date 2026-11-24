"""Task boards/tasks/rewire-read-not (cTAHG): random walk over correct one-NOT circuits (main's hunter moves: mutate,
rewrite; then prune), greedy R6 reduction to a circuit with no gate-saving rewiring, every gate read and the NOT read;
each new such circuit is tested for the one-point F2 STEP at every cube (f2_nonlocal_check).  Prints one json line per new
R6-irreducible circuit; a step failure is saved to one-not/data/witnesses/norewire/.
Run from one-not/:  python3 -I tools/kill_tests/norewire_hunt.py SECONDS SEED start.json ..."""
import sys, os, json, random, time, copy
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here); sys.path.insert(0, os.path.join(here, '..', 'search'))
import f2_nonlocal_check as FC
from norewire_step import correct, live, gate_saving_rewire, load
from core import prune
import core as _core
# main's hunt.py runs main() on import; take only its move functions (mutate, splice, rewrite) from the source
_src = open(os.path.join(here, '..', 'search', 'hunt.py')).read().split('\ndef main():')[0]
hunt = type(sys)('hunt_moves'); hunt.__dict__.update(vars(_core)); exec(compile(_src, 'hunt.py', 'exec'), hunt.__dict__)

def reduce_r6(d):
    while True:
        rw = gate_saving_rewire(d)
        if rw is None: return d
        r, pos, f = rw
        G = [list(x) for x in d['gates']]; G[r - d['n']][pos] = f
        d = prune(dict(d, gates=G))

def main():
    secs = float(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
    starts = [d for _, d in load(sys.argv[3:]) if sum(g[0] == 'not' for g in d['gates']) == 1 and d['n'] <= 8 and correct(d)]
    seen = set(); t0 = time.time(); tried = found = fails = notdead = dup = 0
    os.makedirs('data/witnesses/norewire', exist_ok=True)
    while time.time() - t0 < secs and starts:
        c = copy.deepcopy(rng.choice(starts))
        for _ in range(rng.randrange(1, 12)):
            c2 = hunt.mutate(c, rng, 1) if rng.random() < 0.6 else hunt.rewrite(c, rng, 1)
            if sum(g[0] == 'not' for g in c2['gates']) == 1 and correct(c2): c = c2
        c = prune(c)
        if sum(g[0] == 'not' for g in c['gates']) != 1: continue
        tried += 1
        d = reduce_r6(c)
        if sum(g[0] == 'not' for g in d['gates']) != 1:
            notdead += 1; continue
        Nw = [d['n'] + k for k, g in enumerate(d['gates']) if g[0] == 'not'][0]
        if Nw not in live(d):
            notdead += 1; continue
        key = json.dumps(d)
        if key in seen:
            dup += 1; continue
        seen.add(key); found += 1
        r = FC.analyse(dict(d, name='h'), verbose=False)['F2']
        rec = dict(n=d['n'], s=len(d['gates']), base=r['base_empty'], F2=r['F_empty'], step_fail=r['step_fail'],
                   step_fail_nonlocal=r['step_fail_nonlocal'], nonlocal_cubes=r['nonlocal_cubes'], count_fail=r['count_fail'])
        if r['step_fail'] or r['count_fail']:
            fails += 1
            json.dump(d, open('data/witnesses/norewire/norewire_%d_%d.json' % (int(sys.argv[2]), found), 'w'))
            rec['saved'] = True
        print(json.dumps(rec), flush=True)
    print('SUMMARY walks', tried, 'NOT dead after R6 reduction', notdead, 'R6-irreducible with NOT read: new', found,
          'repeat', dup, 'with a step or count failure', fails, file=sys.stderr)

if __name__ == '__main__':
    main()
