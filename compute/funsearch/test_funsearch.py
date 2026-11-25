#!/usr/bin/env python3
"""python3 -I compute/funsearch/test_funsearch.py     (repository root; NumPy only, no model, about 20 s)
1. the batched tensor evaluator against core.correct on random circuits (correct and broken), and the essential-NOT flag
2. recheck.py (independent, pointwise) agrees with it; its selftest; a nonlinear system is rejected
3. the sandbox blocks network, processes, writes, loops, memory
4. the registry: (a) to (d) are generated; an OPEN line with an evaluator becomes a target
5. the whole loop with the no-model proposer on k1:fano, and on the toy OPEN cell where a planted violation must be FOUND by the
   loop, CONFIRMED by the separate recheck process, and a tampered witness REJECTED"""
import os, sys, json, random, subprocess, tempfile, argparse
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..')); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'search')); sys.path.insert(0, os.path.join(ROOT, 'one-not', 'research', 'open'))
os.chdir(ROOT)
import evalbatch, sandbox, targets as T, fs, core, REF1_phc as R

def main():
    rng = random.Random(5); allsys = T.systems(); n_ok = n_bad = n_ess = 0
    for name in ('PG(2,2)', 'grid33', 'PG(2,3)', 'AG(2,4)'):
        n, sets, _ = allsys[name]; cs = []
        for _ in range(12):
            c = R.switch_circuit(rng, sets, n); c['gates'] = [g[:3] for g in c['gates']]      # REF1 writes some 3-input ANDs; core reads two
            if rng.random() < .5:                                                # break it: retarget one gate input
                k = rng.randrange(len(c['gates'])); g = c['gates'][k]; g[1] = rng.randrange(n + k)
            cs.append({'gates': c['gates'], 'outs': c['outs']})
        res = evalbatch.score(cs, n, sets)
        for c, r in zip(cs, res):
            full = dict(c, n=n, sets=sets)
            if n <= 13: assert core.correct(full) == (r['verdict'] == 'ok'), (name, r)
            with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
                json.dump(dict(r.get('circuit', full), claim={'score': r['score']} if 'circuit' in r else {}), f)
            rc = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'recheck.py'), '--file', f.name], capture_output=True).returncode; os.unlink(f.name)
            assert (rc == 0) == (r['verdict'] == 'ok'), (name, r, rc)
            n_ok += r['verdict'] == 'ok'; n_bad += r['verdict'] != 'ok'; n_ess += bool(r.get('essential'))
            assert r['verdict'] != 'ok' or r['score'] <= 0
    assert n_ok >= 8 and n_bad >= 8
    print('1-2. evaluator == core.correct == recheck.py on %d circuits (%d correct, %d broken, %d with an essential NOT); none below base' % (n_ok + n_bad, n_ok, n_bad, n_ess))
    seeds = T.K1Target('t', ['PG(2,2)'], allsys)
    outs = [sandbox.run_program(s, seeds.preamble, 'build', seeds.instances) for s in seeds.seeds]; res = seeds.evaluate(outs)
    assert [r['score'] for r in res] == [0, -2, -6] and [r['detail']['PG(2,2)']['essential'] for r in res] == [False, False, True], res
    subprocess.check_call([sys.executable, '-I', os.path.join(HERE, 'recheck.py'), '--selftest'])
    subprocess.check_call([sys.executable, '-I', os.path.join(HERE, 'sandbox.py')])
    reg = T.registry(); kinds = {t.kind for t in reg.values()}
    assert 'k1:small' in reg and 'phc:fano' in reg and {'k1', 'command'} <= kinds
    ot = T.open_targets([os.path.join(HERE, 'tests', 'open_cell.md')]); assert len(ot) == 1
    print('4. registry: %d targets (%s); test OPEN cell -> %s' % (len(reg), ', '.join('%s %d' % (k, sum(t.kind == k for t in reg.values())) for k in sorted(kinds)), ot[0].name))
    r = reg['phc:fano']; o = [sandbox.run_program(r.seeds[0], r.preamble, 'build', r.instances)]; e = r.evaluate(o)[0]
    assert e['verdict'] == 'ok' and e['score'] <= 0, e
    print('   phc:fano seed:', e['detail']['fano'])
    with tempfile.TemporaryDirectory() as d:
        a = argparse.Namespace(target='k1:fano', proposer='mutate', model=None, minutes=0, samples=160, out=os.path.join(d, 'k1'), islands=3, batch=8, k=2, reset=25, seed=1, jobs=3, timeout=10)
        s = fs.run(a); assert not s['beat_base'] and s['best']['fano|any'] == 0 and s['resets'] >= 1, s
        a2 = argparse.Namespace(dir=a.out, dry=True, who=None, run=None); fs.record(a2)
        # the toy OPEN cell: the registry is patched to hold it, the loop must find the planted violation
        toy = ot[0]; toy.seeds = ['def build():\n    return {"xs": [1, 2, 3]}\n']; orig = T.registry
        T.registry = lambda: {toy.name: toy}
        try:
            b = argparse.Namespace(target=toy.name, proposer='mutate', model=None, minutes=0, samples=400, out=os.path.join(d, 'toy'), islands=2, batch=8, k=2, reset=50, seed=2, jobs=3, timeout=10)
            s = fs.run(b); assert s['beat_base'] and s['candidates'] >= 1, s
        finally: T.registry = orig
        c = sorted(os.listdir(os.path.join(b.out, 'candidates')))[0]; p = os.path.join(b.out, 'candidates', c)
        assert subprocess.run([sys.executable, '-I', os.path.join(HERE, 'recheck.py'), '--rerun', p], capture_output=True).returncode == 0
        w = json.load(open(p)); w['instance'] = {'xs': [1, 2, 3]}; json.dump(w, open(p, 'w'))
        assert subprocess.run([sys.executable, '-I', os.path.join(HERE, 'recheck.py'), '--rerun', p], capture_output=True).returncode == 1
    print('5. loop ok: k1:fano (no model) stays at base; the planted toy violation was found, confirmed by the separate recheck, and a tampered witness rejected')
    print(json.dumps({'states': n_ok + n_bad, 'ok': True}))

if __name__ == '__main__': main()
