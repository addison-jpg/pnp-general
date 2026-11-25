#!/usr/bin/env python3
"""The independent evaluator: standard library only, no code shared with evalbatch.py, bits.py or core.py.
  python3 -I workshop/compute/funsearch/recheck.py --file WITNESS.json [--nonlinear-ok]
WITNESS.json = {"kind": "k1-circuit", "n", "sets", "gates", "outs", "claim": {"base", "gates", "score"}}.  Checked, in this order:
  every set has >= 2 points inside 0..n-1, any two sets share at most one point (the hypothesis of L_meta_951);
  every gate is and/or with two earlier wires or not with one, at most ONE not gate, one output wire per set;
  POINTWISE: for each of the 2^n inputs the circuit is run gate by gate and every output is compared with the OR of its set
  (bit-sliced Python integers only above n = 18);
  gates = number of gates in the file (nothing pruned), base = sum(|S| - 1), score = base - gates, all equal to the claim.
Exit 0 iff everything holds.  Last stdout line: {"states": 2^n, "seconds": s, "score": k, ...} (the `runner` contract of boards.py).
A witness with score > 0 that passes is a circuit below base: it then needs a SECOND SEAT before any word changes on the board.
  python3 -I workshop/compute/funsearch/recheck.py --rerun WITNESS.json    kind "command": the stored argv is run again twice in fresh
  processes on the stored instance; confirmed iff both runs give the stored outcome (exit code 1, no traceback)
  python3 -I workshop/compute/funsearch/recheck.py --selftest"""
import sys, json, time, os, subprocess, tempfile

def check_circuit(w, nonlinear_ok=False):
    n, sets, gates, outs = w['n'], w['sets'], w['gates'], w['outs']
    assert type(n) is int and 1 <= n <= 26, 'n out of range'
    for S in sets:
        assert len(S) >= 2 and len(set(S)) == len(S) and all(type(u) is int and 0 <= u < n for u in S), 'bad set %r' % (S,)
    if not nonlinear_ok:
        for i in range(len(sets)):
            for j in range(i):
                assert len(set(sets[i]) & set(sets[j])) <= 1, 'sets %d and %d share two points' % (j, i)
    nots = 0
    for k, g in enumerate(gates):
        assert g[0] in ('and', 'or', 'not'), 'bad op at gate %d' % k
        assert len(g) == (2 if g[0] == 'not' else 3), 'bad arity at gate %d' % k
        assert all(type(a) is int and 0 <= a < n + k for a in g[1:]), 'gate %d reads a later wire' % k
        nots += g[0] == 'not'
    assert nots <= 1, '%d NOT gates' % nots
    assert len(outs) == len(sets) and all(type(o) is int and 0 <= o < n + len(gates) for o in outs), 'bad outputs'
    if n <= 18:
        prog = [(0 if g[0] == 'and' else 1 if g[0] == 'or' else 2, g[1], g[-1]) for g in gates]
        masks = [sum(1 << u for u in S) for S in sets]; v = [False] * (n + len(gates))
        for x in range(1 << n):
            for i in range(n): v[i] = bool(x >> i & 1)
            j = n
            for op, a, b in prog:
                v[j] = (v[a] and v[b]) if op == 0 else (v[a] or v[b]) if op == 1 else (not v[a]); j += 1
            for o, mk in zip(outs, masks):
                assert v[o] == bool(x & mk), 'wrong at input %d' % x
    else:
        N = 1 << n; full = (1 << N) - 1; t = []
        for i in range(n):
            blk = ((1 << (1 << i)) - 1) << (1 << i); rep = full // ((1 << (2 << i)) - 1); t.append(blk * rep)
        for g in gates: t.append(t[g[1]] & t[g[2]] if g[0] == 'and' else t[g[1]] | t[g[2]] if g[0] == 'or' else full ^ t[g[1]])
        for o, S in zip(outs, sets):
            want = 0
            for u in S: want |= t[u]
            assert t[o] == want, 'wrong output for set %r' % (S,)
    base = sum(len(S) - 1 for S in sets); score = base - len(gates); cl = w.get('claim', {})
    assert cl.get('base', base) == base and cl.get('gates', len(gates)) == len(gates) and cl.get('score', score) == score, 'claim does not match: base %d gates %d' % (base, len(gates))
    return {'states': 1 << n, 'base': base, 'gates': len(gates), 'score': score, 'nots': nots}

def rerun(w):
    assert w.get('kind') == 'command' and isinstance(w['argv'], list)
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, 'instance.json'); json.dump(w['instance'], open(p, 'w'))
        argv = [p if a == '{INSTANCE}' else a for a in w['argv']]
        for _ in range(2):
            r = subprocess.run(argv, input=json.dumps(w['instance']), capture_output=True, text=True, timeout=600)
            assert r.returncode == 1 and 'Traceback' not in r.stderr and 'usage:' not in r.stderr, 'rerun gave exit %d' % r.returncode
    return {'states': 2, 'reruns': 2}

def selftest():
    tri = {'n': 3, 'sets': [[0, 1, 2]], 'gates': [['or', 0, 1], ['or', 3, 2]], 'outs': [4], 'claim': {'score': 0}}
    assert check_circuit(tri)['score'] == 0
    bad = dict(tri, gates=[['or', 0, 1], ['and', 3, 2]])
    for w, kw in ((bad, {}), (dict(tri, claim={'score': 1}), {}),
                  ({'n': 4, 'sets': [[0, 1, 2], [0, 1, 3]], 'gates': [['or', 0, 1], ['or', 4, 2], ['or', 4, 3]], 'outs': [5, 6]}, {})):
        try: check_circuit(w, **kw); raise SystemExit('selftest: a bad witness passed')
        except AssertionError: pass
    share = {'n': 4, 'sets': [[0, 1, 2], [0, 1, 3]], 'gates': [['or', 0, 1], ['or', 4, 2], ['or', 4, 3]], 'outs': [5, 6]}
    assert check_circuit(share, nonlinear_ok=True)['score'] == 1                 # below "base" only because the sets share two points
    two = dict(tri, gates=[['not', 0], ['not', 3], ['or', 4, 1], ['or', 5, 2]], outs=[6])
    try: check_circuit(two); raise SystemExit('selftest: two NOT gates passed')
    except AssertionError: pass
    big = {'n': 19, 'sets': [[0, 18]], 'gates': [['or', 0, 18]], 'outs': [19]}
    assert check_circuit(big)['score'] == 0
    print('recheck selftest ok')

def main():
    a = sys.argv[1:]; t0 = time.time()
    if a[:1] == ['--selftest']: return selftest()
    if len(a) < 2 or a[0] not in ('--file', '--rerun'): sys.exit(__doc__)
    w = json.load(open(a[1]))
    try: r = rerun(w) if a[0] == '--rerun' else check_circuit(w, '--nonlinear-ok' in a)
    except AssertionError as e:
        print('REJECTED:', e); print(json.dumps({'states': 0, 'seconds': round(time.time() - t0, 3), 'ok': False})); sys.exit(1)
    r['seconds'] = round(time.time() - t0, 3); r['ok'] = True
    print('CONFIRMED' + (' BELOW BASE: a second seat must recheck before any word changes' if r.get('score', 0) > 0 else ''), a[1]); print(json.dumps(r))

if __name__ == '__main__': main()
