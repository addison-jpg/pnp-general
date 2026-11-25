#!/usr/bin/env python3
"""Evaluator command of target (b), "PHC tightness at 1_Q" (Lemma D slack; F1_phc.md).  The contract of every evaluator command:
candidate JSON on stdin, last stdout line = {"score": number, "verdict": "ok" | "invalid" | "VIOLATION-CANDIDATE", ...}; exit 0.
Candidate: a circuit {"n", "sets", "gates", "outs"} that must be correct with exactly one NOT gate on a linear set system.
All of the checking is REF1's code (one-not/research/open/REF1_phc.py): the BottomPay instance at every mixed state (Q, D) when
3^n <= 2200, else at the empty state and the 2n one-point states (a fixed list, no sampling), and Lemma D's inequality
  slack(R) = |R| - sum_w (c_w(E - R) - 1) >= 0   over the deletion sets R (every R when there are <= 14 useful payers).
score = -(least slack over nonempty R); 0 means some instance is TIGHT, a positive score is a violation of Lemma D (PHC fails).
detail: instances, tight instances, the largest tight instance (sets K, useful payers m), so tight structures can be read off.
Truth tables come from the tensor backend (bits.tables)."""
import sys, os, json, random, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
for p in (os.path.join(ROOT, 'one-not', 'research', 'open'), os.path.join(ROOT, 'one-not', 'tools', 'tensor')): sys.path.insert(0, p)

def states(n):
    if 3 ** n <= 2200:
        for code in itertools.product(range(3), repeat=n):
            yield {v for v in range(n) if code[v] == 1}, {v for v in range(n) if code[v] == 2}
        return
    yield set(), set()
    for v in range(n): yield {v}, set(); yield set(), {v}

def main():
    import REF1_phc as R, bits
    t0 = time.time(); c = json.load(sys.stdin); out = lambda **k: print(json.dumps(k))
    try:
        n, G = c['n'], c['gates']
        assert sum(g[0] == 'not' for g in G) == 1, 'need exactly one NOT gate'
        assert all(len(set(x) & set(y)) <= 1 for x, y in itertools.combinations(c['sets'], 2)), 'sets are not linear'
        assert n <= 16 and len(G) <= 400 and bits.correct(c), 'not a correct circuit'
    except Exception as e: return out(score=-99, verdict='invalid', why=str(e)[:200])
    T = bits.tables(c); W = [bits.to_int(r) for r in T]; X = W[:n]; rng = random.Random(0)
    lo = None; ninst = tight = 0; big = None; viol = None; exh = True
    for Q, D in states(n):
        inst = R.bottompay_instances(c, W, X, Q, D, rng)
        if inst is None: continue
        r = R.check(inst, rng); ninst += 1; exh = exh and r['exh']
        if r['min_all'] < 0 and viol is None:
            js = inst.to_json(); js['R'] = [inst.useful[i] for i in range(inst.m) if r['arg'] >> i & 1]
            viol = {'kind': 'lemmaD', 'slack': r['min_all'], 'instance': js, 'circuit': c, 'Q': sorted(Q), 'D': sorted(D)}
        mn = r['min_nontriv']
        if mn is None: continue
        lo = mn if lo is None else min(lo, mn)
        if mn == 0:
            tight += 1
            if big is None or (inst.K, inst.m) > (big['K'], big['m']): big = {'K': inst.K, 'm': inst.m, 'Q': sorted(Q), 'D': sorted(D), 'tight_sets': r['tight']}
    if lo is None: return out(score=-50, verdict='ok', why='no BottomPay instance with two DD sets', instances=ninst)
    res = dict(score=-lo, verdict='VIOLATION-CANDIDATE' if viol else 'ok', rank=-lo + min(0.9, 0.01 * tight) + (min(0.09, 0.001 * big['K'] * big['m']) if big else 0),
               instances=ninst, tight=tight, largest_tight=big, exhaustive=exh, gates=len(G), seconds=round(time.time() - t0, 2))
    if viol: res['witness'] = viol
    out(**res)

if __name__ == '__main__': main()
