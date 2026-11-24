"""Synthesis test for the F2 step (dwV8p, on the owner's request: use the subtasks to synthesize F1 / F2).

F2(Q) = OR gates with a REAL witness (alive w, Z ⊇ Q avoiding S_w, u != u' in S_w, real g(Z) = 0, real g(Z+e_u) =
real g(Z+e_u') = 1). Step x_v := 1 at an alive point v: gain(v) = |F2(Q) minus F2(Q+v)|, cost(v) = Σ_{alive w ∋ v} d_w.

F1* (one statement for heavy and light v; proved from F1 + K0/K1 + Lemma D):
  g in F2(Q+v) and real g(Q+e_v) = 1  =>  h(Q+e_v) = 0, C_0(g)(Q+e_v) = 0, C_1(g)(Q+e_v) = 1, and every witness of g at
  Q+v has h(Z') = 1 (world 0) for a set w' with v not in S_w' and h(top_w') = 1 (type A).
SEE(v)  = {g in F2(Q) : real g(Q+e_v) = 1}   (F2-desc on the star's outputs at Z = Q, u = v produces such gates)
SURV(v) = SEE(v) ∩ F2(Q+v)                    (empty for heavy v by F1; type-A world-0 servants for light v by F1*)
SEE-STEP: exists v with |SEE(v) minus SURV(v)| >= cost(v). It implies the F2 step (SEE minus SURV is part of the gain).
K3(v)   = {g in F2(Q) : every witness of g at Q belongs to a set through v}   (these die: Lemma D / K3)
SEE+K3: exists v with |(SEE(v) minus SURV(v)) ∪ K3(v)| >= cost(v). Also implies the F2 step.
The script checks F1* and Lemma D, and counts SEE-STEP against the F2 step itself (exists v: gain >= cost), split
into heavy (some alive v heavy) / light instances.
Run from one-not/:  python3 work/notes951/lemmaK_referee/f2synth.py N SEED   |   ... f2synth.py files W1.json W2.json ...
"""
import json
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402


def run(c, Q, st, bad):
    n = c.n
    full = (1 << n) - 1
    T, T0, T1 = c.tables(), c.tables(force=0), c.tables(force=1)
    h = T[c.h_wire]
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive:
        return
    apts = sorted({u for i in alive for u in c.sets[i]})
    ors = [n + k for k, g in enumerate(c.gates) if g[0] == 'or']

    def wit(g, Qm):
        res = []
        for i, m in enumerate(sets):
            if m & Qm:
                continue
            free = full & ~(Qm | m)
            sub = free
            while True:
                Z = Qm | sub
                if not (T[g] >> Z & 1) and sum(1 for u in c.sets[i] if T[g] >> (Z | 1 << u) & 1) >= 2:
                    res.append((i, Z))
                if sub == 0:
                    break
                sub = (sub - 1) & free
        return res

    W = {g: wit(g, Q) for g in ors}
    F2 = {g for g in ors if W[g]}
    heavy_any = any(h >> (Q | 1 << v) & 1 for v in apts)
    see_ok = step_ok = heavy_see_ok = seek3_ok = False
    for v in apts:
        Qv = Q | 1 << v
        Wv = {g: wit(g, Qv) for g in ors}
        F2v = {g for g in ors if Wv[g]}
        # Lemma D: g in F2(Q+v) iff some witness at Q has v in Z
        for g in F2:
            if (g in F2v) != any(Z >> v & 1 for (_, Z) in W[g]):
                bad.append(('LemmaD', c.to_dict(), Q, v, g))
                return
        SEE = {g for g in F2 if T[g] >> Qv & 1}
        SURV = SEE & F2v
        for g in SURV:
            ok = (not (h >> Qv & 1)) and not (T0[g] >> Qv & 1) and (T1[g] >> Qv & 1)
            for (i, Z) in Wv[g]:
                ok = ok and (h >> Z & 1) and not (sets[i] >> v & 1) and (h >> (full & ~sets[i]) & 1)
            if not ok:
                bad.append(('F1*', c.to_dict(), Q, v, g))
                return
        cost = sum(len(c.sets[i]) - 1 for i in alive if sets[i] >> v & 1)
        gain = len(F2 - F2v)
        st['surv_nonempty_light'] += bool(SURV)
        if len(SEE - SURV) >= cost:
            see_ok = True
            if h >> Qv & 1:
                heavy_see_ok = True
        if gain >= cost:
            step_ok = True
        K3 = {g for g in F2 if all(sets[i] >> v & 1 for (i, _) in W[g])}
        if len((SEE - SURV) | K3) >= cost:
            seek3_ok = True
    key = 'heavy' if heavy_any else 'light'
    st[key] += 1
    st[key + '_step'] += step_ok
    st[key + '_see'] += see_ok
    st[key + '_seeK3'] += seek3_ok
    if step_ok and not seek3_ok and len(st['seek3_gap_examples']) < 2:
        st['seek3_gap_examples'].append((json.dumps(c.to_dict()), Q))
    if heavy_any:
        st['heavy_see_at_heavy_v'] += heavy_see_ok
    if step_ok and not see_ok and len(st['see_gap_examples']) < 2:
        st['see_gap_examples'].append((json.dumps(c.to_dict()), Q))


def files_mode(paths):
    from w951 import Circuit
    rng = random.Random(0)
    st = {'heavy': 0, 'heavy_step': 0, 'heavy_see': 0, 'heavy_see_at_heavy_v': 0,
          'light': 0, 'light_step': 0, 'light_see': 0, 'surv_nonempty_light': 0, 'see_gap_examples': [], 'heavy_seeK3': 0, 'light_seeK3': 0,
          'seek3_gap_examples': []}
    bad = []
    for p in paths:
        c = Circuit.from_dict(json.load(open(p)))
        if len(c.nots) != 1:
            print(p, 'skip: %d NOTs' % len(c.nots))
            continue
        before = dict((k, v) for k, v in st.items() if not k.endswith('_examples'))
        Qs = [0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) & rng.randrange(1 << c.n) for _ in range(3)]
        for Q in Qs:
            run(c, Q, st, bad)
            if bad:
                print('FAIL', p, bad[0][0], 'Q =', bad[0][2], 'v =', bad[0][3])
                return 1
        diff = {k: st[k] - before[k] for k in before if st[k] - before[k]}
        print(p.split('/')[-1], 'n =', c.n, diff)
    ex = st.pop('see_gap_examples')
    ex3 = st.pop('seek3_gap_examples')
    print('files: no failure of Lemma D / F1*;', st)
    for e in ex3:
        print('SEE+K3 fails but the step holds:', e[0][:300], 'Q =', e[1])
    for e in ex:
        print('SEE-STEP fails but the step holds:', e[0][:300], 'Q =', e[1])
    return 0


def main():
    if sys.argv[1] == 'files':
        return files_mode(sys.argv[2:])
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    st = {'heavy': 0, 'heavy_step': 0, 'heavy_see': 0, 'heavy_see_at_heavy_v': 0,
          'light': 0, 'light_step': 0, 'light_see': 0, 'surv_nonempty_light': 0, 'see_gap_examples': [], 'heavy_seeK3': 0, 'light_seeK3': 0,
          'seek3_gap_examples': []}
    bad = []
    for _ in range(N):
        n = rng.choice((4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None or len(c.sets) < 2:
            continue
        Q = rng.randrange(1 << n) & rng.randrange(1 << n)
        run(c, Q, st, bad)
        if bad:
            print('FAIL', bad[0])
            return 1
    ex = st.pop('see_gap_examples')
    ex3 = st.pop('seek3_gap_examples')
    print('no failure of Lemma D / F1*;', st)
    for e in ex3:
        print('SEE+K3 fails but the step holds:', e[0], 'Q =', e[1])
    for e in ex:
        print('SEE-STEP fails but the step holds:', e[0], 'Q =', e[1])
    return 0


if __name__ == '__main__':
    sys.exit(main())
