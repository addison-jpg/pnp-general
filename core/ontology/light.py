"""Light, two exact checks. Standard library only, Fraction arithmetic.

(a) de Sitter event horizon (source: Addison, the lights going out; core/ontology/SOURCES.md).
    a(t) = e^(Ht). Light leaving at t covers comoving distance int_t^inf c/a(s) ds = c e^(-Ht)/H
    = c/(H a(t)). Proper distance = a(t) * that = c/H, the same at every t.
    Checked here, exactly, for H in a set of rationals and to order N = 40:
    - termwise: int_0^T e^(-Hs) ds has power-series coefficients (-H)^k T^(k+1)/(k+1)!,
      equal to those of (1 - e^(-HT))/H;
    - e^(Ht) * e^(-Ht) = 1 as series (Cauchy product), so a(t) * c e^(-Ht)/H = c/H.
    Written reduction to all orders and T -> inf: both are identities of entire series;
    for H > 0, e^(-HT) -> 0, so the integral tends to 1/H (times c e^(-Ht)). Fact: this is the
    standard de Sitter event horizon (e.g. Rindler 1956, "Visual horizons in world models"; cited,
    not re-read).
(b) Locality on a graph (the swarm's light-cone rule): a signal that moves one edge per step,
    started at v, has reached after t steps exactly the ball {u : d(v,u) <= t}.
    Checked on every connected labelled graph on 1..6 vertices, every v, every t <= n.
    Honest note: flooding and BFS compute the same thing by definition; this checks the code,
    and that the light cone saturates at the eccentricity of v.
"""
from fractions import Fraction as F
from itertools import combinations
from math import factorial

ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name); ok = ok and cond

N = 40
Hs = [F(1), F(1, 2), F(3, 7), F(5), F(22, 7)]
good = True
for H in Hs:
    # series of (1 - e^{-x})/H in x = H T: coefficient of T^(k+1) is -(-H)^(k+1)/(k+1)!/H
    for k in range(N):
        termwise = (-H) ** k / factorial(k + 1)
        closed = -((-H) ** (k + 1)) / factorial(k + 1) / H
        good &= termwise == closed
    e_pos = [H ** k / factorial(k) for k in range(N)]
    e_neg = [(-H) ** k / factorial(k) for k in range(N)]
    prod = [sum(e_pos[i] * e_neg[n - i] for i in range(n + 1)) for n in range(N)]
    good &= prod == [1] + [0] * (N - 1)
want(f"de Sitter: integral of e^(-Hs) matches (1-e^(-HT))/H and e^(Ht)e^(-Ht)=1 to order {N}, H in {[str(h) for h in Hs]}", good)

def connected(n, E):
    adj = {i: set() for i in range(n)}
    for a, b in E: adj[a].add(b); adj[b].add(a)
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == n, adj

graphs = 0; good = True
for n in range(1, 7):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        c, adj = connected(n, E)
        if not c: continue
        graphs += 1
        INF = n + 1
        d = [[0 if i == j else (1 if j in adj[i] else INF) for j in range(n)] for i in range(n)]
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    if d[i][k] + d[k][j] < d[i][j]: d[i][j] = d[i][k] + d[k][j]
        for v in range(n):
            S = {v}
            for t in range(n + 1):
                good &= S == {u for u in range(n) if d[v][u] <= t}
                S = S | {y for x in S for y in adj[x]}
want(f"light cone = BFS ball on all {graphs} connected labelled graphs, 1..6 vertices", good)
want("connected labelled graph counts 1,1,4,38,728,26704 sum to 27476", graphs == 27476)
print("PASS" if ok else "FAIL")
