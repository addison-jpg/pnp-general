"""Lacan's Borromean knot (Real, Symbolic, Imaginary), as the mathematical object it names.
Borromean rings: three rings, no two of them linked, all three together inseparable.
Check (checked-finite): Gauss linking numbers by numerical integration. Each pair of Borromean rings
has linking number 0; a Hopf link (control) has linking number 1. The triple's inseparability is
Milnor's invariant mu(123) = +-1 (Milnor, Annals of Math. 59, 1954): cited, not computed here."""
import math

def ring(axis, n=400):
    pts = []
    for k in range(n):
        t = 2 * math.pi * k / n; a, b = math.cos(t), 2 * math.sin(t)
        pts.append({0: (a, b, 0.0), 1: (0.0, a, b), 2: (b, 0.0, a)}[axis])
    return pts

def linking(P, Q):
    total = 0.0
    for i in range(len(P)):
        p, dp = P[i], [P[(i + 1) % len(P)][k] - P[i][k] for k in range(3)]
        for j in range(len(Q)):
            q, dq = Q[j], [Q[(j + 1) % len(Q)][k] - Q[j][k] for k in range(3)]
            r = [p[k] + dp[k] / 2 - q[k] - dq[k] / 2 for k in range(3)]
            c = [dp[1]*dq[2]-dp[2]*dq[1], dp[2]*dq[0]-dp[0]*dq[2], dp[0]*dq[1]-dp[1]*dq[0]]
            total += sum(r[k] * c[k] for k in range(3)) / sum(x * x for x in r) ** 1.5
    return total / (4 * math.pi)

if __name__ == "__main__":
    R, S, I = ring(0), ring(1), ring(2)
    names = {"Real-Symbolic": (R, S), "Symbolic-Imaginary": (S, I), "Imaginary-Real": (I, R)}
    for name, (a, b) in names.items():
        lk = linking(a, b); print(f"{name}: linking number {lk:+.4f}"); assert abs(lk) < 0.01
    hopf_a = [(math.cos(t), math.sin(t), 0.0) for t in (2 * math.pi * k / 400 for k in range(400))]
    hopf_b = [(1 + math.cos(t), 0.0, math.sin(t)) for t in (2 * math.pi * k / 400 for k in range(400))]
    lk = linking(hopf_a, hopf_b); print(f"Hopf control: linking number {lk:+.4f}"); assert abs(abs(lk) - 1) < 0.01
    print("PASS: no two rings linked; the control links once")
