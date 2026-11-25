"""Discrete evaporation SIMULATION of a stated rule. It is not physics.

Rule (a choice, written exactly):
  1. A mass M is an integer count of quanta, m = M at the start.
  2. The radius is r = m (radius proportional to M, constant set to 1).
  3. The area is the integer quantum count A(m) = 4 * m * m (4 pi r^2 with pi dropped, so it stays an integer).
  4. "Remove one quantum with probability 1/2 per unit of area" is made deterministic by using the expected value:
     each step adds A(m) / 2 to an exact credit (a Fraction). Then floor(credit) quanta are removed
     (at most m), and that many are taken off the credit.
  5. A step count is the number of steps until m = 0. No random numbers are used, so every count is exact.
Method: the exponent is read from the ratio steps(2M) / steps(M), as in physics/blackhole/check.py.
  If the ratio is an exact power of 2, that power is the exponent. If not, the ratio is reported as it is.
Assumptions: the rule is a choice. The result describes this rule only. No claim about real black holes follows.
Run: python3 -I physics/blackhole/sim/evaporate.py   (last line is JSON)
"""
import json
from fractions import Fraction as Fr

def area(m): return 4 * m * m

def steps(M):
    m, credit, n = M, Fr(0), 0
    while m > 0:
        n += 1
        credit += Fr(area(m), 2)
        k = min(m, int(credit))
        m -= k; credit -= k
    return n

def exponent(ratio):
    for k in range(-10, 11):
        if ratio == Fr(2) ** k: return k
    return None

def main():
    rows = {}
    for M in range(2, 13):
        a, b = steps(M), steps(2 * M)
        rows[M] = {"steps_M": a, "steps_2M": b, "ratio": str(Fr(b, a)), "exponent": exponent(Fr(b, a))}
        print(f"M={M:2d} steps={a} steps(2M)={b} ratio={Fr(b, a)}")
    exps = {r["exponent"] for r in rows.values()}
    is3 = exps == {3}
    print("exponents found:", sorted(exps, key=str))
    print("exponent equals 3 for this rule:", is3)
    print("note: this describes the stated rule only, not real black holes")
    print(json.dumps({"rule": "A=4m^2, credit+=A/2 per step, remove floor(credit)", "rows": rows, "exponent_is_3": is3}))

if __name__ == "__main__":
    main()
