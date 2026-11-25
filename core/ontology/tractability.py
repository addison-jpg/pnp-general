#!/usr/bin/env python3
"""Basics of tractability, checked exactly. Standard library only.

Definitions (cited from memory: Cobham 1965, Edmonds 1965, the polynomial-time thesis; Cook 1971, Karp 1972):
a problem is tractable when some algorithm solves it in time bounded by a polynomial in the input size.
  1. The priority heap (workshop/notes/heap.py's structure, rebuilt here with a comparison counter): on EVERY
     sequence of up to 7 push and pop operations over priorities {0, 1, 2}, each operation uses at most
     2 * ceil(log2(n + 1)) comparisons, where n is the size at that moment. Checked on these small cases only; this does not prove the bound for all sizes.
  2. Polynomial beats exponential: for each degree k in 1..10 there is a crossover N_k such that 2^n > n^k for every
     n >= N_k (checked to n = 400 on exact integers), and N_k grows with k.
  3. Closure, for monomials only: x^b composed with x^a is x^(ab), checked exactly on all pairs a, b in 1..6.
     This does not cover general polynomials with lower-order terms.
Reading (analogy): a heap that pushes and pops in logarithmic time is a tractable structure; a search that
tries every subset is not. The exact claims are 1 to 3; the reading is not a result.
Run: python3 -I core/ontology/tractability.py   (last line is JSON)
"""
import itertools, json, math, time

def heap_ops(ops):
    """Run push/pop on a binary min-heap; return the max comparisons used by any single operation, per the bound."""
    h, worst = [], 0
    for op in ops:
        cmp = 0
        if op[0] == "push":
            h.append(op[1]); i = len(h) - 1
            while i > 0:
                p = (i - 1) // 2; cmp += 1
                if h[i] < h[p]: h[i], h[p] = h[p], h[i]; i = p
                else: break
        else:
            if not h: continue
            h[0], h[-1] = h[-1], h[0]; h.pop(); i = 0
            while True:
                l, r, s = 2 * i + 1, 2 * i + 2, i
                if l < len(h):
                    cmp += 1
                    if h[l] < h[s]: s = l
                if r < len(h):
                    cmp += 1
                    if h[r] < h[s]: s = r
                if s == i: break
                h[i], h[s] = h[s], h[i]; i = s
        n = len(h)
        bound = 2 * math.ceil(math.log2(n + 1)) if n >= 0 else 0
        assert cmp <= bound, f"operation used {cmp} comparisons at size {n}"
        worst = max(worst, cmp)
    return worst

def main():
    t0 = time.time(); states = 0; worst_all = 0
    alphabet = [("push", p) for p in (0, 1, 2)] + [("pop", None)]
    for length in range(1, 8):
        for ops in itertools.product(alphabet, repeat=length):
            states += 1; worst_all = max(worst_all, heap_ops(list(ops)))
    print(f"heap: every push/pop sequence up to length 7 stays within 2*ceil(log2(n+1)) comparisons per operation (worst {worst_all})")
    first = {}
    M = 400                                  # checked up to n = 400, exact integers
    for k in range(1, 11):
        last_fail = max((n for n in range(1, M + 1) if 2 ** n <= n ** k), default=0)
        first[k] = last_fail + 1             # from here on 2^n > n^k for every n checked
        states += M
    assert all(first[k] < first[k + 1] for k in range(1, 10)), "the crossover moves out as the degree grows"
    print("from this n on, 2^n > n^k (checked to n = 400), k = 1..10:", list(first.values()))
    for a, b in itertools.product(range(1, 7), repeat=2):
        for n in (2, 3, 5, 7):                       # compose x^a and x^b exactly, then read the degree back
            states += 1
            inner = n ** b                           # q(n) = n^b
            composed = inner ** a                    # p(q(n)) = (n^b)^a
            assert composed == n ** (a * b), "composition is exact"
        # the degree is read off by the exact ratio at two sizes: (2n)^(ab) / n^(ab) = 2^(ab)
        assert (2 * 11) ** (a * b) // 11 ** (a * b) == 2 ** (a * b)
    print("composition: (x^b)^a = x^(ab) exactly, and the degree is read back as the exponent, on all pairs 1..6")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 3), "worst_comparisons": worst_all, "crossover": first}))

if __name__ == "__main__":
    main()
