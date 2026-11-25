"""Quadrant form: specs of the world problems P0(h), P1(h) and of the lifted problem, for a set system and a monotone h
(h given as a truth table list of length 2^n)."""
import itertools
from msat import solve, opt, evalc


def osum(S, x):
    return int(any(x >> v & 1 for v in S))


def spec_h(n, h):
    return ([x for x in range(1 << n) if h[x]], [x for x in range(1 << n) if not h[x]])


def specs0(n, sets, h, with_h=True):
    sp = []
    for S in sets:
        sp.append(([x for x in range(1 << n) if osum(S, x) and h[x]], [x for x in range(1 << n) if not osum(S, x)]))
    if with_h and 0 < sum(h) < len(h): sp.append(spec_h(n, h))
    return sp


def specs1(n, sets, h, with_h=True):
    sp = []
    for S in sets:
        sp.append(([x for x in range(1 << n) if osum(S, x)], [x for x in range(1 << n) if not osum(S, x) and not h[x]]))
    if with_h and 0 < sum(h) < len(h): sp.append(spec_h(n, h))
    return sp


def specsL(n, sets, h):
    """lifted: inputs 0..n-1 = x, input n = y."""
    Y = 1 << n
    sp = []
    for S in sets:
        ones = [x | Y for x in range(1 << n) if osum(S, x)] + [x for x in range(1 << n) if osum(S, x) and h[x]]
        zeros = [x for x in range(1 << n) if not osum(S, x)] + [x | Y for x in range(1 << n) if not osum(S, x) and not h[x]]
        sp.append((ones, zeros))
    if 0 < sum(h) < len(h): sp.append(([x for x in range(1 << n) if h[x]], [x | Y for x in range(1 << n) if not h[x]]))
    return sp


def monotone_functions(n):
    """all monotone truth tables on n variables as tuples of length 2^n (index bit i = x_i)."""
    if n == 0:
        return [(0,), (1,)]
    prev = monotone_functions(n - 1)
    out = []
    for f0 in prev:
        for f1 in prev:
            if all(a <= b for a, b in zip(f0, f1)):
                out.append(f0 + f1)
    return out


def base(sets):
    return sum(len(S) - 1 for S in sets)
