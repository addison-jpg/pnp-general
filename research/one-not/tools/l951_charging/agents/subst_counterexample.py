# Counterexample to front's substitution lemma (helper tooling, not a proof): in a correct live-NOT circuit,
# every read of the NOT wire can be replaced by a constant 0/1 or by an earlier NOT-free wire.
# n=4, sets S_A={0,1}, S_B={2,3}. The single read g = ~x0 & x1 feeds o_A (which needs g=1 at x=e1, so not 0 and
# not any wire that is 0 there) and o_B through g & (x0|x2) (which needs g=0 at x=e0+e1, so not 1); a monotone
# wire u with u(e1)=1 also has u(e0+e1)=1, so no NOT-free wire works either.  NOT a counterexample to 951
# (size 7 > base 2): it shows the substitution lemma needs a minimality / near-base hypothesis.
n = 4; sets = [(0, 1), (2, 3)]
gates = [('not', 0, 0),    # w4 = ~x0
         ('and', 4, 1),    # w5 = g = ~x0 & x1     (the only read of the NOT)
         ('or', 5, 0),     # w6 = x0 | x1  = o_A
         ('or', 0, 2),     # w7 = x0 | x2
         ('and', 5, 7),    # w8 = g & (x0|x2) = ~x0 & x1 & x2
         ('or', 2, 3),     # w9 = x2 | x3
         ('or', 8, 9)]     # w10 = o_B
outs = [6, 10]
def run(gs, x, sub=None):
    w = [(x >> i) & 1 for i in range(n)]
    for k, (op, a, b) in enumerate(gs):
        if sub is not None and k == 1: a = sub  # replace the NOT read in gate w5
        if op == 'not': w.append(1 - w[a])
        else:
            A = sub_val(w, a); B = w[b]
            w.append(A & B if op == 'and' else A | B)
    return w
def sub_val(w, a):
    return {'C0': 0, 'C1': 1}[a] if isinstance(a, str) else w[a]
def correct(sub=None):
    return all(run(gates, x, sub)[o] == int(any(x >> v & 1 for v in S)) for x in range(1 << n) for S, o in zip(sets, outs))
print('original circuit correct:', correct(None))
cands = ['C0', 'C1'] + list(range(n))          # constants and every NOT-free wire earlier than w5 (inputs only)
for c in cands: print(f'replace NOT read in w5 by {c}: correct = {correct(c)}')
