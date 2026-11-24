"""knot.py -- SAT search for fan-in-2 AND/OR/NOT circuits with AT MOST k NOT gates computing a
Boolean-sum system (o_w = OR(S_w)).  Own encoder (not a copy of w951.sat); w951.Circuit is imported
and used as the independent verifier.

Model (same as the project): wires 0..n-1 inputs, gate j is wire n+j, gates are AND(a,b), OR(a,b), NOT(a),
every gate (NOT included) counts 1, no constants, each output is a gate wire.

Encoding ("channel" style, gate TYPE is a variable, so NOTs may sit anywhere):
  A[j][i], B[j][i]  one-hot selectors over earlier wires i < n+j, A <= B (as wire index)
  N[j]  gate j is a NOT (then B = A and value = not a);   P[j]  op bit (AND if true), false for NOT
  W[j][r] value of gate j on row r;  a[j][r], b[j][r] selected input values
  sum_j N[j] <= k   (and optionally "= k", "NOT positions fixed")
Because op(w, w) = w is allowed (A <= B), "exactly s gates" covers every size <= s.

Normal forms (each is 'exists circuit of size <= s  =>  exists one of size exactly s in normal form'):
  used:  every gate is an output or read by a later gate (pad at an output: o' = OR(o, o))
  nodd:  no NOT reads a NOT
  order: if gate j+1 does not read gate j then B[j+1] >= B[j]   (lexicographically least topological
         order of the B-sequence; swapping two adjacent independent gates only changes those two entries)
All three can be switched off (sym=False) -- the validation script checks both give the same answers.

Rows: solve(...) is CEGAR over rows -- start with a row subset, verify the model exhaustively with
bit-parallel truth tables, add a violated row, repeat.  UNSAT on a subset of rows is UNSAT.
"""
import sys, time, json, itertools
sys.path.insert(0, '/home/user/coord951/tools')
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from w951 import Circuit


class Enc:
    def __init__(self, n, sets, s, k, sym=True, exact_k=False, essential=False, solver='cadical195', targets=None):
        self.n, self.sets, self.s, self.k = n, [tuple(S) for S in sets], s, k
        # targets: optional truth tables (ints) replacing OR(S) -- used only to validate on XOR / parity
        self.tt = targets if targets is not None else [or_table(n, S) for S in self.sets]
        if targets is not None:
            self.sets = list(range(len(targets)))
        self.top = 0
        self.sol = Solver(name=solver)
        self.rows = []
        self.A, self.B, self.N, self.P, self.W = [], [], [], [], []
        self.essential = essential
        add = self.sol.add_clause
        for j in range(s):
            m = n + j
            A = [self.nv() for _ in range(m)]
            B = [self.nv() for _ in range(m)]
            self.ex1(A); self.ex1(B)
            Nj, Pj = self.nv(), self.nv()
            add([-Nj, -Pj])
            # A <= B via prefix variables: pa[i] = (A index <= i)
            for i in range(m):
                for i2 in range(i):
                    add([-A[i], -B[i2]])
                add([-Nj, -A[i], B[i]])                      # NOT: B = A
            self.A.append(A); self.B.append(B); self.N.append(Nj); self.P.append(Pj); self.W.append({})
        if k < s:
            enc = (CardEnc.equals if exact_k else CardEnc.atmost)(lits=self.N, bound=k, top_id=self.top,
                                                                 encoding=EncType.seqcounter)
            self.top = max(self.top, enc.nv)
            for c in enc.clauses:
                add(c)
        elif exact_k:
            for x in self.N:
                add([x])
        if k == 0:
            for x in self.N:
                add([-x])
        # outputs
        self.O = []
        for S in self.sets:
            o = [self.nv() for _ in range(s)]
            self.ex1(o)
            self.O.append(o)
        if len(set(self.sets)) == len(self.sets):            # distinct sets -> distinct output gates
            for j in range(s):
                for o1, o2 in itertools.combinations(self.O, 2):
                    add([-o1[j], -o2[j]])
        if sym:
            for j in range(s):
                w = n + j
                add([o[j] for o in self.O] + [self.A[l][w] for l in range(j + 1, s)]
                    + [self.B[l][w] for l in range(j + 1, s)])                     # used
                for i in range(n, w):                                               # nodd
                    add([-self.N[j], -self.A[j][i], -self.N[i - n]])
            for j in range(s - 1):                                                  # order
                w = n + j
                for i in range(w):
                    for i2 in range(i):
                        # B[j] = i, B[j+1] = i2 < i  -> gate j+1 reads wire w
                        add([-self.B[j][i], -self.B[j + 1][i2], self.A[j + 1][w], self.B[j + 1][w]])
        if essential:
            self._essential_init()

    def nv(self):
        self.top += 1
        return self.top

    def ex1(self, lits):
        if len(lits) == 1:
            self.sol.add_clause(lits)
            return
        enc = CardEnc.equals(lits=lits, bound=1, top_id=self.top, encoding=EncType.seqcounter)
        self.top = max(self.top, enc.nv)
        for c in enc.clauses:
            self.sol.add_clause(c)

    # ---- rows -------------------------------------------------------------------------------------
    def _gate_row(self, j, r, W, N_forced=None):
        """Clauses defining gate j on row r in value map W (W[j'][r] for earlier gates).
        N_forced = (gate index f, const c): in this copy gate f, IF it is a NOT, outputs c."""
        n, add = self.n, self.sol.add_clause
        g, a, b = self.nv(), self.nv(), self.nv()
        W[j][r] = g
        for sel, v in ((self.A[j], a), (self.B[j], b)):
            for i, x in enumerate(sel):
                if i < n:
                    add([-x, v if r >> i & 1 else -v])
                else:
                    y = W[i - n][r]
                    add([-x, -y, v]); add([-x, y, -v])
        Nj, Pj = self.N[j], self.P[j]
        if N_forced is not None and N_forced[0] == j:
            add([-Nj, g if N_forced[1] else -g])
        else:
            add([-Nj, g, a]); add([-Nj, -g, -a])
        add([Nj, -Pj, -g, a]); add([Nj, -Pj, -g, b]); add([Nj, -Pj, g, -a, -b])
        add([Nj, Pj, g, -a]); add([Nj, Pj, g, -b]); add([Nj, Pj, -g, a, b])

    def add_row(self, r):
        self.rows.append(r)
        add = self.sol.add_clause
        for j in range(self.s):
            self._gate_row(j, r, self.W)
        for T, o in zip(self.tt, self.O):
            t = T >> r & 1
            for j in range(self.s):
                add([-o[j], self.W[j][r] if t else -self.W[j][r]])

    # ---- essential NOTs: for each gate f and const c, if f is a NOT then forcing it to c is wrong ----
    def _essential_init(self):
        """Full-row copies (all 2^n rows) for each (f, c); only use for small n."""
        n, s, add = self.n, self.s, self.sol.add_clause
        for f in range(s):
            for c in (0, 1):
                W = [dict() for _ in range(s)]
                errs = []
                for r in range(1 << n):
                    for j in range(s):
                        if j < f:
                            pass
                        self._gate_row(j, r, W, N_forced=(f, c))
                    for T, o in zip(self.tt, self.O):
                        t = T >> r & 1
                        for j in range(s):
                            e = self.nv()           # e -> output o is gate j and wrong on row r
                            add([-e, o[j]])
                            add([-e, -W[j][r] if t else W[j][r]])
                            errs.append(e)
                add([-self.N[f]] + errs)

    # ---- decode / verify --------------------------------------------------------------------------
    def decode(self, model):
        M = set(x for x in model if x > 0)
        gates = []
        for j in range(self.s):
            a = next(i for i, x in enumerate(self.A[j]) if x in M)
            b = next(i for i, x in enumerate(self.B[j]) if x in M)
            if self.N[j] in M:
                gates.append(['not', a])
            else:
                gates.append(['and' if self.P[j] in M else 'or', a, b])
        outs = [self.n + next(j for j, x in enumerate(o) if x in M) for o in self.O]
        return gates, outs

    def block(self, model):
        M = set(x for x in model if x > 0)
        c = []
        for j in range(self.s):
            c += [-x for x in self.A[j] + self.B[j] if x in M]
            c += [-self.N[j] if self.N[j] in M else self.N[j], -self.P[j] if self.P[j] in M else self.P[j]]
        self.sol.add_clause(c)


def tables(n, gates):
    """Own bit-parallel evaluator: truth tables (ints over 2^n rows, bit r = value on row r)."""
    full = (1 << (1 << n)) - 1
    t = []
    for i in range(n):
        blk = (1 << (1 << i)) - 1
        x = 0
        for q in range(0, 1 << n, 2 << i):
            x |= blk << (q + (1 << i))
        t.append(x)
    for g in gates:
        if g[0] == 'not':
            t.append(full ^ t[g[1]])
        elif g[0] == 'and':
            t.append(t[g[1]] & t[g[2]])
        else:
            t.append(t[g[1]] | t[g[2]])
    return t


def or_table(n, S):
    t = tables(n, [])
    want = 0
    for v in S:
        want |= t[v]
    return want


def wrong_row(n, tts, gates, outs):
    """None if correct, else a row where some output is wrong.  tts: target truth tables."""
    t = tables(n, gates)
    for want, o in zip(tts, outs):
        d = want ^ t[o]
        if d:
            return (d & -d).bit_length() - 1
    return None


def verify(n, sets, gates, outs, k=None):
    """Independent check: own tables AND w951.Circuit.is_correct(); also the NOT count."""
    ok1 = wrong_row(n, [or_table(n, S) for S in sets], gates, outs) is None
    c = Circuit(n, [tuple(g) for g in gates], [list(S) for S in sets], list(outs))
    c.validate(sums=False)
    ok2 = c.is_correct()
    assert ok1 == ok2, 'evaluators disagree'
    nn = sum(g[0] == 'not' for g in gates)
    return ok1 and (k is None or nn <= k)


def start_rows(n, sets):
    rows = {0, (1 << n) - 1}
    for i in range(n):
        rows.add(1 << i)
        rows.add(((1 << n) - 1) ^ (1 << i))
    for i, j in itertools.combinations(range(n), 2):
        rows.add(1 << i | 1 << j)
    return sorted(rows)


def solve(n, sets, s, k, sym=True, exact_k=False, essential=False, full=False, log=None, solver='cadical195',
          targets=None):
    """Is there a circuit with <= s gates, <= k NOTs?  Returns (gates, outs) or None (UNSAT).
    full=True: all 2^n rows from the start (no CEGAR)."""
    if s < 1:
        return None                                      # every output is a gate wire
    E = Enc(n, sets, s, k, sym=sym, exact_k=exact_k, essential=essential, solver=solver, targets=targets)
    for r in (range(1 << n) if full else start_rows(n, sets)):
        E.add_row(r)
    it = 0
    while True:
        it += 1
        if not E.sol.solve():
            E.sol.delete()
            return None
        gates, outs = E.decode(E.sol.get_model())
        r = wrong_row(n, E.tt, gates, outs)
        if r is None:
            E.sol.delete()
            assert targets is not None or verify(n, E.sets, gates, outs, k)
            return gates, outs
        assert r not in E.rows
        E.add_row(r)
        if log:
            log('  cegar it %d rows %d' % (it, len(E.rows)))


def base(sets):
    return sum(len(S) - 1 for S in sets)


def nmax(sets):
    return 1 + max(v for S in sets for v in S)


if __name__ == '__main__':
    # CLI: python3 knot.py '<sets json>' s k [name]   -> appends one JSON line to results.jsonl
    sets = json.loads(sys.argv[1]); s = int(sys.argv[2]); k = int(sys.argv[3])
    name = sys.argv[4] if len(sys.argv) > 4 else ''
    n = nmax(sets)
    t0 = time.time()
    res = solve(n, sets, s, k, log=lambda m: print(m, flush=True))
    rec = dict(name=name, n=n, sets=sets, base=base(sets), s=s, k=k, sat=res is not None,
               secs=round(time.time() - t0, 1), enc='knot.solve sym=True cegar cadical195')
    if res:
        rec['gates'], rec['outs'] = res
    print(json.dumps(rec), flush=True)
    with open('/home/user/ku951/results.jsonl', 'a') as f:
        f.write(json.dumps(rec) + '\n')
