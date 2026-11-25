# Fano plane test of L-meta-951 (helper tooling, not a proof): is there a 13-gate circuit with <= 1 NOT computing
# OR of all 7 lines? (base = 14). Split into cells: 'mono' (no NOT, sat951.build with K=0) and p = 0..11
# (NOT at gate p, read by a later gate; ov951.build). The 13 cells together cover the whole question.
# SAT in any cell = counterexample to 951; the circuit is decoded and re-checked on all 128 inputs.
#   python3 research/tools/l951_charging/fano_cells_scaffold.py TIMEOUT_SECONDS WORKERS CELL [CELL ...]   (CELL = mono or 0..11)
import sys, time, threading, types, multiprocessing as mp
FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
S = 13
def load_ov():
    src = open('research/tools/l951_charging/ov951.py').read().split('random.seed(')[0]
    m = types.ModuleType('ov'); exec(src, m.__dict__); return m
def run(args):
    cell, tmo = args
    from pysat.solvers import Cadical153
    t = time.time(); ov = load_ov()
    if cell == 'mono':
        sys.path.insert(0, 'research/tools/l951_charging'); import sat951
        cl, *_ = sat951.build(7, FANO, S, 0)
    else:
        cl, SEL, O = ov.build(7, FANO, S, cell, [])
    s = Cadical153(bootstrap_with=cl); tb = time.time() - t
    tm = threading.Timer(tmo, s.interrupt); tm.start()
    r = s.solve_limited(expect_interrupt=True); tm.cancel()
    out = f'cell={cell} clauses={len(cl)} build={tb:.0f}s solve={time.time()-t-tb:.0f}s result={"TIMEOUT" if r is None else ("SAT" if r else "UNSAT")}'
    if r and cell != 'mono':
        g, o = ov.decode(s.get_model(), 7, S, cell, SEL, O)
        ok = all(ov.wires(7, g, x)[w] == int(any(x >> v & 1 for v in L)) for x in range(128) for L, w in zip(FANO, o))
        out += f' gates={g} outs={o} recheck={ok}'
    elif r: out += ' (monotone 13-gate circuit; rerun sat951.py fano 13 0 to print it)'
    print(out, flush=True); return out
if __name__ == '__main__':
    tmo = float(sys.argv[1]); W = int(sys.argv[2])
    cells = [c if c == 'mono' else int(c) for c in sys.argv[3:]]
    with mp.Pool(W) as P:
        for _ in P.imap_unordered(run, [(c, tmo) for c in cells]): pass
    print('ALL DONE', flush=True)
