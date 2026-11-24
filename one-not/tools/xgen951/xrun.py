# Wrapper around scaffold's xgen.gen (imported, unchanged): one (system, size) per call; prints PROGRESS every 25 solver
# calls and a PARTIAL summary (solves so far = circuits found + 1 at most) if stopped by SIGTERM (timeout).
#   python3 xrun.py SETS_JSON S LIMIT [ess]     (XGEN_DIR = scaffold's f15 folder)
import sys, os, json, time, signal
sys.path.insert(0, os.environ['XGEN_DIR'])
import xgen
t0 = time.time(); cnt = {'solves': 0}
class CountingSolver(xgen.Solver):
    def solve(self, *a, **k):
        r = super().solve(*a, **k); cnt['solves'] += 1
        if cnt['solves'] % 25 == 0:
            print(json.dumps({'kind': 'PROGRESS', 'solves': cnt['solves'], 'sec': round(time.time() - t0)}), flush=True)
        return r
xgen.Solver = CountingSolver
sets = json.loads(sys.argv[1]); s = int(sys.argv[2]); lim = int(sys.argv[3]); ess = 'ess' in sys.argv[4:]
def stop(*_):
    print(json.dumps({'kind': 'PARTIAL', 'sets': sets, 's': s, 'ess': ess, 'solves': cnt['solves'], 'sec': round(time.time() - t0)}), flush=True)
    os._exit(0)
signal.signal(signal.SIGTERM, stop)
st = xgen.gen(sets, 0, s, lim, ess=ess)
print(json.dumps({'kind': 'SUMMARY', 'sets': sets, 'w': 0, 's': s, 'ess': ess, **st}), flush=True)
