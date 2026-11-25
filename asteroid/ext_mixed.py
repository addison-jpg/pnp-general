"""asteroid extension: mixed slack (points fixed to 1 AND points fixed to 0).
  claim mslack(NAME, {q1 q2 ...}, {r1 r2 ...}) OP INTEGER [by lean]
  claim forall states mslack(NAME) >= 0 [by lean]       all 3^n states (Q, R)
  claim forall states mixedstep(NAME) [by lean]         MixedStep at every state with positive base
  (claim! forces the claim to Lean even when Python says false.)
Definitions are in asteroid/SPEC.md; Lean side: proofs/w951/PEqualNP/W951/AsteroidMixed.lean.
Python uses continuous.slack_table / continuous.mixed_margin; `direct_*` below is an independent, naive implementation
used to cross-check (every single-state claim is checked against it; asteroid/tests/test_mixed.py does whole circuits)."""
import re, operator
import asteroid.asteroid as A

OPS = {"=": operator.eq, "!=": operator.ne, "<": operator.lt, "<=": operator.le, ">": operator.gt, ">=": operator.ge}
MODULE = "PEqualNP.W951.AsteroidMixed"

# ---------- direct (naive) implementation, bit-parallel ints, no numpy ----------
def _tables(c):
    n = c["n"]; N = 1 << n; w = [sum(((z >> i) & 1) << z for z in range(N)) for i in range(n)]; full = (1 << N) - 1
    for g in c["gates"]:
        w.append(full ^ w[g[1]] if g[0] == "not" else (w[g[1]] & w[g[2]] if g[0] == "and" else w[g[1]] | w[g[2]]))
    return w

def direct_parts(c, Q, R, tabs=None):
    """(#OR-gate witnesses, base) at the mixed state (Q, R) (bit masks). Straight from the definition."""
    n = c["n"]; w = tabs or _tables(c); cnt = 0; base = 0
    alive = []
    for S in c["sets"]:
        Sr = [u for u in S if not R >> u & 1]
        if all(not Q >> s & 1 for s in S) and len(Sr) >= 2: alive.append((S, Sr)); base += len(Sr) - 1
    for k, g in enumerate(c["gates"]):
        if g[0] != "or": continue
        t = w[n + k]; hit = False
        for S, Sr in alive:
            sm = sum(1 << s for s in S)
            for z in range(1 << n):
                if z & Q == Q and not z & R and not z & sm and not t >> z & 1 and sum(t >> (z | 1 << u) & 1 for u in Sr) >= 2: hit = True; break
            if hit: break
        cnt += hit
    return cnt, base

def direct_mixedstep(c):
    """(holds, #states, #states with positive base): every state with base > 0 has a paying 1-step or 0-step with mslack no larger."""
    n = c["n"]; w = _tables(c); memo = {}
    def P(Q, R):
        if (Q, R) not in memo: memo[(Q, R)] = direct_parts(c, Q, R, w)
        return memo[(Q, R)]
    ok = True; ns = npos = 0
    for R in range(1 << n):
        for Q in range(1 << n):
            if Q & R: continue
            ns += 1; cnt, base = P(Q, R)
            if base == 0: continue
            npos += 1; sl = cnt - base; good = False
            for v in range(n):
                if (Q | R) >> v & 1: continue
                for (Q2, R2) in ((Q | 1 << v, R), (Q, R | 1 << v)):
                    c2, b2 = P(Q2, R2)
                    if b2 < base and c2 - b2 <= sl: good = True
            ok &= good
    return ok, ns, npos

# ---------- Python via continuous.py ----------
def _C():
    A.need("numpy", "mixed slack (mslack, mixedstep)"); import continuous; return continuous

def _compress(Q, R, n):
    """index of Q among the points outside R (the sub-vector convention of continuous.slack_table)"""
    idx = 0; i = 0
    for v in range(n):
        if R >> v & 1: continue
        idx |= (Q >> v & 1) << i; i += 1
    return idx

def mslack_state(c, Q, R):
    cnt, base = _C().slack_table(c, R, parts=True); j = _compress(Q, R, c["n"]); return int(cnt[j]), int(base[j])

def forall_min(c):
    """(least mslack, #states, #states with positive base) over all 3^n states, via continuous.slack_table"""
    n = c["n"]; C = _C(); mn = None; ns = pos = 0
    for R in range(1 << n):
        cnt, base = C.slack_table(c, R, parts=True); sl = cnt - base
        ns += len(sl); pos += int((base > 0).sum()); m = int(sl.min()); mn = m if mn is None else min(mn, m)
    return mn, ns, pos

def mixedstep_holds(c):
    """MixedStep via continuous.mixed_margin: m = max over states with base > 0 of the least slack change over the paying steps; holds iff m <= 0."""
    m, k = _C().mixed_margin(c); return m <= 0, m, k

def _mask(s): return sum(1 << int(x) for x in s.split())

def claim_expr(text, lean, api, force=False):
    """Evaluate a mixed claim expression (no leading `claim`). Returns (ok, detail, text) or None if not a mixed form."""
    env, ln = api["env"], api["ln"]
    m = re.fullmatch(r"mslack\((\w+),\s*\{([\d ]*)\},\s*\{([\d ]*)\}\)\s*(=|!=|<=|>=|<|>)\s*(-?\d+)", text)
    m2 = None if m else re.fullmatch(r"forall states (mslack|mixedstep)\((\w+)\)(?:\s*>=\s*0)?", text)
    if not m and not m2: return None
    if m:
        name, qs, rs, op, k = m.group(1), m.group(2), m.group(3), m.group(4), int(m.group(5)); c = env[name]; n = c["n"]
        Q, R = _mask(qs), _mask(rs)
        if Q & R or max(Q | R, 0) >> n: raise SystemExit(f"{api['script']}:{ln}: Q and R must be disjoint points < {n}")
        cnt, base = mslack_state(c, Q, R); dc, db = direct_parts(c, Q, R)
        assert (cnt, base) == (dc, db), f"cross-check failed: continuous {(cnt, base)} vs direct {(dc, db)}"
        v = cnt - base; ok = OPS[op](v, k)
        text = f"mslack({name}, {{{qs.strip()}}}, {{{rs.strip()}}}) {op} {k}"
        detail = f"mslack = {cnt} witness gates - base {base} = {v}"
        if lean and (ok or force):
            Lk = {">=": [f"mslackGe {name} {Q} {R} ({k}) = true"], "<=": [f"mslackLe {name} {Q} {R} ({k}) = true"],
                  ">": [f"mslackGe {name} {Q} {R} ({k + 1}) = true"], "<": [f"mslackLe {name} {Q} {R} ({k - 1}) = true"],
                  "!=": [f"mslackVal {name} {Q} {R} ≠ {k}"]}
            Lk["="] = Lk[">="] + Lk["<="]
            for st in Lk[op]: api["lean_claims"].append((name, "claim", st, text))
    else:
        kind, name = m2.group(1), m2.group(2); c = env[name]; n = c["n"]
        if kind == "mslack":
            mn, ns, pos = forall_min(c); ok = mn >= 0; text = f"forall states mslack({name}) >= 0"
            detail = f"least mslack over {ns} states = {mn} ({pos} states with positive base)"
            st = f"mslackNonnegAll {name} = true"
        else:
            holds, mm, k = mixedstep_holds(c); ok = holds; _, ns, pos = _count_states(c); text = f"forall states mixedstep({name})"
            detail = f"{pos} of {ns} states have positive base; max over them of the least change over paying steps = {mm} ({k} states attain it)"
            st = f"mixedStepAll {name} = true"
        if lean and (ok or force): api["lean_claims"].append((name, "claim", st, text))
    if lean and (ok or force) and MODULE not in api["extra_lean"]["imports"]: api["extra_lean"]["imports"].append(MODULE)
    return ok, detail, text

def handle(line, api):
    m = re.fullmatch(r"claim(!?) (.+?)(\s+by lean)?", line)
    if not m: return False
    r = claim_expr(m.group(2).strip(), bool(m.group(3)), api, force=bool(m.group(1)))
    if r is None: return False
    ok, detail, text = r
    api["results"].append((api["ln"], text, ok, bool(m.group(3))))
    print(f"{api['ln']}: claim {text}: python {'TRUE' if ok else 'FALSE'} ({detail})")
    return True

def _count_states(c):
    n = c["n"]; ns = pos = 0
    for R in range(1 << n):
        cnt, base = _C().slack_table(c, R, parts=True); ns += len(base); pos += int((base > 0).sum())
    return None, ns, pos
