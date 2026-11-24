"""asteroid extension: claims over many circuits at once.
  corpus NAME = GLOB [where n <= K] [where nots <= T]
  claim forall c in NAME: EXPR [by lean]
  count c in NAME: EXPR
  plot hist FUNC NAME -> FILE.png
EXPR is any core claim expression written with the variable c, e.g. slack(c) >= 0."""
import re, os, glob, json
import asteroid.asteroid as A

CORPORA = {}          # NAME -> [(label, generated circuit name)]
LEAN_MAX, LEAN_MAX_N_CUBES = 40, 8

def _circuits(path):
    """yield (label, dict) for every circuit in a .json or .jsonl file; non-circuits yield (label, None)"""
    base = os.path.basename(path)
    try:
        if path.endswith(".jsonl"):
            for i, line in enumerate(open(path)):
                if line.strip():
                    try: yield f"{base}#{i}", json.loads(line)
                    except ValueError: yield f"{base}#{i}", None
        else: yield base, json.load(open(path))
    except (ValueError, OSError): yield base, None

def _norm(d):
    if isinstance(d, dict) and isinstance(d.get("circuit"), dict): d = d["circuit"]
    if not (isinstance(d, dict) and all(k in d for k in ("n", "sets", "gates", "outs"))): return None
    return {k: d[k] for k in ("n", "sets", "gates", "outs")}

def _sub(expr, name): return re.sub(r"\(c\)", f"({name})", expr)

def _lean_safe(corp): return re.sub(r"\W", "_", corp)

def handle(line, api):
    env, core = api["env"], api["core"]; ln = api["ln"]
    if m := re.fullmatch(r"corpus (\w+) = (\S+)((?:\s+where (?:n|nots) <= \d+)*)", line):
        name, pat, wh = m.group(1), m.group(2), m.group(3)
        lim = {k: int(v) for k, v in re.findall(r"where (n|nots) <= (\d+)", wh)}
        items, skip = [], {}
        def sk(why): skip[why] = skip.get(why, 0) + 1
        for path in sorted(glob.glob(pat, recursive=True)):
            if not path.endswith((".json", ".jsonl")) or os.path.isdir(path): continue
            for label, d in _circuits(path):
                c = _norm(d)
                if c is None: sk("not a circuit"); continue
                if "n" in lim and c["n"] > lim["n"]: sk("n too large"); continue
                if "nots" in lim and core.nots(c) > lim["nots"]: sk("too many NOT gates"); continue
                try: good = core.correct(c)
                except Exception: good = False
                if not good: sk("incorrect"); continue
                gen = f"{_lean_safe(name)}_{len(items)}"; env[gen] = c; api["src"][gen] = path; items.append((label, gen))
        CORPORA[name] = items
        why = ", ".join(f"{v} {k}" for k, v in skip.items()) or "none"
        print(f"{ln}: corpus {name}: {len(items)} circuits loaded; skipped {sum(skip.values())} ({why})")
        return True
    m = re.fullmatch(r"claim forall c in (\w+):\s*(.+?)(\s+by lean)?", line)
    if m:
        name, expr, lean = m.group(1), m.group(2).strip(), bool(m.group(3))
        items = CORPORA[name]; text = f"forall c in {name}: {expr}"
        if lean:
            big = "forall cubes" in expr and any(env[g]["n"] > LEAN_MAX_N_CUBES for _, g in items)
            if len(items) > LEAN_MAX or big:
                why = f"{len(items)} circuits (limit {LEAN_MAX})" if len(items) > LEAN_MAX else f"forall cubes needs n <= {LEAN_MAX_N_CUBES}"
                raise SystemExit(f"{api['script']}:{ln}: `by lean` refused: {why}; use a smaller corpus (where n <= K)")
        bad = []; A.FORCE = False
        for label, g in items:
            try: ok, _ = A.do_claim(_sub(expr, g), lean)
            except Exception as e: ok = False
            if not ok: bad.append(label)
        ok = not bad; k = len(items)
        res = f"python TRUE on {k} of {k}" if ok else f"FALSE on {len(bad)} of {k}: first failures {', '.join(bad[:3])}"
        api["results"].append((ln, text, ok, lean)); print(f"{ln}: claim {text}{' by lean' if lean else ''}: {res}")
        return True
    m = re.fullmatch(r"count c in (\w+):\s*(.+)", line)
    if m:
        name, expr = m.group(1), m.group(2).strip(); n = 0; items = CORPORA[name]; err = 0
        for label, g in items:
            try: n += bool(A.do_claim(_sub(expr, g), False)[0])
            except Exception: err += 1
        print(f"{ln}: count c in {name}: {expr}: {n} of {len(items)}" + (f" ({err} could not be evaluated)" if err else ""))
        return True
    m = re.fullmatch(r"plot hist (\w+) (\w+) -> (\S+)", line)
    if m:
        func, name, out = m.groups(); vals = [A.F(func, g) for _, g in CORPORA[name]]
        import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
        os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
        fig, ax = plt.subplots(figsize=(6, 3.8)); lo, hi = int(min(vals)), int(max(vals))
        ax.hist(vals, bins=[x - .5 for x in range(lo, hi + 2)], color="#3b6ea5", edgecolor="white")
        ax.set_xlabel(f"{func}(c)"); ax.set_ylabel("circuits"); ax.set_title(f"{func} over corpus {name} ({len(vals)} circuits)")
        fig.tight_layout(); fig.savefig(out, dpi=150); plt.close(fig)
        print(f"{ln}: wrote {out} ({func} from {lo} to {hi})"); return True
    return False
