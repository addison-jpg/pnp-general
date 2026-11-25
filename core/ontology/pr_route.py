#!/usr/bin/env python3
"""Qualify a branch or pull request from the memory cache (center/shards), cheapest checks first. Read-only.

  python3 -I core/ontology/pr_route.py origin/main origin/mst-lean

The rule (proposed; tried on two pull requests, see core/ontology/PR_RULE.md):
  1. Paths to memory. Every changed path is looked up in the centre store: which recorded findings cite
     evidence there. The shards are the memory: a path no record cites carries no recorded result.
  2. Records to rechecks. For each cited record, its recheck (RESULTS.md) is listed, cheapest first. Nothing is run.
  3. The change's own claim, as a tiny exact check. Here, one: when .lean files are removed or added, every
     declaration (theorem, lemma, def, ...) before must exist after with the same text, whitespace aside.
  4. Freshness. How far the branch is behind, and whether it merges cleanly (git merge-tree, nothing written).
Verdict: the weakest of the four. A branch whose paths no record cites and that does not merge is "superseded":
nothing recorded depends on it, and its own claim (step 3) says whether its content is worth re-applying.
Exit codes: 0 qualified, 1 not qualified, 2 usage."""
import glob, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s:(\[{]+)", re.M)
REF = re.compile(r"^[\w./-]+$")

def git(*a, ok=False):
    r = subprocess.run(["git", "-C", ROOT, *a], capture_output=True, text=True)
    if r.returncode and not ok: raise SystemExit(f"git {' '.join(a[:2])} failed: {r.stderr.strip()[:200]}")
    return r

def memory():
    recs = []
    for f in sorted(glob.glob(os.path.join(ROOT, "center", "shards", "*.jsonl"))):
        for line in open(f, encoding="utf-8"):
            try: recs.append(json.loads(line))
            except ValueError: pass
    return recs

def cited(recs, path):
    return [r for r in recs if any(str(e).split("::")[0] == path or str(e).split("::")[0].startswith(path.rstrip("/") + "/")
                                   for e in (r.get("evidence") or []))]

def decls(rev, files):
    out = {}
    for f in files:
        r = git("show", f"{rev}:{f}", ok=True)
        if r.returncode: continue
        ms = list(DECL.finditer(r.stdout))
        for i, m in enumerate(ms):
            body = r.stdout[m.start(): ms[i + 1].start() if i + 1 < len(ms) else len(r.stdout)]
            body = re.split(r"\n(?:end\b|namespace\b|section\b|open\b|/--|--)", body)[0]
            out.setdefault((m.group(1), m.group(2)), set()).add(" ".join(body.split()))
    return out

def main(argv):
    if len(argv) != 2 or not all(REF.fullmatch(a) for a in argv): print(__doc__); return 2
    main_ref, head = argv
    base = git("merge-base", main_ref, head).stdout.strip()
    rows = [l.split("\t") for l in git("diff", "--name-status", "-M", base, head).stdout.splitlines()]
    before = [r[1] for r in rows if r[0][0] in "DMR"]; after = [r[-1] for r in rows if r[0][0] in "AMR"]
    recs = memory(); verdicts = []
    print(f"branch {head}: {len(rows)} changed paths against {main_ref} (merge base {base[:8]})")
    hit = {}
    for p in sorted(set(before) | set(after)):
        for r in cited(recs, p): hit[r.get("id", "?")] = r
    if hit:
        print(f"[memory] {len(hit)} recorded findings cite evidence on changed paths")
        for r in sorted(hit.values(), key=lambda r: str(r.get("id")))[:12]:
            print(f"  [{r.get('word') or r.get('label') or 'open'}] {r.get('id')}: {str(r.get('statement') or r.get('text') or '')[:90]}")
        if len(hit) > 12: print(f"  ... and {len(hit) - 12} more")
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import route
        changed = set(before) | set(after); rcs = {}
        if os.path.isfile(os.path.join(ROOT, "RESULTS.md")):
            for line in open(os.path.join(ROOT, "RESULTS.md"), encoding="utf-8"):
                m = route.ROW.match(line.rstrip("\n"))
                if not m: continue
                ev = {e.strip("` ").split("::")[0] for e in m.group(3).split(",")}
                pm = route.PLAIN.match(m.group(4).strip())
                if pm and ev & changed:
                    f = os.path.join(ROOT, pm.group(1))
                    n = sum(1 for _ in open(f, encoding="utf-8", errors="replace")) if os.path.isfile(f) else None
                    rcs.setdefault(pm.group(1), (route.ORDER[m.group(1)], n if n is not None else 10 ** 9, m.group(1), n))
        print(f"  rechecks whose evidence changed, cheapest first (lines; a proxy, nothing run): {len(rcs)}")
        for rel, (_o, _s, label, n) in sorted(rcs.items(), key=lambda kv: kv[1][:2])[:12]:
            print(f"  [{label}] python3 -I {rel}  ({n} lines)")
        verdicts.append("touches recorded results: run their rechecks")
    else:
        print("[memory] no recorded finding cites any changed path: nothing recorded depends on this change")
    lb, la = [f for f in before if f.endswith(".lean")], [f for f in after if f.endswith(".lean")]
    if lb or la:
        old, new = decls(base, lb), decls(head, la)
        missing = [k for k in old if k not in new]; changed = [k for k in old if k in new and not old[k] <= new[k]]
        added = [k for k in new if k not in old]
        ok = not missing and not changed
        print(f"[{'checked-finite' if ok else 'refuted'}] lean declarations: {len(old)} before, {len(new)} after; "
              f"missing {len(missing)}, text changed {len(changed)}, new {len(added)}" + (f"; e.g. {(missing + changed)[:3]}" if not ok else ""))
        if not ok: verdicts.append("declarations lost or changed")
    behind = git("rev-list", "--count", f"{head}..{main_ref}").stdout.strip()
    mt = git("merge-tree", "--write-tree", "--name-only", main_ref, head, ok=True)
    conflicts = mt.stdout.count("\nCONFLICT") + mt.stdout.startswith("CONFLICT")
    print(f"[tested] freshness: {behind} commits behind {main_ref}; " + ("merges cleanly" if mt.returncode == 0 else f"{conflicts} conflicts"))
    if mt.returncode: verdicts.append("superseded" if not hit else "conflicts with recorded results in play")
    print("verdict: " + ("qualified" if not verdicts else "; ".join(verdicts)))
    return 0 if not verdicts else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
