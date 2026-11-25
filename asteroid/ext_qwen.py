"""asteroid extension: proposals. The model guesses, asteroid decides.
  propose NAME "TASK" [model 0.5B|1.5B] [n K]
asks a local Qwen model (chat template, greedy decoding) for up to K candidate claim lines for TASK (K <= 8,
default 3). Each candidate is run through asteroid's own claim machinery in an isolated scratch session: a separate
process on a temporary .ath file that holds the pure definitions above this line (seq literal or from, kripke, dist)
and the candidate. Each candidate prints TRUE, FALSE or REJECTED (not a claim line, or it would have side effects).
Rules. A proposal never writes a record or a frame, and never counts as a claim: it does not change the summary or
the exit code. Only a candidate copied into a program as a claim, and passing there, can become a result.
Model outputs are cached by prompt hash in asteroid/out/qwen_cache.json (or $ASTEROID_QWEN_CACHE), so reruns are
deterministic and cheap. Without the model or transformers the line prints a message and does nothing.
The model runs in $ASTEROID_QWEN_PYTHON (default: a python with transformers; see SPEC.md)."""
import hashlib, json, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MODELS = {"0.5B": "Qwen/Qwen2.5-0.5B-Instruct", "1.5B": "Qwen/Qwen2.5-1.5B-Instruct"}
KMAX = 8
PROPOSALS = {}      # name -> list of (candidate, verdict); for display only, never read by a claim
SAFE_DEF = re.compile(r'(seq \w+ = (from \S+( "[^"]*")?|\[[^\]]*\])|kripke \w+ = .+|dist \w+ = .+)')
CLAIM = re.compile(r'claim (?!!)(?!forall c in )(.+)')
SYSTEM = ("You write lines of the asteroid language. Output only candidate lines, one per line, no prose, no numbering.\n"
          "Allowed forms:\n"
          '  claim formula SEQ = "EXPR" [from K]     EXPR uses n, integers, + - * // ** ( ), n!, n!!, C(a, b)\n'
          "  claim SEQ = [1, 2, 5]\n"
          '  claim valid FRAMES "FORMULA"   claim invalid FRAMES "FORMULA"   claim defines FRAMES "FORMULA" PROPS\n'
          "Modal formulas use atoms p q, ~, [], <>, &, |, ->. PROPS: reflexive transitive symmetric euclidean serial joined by +.\n"
          "Examples (other tasks):\n"
          '  claim formula squares = "n**2"\n'
          '  claim formula evens = "2*n" from 0\n'
          '  claim defines all3 "[]p -> p" reflexive\n')

def cache_path(): return os.environ.get("ASTEROID_QWEN_CACHE") or os.path.join(HERE, "out", "qwen_cache.json")

def _load_cache():
    try: return json.load(open(cache_path(), encoding="utf-8"))
    except (OSError, ValueError): return {}

def _save_cache(c):
    p = cache_path(); os.makedirs(os.path.dirname(p), exist_ok=True)
    tmp = p + ".tmp"; json.dump(c, open(tmp, "w", encoding="utf-8"), indent=1, sort_keys=True); os.replace(tmp, p)

def _python():
    """A python that has transformers, or None."""
    cands = [os.environ.get("ASTEROID_QWEN_PYTHON"), os.path.join(ROOT, ".venv", "bin", "python"), sys.executable]
    for py in [c for c in cands if c and os.path.exists(c)]:
        try:
            r = subprocess.run([py, "-c", "import transformers, torch"], capture_output=True, timeout=120)
            if r.returncode == 0: return py
        except (OSError, subprocess.TimeoutExpired): pass
    return None

def generate(model, system, user, k):
    """Ask the model once. Returns its text, or raises RuntimeError with a plain reason. Tests replace this."""
    py = _python()
    if not py: raise RuntimeError("no python with transformers and torch (set ASTEROID_QWEN_PYTHON)")
    env = dict(os.environ); env.setdefault("HF_HUB_OFFLINE", "1")
    job = json.dumps({"model": model, "system": system, "user": user})
    try: r = subprocess.run([py, os.path.abspath(__file__), "--generate"], input=job, capture_output=True, text=True, env=env, timeout=900)
    except subprocess.TimeoutExpired: raise RuntimeError("the model timed out after 900 s")
    if r.returncode != 0: raise RuntimeError(f"the model did not run (exit {r.returncode}): " + (r.stderr.strip().splitlines() or ["no message"])[-1][:200])
    return r.stdout

def _gen_main():
    """Run inside the model's python: greedy decoding with the chat template."""
    job = json.loads(sys.stdin.read())
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    torch.manual_seed(0); torch.set_num_threads(max(1, (os.cpu_count() or 2) // 2))
    tok = AutoTokenizer.from_pretrained(job["model"]); m = AutoModelForCausalLM.from_pretrained(job["model"], torch_dtype=torch.float32).eval()
    text = tok.apply_chat_template([{"role": "system", "content": job["system"]}, {"role": "user", "content": job["user"]}], tokenize=False, add_generation_prompt=True)
    ids = tok(text, return_tensors="pt")
    with torch.no_grad(): out = m.generate(**ids, max_new_tokens=200, do_sample=False)
    sys.stdout.write(tok.decode(out[0][ids["input_ids"].shape[1]:], skip_special_tokens=True))

def candidates(text, k):
    """The first k distinct lines that look like asteroid lines (backticks, bullets and numbering stripped)."""
    out = []
    for l in text.splitlines():
        l = re.sub(r"^\s*(?:[-*]|\d+[.)])\s*", "", l).strip().strip("`").strip()
        if l and not l.startswith("```") and l not in out: out.append(l)
        if len(out) == k: break
    return out

def context(script, ln):
    """The pure definition lines above line ln of the script: they define names, they write nothing."""
    try: lines = open(script, encoding="utf-8").read().splitlines()[:ln - 1]
    except OSError: return []
    out, here = [], os.path.dirname(os.path.abspath(script))
    for l in lines:
        l = l.split("#", 1)[0].strip()
        if not SAFE_DEF.fullmatch(l): continue
        if m := re.fullmatch(r'(seq \w+ = from )(\S+)(.*)', l):     # make the path absolute: the scratch file lives elsewhere
            f = m.group(2) if os.path.isabs(m.group(2)) else next((x for x in (os.path.join(here, m.group(2)), os.path.join(ROOT, m.group(2))) if os.path.exists(x)), m.group(2))
            l = m.group(1) + f + m.group(3)
        out.append(l)
    return out

def judge(defs, cand):
    """Run one candidate in an isolated scratch session. Returns 'TRUE', 'FALSE' or 'REJECTED: why'."""
    c = re.sub(r"\s+by lean\s*$", "", cand.split("#", 1)[0].strip())
    if re.match(r"(formula|valid|invalid|defines|worlds) ", c): c = "claim " + c      # a missing verb is added, nothing else
    if not CLAIM.fullmatch(c): return "REJECTED: not a claim line"
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "proposal.ath")
        open(f, "w", encoding="utf-8").write("\n".join(defs + [c]) + "\n")
        env = dict(os.environ); env["ASTEROID_FRAMES"] = os.path.join(d, "frames.jsonl")
        try: r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "asteroid.py"), "--no-lean", f], cwd=ROOT, capture_output=True,
                                text=True, encoding="utf-8", errors="replace", env=env, timeout=300)
        except subprocess.TimeoutExpired: return "FALSE (timed out)"
    m = re.search(rf"^{len(defs) + 1}: claim .*: python (TRUE|FALSE) \((.*)\)$", r.stdout, re.M)
    if not m: return "REJECTED: " + ((r.stderr or r.stdout).strip().splitlines() or ["no output"])[-1][:120]
    return m.group(1) if m.group(1) == "TRUE" else f"FALSE ({m.group(2)[:80]})"

def propose(name, task, size, k, script, ln, say):
    model = MODELS[size]
    defs = context(script, ln)
    user = (f"Task: {task}\n" + ("Names already defined:\n" + "\n".join(defs) + "\n" if defs else "")
            + f"Give up to {k} candidate lines.")
    key = hashlib.sha256(json.dumps([model, SYSTEM, user, k]).encode()).hexdigest()
    cache = _load_cache()
    if key in cache: text, how = cache[key]["text"], "cached"
    else:
        try: text = generate(model, SYSTEM, user, k)
        except Exception as e:
            say(f"{ln}: propose {name}: model unavailable ({e}); nothing proposed, nothing changed"); return
        cache[key] = {"model": model, "task": task, "k": k, "text": text}; _save_cache(cache); how = "model output"
    cs = candidates(text, k)
    say(f"{ln}: propose {name}: {len(cs)} candidates from {model} ({how}); proposals only, not claims")
    PROPOSALS[name] = []
    for c in cs:
        v = judge(defs, c); PROPOSALS[name].append((c, v)); say(f"    {v.split(' ')[0].rstrip(':'):<9} {c}" + (f"   [{v}]" if v not in ("TRUE",) else ""))
    t = sum(v == "TRUE" for _, v in PROPOSALS[name])
    say(f"    {t} of {len(cs)} candidates TRUE in scratch (tested, model output). Copy one into the program as a claim to make it count.")

def handle(line, api):
    m = re.fullmatch(r'propose (\w+) "([^"]+)"(?: model (0\.5B|1\.5B))?(?: n (\d+))?', line)
    if not m: return False
    k = int(m.group(4) or 3)
    if not 1 <= k <= KMAX: raise SystemExit(f"{api['script']}:{api['ln']}: n must be 1..{KMAX}")
    import asteroid.asteroid as A
    propose(m.group(1), m.group(2), m.group(3) or "0.5B", k, api["script"], api["ln"], A.say)
    return True

if __name__ == "__main__" and sys.argv[1:] == ["--generate"]: _gen_main()
