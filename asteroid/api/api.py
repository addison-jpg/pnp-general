"""asteroid's HTTP API: read-only JSON over the repository's verified state, a guarded /check, and Discord's
interactions endpoint. Standard library plus pynacl (only for /interactions). Writes nothing to the repository.

  GET  /health               {"ok": true}
  GET  /status               verified count and counts by label (from the centre shards)
  GET  /results?program=P    verified findings (id, program, word, text, runner), optional program filter
  GET  /frames?status=OPEN   frames from frames.jsonl, highest score first
  GET  /programs             the top-level .ath programs that /check accepts
  POST /check  {"program": "gravity.ath"}   run one allowlisted program with --no-lean; {"program","exit","summary"}
  POST /interactions         Discord slash commands (see ../discord)

Env: REPO_DIR (a checkout), PORT (default 8080), DISCORD_PUBLIC_KEY (for /interactions), API_KEY (optional: if set,
POST /check needs the header X-API-Key). One /check runs at a time; others get 429.
"""
import collections, glob, hmac, json, os, subprocess, sys, threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

LOCK = threading.Lock()

def repo(env=os.environ): return env.get("REPO_DIR", os.getcwd())

def _commits(r, f):
    """True if the program has a commit statement: /check must never make asteroid commit."""
    try: return any(l.strip().startswith("commit") for l in open(os.path.join(r, f), encoding="utf-8"))
    except OSError: return True

def programs(r):
    return sorted(f for f in os.listdir(r) if f.endswith(".ath") and f != "hello.ath" and not _commits(r, f))

def records(r):
    out = []
    for f in sorted(glob.glob(os.path.join(r, "center", "shards", "*.jsonl"))):
        for line in open(f, encoding="utf-8"):
            if line.strip(): out.append(json.loads(line))
    return out

def verified(r):
    ok = ("checked", "checked-finite", "checked-infinite", "tested", "refuted")
    return [x for x in records(r) if x.get("kind") == "finding" and not x.get("why_not") and x.get("word") in ok]

def status(r):
    v = verified(r)
    return {"verified": len(v), "by_label": dict(collections.Counter(x["word"] for x in v)),
            "by_program": dict(collections.Counter(x["program"] for x in v))}

def results(r, program=None):
    return [{"id": x["id"], "program": x["program"], "word": x["word"], "text": x["text"], "runner": x.get("runner")}
            for x in verified(r) if program is None or x["program"] == program]

def frames(r, st=None):
    p = os.path.join(r, "frames.jsonl")
    rows = [json.loads(l) for l in open(p, encoding="utf-8") if l.strip()] if os.path.isfile(p) else []
    if st: rows = [x for x in rows if x.get("status") == st.upper()]
    return sorted(rows, key=lambda x: -x.get("score", 0))

def check(r, name):
    if name not in programs(r): return 400, {"error": f"{name!r} is not an allowed program"}
    if not LOCK.acquire(blocking=False): return 429, {"error": "a check is already running"}
    try:
        p = subprocess.run(["bin/asteroid", "--no-lean", name], cwd=r, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return 504, {"error": "timed out"}
    finally:
        LOCK.release()
    last = [l for l in p.stdout.splitlines() if l.startswith("claims:")]
    return 200, {"program": name, "exit": p.returncode, "summary": last[-1] if last else None}

def route(method, path, query, body, headers, env=os.environ):
    r = repo(env)
    if method == "GET":
        if path == "/health": return 200, {"ok": True}
        if path == "/status": return 200, status(r)
        if path == "/results": return 200, results(r, (query.get("program") or [None])[0])
        if path == "/frames": return 200, frames(r, (query.get("status") or [None])[0])
        if path == "/programs": return 200, programs(r)
        return 404, {"error": "not found"}
    if method == "POST":
        if path == "/check":
            key = env.get("API_KEY")
            if key and not hmac.compare_digest(headers.get("x-api-key", ""), key): return 401, {"error": "bad key"}
            try: name = json.loads(body or b"{}").get("program", "")
            except ValueError: return 400, {"error": "bad json"}
            return check(r, name)
        if path == "/interactions":
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "discord"))
            import app
            return app.handle(body, headers, env)
    return 404, {"error": "not found"}

class H(BaseHTTPRequestHandler):
    def _go(self, method):
        u = urlparse(self.path); n = int(self.headers.get("Content-Length", "0") or 0)
        if n > 100_000: code, out = 413, {"error": "too large"}
        else: code, out = route(method, u.path, parse_qs(u.query), self.rfile.read(n) if n else b"",
                                {k.lower(): v for k, v in self.headers.items()})
        data = json.dumps(out).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data))); self.end_headers(); self.wfile.write(data)
    def do_GET(self): self._go("GET")
    def do_POST(self): self._go("POST")
    def log_message(self, *a): pass

if __name__ == "__main__":
    ThreadingHTTPServer(("0.0.0.0", int(os.environ.get("PORT", "8080"))), H).serve_forever()
