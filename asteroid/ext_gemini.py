"""asteroid extension: gemini. An outside second opinion on ONE short excerpt. Proposals only.
  python3 -m asteroid.ext_gemini EXCERPT.txt "QUESTION"            dry run (default): prints exactly what would be sent
  python3 -m asteroid.ext_gemini EXCERPT.txt "QUESTION" --send     sends it (needs GEMINI_API_KEY in the environment)
Rules (board card boards/tasks/gemini-second-opinion.md, approved 2026-11-26):
  - one excerpt, at most 4000 bytes; never a directory, never a repository or corpus path (data/, one-not/data/, out/)
  - the key is read from GEMINI_API_KEY only; it is never written to disk or logged
  - every send (and every refusal) appends one line to notes/gemini/LOG.md
  - the reply is printed as a PROPOSAL; nothing here marks anything as checked, paper or tested
Model: GEMINI_MODEL (default gemini-2.0-flash) via the public REST endpoint, key in the x-goog-api-key header."""
import datetime, json, os, sys, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
LOG = os.path.join(ROOT, "notes", "gemini", "LOG.md")
MAX = 4000
FORBIDDEN = ("data/", "one-not/data/", "asteroid/out/", ".git/")
URL = "https://generativelanguage.googleapis.com/v1beta/models/{m}:generateContent"

def log(line):
    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    if not os.path.exists(LOG):
        open(LOG, "w", encoding="utf-8").write("# Gemini log (every request and refusal; excerpts are not copied here)\n\n")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    open(LOG, "a", encoding="utf-8").write(f"- {stamp} {line}\n")

def check(path):
    """Return (ok, reason, text)."""
    rel = os.path.relpath(os.path.abspath(path), ROOT).replace(os.sep, "/")
    if not os.path.isfile(path): return False, "not a file", ""
    if rel.startswith("..") or any(rel.startswith(f) for f in FORBIDDEN): return False, f"path not allowed: {rel}", ""
    raw = open(path, "rb").read()
    if len(raw) > MAX: return False, f"excerpt is {len(raw)} bytes; the limit is {MAX} (pick the one lemma, not the file)", ""
    return True, rel, raw.decode("utf-8", "replace")

def send(question, excerpt, model):
    key = os.environ.get("GEMINI_API_KEY")
    if not key: raise RuntimeError("GEMINI_API_KEY is not set; nothing was sent")
    body = json.dumps({"contents": [{"parts": [{"text": "You are an outside reviewer. Be brief and say what would falsify your answer.\n\nQUESTION: " + question + "\n\nEXCERPT:\n" + excerpt}]}]}).encode()
    req = urllib.request.Request(URL.format(m=model), data=body, headers={"Content-Type": "application/json", "x-goog-api-key": key})
    with urllib.request.urlopen(req, timeout=120) as r:
        d = json.load(r)
    return d["candidates"][0]["content"]["parts"][0]["text"]

def main(argv):
    if len(argv) < 2: print(__doc__); return 2
    path, question = argv[0], argv[1]; do_send = "--send" in argv
    ok, reason, text = check(path)
    if not ok:
        log(f"REFUSED {reason}"); print("refused:", reason); return 1
    model = os.environ.get("GEMINI_MODEL", "gemini-2.0-flash")
    if not do_send:
        print(f"DRY RUN. Would send to {model}:\n  excerpt: {reason} ({len(text.encode())} bytes)\n  question: {question}\n---\n{text}\n---")
        print("Nothing was sent. Add --send with GEMINI_API_KEY set to send."); return 0
    try:
        reply = send(question, text, model)
    except Exception as e:
        log(f"FAILED excerpt={reason} error={type(e).__name__}"); print("failed:", type(e).__name__); return 1
    log(f"SENT excerpt={reason} model={model} question={question!r} reply_chars={len(reply)}")
    print("PROPOSAL (unchecked, from Gemini):\n" + reply); return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
