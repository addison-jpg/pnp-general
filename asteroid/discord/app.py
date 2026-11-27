"""asteroid's Discord interactions endpoint: one function, host-neutral.

Discord POSTs signed requests here. We verify the Ed25519 signature with the application's public key, answer
PING, and handle two slash commands:
  /status           the verified count from RESULTS.md and the latest commit line (read-only)
  /check PROGRAM    run one allowlisted top-level .ath program with --no-lean and reply TRUE/FALSE
Nothing else runs. It never commits to the repository, though an allowed program may record its normal findings.
Env: DISCORD_PUBLIC_KEY (hex), REPO_DIR (path to a checkout).
"""
import json, os, re, subprocess
from nacl.signing import VerifyKey
from nacl.exceptions import BadSignatureError

def _programs(repo):
    out = set()
    for f in os.listdir(repo):
        if not f.endswith(".ath") or f == "hello.ath": continue
        try:
            if any(l.strip().startswith("commit") for l in open(os.path.join(repo, f), encoding="utf-8")): continue
        except OSError:
            continue
        out.add(f)
    return out

def verify(public_key_hex, signature_hex, timestamp, body: bytes) -> bool:
    try:
        VerifyKey(bytes.fromhex(public_key_hex)).verify(timestamp.encode() + body, bytes.fromhex(signature_hex))
        return True
    except (BadSignatureError, ValueError):
        return False

def _status(repo):
    text = open(os.path.join(repo, "RESULTS.md"), encoding="utf-8").read()
    m = re.search(r"(\d+) verified findings", text)
    return f"verified findings: {m.group(1) if m else 'unknown'}"

def _check(repo, name):
    if name not in _programs(repo):
        return f"`{name}` is not an allowed program"
    r = subprocess.run(["bin/asteroid", "--no-lean", name], cwd=repo, capture_output=True, text=True, timeout=600)
    last = [l for l in r.stdout.splitlines() if l.startswith("claims:")]
    return f"{name}: exit {r.returncode}. " + (last[-1] if last else "no summary line")

def handle(body: bytes, headers: dict, env=os.environ):
    """Return (status, json_body). headers: lower-cased header names."""
    if not verify(env["DISCORD_PUBLIC_KEY"], headers.get("x-signature-ed25519", ""),
                  headers.get("x-signature-timestamp", ""), body):
        return 401, {"error": "bad signature"}
    req = json.loads(body)
    if req.get("type") == 1:                     # PING
        return 200, {"type": 1}
    if req.get("type") == 2:                     # slash command
        repo = env["REPO_DIR"]
        name = req["data"]["name"]
        if name == "status":
            content = _status(repo)
        elif name == "check":
            opts = req["data"].get("options", [])
            content = _check(repo, opts[0]["value"]) if opts else "usage: /check PROGRAM.ath"
        else:
            content = "unknown command"
        return 200, {"type": 4, "data": {"content": content[:1900]}}
    return 400, {"error": "unsupported interaction"}
