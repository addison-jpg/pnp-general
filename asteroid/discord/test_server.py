import json, os, sys, tempfile, threading, urllib.request, urllib.error
from nacl.signing import SigningKey
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sk = SigningKey.generate(); os.environ["DISCORD_PUBLIC_KEY"] = sk.verify_key.encode().hex()
repo = tempfile.mkdtemp(); open(os.path.join(repo, "RESULTS.md"), "w").write("135 verified findings\n"); os.environ["REPO_DIR"] = repo
import server
from http.server import ThreadingHTTPServer
srv = ThreadingHTTPServer(("127.0.0.1", 0), server.H); threading.Thread(target=srv.serve_forever, daemon=True).start()
url = f"http://127.0.0.1:{srv.server_address[1]}/interactions"
def post(body, signed=True):
    h = {"Content-Type": "application/json"}
    if signed: h.update({"X-Signature-Ed25519": sk.sign(b"1" + body).signature.hex(), "X-Signature-Timestamp": "1"})
    try: return urllib.request.urlopen(urllib.request.Request(url, data=body, headers=h)).status, None
    except urllib.error.HTTPError as e: return e.code, None
fails = 0
for name, ok in [("signed ping accepted", post(b'{"type":1}')[0] == 200), ("unsigned request rejected", post(b'{"type":1}', False)[0] == 401)]:
    print(("PASS " if ok else "FAIL ") + name); fails += not ok
print(f"{fails} failures"); sys.exit(1 if fails else 0)
