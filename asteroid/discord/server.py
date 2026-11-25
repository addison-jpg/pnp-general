"""Run the interactions endpoint: python3 -I server.py   (listens on $PORT, default 8080; POST /interactions).
Needs DISCORD_PUBLIC_KEY and REPO_DIR in the environment, and pynacl. Put it behind any HTTPS host."""
import json, os
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import app

class H(BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path != "/interactions":
            self.send_response(404); self.end_headers(); return
        n = int(self.headers.get("Content-Length", "0") or 0)
        if n > 100_000:
            self.send_response(413); self.end_headers(); return
        body = self.rfile.read(n)
        code, out = app.handle(body, {k.lower(): v for k, v in self.headers.items()})
        data = json.dumps(out).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data))); self.end_headers(); self.wfile.write(data)
    def log_message(self, *a): pass

if __name__ == "__main__":
    ThreadingHTTPServer(("0.0.0.0", int(os.environ.get("PORT", "8080"))), H).serve_forever()
