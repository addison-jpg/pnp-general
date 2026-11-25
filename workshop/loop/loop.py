#!/usr/bin/env python3
"""A small Mobius-style loop. Standard library only.

  python3 -I workshop/loop/loop.py [passes]

One pass reads the last 5 lines of out.jsonl (the memory) and appends one line:
  pass  = previous pass + 1 (or 1 if empty)
  total = previous total + pass
  seen  = number of memory lines read this pass
What one pass writes is what the next pass reads. An O_EXCL lock (as in
workshop/notes/stack.py) stops two passes from interleaving.
"""
import json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FILE = os.path.join(HERE, "out.jsonl")
LOCK = FILE + ".lock"
MEMORY = 5

def acquire(timeout=10.0):
    t0 = time.time()
    while True:
        try:
            fd = os.open(LOCK, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.write(fd, str(os.getpid()).encode()); os.close(fd)
            return
        except FileExistsError:
            if time.time() - os.path.getmtime(LOCK) > 60:
                raise SystemExit(f"stale lock {LOCK} (older than 60 s): check it, then remove it by hand")
            if time.time() - t0 > timeout: raise SystemExit("lock busy: try again")
            time.sleep(0.05)

def release():
    try: os.remove(LOCK)
    except FileNotFoundError: pass

def memory():
    if not os.path.exists(FILE): return []
    lines = [l for l in open(FILE, encoding="utf-8") if l.strip()]
    return [json.loads(l) for l in lines[-MEMORY:]]

def one_pass():
    acquire()
    try:
        mem = memory()
        last = mem[-1] if mem else {"pass": 0, "total": 0}
        k = last["pass"] + 1
        row = {"pass": k, "total": last["total"] + k, "seen": len(mem)}
        with open(FILE, "a", encoding="utf-8") as f: f.write(json.dumps(row) + "\n")
        return row
    finally:
        release()

def main(argv):
    n = int(argv[0]) if argv else 1
    rows = [one_pass() for _ in range(n)]
    for r in rows: print(f"pass {r['pass']}: total {r['total']}, seen {r['seen']}")
    print(json.dumps(rows[-1]))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
