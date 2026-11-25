#!/usr/bin/env python3
"""A shared stack of pending agent tasks, in one file. Standard library only.

  python3 -I workshop/notes/stack.py push "task text" [owner]
  python3 -I workshop/notes/stack.py pop          (the most recent task, removed; prints it)
  python3 -I workshop/notes/stack.py peek         (the most recent task, not removed)
  python3 -I workshop/notes/stack.py list

Last in, first out. The file is workshop/notes/stack.jsonl, one JSON object per line. A lock file (O_EXCL)
serialises writers, so two agents cannot interleave a push and a pop. A stale lock (older than 60 s) is
reported, not silently removed. Nothing here is memory: it is a list of work waiting to be done.
"""
import json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FILE = os.path.join(HERE, "stack.jsonl")
LOCK = FILE + ".lock"

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

def load():
    if not os.path.exists(FILE): return []
    return [json.loads(l) for l in open(FILE, encoding="utf-8") if l.strip()]

def save(items):
    tmp = FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for it in items: f.write(json.dumps(it, ensure_ascii=False) + "\n")
    os.replace(tmp, FILE)

def main(argv):
    if not argv or argv[0] not in ("push", "pop", "peek", "list"):
        print(__doc__); return 2
    cmd = argv[0]
    acquire()
    try:
        items = load()
        if cmd == "push":
            if len(argv) < 2: print("push needs a task"); return 2
            items.append({"task": argv[1], "owner": argv[2] if len(argv) > 2 else "unknown", "at": time.strftime("%Y-%m-%dT%H:%M:%S")})
            save(items); print(f"pushed; depth {len(items)}")
        elif cmd in ("pop", "peek"):
            if not items: print("empty"); return 1
            top = items[-1]
            if cmd == "pop": items.pop(); save(items)
            print(json.dumps(top, ensure_ascii=False))
        else:
            for i, it in enumerate(reversed(items)): print(f"{len(items)-i}: {it['task']}  [{it['owner']}, {it['at']}]")
    finally:
        release()
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
