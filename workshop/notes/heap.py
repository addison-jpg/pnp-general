#!/usr/bin/env python3
"""A shared priority heap of pending agent tasks. Standard library only. Lowest priority number pops first.

  python3 -I workshop/notes/heap.py push PRIORITY "task text" [owner]   (PRIORITY is an integer; 1 is most urgent)
  python3 -I workshop/notes/heap.py pop        (the most urgent task, removed; ties go to the earlier push)
  python3 -I workshop/notes/heap.py peek
  python3 -I workshop/notes/heap.py list       (in pop order, not removed)

The file is heap.jsonl, one JSON object per line. It uses the same O_EXCL lock as stack.py (imported from it),
so a push and a pop cannot interleave. Ties are broken by a sequence number, so order is deterministic.
"""
import heapq, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stack as _lock   # the lock helpers: acquire() and release() around the file

HERE = os.path.dirname(os.path.abspath(__file__))
FILE = os.path.join(HERE, "heap.jsonl")

def load():
    if not os.path.exists(FILE): return []
    items = [json.loads(l) for l in open(FILE, encoding="utf-8") if l.strip()]
    heapq.heapify([(it["priority"], it["seq"], it) for it in items])
    return items

def save(items):
    tmp = FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for it in items: f.write(json.dumps(it, ensure_ascii=False) + "\n")
    os.replace(tmp, FILE)

def main(argv):
    if not argv or argv[0] not in ("push", "pop", "peek", "list"):
        print(__doc__); return 2
    cmd = argv[0]
    _lock.LOCK = FILE + ".lock"
    _lock.acquire()
    try:
        items = load()
        if cmd == "push":
            if len(argv) < 3 or not argv[1].lstrip("-").isdigit(): print("push needs an integer priority and a task"); return 2
            seq = max((it["seq"] for it in items), default=0) + 1
            items.append({"priority": int(argv[1]), "seq": seq, "task": argv[2], "owner": argv[3] if len(argv) > 3 else "unknown",
                          "at": time.strftime("%Y-%m-%dT%H:%M:%S")})
            save(items); print(f"pushed at priority {argv[1]}; size {len(items)}")
        elif cmd in ("pop", "peek"):
            if not items: print("empty"); return 1
            top = min(items, key=lambda it: (it["priority"], it["seq"]))
            if cmd == "pop": items.remove(top); save(items)
            print(json.dumps(top, ensure_ascii=False))
        else:
            for it in sorted(items, key=lambda it: (it["priority"], it["seq"])):
                print(f"p{it['priority']}: {it['task']}  [{it['owner']}, {it['at']}]")
    finally:
        _lock.release()
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
