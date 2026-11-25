#!/usr/bin/env python3
"""Differential test of astmin's memory link: the binary's byte scan of center/shards/*.jsonl against
Python's json reading of the same files, compared byte for byte over the whole prompt transcript.

  python3 -I asteroid/astmin/memory_diff.py [BINARY]

BINARY defaults to $CARGO_TARGET_DIR/release/astmin, else asteroid/astmin/target/release/astmin.
Three stores: the repository's, named by argument; the same, read from the current directory (no
argument); and a made-up one written here with center.py's json.dumps call, holding the edge cases:
a record of exactly LINE bytes, one of LINE + 1, an empty line, a last line with no newline, a hidden
file, a file that is not .jsonl, a non-ASCII word, a record with no word. Exit 1 on any difference."""
import collections, difflib, glob, json, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
LINE = int(re.search(r"const LINE: usize = (\d+);", open(os.path.join(HERE, "src", "main.rs")).read())[1])
BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.environ.get("CARGO_TARGET_DIR", os.path.join(HERE, "target")), "release", "astmin")

def reference(root, shown, finds):
    """The transcript the binary must print for `:memory` and one `:find` per word, computed with json."""
    files = sorted(glob.glob(os.path.join(root, "center", "shards", "*.jsonl")))
    recs, skipped = [], 0
    for f in files:
        for line in open(f, "rb").read().split(b"\n"):
            if len(line) > LINE: skipped += 1
            elif line: recs.append((line, json.loads(line)))
    head = b"%s/center/shards: %d shard files, %d records, %d skipped (too long)\n" % (shown, len(files), len(recs), skipped)
    pairs = collections.Counter((r.get("kind", "-").encode(), r.get("word", "-").encode()) for _, r in recs)
    out = b"4ST> " + head + b"".join(b"%6d %s %s\n" % (n, k, w) for (k, w), n in sorted(pairs.items()))
    out += b"recorded words, not verification: these count what the store says; nothing was re-checked\n"
    for word in finds:
        hits = [r for line, r in recs if word in line]
        out += b"4ST> " + b"".join(b"  id %s  program %s\n" % (r.get("id", "-").encode(), r.get("program", "-").encode()) for r in hits[:3])
        out += b'records containing "%s": %d\n' % (word, len(hits)) + head
    return out + b"4ST> \n", f"{len(files)} shard files, {len(recs)} records, {skipped} skipped (too long), {len(pairs)} (kind, word) pairs"

def check(name, root, args, cwd, shown, finds):
    want, counts = reference(root, shown, finds)
    run = subprocess.run([BIN] + args, cwd=cwd, input=b"".join([b":memory\n"] + [b":find %s\n" % w for w in finds]), capture_output=True)
    same = run.stdout == want and run.returncode == 0
    print(f"{name}: {counts}, {len(finds)} :find words: {'equal' if same else 'DIFFERENT'} ({len(run.stdout)} bytes, exit {run.returncode})")
    if not same:
        sys.stdout.writelines(difflib.unified_diff(want.decode(errors="replace").splitlines(True), run.stdout.decode(errors="replace").splitlines(True), "json", "astmin"))
    return same

def rec(size=0, **kw):
    """One record as center.py writes it, padded with a text field to `size` bytes when asked."""
    kw["text"] = ""
    kw["text"] = "a" * max(0, size - len(json.dumps(kw, ensure_ascii=False, sort_keys=True)))
    return json.dumps(kw, ensure_ascii=False, sort_keys=True)

if not os.path.exists(BIN): sys.exit(f"no binary at {BIN}: build it first (asteroid/astmin/README.md)")
finds = [b"checked-finite", b"Lean", b"lean", b'"word": "refuted"', b"no record holds this"]
ok = check("store, root as argument", REPO, [REPO], "/", REPO.encode(), finds)
ok &= check("store, current directory", REPO, [], REPO, b".", finds)
with tempfile.TemporaryDirectory() as d:
    os.makedirs(os.path.join(d, "center", "shards"))
    put = lambda name, text: open(os.path.join(d, "center", "shards", name), "w", encoding="utf-8").write(text)
    put("b.jsonl", rec(LINE, id="b1", kind="finding", program="made-up", word="tested") + "\n"
        + rec(LINE + 1, id="b2", kind="finding", program="made-up", word="tested") + "\n\n" + rec(id="b3", kind="cell", program="made-up"))
    put("a.jsonl", rec(id="a1", kind="frame", program="made-up", word="réfuté") + "\n" + rec(id="a2", kind="finding", program="made-up", word="tested") + "\n")
    put(".hidden.jsonl", rec(id="h1", kind="finding", program="hidden", word="checked") + "\n")
    put("notes.txt", rec(id="n1", kind="finding", program="notes", word="checked") + "\n")
    assert [len(rec(LINE, id="b1", kind="finding", program="made-up", word="tested").encode()), len(rec(LINE + 1, id="b2", kind="finding", program="made-up", word="tested").encode())] == [LINE, LINE + 1]
    ok &= check("made-up store (edge cases)", d, [d], "/", d.encode(), [b"made-up", "réfuté".encode(), b"hidden", b"b2"])
print("ok: astmin's output equals the json reference, byte for byte" if ok else "MISMATCH: astmin's output differs from the json reference")
sys.exit(0 if ok else 1)
