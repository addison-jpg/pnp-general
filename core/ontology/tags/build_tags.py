#!/usr/bin/env python3
"""Parse the two structure-tag tables (markdown) into JSON. Reproducible and standard library only.

  python3 -I core/ontology/tags/build_tags.py [--culture MD] [--pillar MD] [--out DIR]

The two markdown tables were written by an agent and have NOT been reviewed by a person. The JSON says so in
its top-level "status" field, and every answer that uses it says so. The same input gives the same bytes: no
timestamps; the sha256 of each source file is recorded instead.

Inputs default to the files named in the environment variables TAGS_CULTURE_MD and TAGS_PILLAR_MD, else to
the scratch location where the agent left them. The markdown is not kept in the repository; the JSON is the
durable form.

Outputs (in --out, default: this folder): tags_culture.json, tags_formal.json.
Each row: corpus (or pillar), name, reading, tags, new_tags_proposed, label, label_word, file.
A tag written "X (new)" in the table goes in new_tags_proposed, not in tags: it is not adopted.
For a formal row, "name" is the result as stated and "reading" is null: a result is not a reading.
The three tags the table proposed that are not in the vocabulary (diagonal, min-cut, seriality) go in
"proposed_vocabulary", marked not adopted."""
import hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SCRATCH = "/tmp/claude-0/-home-user/c7c2895f-eb04-517d-b538-6d0d59d567a9/scratchpad/synth"
STATUS = "proposed tags, unreviewed"
LABEL_WORDS = ["checked-infinite", "checked-finite", "checked", "tested", "refuted", "analogy", "open", "join", "paper", "premise"]
TAG = re.compile(r"[A-Za-z][A-Za-z0-9-]*")
PROPOSED_VOCAB = [
    {"tag": "diagonal", "definition": "no system holds a total judge of itself (Lawvere, Cantor)"},
    {"tag": "min-cut", "definition": "least edge weight separating a region of a weighted graph"},
    {"tag": "seriality", "definition": "every world reaches some world, so no dead end"},
]

def label_word(raw):
    m = re.match(r"[a-z][a-z-]*", raw.strip())
    return m.group(0) if m and m.group(0) in LABEL_WORDS else "unlabelled"

def split_tags(cell):
    """(adopted tags, proposed new tags). "diagonal (new)" is a proposed new tag; "(none fits)" gives no tag."""
    out, new = [], []
    for t in cell.split(","):
        t = t.strip()
        if t.endswith(" (new)"):
            t = t[:-6].strip()
            if TAG.fullmatch(t) and t not in new: new.append(t)
        elif TAG.fullmatch(t) and t not in out: out.append(t)
    return out, new

def table_rows(text, heading_start, ncells):
    """The data rows of the table that follows the heading line starting with heading_start."""
    lines, rows, inside = text.splitlines(), [], False
    for i, l in enumerate(lines):
        if l.startswith("## "):
            if inside: break
            inside = l.startswith(heading_start); continue
        if not inside or not l.startswith("|"): continue
        if re.fullmatch(r"\|[-| :]+\|?", l.strip()): continue                      # the separator line
        cells = [c.strip() for c in l.strip().strip("|").split(" | ")]
        if len(cells) != ncells: raise SystemExit(f"line {i + 1}: expected {ncells} cells, found {len(cells)}: {l[:80]}")
        rows.append(cells)
    return rows[1:]      # drop the header row

def build(culture_md, pillar_md):
    ct, pt = open(culture_md, encoding="utf-8").read(), open(pillar_md, encoding="utf-8").read()
    crow = [{"corpus": c[0], "name": c[1], "reading": c[2], "tags": split_tags(c[3])[0], "new_tags_proposed": split_tags(c[3])[1],
             "label": c[4], "label_word": label_word(c[4]), "file": c[5]} for c in table_rows(ct, "## Table 1", 6)]
    frow = [{"pillar": c[0], "name": c[1], "reading": None, "tags": split_tags(c[2])[0], "new_tags_proposed": split_tags(c[2])[1],
             "label": c[3], "label_word": label_word(c[3]), "file": c[4]} for c in table_rows(pt, "## Table 1", 5)]
    sha = lambda t: hashlib.sha256(t.encode("utf-8")).hexdigest()
    note = ("Agent-produced tag table. Not reviewed by a person. A tag is a proposed structural label for a row; "
            "the row's own label (label, label_word) is what the repo records for the claim, not for the tag.")
    mk = lambda kind, rows, src: {"status": STATUS, "kind": kind, "note": note, "source_sha256": sha(src),
                                  "rows": rows, "proposed_vocabulary": {"status": "proposed, not adopted", "tags": PROPOSED_VOCAB}}
    return mk("culture", crow, ct), mk("formal", frow, pt)

def main(argv):
    a = {"--culture": os.environ.get("TAGS_CULTURE_MD") or os.path.join(SCRATCH, "culture_tags.md"),
         "--pillar": os.environ.get("TAGS_PILLAR_MD") or os.path.join(SCRATCH, "pillar_tags.md"), "--out": HERE}
    i = 0
    while i < len(argv):
        if argv[i] not in a or i + 1 >= len(argv): raise SystemExit(__doc__)
        a[argv[i]] = argv[i + 1]; i += 2
    for k in ("--culture", "--pillar"):
        if not os.path.isfile(a[k]): raise SystemExit(f"build_tags: no such file: {a[k]}")
    c, f = build(a["--culture"], a["--pillar"])
    os.makedirs(a["--out"], exist_ok=True)
    for name, d in (("tags_culture.json", c), ("tags_formal.json", f)):
        with open(os.path.join(a["--out"], name), "w", encoding="utf-8", newline="\n") as fh:
            json.dump(d, fh, indent=1, sort_keys=True, ensure_ascii=False); fh.write("\n")
        print(f"wrote {os.path.join(a['--out'], name)}: {len(d['rows'])} rows, {len({t for r in d['rows'] for t in r['tags']})} tags ({d['status']})")

if __name__ == "__main__":
    main(sys.argv[1:])
