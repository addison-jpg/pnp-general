#!/usr/bin/env python3
"""Build docs/index.html: one static page from the centre (verified results, open frames) in the repo's palette.
Run: python3 -I center.py && python3 -I site/build_site.py     Serve docs/ with GitHub Pages (Settings > Pages > main /docs)."""
import collections, glob, html, json, os
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
pal = json.load(open("site/palette.json"))
recs = [json.loads(l) for f in sorted(glob.glob("center/shards/*.jsonl")) for l in open(f, encoding="utf-8") if l.strip()]
ok = ("checked", "checked-finite", "checked-infinite", "tested", "refuted")
ver = [r for r in recs if r.get("kind") == "finding" and not r.get("why_not") and r.get("word") in ok]
frames = [json.loads(l) for l in open("frames.jsonl", encoding="utf-8") if l.strip()] if os.path.isfile("frames.jsonl") else []
openf = sorted([f for f in frames if f.get("status") == "OPEN"], key=lambda f: -f.get("score", 0))
byw = collections.Counter(r["word"] for r in ver)
byp = collections.defaultdict(list)
for r in ver: byp[r["program"]].append(r)
e = lambda s: html.escape(str(s))
def css(m): return "".join(f"--{k.replace('_','-')}:{v};" for k, v in pal[m].items())
rows = []
for p in sorted(byp):
    items = "".join(f"<li><b class='w {e(r['word'])}'>{e(r['word'])}</b> {e(r['text'][:260])}"
                    + (f"<br><code>{e(r['runner'])}</code>" if r.get("runner") else "") + "</li>" for r in byp[p])
    rows.append(f"<details><summary>{e(p)} <span class='n'>{len(byp[p])}</span></summary><ul>{items}</ul></details>")
fr = "".join(f"<li><b>{e(f.get('source',''))[:120]}</b><br>{e(f.get('reading',''))[:200]}</li>" for f in openf[:12])
page = f"""<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>asteroid</title><style>
:root{{{css('light')}}}
@media (prefers-color-scheme: dark){{:root{{{css('dark')}}}}}
body{{margin:0;background:var(--background);color:var(--text);font:16px/1.55 system-ui,sans-serif}}
main{{max-width:46rem;margin:0 auto;padding:1.5rem 1rem 4rem}}
h1{{font-size:2rem;margin:.2rem 0}} h2{{margin-top:2rem}} a{{color:var(--accent)}}
.stats{{display:flex;flex-wrap:wrap;gap:.6rem;margin:1rem 0}} .stat{{background:var(--surface);padding:.5rem .8rem;border-radius:.5rem}}
.stat b{{font-size:1.4rem;display:block}} details{{background:var(--surface);border-radius:.5rem;margin:.4rem 0;padding:.4rem .8rem}}
summary{{cursor:pointer;font-weight:600}} .n{{color:var(--muted);font-weight:400}} ul{{padding-left:1.1rem}} li{{margin:.5rem 0}}
code{{background:var(--code-background);color:var(--code-text);padding:.05rem .3rem;border-radius:.25rem;font-size:.85em;word-break:break-all}}
.w{{font-size:.72rem;text-transform:uppercase;padding:.05rem .35rem;border-radius:.25rem;background:var(--code-background)}}
.checked,.checked-finite,.checked-infinite{{color:var(--proved)}} .refuted{{color:var(--refuted)}} .tested{{color:var(--open)}}
.limits{{background:var(--surface);border-left:4px solid var(--open);padding:.6rem 1rem;border-radius:.3rem}}
</style></head><body><main>
<h1>asteroid</h1>
<p>One language, one standard of proof, every field. Circuit complexity, quantum gravity, cosmology, knot theory, neuroscience, biology, privacy, transit, modal logic and philosophy are written as <code>.ath</code> programs that check themselves.</p>
<div class="stats"><div class="stat"><b>{len(ver)}</b>verified results</div>{''.join(f'<div class="stat"><b>{n}</b>{e(w)}</div>' for w, n in byw.most_common())}</div>
<p><a href="https://github.com/addison-jpg/pnp-general">Repository</a> · <a href="https://github.com/addison-jpg/pnp-general/blob/main/RESULTS.md">RESULTS.md</a> · <a href="https://github.com/addison-jpg/pnp-general/blob/main/asteroid/SPEC.md">Language spec</a></p>
<div class="limits"><b>Honest limits.</b> The Lean results formalize known theorems, and the axiom audit of the <code>lean/</code> project is pending. Readings of philosophy and fiction are labelled readings, never results. Nothing here claims progress on P versus NP.</div>
<h2>Verified results</h2>{''.join(rows)}
<h2>The open edge</h2><ul>{fr}</ul>
<p style="color:var(--muted)">Generated from the repository's centre store by <code>site/build_site.py</code>.</p>
</main></body></html>"""
os.makedirs("docs", exist_ok=True); open("docs/index.html", "w", encoding="utf-8").write(page)
print("docs/index.html:", len(ver), "results,", len(openf), "open frames,", len(page) // 1024, "KB")
