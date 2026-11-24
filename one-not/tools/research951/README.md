# research951: research session tools and data (private)

Board summaries: agents/research-*.md on branch `board`.
- relax.py      one-NOT (or monotone) circuit SAT (python-sat, CaDiCaL) correct only on a chosen row set (weight <= k or all).
                `python3 relax.py '<json sets>' n s mode [--mono]`, mode = 'w<=1' | 'w<=2' | 'all'. Result: research-relax.md.
- sweep.py      sweep over (1,1)-disjoint systems from nauty-genbg (set-circuit / Wegener p.214 question); data/sc_n*.jsonl
                (n=4: 3, n=5: 32, n=6: 394 systems; none beats base).
- frontier.py   weight<=1 relaxation on front's base-15 frontier (data/front33.json); too slow at s=14, superseded by scaffold.
- cores.py      regenerate core systems with nauty (research-cores.md).
- kget.py       download PDFs from Kyoto RIMS repository by handle (DSpace REST API).
- crawl/        OpenAlex forward-citation crawl (seeds.py resolves seeds, forward.py crawls + ranks; zb.py zbMATH lookup).
                data/forward.json = 255 citing works with abstracts; data/seeds.json. Result: research-crawl.md.
Requirements: python3, python-sat, networkx, nauty (genbg).
- fableW/        Fable W: plane2.py = monotone circuit for AG(2,q^2) lines correct on all inputs of weight <= k (default 2);
                 `python3 plane2.py 5 --verify` (q=5: n=625, base 15600, 14970 gates; scan.py T=4: 12370). Barrier for weight-bounded proofs.
- verifyW/       research's independent checker for fableW (check.py q [T]: exhaustive weight<=2; w3.py: weight-3 sanity).
- fableK/        Fable K (paused by spend limit): world/quadrant experiments for the Sokolov game form.
