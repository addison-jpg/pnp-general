# Credibility actions

Merged from three audits (outsider read, fresh-clone run, GitHub/linguist rules), 2026-11-25.
[git] = can be done by a commit. [owner] = needs Addison's GitHub or other account.
Ranked by credibility gain per effort.

## Ranked actions

1. [git] Add CITATION.cff. Done as a file in this change (not committed). GitHub shows "Cite this repository" once it is on the default branch.
2. [git] Fix asteroid/asteroid.py:78. It hardcodes /home/user/pequalnp-proofs/tools/bin. On any other machine `by lean` claims are only evaluated, not proved. Look on PATH and ~/.elan only.
3. [git] Add a CI workflow that runs `lake build PEqualNP.Verify.All` and point the proofs badge at it. Biggest single gain.
4. [git] Run the axiom check over lean/QuantumGravity/Open. Until then, mark those results "checked by Lean, axiom audit pending". README line 38 ("All theorems here are checked") contradicts line 129.
5. [git] Rewrite the README top (paragraph below). Remove the P vs NP framing from "Why this is open". BOARD.md marks that aim SUPERSEDED. Say the PEqualNP namespace comes from the upstream library.
6. [git] Move the Lacan/Borromean bullet out of the top. Cite `python3 philosophy/milnor.py` next to it wherever it stays.
7. [git] One status per result in every section. Call PSPACE ⊆ P_CTC ⊆ EXP, KAK and CKW "formalizations of known theorems", with citations (Aaronson–Watrous for P_CTC). Remove the PSPACE ⊆ P_CTC item from "What is open" or explain what remains.
8. [git] State the many-NOT bound exactly: n minus the number of components, tight for disjoint sets and chains.
9. [git] Results table first: statement | status | file::theorem | citation | check command. Generate it from boards/TREE.md. Link an index of the "47 statements".
10. [git] Add an "Install Lean" step (elan, toolchain from one-not/lean/lean-toolchain, `lake exe cache get` size). Warn that the first `by lean` run takes minutes (hello.ath took about 205 s).
11. [git] Replace "Please do not push" with CONTRIBUTING.md: issues and PRs welcome, how to report a proof error.
12. [git] Remove asteroid.exe and `__pycache__/` from the tree. Add `__pycache__/` to .gitignore.
13. [owner] Set repository description, topics and homepage (text below). Repo page, gear icon next to About.
14. [owner] Tag v0.1.0 and publish a GitHub Release with asteroid.exe, the Linux build and editors/vscode/asteroid-0.1.0.vsix, plus SHA-256 checksums.
15. [owner] Zenodo DOI: log in to zenodo.org with GitHub, enable the repo, then cut the release. Add the DOI to CITATION.cff after.
16. [git] Move culture/homestuck/, culture/lifeisstrange/, culture/zodiac/, personal-tools/ to another repo or under misc/.
17. [git] Collapse the install section into one table by platform. Fix `--doctor` vs `doctor` mismatch. Show expected run-cpu output (halts at PC=4).
18. [git] Link biology/privacy/check.py, biology/brain/neuron/check.py and biology/compbio/ from the README, or drop "biology" from the tagline.
19. [git] Add a .gitattributes with a linguist-language override for *.ath so repo stats and highlighting work.
20. [owner] Publish the extension to Open VSX: open-vsx.org login, eclipse.org account, Publisher Agreement, then `npx ovsx create-namespace asteroid -p TOKEN` and `npx ovsx publish editors/vscode/asteroid-0.1.0.vsix -p TOKEN`.
21. [owner] Social preview image: Settings > General.
22. [owner] Linguist PR: not yet. It needs about 2000 .ath files indexed in the last year across many users. One repo cannot qualify. Source: https://raw.githubusercontent.com/github-linguist/linguist/main/CONTRIBUTING.md

README indexing: GitHub code search indexes the default branch. READMEs already there need no further step. Not verified against docs.github.com (blocked in the audit session).

## Paste: repository topics (20)

```
lean4 formal-verification theorem-proving mathlib circuit-complexity boolean-circuits computational-complexity monotone-circuits negation-limited-circuits quantum-computing quantum-circuits closed-timelike-curves knot-theory combinatorics finite-geometry counterexample proof-assistant domain-specific-language vscode-extension mathematics
```

## Paste: description (under 350 chars)

```
Machine-checked results on Boolean circuit size with few NOT gates, plus Lean 4 formalizations of known results in quantum computing and combinatorics. Each result is labelled by how it was checked: Lean proof, computed counterexample, or script. Includes the asteroid (.ath) claim language and checker.
```

Homepage: link the GitHub Release page once it exists.

## Proposed new top-of-README paragraph

> **pnp-general** collects results on how many gates a Boolean circuit needs when it may use only a few NOT gates, a question posed by Jukna and Sergeev (2013) and again by Blum (2024). Results are checked in Lean 4 or by a script in this repository, and each one is labelled with its status, its Lean theorem name and the command that checks it. Some entries are Lean formalizations of known theorems from quantum computing (KAK gate count, CKW inequality, PSPACE ⊆ P_CTC ⊆ EXP), cited to their sources. The Lean project under `lean/` is awaiting a full axiom audit. Nothing here claims progress on P versus NP; the name and the `PEqualNP` namespace come from the upstream library this work started from.
