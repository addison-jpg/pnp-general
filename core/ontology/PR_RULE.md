# Qualifying a pull request from the memory cache

Rule (proposed; tried on two pull requests and one branch). Tool: `python3 -I core/ontology/pr_route.py MAIN BRANCH`. Read-only: it runs git and reads files, and it runs no check.

1. **Paths to memory.** Each changed path is looked up in `center/shards`: which recorded findings cite evidence there. A path no record cites carries no recorded result.
2. **Records to rechecks.** The RESULTS.md rechecks whose evidence changed are listed, exact checks first, then by script length (a proxy, not a measured time).
3. **The change's own claim, as a tiny exact check.** One so far: when `.lean` files move, every declaration before must exist after with the same text, whitespace aside.
4. **Freshness.** Commits behind, and whether it merges (`git merge-tree`, nothing written).

Verdict: the weakest step. A branch that no record depends on and that does not merge is **superseded**.

## First run (2026-11-25)

| branch | memory | own claim | freshness | verdict |
|---|---|---|---|---|
| mst-lean (#22) | no record cites its paths | 1103 Lean declarations before and after, none lost or changed (checked-finite) | 673 behind main, 13 conflicts | superseded |
| mst-readme (#21) | no record cites its paths | (no claim check for README removal yet) | 655 behind main, 6 conflicts | superseded |
| refactor/pillars (control) | 72 records cite its paths; 14 rechecks listed | none | merges | touches recorded results |

Both pull requests edit `951/`, which on main now holds 1 Lean file; the live tree is `one-not/lean` (216 files), and every record cites `one-not/`, none `951/`. #22's content is intact by its own claim, so it could be re-applied to `one-not/lean` if still wanted. That is a decision for Addison, not something this rule decides.

## Limits

- Step 3 has one claim check. A README-removal check (no remaining file links to a removed path) is the next one to add.
- Step 2 lists; a person or agent runs the rechecks. Script length is not cost.
- n = 3 branches. The rule is proposed, not tested at scale.
