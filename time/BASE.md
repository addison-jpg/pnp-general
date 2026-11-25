# Time: a local big bang, a multiverse big bang, moving forward

Source: Addison, 2026-11-25 (`ontology/SOURCES.md`). Code: `time/check.py` (standard library, exact, git read-only). Programs: `time/time.ath`, `frames_time.ath`. Level: `time/level.json`.

Words: fact (cited with read status), checked-finite, checked-infinite (written reduction), tested, join, analogy (reading, never labelled checked), open.

Numbers below are from one run on 2026-11-25. Other jobs commit while this runs, so the counts grow. The structural checks do not depend on the counts.

## 1. Our local big bang: the repository's own history

- The history to HEAD has one root commit, `16a0185`. That is t = 0. Checked-finite.
- At writing: 1062 commits, 82 merges. Branches rejoin, so the history is a DAG, not a tree. Checked-finite.
- It is acyclic: a topological order covers every commit. Every commit reaches the root. Checked-finite.
- The alpha line is a longest root-to-HEAD path: 975 commits. 87 commits are off it. The first-parent line is shorter (862). Confirmed by edge relaxation: no edge makes any path longer. Checked-finite.
- Join: `DAG.lean` (rejoining histories; `lost_undone_iff_rejoin`, `rejoin_iff_not_clash`). A merge is a rejoin.
- Analogy (reading): Homestuck's alpha timeline is the alpha line; commits off it are the doomed branches (`homestuck/BASE.md` section 1). A doomed commit is not lost: a merge brings its work back. That differs from the comic.

## 2. A multiverse big bang: an initial object

- In a preorder of levels ordered by "can be transported into", an initial object is an element below every other. In a preorder the map is unique when it exists.
- A local origin propagates to the whole multiverse exactly when it is initial. That is the definition, read as a claim.
- Preorders on 1..4 elements: 1, 4, 29, 355. With a least element: 1, 3, 16, 145. The second formula sum_k C(n,k) * preorders(n-k) gives the same counts. Checked-finite.
- Uniqueness up to isomorphism, every n: if a and b are both least, then a <= b and b <= a. Checked-infinite (two-line reduction); exhaustive for n <= 4.
- The actual ontology: the 6 `*/level.json` files with arrow targets give 8 levels. Join arrows close to 14 pairs. There is no least element. Checked-finite.
- What would supply one: 5 new verified joins, from `homestuck` (to asteroid, carseat, cosmos, essays, time) or from `time` (to carseat, cosmos, essays, homestuck, metaphysics). `carseat` and `essays` have no incoming join at all, so any origin needs a join into each. Open.

## 3. Moving forward through time

- A time step is one round of checks on the centre. A forward step only adds passing checks.
- Monotonicity: a verified record never becomes unverified by a forward step. This is Fisher's `lost_mono` shape, inverted: there, lost stays lost along the order; here, settled stays settled.
- Checked-finite: all stores of 1..4 records, all start states, all orders of 0..4 steps (6558 cases). Checked-infinite by induction on steps: a forward step only sets records to verified.
- A failing re-check breaks it: {0: verified} goes to {0: unverified}. So monotonicity holds only for forward steps.
- Tested on the real history: every version of every `*/findings.jsonl` in git (44 versions at writing). Records removed: 0. Downgraded: 0. Superseded: 1 (`ontology/findings.jsonl`, commit `2b9f582`: the qual-quant record was rerun with new counts under a new id; same `serves`, same word). Confirmation lines (`id`, `by` only) are skipped. This is history, not a theorem.

## 4. Homestuck, Beauvoir, ~ATH

- Beauvoir (not re-read; `Beauvoir.lean`: `ambiguity`, `facticity_isChain`, `barbarian_iff_no_common_future`): freedom is exercised forward from a situation. Read: the accessible successors in an S4 frame. Reciprocity is symmetry. Fact: no poset on 1..4 worlds with an edge is symmetric (242 posets). Checked-finite; every n by the reduction in `time/level.json`. On S4 frames, B fails (countermodel printed by `frames_time.ath`). The Beauvoir link is analogy.
- ~ATH (facts in `ontology/SOURCES.md`, not re-read): a loop bound to a lifetime runs until a death. Asteroid's time step always halts because every claim has a size limit (`asteroid/SPEC.md`: Kripke N <= 12, N <= 4 for `all`, 2 000 000 pairs; finite claims 10^7 steps; 900 s per run). No check tests that asteroid halts. Open.
- Homestuck: the alpha line of section 1. Analogy.

## 5. Multiverse-level postmodernism, formally

- Definition. A claim is postmodern-safe for a class K of frames if it holds in every frame of K, at every world, under every valuation. For orderings, `cosmos/invariant.py`'s criterion: the same value in every ordering.
- Two classes are stated. S4 (reflexive, transitive): every branching history. S5 (an equivalence): no privileged world.
- Checked-finite on all 34 S4 and 8 S5 frames on 1..3 worlds:

| claim | formula | every branch (S4) | no privileged world (S5) |
|---|---|---|---|
| T | []p -> p | yes | yes |
| 4 | []p -> [][]p | yes | yes |
| B (reciprocity) | p -> []<>p | no | yes |
| 5 | <>p -> []<>p | no | yes |
| .2 (rejoining) | <>[]p -> []<>p | no | yes |
| D' | []<>T | yes | yes |
| no contradiction | ~(p & ~p) | yes | yes |

- The framework. A result crosses to the multiverse only if it is postmodern-safe for the class the multiverse is taken to be. T, 4, D' and non-contradiction cross under both. B, 5 and .2 cross only if no world is privileged; on a directed, branching history they fail.
- From `cosmos/invariant.py`: a property's frequency is ordering-independent at every cutoff iff the property is constant (n <= 7). So "n*n mod 4 is 0 or 1" crosses; evenness (1/2 vs 1/3) does not.
- The Lyotard link (incredulity toward metanarratives as "no privileged world") is analogy.

## 6. Qual-quant

Types and rules as in `ontology/QUALQUANT.md`, applied by `time/check.py` to `frames_time.ath`: structure 10 (10 with a claim), contested 1 (0 with a claim), effect 0. So 10 of 11 frames converted to checks. The open one is the ~ATH halting frame. Its reading names a finite object (the size limits), so by the hand rule of `ontology/QUALQUANT.md` it is structure whose check is not written; the code rules here call it contested because it ends in "reading".
