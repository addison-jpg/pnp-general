# Tractability guide for 951 agents (read before writing a helper)

This guide exists so that "consider a better approach" is the default and does not need a reminder. It describes
where shared code lives, what to check first, and how to refactor without breaking anyone.
Private repo only. Results go on the board first (branch `board`).

## 1. Before you write a lemma or a script

1. **Search the index.** Board `agents/kernel-index.md` lists every public Kernel/Base/W951 declaration, with
   signature and doc line. Regenerate it with `python3 tools/lean_index.py lean/PEqualNP Kernel Base W951`.
   If something with the shape you need exists, import it.
2. **Prefer a known theorem or a lateral move over a long case split.** Mathlib at the pinned rev has Hall and
   Hahn–Banach. It has no König, max-flow, Menger, LP duality or matroid union: we built what we needed (see section 2).
   Literature status is in `agents/tractability-lit.md` and `agents/tractability-nominCE.md`.
3. **For experiments, use `tools/w951` (Python).** Do not copy `bmatch`, `ev`, `cone` or the menu code into a new
   script. Copies have caused wrong results before (the spurious TWFAIL). Run its tests with
   `python3 -m pytest -q tools/w951/tests`.

## 2. Where shared code lives (layers; lower layers never import higher ones)

| Layer | What it is | Main entry points |
|---|---|---|
| `Base/Matching` | combinatorics, no circuits | `hasBMatching_iff` (Hall with capacities), `hasSimpleBMatching_iff` (each vertex uses an item at most once, i.e. max-flow/min-cut), `exists_frac_iff_prices` (LP duality), `load_le_one_of_injective`, `sum_card_le_of_pairwiseDisjoint`, `image_props_of_injective*` |
| `Kernel/Circuit` | well-scoped Dag: gate `i` reads `Fin (n+i)`, any arity, `KGate` = W951 op + input list | `val_natAdd`, `snocInduction`, `val_rel` (`agree_off`, `val_le_val`, `val_mono`), `sandwich`, `restrict`/`restrictGE`, `cone`, `orOf`/`ComputesOn` |
| `Kernel/GateShape` | arity/op case analysis, done once | `inputs_cases`, `and_or_shape`, `not_shape` |
| `Kernel/Privacy`, `Kernel/AndReplace` | Wegener §6.6 machinery | `supp`, `privacy_*`, `boolSum_and_split`, `card_biUnion_supp_le`; `sum_card_sub_one_le_andOr` = exact Nechiporuk for monotone circuits on `{x ≥ z}` |
| `Kernel/Minimal` | operations with exact gate counts | `keep` (delete + reindex), `restrictOutputs`, `restrictVar`, `card_simplify` |
| `Kernel/MultiBase` | the counting skeleton | `sum_card_sub_one_le_of_classes` (classes ⇒ bound), `sum_card_sub_one_le_gates_ownBase` (OR-only, base per output), `multiBase_without_compat_false` (counterexample) |
| `Kernel/W951*` | bridges from W951's `List Gate`/`val` | `ofList_valN` (no hypotheses), `listVal_rel_off`, `*_viaDag`, `nech_one_point`/`nech_zero_point`/`nech_interval`, `list_keep`, `list_restrictVar`, `restrictVar_bound_*` |
| `W951/*` | the 951 proof | the only `sorry` is `no_minCE` (MinCE.lean) |

New generic facts belong in the lowest layer that can state them. If a lemma mentions only Dag/KGate, put it in
Kernel. If it mentions `List Gate` but no MinCE, put it in a `Kernel/W951*` file.

## 3. Refactoring rules (all refactors so far followed these)

- **Statements stay identical.** Public names, types and def bodies do not change. If something moves, leave an
  alias. Check with a signature dump (name, type hash, def-value hash) before and after; only `_proof_*`/`match_*`
  names may differ.
- **One fact, one proof.** When two files prove the same thing, keep the more general proof and make the other
  name a short instance.
- **Branches.** One branch per step, based on the current `coord-951` head, and no force-pushes. Coord fast-forwards
  after checking.
- **Check before every push:**
  1. `lake build` of every `W951/*` and `Kernel/*` module and `PEqualNP`;
  2. `work/bin/merge951.sh` single file: 0 errors and exactly 1 sorry;
  3. `pytest tools/w951/tests` if Python changed.
  4. Keep `merge951.sh` FILES equal to the transitive imports of its listed modules in topological order. Regenerate
     it rather than hand-merge it.
- **Ownership.** Front owns `Dead/Lower/Core/Restrict/Absorb/Bottom`; coord owns
  `Main/Core-chain/Hard/Final/MinCE*/Lift*/PairLemma/Heredity`; tractability owns Kernel and Base. Ask the owner
  (one line on the board) before editing another owner's file.

## 4. Known traps

- A file named `Foo2`, `Foo3`... created to dodge heartbeats means an abstraction is missing. Add a kernel lemma
  instead.
- With AND gates, per-output cubes are too weak. The K_{2,2} counterexample is proved in `Kernel/MultiBase`.
- Pairwise compatibility of base points is the same as one common base point, so it adds no content.
- Sandwich/one-NOT bounds must use inputs of weight ≥ 2. The canonical 1-slice is cheap (Hiltgen–Paterson).
- A single-world Nechiporuk bound reaches only about half of base on the known instances, so the two worlds must be
  combined.

## 5. Open refactor map

Board `agents/tractability-audit.md` lists the remaining targets. The main one is the legacy HardCase chain in
`Main`/`Core`, which waits for coord.
