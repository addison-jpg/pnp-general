# tools/w951 — one Python toolkit for the L-meta-951 experiments

Boolean sums `S_w ⊆ [n]` (`|S_w| ≥ 2`, pairwise `|S∩S'| ≤ 1`), circuits of fan-in-2 AND/OR gates with one NOT.
The front / scaffold / tractability scripts each carry their own copy of the evaluator, the cone walk, the
checks, the test systems, the matcher and the LP. This package holds each of them once.

```python
import sys; sys.path.insert(0, 'tools')          # from the repo root
from w951 import Circuit, load, systems, lp, rules, matching
c = load('cx1.json')[0]                           # or Circuit.from_dict(json_dict)
c.verify()                                        # {'correct':…, 'C0':…, 'C1':…, 'clean':…, 'read':…, 's':…, 'base':…}
M = systems.menus(c)                              # all Lean test systems, maximal counted sets
L, lam, M = lp.fraclp(c)                          # FracMatch holds iff L <= 1
L_rel, pi, F = rules.rel_rule(c, WT=2)            # relative-sandwich rule
r = c.restrict(0, 0)                              # r.circuit, r.removed, r.detail, r.wire_map
```

Needs: Python 3.8+; `scipy` for `lp` / `rules`; `python-sat` for `sat`. `circuit`, `systems`, `matching` are pure Python.

Tests: `python3 tools/w951/tests/test_w951.py` (or `pytest tools/w951/tests`), about 80 s.

## Conventions

- **Circuit JSON**: `{"n":…, "sets":[[…]], "gates":[["or",a,b],["and",a,b],["not",a]], "outs":[…]}`; wires `0..n-1` are
  inputs, gate `k` is wire `n+k`. The SAT tools write NOT as `("not", a, a)`; `Circuit` reads both, stores `("not", a)`,
  and `to_dict(not_arity=3)` / `triples()` give the 3-field form back.
- **Points are ints**: bit `i` is `x_i`; `e_u = 1 << u`, `z_Q = z_of(n, Q)`. `Circuit.eval` also takes a 0/1 list.
- **Truth tables are ints** over the `2^n` points (bit `r` = value at point `r`). The scripts that tabulate with
  `itertools.product` have `x_0` as the most significant bit; `table_in_product_order(w)` / `product_index(n, pt)` convert.
- Every function takes a `Circuit` or the JSON dict. `Circuit` also answers `c['n']`, `c['gates']`, `c['sets']`, `c['outs']`.
- Transformations never mutate; they return `Reduced(circuit, wire_map, removed, detail)`.

## API

### `circuit.py`
| | |
|---|---|
| `Circuit(n, gates, sets, outs)`, `Circuit.from_dict(d)`, `.to_dict(not_arity=2)`, `.triples()` | construction, JSON |
| `load(path)`, `save(c, path)` | `.json` (one) / `.jsonl` (one per line; `{'c': …}` wrappers accepted) |
| `.s`, `.W`, `.base`, `.demands`, `.nots`, `.not_wire`, `.h_wire`, `.gate_wires` | sizes, the NOT gate and its input `h` |
| `.eval(x, force=None)` | all wire values at one point; `force=0/1` is the circuit `C0` / `C1` |
| `.tables(force=None)`, `.table(w)`, `.value(w, pt)`, `.point_mask(pt)`, `.or_table(S)`, `.cube_table(z)` | bitmask truth tables (cached) |
| `.cone(o)`, `.cones()`, `.downstream(w=NOT)`, `.readers()`, `.unread()`, `.live(outs)` | structure |
| `.is_correct(force=None)`, `.is_essential()`, `.is_clean(constants=True)`, `.all_read()`, `.not_is_live()` | checks |
| `.verify()` | the dict of `w8/verify.py` |
| `.verify_full()` | the dict of `w9/fc/lib.py` `verify` (adds `h0`, `hard`, `nset`, `hardN`, `DD`) |
| `.validate(sums=True, one_not=None)` | well-formedness, Boolean-sum conditions |
| `.restrict(v, b, semantic=True)` | `x_v := b`, merge + dead-gate removal, accounting (below) |
| `.propagate(assign, keep=None)` | syntactic constant propagation for any wires (e.g. `{v: 1, NOT: 0}`), keeps the cones of outputs `keep` |
| `.delete_outputs(F)` | drop the outputs in `F`, keep only the cones of the rest |
| `.remove_dead()`, `.cleanup()`, `.drop_gate(k, j)` | dead gates; merge duplicate tables + dead; Lean's `dropGate` |

`restrict(v, b)`: input `v` stays as an unused input (wire numbers do not move). For `b = 0` every set loses `v`;
for `b = 1` the sets through `v` are dropped. `semantic=True` identifies a gate with a constant, an input or the
first earlier gate that agrees with it on the subcube `x_v = b`, then removes dead gates; the new gate count is
the `restr(c, v, b)` of `w9/fe/kill.py`. `detail` has disjoint lists `const`, `merged`, `dead` (old gate wires) whose
lengths sum to `removed`, plus `sets` (surviving set indices) and `through` (number of sets containing `v`).
`semantic=False` is constant propagation only. The semantic count is usually but not always the smaller one: it keeps
the first gate of each function, which can have a larger cone than a later copy.

### `systems.py`
| | |
|---|---|
| `counted(c, S, z, atoms, K=None)` | the definition: `g ∈ K`, `g(z) = 0`, `g(atom_u) = 1` for ≥ 2 `u ∈ S` |
| `cnt_z(c, S, z, K=None)`, `cnt_unit(c, S, z, K=None)` | atoms `z + e_u` / atoms `e_u` |
| `rstar(c)` | rule R*: `z_S`, atoms `z + e_u`, all gates |
| `good_zero_sets(c, w, good)` | Good `Q ⊇ S_w` in script order; `good` ∈ `strict`, `du`, `cone_du`, `cone_strict` |
| `canon(c)`, `canon_Q(c)`, `worlds(c)` | canonical system (first Good `Q`, unit atoms, cone); `(canon, rstar)` |
| `chargeok(c)`, `conedbl(c)`, `lean_slack(c)` | min-`|D|` over Good `Q` in the three variants the scripts use |
| `menus(c, coneonly=False)` | all Lean test systems `(z, fat atoms, K)`: maximal counted sets with witnesses |
| `menu_sets(c)`, `menu_witnesses(c)` | menus as sorted lists; with `(z, h(z))` |
| `priv(c, M=None)` | rule PRIV deficits |
| `nsets(c)`, `good_Qs(c, permissive)`, `family(c, permissive)` | hard N-sets, minimal Good `Q`, Theorem-X families |
| `gapg_systems(c, w)`, `gapg(c, allow_B=True)` | type A(Q)/B systems, disjoint choice |
| `system(c, S, z, atoms)`, `merges(c, S, B)` | fable-A frame + union-find merge run |
| `maxviol(c)` | `max_F P(F) − d(F)` via `delete_outputs` |

### `matching.py`
Verbatim copy of `tools/matching/matching.py` (branch `tractability`, commit f6ccd76): `bmatch`, `simple_bmatch`,
`max_matched`, `frac_feasible_half`, `hall_check`. See that file's docstring.

### `lp.py`
| | |
|---|---|
| `min_max_load(M, dem, cap=None, fixed=None, free=None)` → `LoadLP(L, lam, pi, mu, load, status)` | the FracMatch LP with duals |
| `fraclp(c, coneonly=False, M=None)` → `(L*, lam, M)` | on the full menus of `c` |
| `fixed_load(Dlist, lams, dem)` | fixed-weight mixing LP |
| `Dual(M, dem)` with `.solve()`, `.flat(L)`, `.sparse(L, rng)`; `lpdual(M, dem)` | explicit dual LP, tie-breaks among optimal prices |
| `resid_lp(Mr, dem)`, `cheap(pi, C, d)`, `ratio(pi, M, dem)` | residual LP, price helpers |

### `rules.py`
| | |
|---|---|
| `private(c)` → `(Dc, Pc)` | dedicated-below / private-above classes |
| `sandwich_classes(c)` → `[(L_w, U_w)]` | fable A's sandwich classes |
| `relmenu(c, WT=2, above=False)`, `rel_rule(c, WT=2, above=False)` → `(L_rel, pi, F)` | relative-sandwich rule (`work/duals/relrule.py` semantics) |
| `relmenus_minimal(c)`, `rel_classes(c, maxw=2)` | front's two earlier variants of the same rule |
| `roles(c)`, `xrule(c)`, `residual(c)` | gate roles, X-rule, residual LP analysis |
| `mix(c, a=0.5)` | coin rule canonical / R* |
| `hall(Ds, dem)`, `two_world(c)`, `union_hall(c, Dc, Dr)` | the matching checks, on `matching.py` |

### `sat.py`
`build(n, sets, s, p, blocks=(), live=False, clean=False)`, `build_channel(...)` (same arguments and return value), `decode`, `decode_circuit`, `block`, `enumerate_circuits(..., encoding='quadratic'|'channel')`.

`build_channel` is the linear channel encoding of scaffold's `scaffold_runs/chan_sat.py`: per gate and truth-table row one value variable per gate input (selector -> value equality), so O(wires) clauses per gate and row instead of `build`'s O(wires^2 * 8) (about 6.8x fewer clauses at n=6, s=10). Gates read A <= B, so exact size s also covers every size <= s (padding `op(w, w)`). Its clause list starts with exactly the clauses of `chan_sat.py` (same numbering); `live=` / `clean=` work as in `build`.

## Old script function → new function

Paths: **F** = branch `front-match`, **S** = `scaffold-951`, **T** = `tractability`; `N/` = `work/notes951/`.
Line numbers are those of the copies in `tests/legacy/`.

| old | new |
|---|---|
| F `N/scripts/w8/verify.py:2` `evalN`; F `N/scripts/chargeok_check.py:6` `evaluate`; F `N/scripts/w8b/rstar.py:4`, `N/w9/fa/lib.py:7`, `N/w9/fc/lib.py:5`, `N/w9/tw/tw.py:5`, `N/w9/fb/top2.py:6`, `N/scripts/gen_clean.py:10` `ev`; S `N/scripts/scaffold_runs/climbrel.py:12` (and `climb.py`, `climb2.py`) `ev`; F `tools/l951_charging/ov951.py:58` `wires`; S `N/scripts/payment/payer.py:7` `evalc` | `Circuit.eval(x, force)` |
| F `N/w9/fa/sand.py:6` `tts`; T `work/duals/relrule.py:10-13` and `climbr.py:8-16` (`X`, `w` arrays) | `Circuit.tables(force)` |
| T `work/duals/resid.py:7`, F `N/w9/fc/relrule.py:6`, F `N/w9/tw/clean.py:4` `tables`; S `N/scripts/payment/ana.py:5` `table`; F `N/w9/fe/rel.py:5` `tt` | `Circuit.tables()` + `.value(w, pt)` / `.table_in_product_order(w)` |
| F `N/scripts/chargeok_check.py:15`, `N/w9/fc/lib.py:12`, `N/w9/tw/tw.py:12`, `N/w9/fb/irr.py:3`, `N/scripts/w8/allsys.py:10`; T `work/duals/dualp.py:109`; S `N/scripts/payment/ana.py:14`, `N/scripts/scaffold_opus/gen.py:12` `cone` | `Circuit.cone(o)` |
| F `N/w9/fa/sig.py:6` `down`; `down=` in F `allsys.py:7-9`, T `dualp.py:106-108` | `Circuit.downstream()` |
| F `N/w9/fa/lib.py:14-15` `nw`, `hw` | `Circuit.not_wire`, `.h_wire` |
| F `N/scripts/conedbl.py:5`, `N/w9/fa/lib.py:2`, `N/w9/tw/tw.py:20` `norm`; F `N/w9/fa/lib.py:4`, `N/w9/tw/tw.py:68` `load` | `Circuit.from_dict`, `load` |
| F `N/scripts/w8/verify.py:9` `verify` | `Circuit.verify()` |
| F `N/w9/fc/lib.py:19` `verify` | `Circuit.verify_full()` |
| F `N/w9/fa/lib.py:16` `verify` → `(ok, c0w, c1w)` | `(c.is_correct(), not c.is_correct(0), not c.is_correct(1))` |
| S `N/scripts/scaffold_opus/gen.py:19` `essential`; F `N/scripts/gen_clean.py:42` `okN` | `Circuit.is_essential()`, `.is_correct(force)` |
| T `work/duals/climbr.py:7` `tt_ok` (also `climbx.py`) | `c.is_correct() and c.is_clean() and c.is_essential() and c.all_read()` |
| S `N/scripts/scaffold_runs/climbrel.py:19` `ok` (also `climb.py`, `climb2.py`) | `c.is_correct() and c.is_essential() and c.not_is_live()` |
| F `N/w9/fe/kill.py:5` `restr(c, v, b)` | `c.restrict(v, b).circuit.s` |
| F `tools/l951_charging/agents/restr951.py:5` `restrict_count(n, gates, outs, p, Mset, keep)` | `c.propagate({**{v: 1 for v in Mset}, c.not_wire: 0}, keep).circuit.s` |
| F `N/w9/fb/cfgI.py:14` `prune` | `c.remove_dead().circuit` |
| F `N/w9/tw/clean.py:7` `cleanup` | `c.cleanup().circuit` |
| F `N/w9/fb/irr.py:10` `maxviol` | `systems.maxviol(c)` (`c.delete_outputs(F).removed` is `P(F)`) |
| `dropGate` / `redir`, `lean/PEqualNP/W951/Cleanup.lean:11,69` | `c.drop_gate(k, j)` |
| F `N/scripts/w8b/rstar.py:11` `cnt_z`; F `N/w9/fb/top2.py:13` `cntz`; F `N/w9/tw/tw.py:22` `cnt` | `systems.cnt_z` / `systems.cnt_unit` |
| F `N/scripts/w8b/rstar.py:17` `rstar` | `systems.rstar` |
| F `N/scripts/hallcheck.py:6` `canon`; F `N/w9/tw/tw.py:28,42` `canonQ`, `worlds` | `systems.canon`, `canon_Q`, `worlds` |
| F `N/scripts/chargeok_check.py:24` `check` | `systems.chargeok` |
| F `N/scripts/conedbl.py:7` `analyse` | `systems.conedbl` |
| F `N/scripts/gen_clean.py:15` `slack(n, sets, gates)` | `systems.lean_slack(c)` |
| F `N/scripts/w8/allsys.py:4` `menus` | `systems.menus` |
| T `work/duals/dualp.py:10` `get_menus`; T `work/duals/resid.py:23` `full` | `systems.menu_sets`, `systems.menu_witnesses` |
| F `N/w9/fc/priv.py:6` `priv` | `systems.priv` |
| F `N/scripts/nsets.py:6` `analyse` | `systems.nsets` |
| F `N/scripts/gapg_check.py:5,37` `systems`, `gapg`; S `N/scripts/scaffold_runs/needsB.py:6` `choice` | `systems.gapg_systems`, `systems.gapg(c, allow_B)` |
| F `N/w9/fc/lib.py:44,62` `goodQs`, `family` | `systems.good_Qs`, `systems.family` |
| F `N/w9/fa/lib.py:26,33` `system`, `merges` | `systems.system`, `systems.merges` |
| F `N/scripts/hallcheck.py:24`, `N/scripts/w8/allsys.py:49`, `N/scripts/w8b/rstar.py:19` `bmatch(Ds, demand)` | `rules.hall(Ds, dem)` = `matching.max_matched` |
| F `N/w9/tw/tw.py:48,60,64` `bmatch(Ds, demand, cap)`, `twoworld`, `unionhall` | `matching.max_matched(T, d, cap, simple=True)`, `rules.two_world`, `rules.union_hall` |
| F `N/w9/fraclp.py:10` `fraclp` | `lp.fraclp` |
| F `N/w9/fb/dual.py:9` `lp(M, dem, cap, fixed)` → `(L, pi, mu, lam, load)` | `lp.min_max_load(M, dem, cap, fixed)` → fields `L, pi, mu, lam, load` |
| T `work/duals/resid.py:62` `resid_lp`; `:30` `lpdual`; `:36` `run` | `lp.resid_lp`, `lp.lpdual`, `rules.residual` |
| F `N/w9/mixrule.py:14,42` `fixedlp`, `mix` | `lp.fixed_load`, `rules.mix` |
| T `work/duals/dualp.py:16,17,19` `cheap`, `ratio`, `Dual`; F `N/w9/fb/dual.py:53` `cheap` | `lp.cheap`, `lp.ratio`, `lp.Dual` |
| T `work/duals/dualp.py:103` `roles` | `rules.roles` |
| T `work/duals/resid.py:13` `private` | `rules.private` |
| F `N/w9/fa/sand.py:19` `classes` | `rules.sandwich_classes` |
| T `work/duals/relrule.py:8,35` `relmenu`, `run` | `rules.relmenu`, `rules.rel_rule` |
| F `N/w9/fc/relrule.py:8` `relmenus` | `rules.relmenus_minimal` |
| F `N/w9/fe/rel.py:8` `analyse` (its `cls`) | `rules.rel_classes` |
| T `work/duals/xrule.py:6` `xrule` | `rules.xrule` |
| F `tools/l951_charging/ov951.py:4,50` `build`, `decode`; `live951.py:9` `build_live`; `clean951_scaffold.py:10` `build_clean` | `sat.build(…, live=, clean=)`, `sat.decode` |
| S `N/scripts/scaffold_runs/chan_sat.py:23` `build(p)` (script-level, linear channel encoding) | `sat.build_channel(n, sets, s, p)` |

### How many copies each one replaces
Counted over the three branches (a file that is on two branches counts once); files that carry their own
implementation of the thing, found by pattern, so the numbers are approximate.

| new | files with their own copy |
|---|---|
| `Circuit.eval` | 24 |
| `Circuit.tables` | 14 |
| `Circuit.cone` | 15 |
| `Circuit.downstream` | 4 |
| correctness / C0 / C1 / essential / clean checks | 19 |
| `Circuit.from_dict` / `load` (the `norm`, `del g[2:]` and json/jsonl idioms) | 21 |
| Good-`Q` canonical / min-`D` loops (`good_zero_sets`) | 10 |
| `cnt_z` / `rstar` | 4 |
| `matching` (augmenting-path `bmatch`) | 4 |
| `lp.min_max_load` / `fixed_load` | 4 |
| `restrict` / `propagate` / `remove_dead` / `cleanup` | 4 |
| `sat.build` / `sat.build_channel` | 3 (`ov951`, `live951`, `clean951_scaffold`) / 1 (`chan_sat`); 15 other files have encodings of their own, not ported |

## Tests

`tests/test_w951.py` runs every function above next to the original implementation and asserts equal results.
- `tests/legacy/<branch>/<original path>`: 38 verbatim copies of the original scripts. `tests/legacy_loader.py` imports
  them; scripts that do work at import time are cut at a marker and only their `def`s run.
- `tests/instances/`: the 26 instance JSONs found on the branches (cx1–3, cxr, cfgI ×2, cx44_0/1, cxT2, cxT4, cxe3,
  cxtw3/3c/4/4c from F; j_cx1, r_cx1, r_v1, v1, ce1–3 from S; relfail1, reltight1, relworst_a, xfail1 from T).
  No `.jsonl` dumps are committed on any of the three branches.
- Random: 150 arbitrary one-NOT circuits (for the syntactic definitions), 120 correct ones (OR trees with NOT
  identities spliced in), 40 climb mutants of cx1 / cx2 that stay correct, essential, clean and fully read.
- Compared exactly: wire values, truth tables, cones, `verify` dicts, restricted gate counts, canonical and R* counted
  sets, menus including their order and witnesses, Gap-G systems, families, private and sandwich classes, relative
  menus, X-rule records, SAT clause lists. LP outputs (`L*`, `lam`, `pi`, `mu`, loads, `L_rel`, mix values) are compared
  with tolerance 1e-9; the observed difference in `L*` is 0.
- Property tests: a restricted circuit agrees with the original on the subcube for every surviving wire, and no two
  of its wires agree there; the accounting adds up; `delete_outputs` keeps the remaining outputs' functions and
  removes exactly the gates outside their cones; `drop_gate` keeps all functions; I/O round trips;
  `two_world` agrees with brute-force Hall and `frac_feasible_half`; strong duality `Dual.solve` = `min_max_load`.
- cxT4 (`n = 15`) runs the full menu, `fraclp`, `rel_rule`, `verify`, canon, R*; the other legacy comparisons are
  limited to `n ≤ 11` because the originals enumerate `2^n` points in pure Python.

Three places where the originals crash and the new code does not (the tests skip the comparison there):
`conedbl.analyse` / `gen_clean.slack` when a set has no Good `Q`; `clean.cleanup` when a duplicate gate's original is
itself unread (`KeyError`); `fraclp` when the LP is infeasible (`min_max_load` returns `L = None`).

## Not ported
- `dualp.best01` (its README calls the MILP buggy), `dualp.analyse` / `show`, the printing `__main__` blocks.
- The payment scripts (`payment/ana.check`, `payer.py`), `fc/pool.py` `mergesets`, `fb/top2.py` `top2`, `fa/sig.py`
  `sig`, `fe/rel.py` `check`, `scaffold_opus/rules.py` `rule_systems` / `lean_excess` (expressible as
  `counted` + `good_zero_sets(…, 'cone_strict')`, not tested against the original).
- The climb drivers and the other SAT encodings (`sat951.py`, `satpool*.py`, `sat2*.py`, `rgen*.py`, `cxtw.py`, …).

## Migration note for front / scaffold

1. Put `tools/` on `sys.path` and replace the local helpers by the imports in the table. The scripts' `sys.path`
   juggling between `chk/`, `w8/`, `w8b/`, `w9/` and the `exec(open('…ov951.py').read().split(…))` loaders go away.
2. Functions accept the JSON dict unchanged, so a script can migrate one call at a time. Returned shapes are the
   old ones for `verify`, `menus`, `canon`, `rstar`, `fraclp`, `mix`, `relmenu`, `private`, `roles`, `xrule`, `gapg`,
   `nsets`, `chargeok`, `conedbl`. Differences:
   - points are ints where a script passed 0/1 lists to `cnt_z`-style helpers (`Circuit.eval` and `systems.system`
     take either);
   - `rules.rel_rule` returns what `relrule.run(c, verbose=False)` returned and prints nothing;
   - `rules.rel_classes` returns only the `cls` dict of `rel.analyse`;
   - `lp.min_max_load` returns a named tuple; `fb/dual.lp`'s order was `(L, pi, mu, lam, load)`;
   - `Circuit.restrict` returns the restricted circuit; the old `restr` count is `.circuit.s`.
3. `systems.menus` reproduces `allsys.menus` in the same enumeration order, so saved witnesses `(z, atoms)` and
   `lam` keys `(w, j)` from earlier runs still refer to the same menu items.
4. The pickle cache of `dualp.get_menus` (`work/duals/out/menu_*.pkl`) is not used; `menus` is 3–10× faster than
   the original (cxtw4: 1.1 s → 0.2 s) and caches nothing on disk.
5. `matching.py` here is a copy; when `tools/matching/` from `tractability` lands on the same branch, make this file
   `from matching import *` or delete one of the two.
