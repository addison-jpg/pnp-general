Serves the asteroid language (task asteroid-bridge)

# fable-asteroid-sound: what asteroid's kernel checks say about the project's circuits

Files: `one-not/lean/PEqualNP/W951/AsteroidSound.lean` (layers 1 to 3), `AsteroidSound2.lean` (layer 4).
Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound`. Build: `lake build PEqualNP.W951.AsteroidSound2`.

## Proof structure

Layer 1 (tables are pointwise).
- `foldr_bits_testBit`: the fold `acc <<< 1 ||| bit` over a list puts element `k` at bit `k`. So `varTT_testBit`.
- `tt_eq`: the `Array` fold of `tt` is a `List` fold with step `ttStep`.
- `foldl_ttStep_map`: invariant `tables.map (testBit r) = wires`, one gate at a time (`ttStep_testBit`:
  AND/OR by `Nat.testBit_and/or`; NOT is `xor full`, and bit `r` of `full = 2^(2^n) − 1` is 1 for `r < 2^n`).
- Result `tables_map_testBit`, `tables_testBit`.

Layer 2. `correctB_sound`: take bit `r` of both sides of the table equation; `foldl_lor_testBit` turns the
fold of `lor` into `List.any`. A point `u ≥ n` reads `false` on both sides (`ins_getD_testBit`), so no
hypothesis on the sets.

Layer 3. `gateVal_eq_eval` (gate by gate, `GateOp.eval` on `[a, b]` or `[a]`), `wiresFrom_eq_wires` (any
start list), `ofFn_eq_range_testBit` (the input `x` is the row `Nat.ofBits x`), so `wiresAt_eq_wires`.
Headline `correctB_sound_project`; hypothesis `sets.length ≤ outs.length` because `zip` drops the sets
without an output wire.

Layer 4. Rows and inputs: `rowOf n r`, `ofBits_rowOf`, `rowOf_ofBits`, `rowOf_or` (`r ||| 2^u` is
`Function.update Z u true`), `table_val` (table bit = `val C.toGates`).
- `hasWitnessAt_iff_F2Wit`: both directions, by `alive_iff` (mask avoids the set ⇔ `Disjoint`),
  `exists_two_of_filter` (needs `Nodup`) and `two_le_filter`.
- `orWitnessAt_eq`: the zip of tables and gates is a map over gate numbers; `isOrAt_toGates`.
- `card_F2_eq_orWitnessAt`: `F2` is the image under `k ↦ n + k` of the gate numbers counted by asteroid.
- `baseAt_eq_baseDQ` (`card_setFin`), `slackNonnegAll_sound`, `slackGe_sound`, `MUF2_of_slackGe`,
  `base_le_gates_of_slackGe`.

## Exact differences from the project's statements

- `correctB_sound_project` is the correctness hypothesis of `L_meta_951` (Final.lean) instantiated at
  `n := C.n`, `m := C.sets.length`, `S := C.setFin`, `gates := C.toGates`, `out := fun w => C.outs.getD w 0`.
  Same expression; the only reading needed is `out w = C.outs.getD w 0`.
- Layer 4 needs `Circ.SetsOk` (sets without repetition, points `< n`). Without it the counts can differ:
  a repeated point counts twice in `(S.filter …).length ≥ 2` where `F2Wit` wants `u ≠ u'`; a point `u ≥ n`
  reads bit `r ||| 2^u ≥ 2^n` of a table, where a NOT gate leaves ones.
- A cube is `maskOf Q` for `Q : Finset (Fin n)`; every `q < 2^n` is one (not stated as a theorem).

## Not done

- `witnessCount` / `hasWitness` (gates of any type): no project definition to match (`F2` is OR gates only).
- `asteroid.py` does not write these corollaries into the generated modules.
- The mixed slack of `AsteroidMixed.lean` (another seat) is not covered.
