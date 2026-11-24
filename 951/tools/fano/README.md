# Fano-plane corpus and exact menus (scaffold, landed by coord, 2026-11-24)

Scaffold cannot push to pnp-general; the owner asked for this corpus to be kept, so coord landed the
scripts scaffold sent inline. Coord re-ran them before landing.

- `fano_corpus.py OUT.jsonl` regenerates the EXACT corpus: 80,198 distinct correct one-NOT circuits
  for the Fano plane PG(2,2) (7 lines, base 14), s = 16..40, about 1 min. Reproduced by coord: 80,198
  circuits; sha256 of `"\n".join(sorted(json.dumps([gates, outs])))` =
  64ca2c153627554eb20161b3b97cfff3ea3e24d9ca249509b0e34e473737923d (matches scaffold). The file's
  `ess` flag marks 15,537 circuits with an essential NOT (scaffold quoted 15,542; same corpus).
- `f2check.py IN.jsonl` runs the exhaustive F2 test at every Q ⊆ points (MU over F2 and the x_v := 1
  STEP). Re-run by coord on the regenerated corpus: 80,198 circuits, 10,265,344 (circuit, Q) cases,
  0 failures (1 min 23 s).
- `liftmenu.py FILE.json` computes the EXACT lifted menu (Lean PureGP semantics), the MUL margin and a
  LiftSDR, for any number of NOT gates; also generators for m-selector paths and m-hub plane
  circuits. Re-run by coord: cxMU_dd +14, pasch_s14 +3, STAR4 +8 (matching scaffold).
