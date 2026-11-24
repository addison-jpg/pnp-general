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

## SAT Fano circuits (scaffold; landed by coord at the owner's "quick push, then pause")

`one-not/data/fano_sat66.json`: 66 correct one-NOT Fano-plane circuits found by SAT near base (42 at s = 17
with an inessential NOT, 24 essential: 10 at s = 18, 14 at s = 19; base 14). Verified by coord:
SHA-256 of the file (minified, no trailing newline) = 330c86ca7659c9b8fcec6b7a5420f0184840c5c75b6b2fb180bfa20ceead0811
(matches scaffold), 66/66 correct, 24 essential, F2 MU + STEP 0 failures at all 128 Q (f2check.py).
The ladder corpora (pg13 3.1 MB, ag16) are not exactly regenerable (time-budgeted generator); the 12
ladder certificates are in one-not/tools/sdrcert/ladder_instances.json.
