Folder summary: [`../../README.md`](../../README.md).

## SAT Fano circuits (scaffold; landed by coord at the owner's "quick push, then pause")

`951/data/fano_sat66.json`: 66 correct one-NOT Fano-plane circuits found by SAT near base (42 at s = 17
with an inessential NOT, 24 essential: 10 at s = 18, 14 at s = 19; base 14). Verified by coord:
SHA-256 of the file (minified, no trailing newline) = 330c86ca7659c9b8fcec6b7a5420f0184840c5c75b6b2fb180bfa20ceead0811
(matches scaffold), 66/66 correct, 24 essential, F2 MU + STEP 0 failures at all 128 Q (f2check.py).
The ladder corpora (pg13 3.1 MB, ag16) are not exactly regenerable (time-budgeted generator); the 12
ladder certificates are in 951/tools/sdrcert/ladder_instances.json.
