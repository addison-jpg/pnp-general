# scaffold: stress data (Nov 23-24), all SAT-generated correct circuits, NOT in an output cone
- cone-D target, raw: ~390k circuits, 0 violations, min slack 1. Gap-G (front gapg, unchanged): ~800k raw circuits, ~495 BAD,
  0 without a disjoint choice. Two-World (twoworld2): smoke 3/3; coord's K4 forced-h run 7,200/7,200 closed.
- Canonical Hall (hallcheck): 14,889 essential/BAD circuits OK, mostly graphs; REFUTED later by front's cx1-3 (triples, ~base+12).
- K4 with h forced to (x0|x1)(x2|x3)|x2x3, essential forced by SAT (predicted Gap-G obstruction): 0 BAD in 7,200+, never exercised.
- Refuted statements with re-checking script: scaffold-951 research/tools/l951_charging/agents/counterexamples951.py (full-D ChargeOK, DC,
  'no gate charged twice', Lemma R, per-read substitution).
Drivers: scaffold-951 work/notes951/scripts/scaffold_runs/ (drive, needsB, gen_ess, gen_fixh, gen_tri).
