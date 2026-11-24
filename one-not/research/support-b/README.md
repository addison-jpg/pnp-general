# front612: no_minCE numerics (support-B), Config (I) prices, MergeFrac world analysis

Moved 1:1 from pequalnp-work mirror/laughing-mccarthy-ifdzly (session front-612, merged into the 951 front seat).
Everything here is Python/LP data unless a file says Lean. Corpora are not copied: harness.py expects
supportB/corpora/ (data-fixh16, front-match w9/*.json, and pequalnp-work branch data-corpora 2aa9856).
W951 tools: harness.py imports tools/w951 from a coord-951 checkout (env W951_TOOLS).

- supportB/: harness (merge-tree profile + rule slot), baseline B1/B2, MergeFrac LP on 163 circuits (L* <= 1, 0/1 duals),
  dual supports + world choice on the 14 adversarial circuits, heavy split v2 / R4 menus.
- cfgI/: Config (I) price vertices, world-restricted contradiction (L = 2 when both 4-sets are h = 0),
  FracMatch 7/20, hill-climb (no MergeFrac L* > 1), witness JSON, and CfgIWorld0.lean:
  Lean-checked (core only, decide +kernel, axioms propext/Classical.choice/Quot.sound) world-0 and MergeFrac
  dual certificates. Its `merges` is its own definition (differs from W951 mergeSet on gates seeing >= 3 blocks):
  research evidence, not a 951 row.
- fable_worlds.md: proof attempt (MergeSDR conjecture, cut sandwich, chain-pair, pair theorem / O2, ADV3, ADV4,
  O2-PAIR, tests F1-F5). CORRECTION (09:25, verified with w951 is_correct(0/1) and is_essential()): ADV3 and ADV4 ARE
  essential (C0 and C1 both wrong). The entries in (b5) that said 'NOT essential' were wrong; the header was right.
  An earlier front612 message called them not essential: that was wrong too.
