# Ladder report

## pg13 (v=13)

- #circuits (distinct, essential, verified): 2159  (embed: 796, climb: 1363)
- slack distribution: {"4": 264, "5": 1409, "6": 435, "7": 50, "8": 1}
- kstar_max histogram: {"0": 390, "1": 1769}; overall max = 1
- k* state histogram (aggregate over sampled states): {"1": 3319}
- Lavoid_min_options: {"1": 2159}; min = 1
- MergeSDR held on all: True (False count: 0)
- h-minterm size patterns (sorted sizes of minimal true points of the NOT input) -> count: {"(1,)": 1432, "(1, 1)": 702, "(1, 1, 1)": 15, "(1, 2)": 6, "(1, 1, 2)": 3, "(1, 2, 2)": 1} (6 distinct patterns)
- **heavy_CLASS_all False: 0; heavy_MERGE_all False: 0; both: 0; only CLASS: 0; only MERGE: 0** (None/cap-hit entries: 0)
- heavy point counts: {"1": 1439, "2": 705, "3": 15}
- **pure_SDR False: 0; pure_D_viol > 0: 0**; pure_SDR True count: 2159/2159
- pure_min_I0 distribution: {"0": 1978, "1": 178, "2": 3}
- pure_topZ_only_possible_any: {"False": 2159}
- pure_typeA_in_I1_minSDR: {"1": 1914, "0": 171, "2": 74}
- pure_D_viol distribution: {"0": 2159}
- kstar_max >= 3 or 99 (None): 0

## ag16 (v=16)

- #circuits (distinct, essential, verified): 65  (embed: 23, climb: 42)
- slack distribution: {"4": 7, "5": 54, "6": 4}
- kstar_max histogram: {"0": 9, "1": 56}; overall max = 1
- k* state histogram (aggregate over sampled states): {"1": 85}
- Lavoid_min_options: {"1": 65}; min = 1
- MergeSDR held on all: True (False count: 0)
- h-minterm size patterns (sorted sizes of minimal true points of the NOT input) -> count: {"(1,)": 54, "(1, 1)": 11} (2 distinct patterns)
- **heavy_CLASS_all False: 0; heavy_MERGE_all False: 0; both: 0; only CLASS: 0; only MERGE: 0** (None/cap-hit entries: 0)
- heavy point counts: {"1": 54, "2": 11}
- **pure_SDR False: 0; pure_D_viol > 0: 0**; pure_SDR True count: 65/65
- pure_min_I0 distribution: {"0": 64, "1": 1}
- pure_topZ_only_possible_any: {"False": 65}
- pure_typeA_in_I1_minSDR: {"1": 60, "2": 1, "0": 4}
- pure_D_viol distribution: {"0": 65}
- kstar_max >= 3 or 99 (None): 0
