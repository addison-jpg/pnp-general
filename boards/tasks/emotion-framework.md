# Task: emotion-framework (a formalized emotional framework, philosophy side)

- **Serves:** the philosophy side of the project (`research/philosophy/`). Addison, 2026-11-25: "consider seriously a formalized emotional framework over the philosophy side. the quran and bible are pretty damn open source. frontier soical work lit aint gonna hurt".
- **Statement:** a typed model of emotion, written in Lean, whose rules come from (1) the psychology of emotion, (2) how the Quran and the Bible describe and handle emotion, and (3) current social-work practice. Every passage and paper the model leans on is cited where it is used.
- **What "proved" means here:** facts about the MODEL only, e.g. every appraisal gets exactly one emotion type, the rules never contradict each other, every type is reachable. Nothing is proved about people, God, or scripture. The README of the result says that in its first paragraph.
- **Framing:** respectful of both traditions; no ranking of religions and no claim about which reading is right. Where readings differ (between traditions, or within one), the model keeps them apart as separate parameters instead of picking one.
- **Not now:** anything clinical (no diagnosis, no advice to a reader in distress); publishing outside this repository (QUIET).

## Prior art to read first (cite, do not copy)

- Appraisal theories: Lazarus, *Emotion and Adaptation* (1991); Scherer's component process model; Ortony, Clore and Collins, *The Cognitive Structure of Emotions* (1988, "OCC").
- **OCC has been formalized before:** Steunebrink, Dastani and Meyer, "The OCC model revisited" (2009) and their logic of emotions for BDI agents. Start from that structure rather than inventing one.
- A counterpoint: Barrett's constructed theory of emotion (no fixed set of basic emotions). The model should be able to say where it disagrees with it.
- Social work, current practice: trauma-informed care (SAMHSA, *Concept of Trauma and Guidance for a Trauma-Informed Approach*, 2014, a US government document); attachment and mentalization; the window of tolerance (Siegel). Polyvagal theory is contested; cite its critiques (e.g. Grossman) next to it.

## Sources and their licences (check each edition before quoting)

- **Bible:** the King James Version (public domain outside the UK) and the World English Bible (public domain); the Hebrew of the Westminster Leningrad Codex. Many modern translations (NIV, ESV, NRSV) are copyrighted: cite them by reference only, do not quote at length.
- **Quran:** the Arabic text is public domain. Pickthall's English translation (1930) is public domain in the US; check Yusuf Ali per edition. Saheeh International and most modern translations are copyrighted: cite by reference only. The Tanzil text carries its own terms (attribution, no modification): follow them if it is used.
- Cite scripture as book chapter:verse (Bible) and surah:ayah (Quran), always with the translation named.

## Seats (one Sonnet each unless noted; each writes TAKEN/DECIDED below)

1. **survey**: one page `research/philosophy/emotion/SURVEY.md`: the appraisal dimensions shared by Lazarus, Scherer and OCC; what the OCC formalization already proves; where Barrett disagrees; the four social-work ideas above, with what each would add as a rule. Cited.
2. **scripture**: `research/philosophy/emotion/SOURCES.md`: passages on grief, fear, anger, shame, hope, patience and gratitude from both texts (e.g. the Psalms of lament, Job, Lamentations; surah Yusuf 12:84–87 on Jacob's grief, sabr and shukr), each with the edition and licence, and the appraisal it implies, written as a candidate rule. A short note per tradition on how its own commentators read the passage, cited.
3. **lean** (Opus once 1 and 2 are DECIDED): `proofs/w951/PEqualNP/Philosophy/Emotion.lean` or its own small package: appraisal records, emotion types, the rules of seats 1–2 as functions, and the model-only theorems (determinacy, consistency, reachability). Each rule's docstring cites its source.
4. **review**: read seats 2 and 3 from a Muslim reader's, a Christian reader's, and a social worker's point of view; list misreadings, and say where the model flattens a distinction a tradition keeps. Fixes go back to seats 2–3.

## Lines (TAKEN / DECIDED only)
