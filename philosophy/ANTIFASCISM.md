# Anti-fascism, baked into the philosophy frameworks

Code: `philosophy/antifascism.py`. Frames: `frames_antifascism.ath`. Source line: `ontology/SOURCES.md` (Addison, 2026-11-25).

Words used here. **fact**: cited, with read status. **checked-finite**: exhaustive on stated small sizes. **tested**: measured, with a stated false-positive rate. **analogy**: a reading, never labelled checked. **open**: no claim yet.

## 1. Framework

- Umberto Eco, "Ur-Fascism" (1995; Italian original "Il fascismo eterno"). Not re-read. Feature names, in our words: cult of tradition; rejection of modernity; action for its own sake; disagreement as treason; fear of difference; appeal to a frustrated middle class; obsession with a plot; the enemy as both too strong and too weak; life as permanent war; contempt for the weak; cult of heroic death; machismo; selective populism; impoverished language ("Newspeak").
- Jason Stanley, *How Fascism Works* (2018). Not re-read. Feature names, in our words: mythic past; propaganda; anti-intellectualism; unreality; hierarchy; victimhood; law and order; sexual anxiety; appeals to the heartland; dismantling of public welfare and unity.
- Context only: the Institut fuer Zeitgeschichte critical edition is the scholarly standard for reading that 1925 book critically: Hartmann, Vordermayer, Ploeckinger, Toeppel (eds.), *Hitler, Mein Kampf. Eine kritische Edition*, Institut fuer Zeitgeschichte, Munich 2016, 2 vols. Confirmed by web search (bpb.de; epub.ub.uni-muenchen.de). Cited, not quoted. This repo quotes no fascist text.

## 2. Mappings

| Source | Reading | Structure | Label |
|---|---|---|---|
| Beauvoir, *Pour une morale de l'ambiguite* (1947): the serious man; oppression | Reciprocity is symmetry (B axiom, already checked in `frames_sync.ath`). Fascism refuses reciprocity: one class reaches all and is reached by none. | On every Kripke frame on 2..4 worlds (66064 frames, 2100 such classes), B fails at every member of that class. | checked-finite (fact); the link is analogy |
| Deleuze and Guattari, *L'Anti-Oedipe* (1972); Foucault, preface "Anti-Oedipus: Introduction to the Non-Fascist Life" (1977) | Microfascism: desire organised around one centre. The rhizome has no critical part; the tree has only critical parts. | Joins `philosophy/rhizome.py` (every edge critical iff tree). New: a connected graph whose edges all touch one vertex and are all critical is exactly the star (18 stars, 3..6 vertices, every graph checked). The single critical centre is the formal shape they warn about. | checked-finite (fact); the link is analogy |
| Fisher, *Capitalist Realism* (2009) | "No alternative" as an absorbing class. | `transit/social.py` part a: absorption into closed classes with probability 1. | analogy (reading); open in frames |
| Lacan, paranoia | Eco's obsession with a plot: all meaning anchored to one persecuting master signifier. | none | analogy (reading); open |
| Grok incidents, 2025 (NPR 2025-07-09; TechCrunch 2025-05-14, 2025-07-12; relayed, not re-read) | Topic intrusion as aberrant salience (Kapur 2003, already cited) and as obsession with a plot. Removing a filter as removed reality testing. One upstream change as a single critical part (cf. the star fact). | none | analogy (reading); open |

## 3. Detector (tested, crude)

`antifascism.py` part C. Each feature has a small regex marker set, written openly in the file. The score is the number of markers hit per feature.

It is a crude keyword measure. It flags text for a person to review. It is never a verdict on a person or a group. It is never labelled checked.

Measured on 20 synthetic sentences written for this file (10 flag-worthy, 10 neutral; placeholders like "group X"; no real quotes, no real groups):

- TP 10, FP 1, FN 0, TN 9.
- Precision 0.91. Recall 1.00. False-positive rate 0.10.
- The false positive: "Weeds must be eliminated from the garden in spring." Keyword matching cannot see context.
- Recall on 10 sentences written by the same author as the markers is optimistic. Expect worse on real text.

Run on the repo: 0 of 429 records in `center/shards/*.jsonl` flagged; 0 of 76 strings in `compute/monqwensor/proposals.json` flagged. Expected near zero. The record count grows as frames are written.

## 4. Open

- Fisher, Lacan and Grok mappings have no checked structure.
- The detector has no held-out set and no real-text evaluation.
