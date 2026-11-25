# Homestuck as a formal base

Source: Andrew Hussie, *Homestuck* (2009–2016), cited by act and in my own words; no text is reproduced. A note on lineage: asteroid takes its name, logo and fonts from Homestuck (Terezi and Vriska); its mathematics is circuits, not the comic. What follows treats the comic's mechanics as formal structures and says which of them join this repository's checked work. Three labels as everywhere else: **join** (a theorem in the repository already covers it), **analogy**, **open**.

## 0. Reading it as literature

*Homestuck* is a serious work of literature and is read here as one: a long multimodal narrative (prose, dialogue logs, animation, music, interactive pages) whose formal experiments are part of its meaning. It belongs to a lineage of time-loop and recursive fiction, and it is a work about growing up through fixed fates, about grief and doomed selves, and about authors who are characters (Hussie appears inside the story; Caliborn and Lord English contest who writes it).

The formal readings below take its structures seriously as structures. They are not a substitute for literary criticism, and they do not reduce the work to its mechanics. Open: a literature row for every scholarly source on *Homestuck* (studies of webcomics, multimodal and interactive narrative, fan culture), each with its read status, added only once actually found and opened. None is cited here, to avoid inventing references.

## 1. The time mechanic: one consistent history among doomed ones

In the work, there is one *alpha* timeline. Any branch that cannot be made consistent with it becomes *doomed* and ends. Time players (Dave, Aradia) can loop back; their loops must close consistently, and many copies of a time player die on doomed branches. That is the "million dead Daves".

- **Join: CTC consistency.** "Only self-consistent histories survive" is Deutsch's consistency condition on closed timelike curves, which this repository already proves things about. `L169.lean` (P_CTC ⊆ EXP) and `CtcReset.lean` (a reset machine's consistent distributions sit on its start cycle) say that the surviving history is a fixed point of the time-step map, and that finding it takes at most exponential time. The comic's alpha timeline is the fixed point, and the doomed timelines are the iterates that do not land on it.
- **Join: lost futures.** Doomed branches are Fisher.lean's lost futures in a branching frame (`lost_mono`: once lost, a future stays lost). DAG.lean's correction applies too: where branches can rejoin (the comic's retcon in Act 6), loss is no longer permanent (`lost_forever_iff_clash`).
- **Analogy: the dead Daves as brute-force search.** Every doomed Dave is a candidate history that was tried and failed the consistency check. That is the shape of a swarm of agents running the same task, most of whose runs get discarded. The comparison holds at the level of the search loop. It does not say the comic's selection is efficient: by L169, consistency is reachable in exponential time in general.

## 2. Characters as relations

- **Terezi (Seer of Mind)** sees the consequences of choices: a lookahead over the branching frame. Formal reading: evaluating each branch's future before choosing. Analogy.
- **Vriska (Thief of Light)** manipulates luck: she reweights the probability of branches. Formal reading: changing the distribution over histories, which Deutsch consistency then has to accommodate. Analogy.
- **Dave and Aradia (time players)** are the agents who create loops. Their loops are the CTC register in L169's model. Join, through section 1.
- **Relations among characters across time**: who meets whom, and which version, forms a directed graph whose edges carry timeline labels. Consistency requires every loop in it to close. Open: encode a small, concrete arc (with the act cited) as such a graph and run the consistency check.

## 3. The game's mythology

- **Sburb / Sgrub**, the game, is a fixed set of rules, and each session either reaches its goal (a universe) or fails (a void or dead session). Formal reading: a finite-state game with a terminal win condition; a dead session is a run that cannot reach it. Analogy, with an open edge: state the win condition as reachability and count winning runs on a toy session.
- **Jack Noir** breaks the game by gaining power outside its intended rules. Formal reading: a transition the specification did not allow, a soundness failure of the game. It is the same failure `eval_sound` rules out for asteroid's evaluator. Analogy.
- **Caliborn, becoming Lord English**, is an entity that cannot be defeated from inside the narrative; he has to be handled from outside it. Formal reading: Lawvere's diagonal (`lateral/`). A system cannot contain a total judge of itself, so the answer has to come from outside. Analogy; `lateral/README.md` holds the theorem it rhymes with.
- **Alchemy** is already here as a counted model: `alchemy.py` and `../alchemy.ath` (sharing gives gates 4 < base 5 when items overlap in two base items).

## 4. Philosophy, through the existing files

- **Fisher:** hauntology is doomed timelines haunting the alpha one. The comic stages it literally (ghosts of doomed selves in the dream bubbles).
- **Beauvoir:** each player is defined through the others (teams, relationships across sessions), and freedom is exercised in a situation fixed by the game.
- **Camus:** a game whose rules cannot be escaped, played anyway.

Analogies, all; `philosophy/REVIEW.md` sets the standard for not selling them as theorems.

## 5. The meteor: a vessel between universes

In Act 6 the trolls cross from their session to the kids' session on a meteor, a three-year trip. In canon it is a meteor, not an asteroid. It is the one object that keeps working across the boundary between two universes: it carries players and memory, and the game's rules still hold inside it.

- **Formal reading: transport.** A vessel between worlds is a structure-preserving map between two models. It carries a fact proved in one world into another, provided both worlds share the structure the fact depends on. Analogy, with real instances below.
- **Join:** the neuron and phylogenetics match (`brain/neuron/check.py`) is such a crossing: the count (2n − 3)!! and the two growth models carry exactly from one field to the other, and the check confirms the cargo arrives intact.
- **Between foundations:** every check here lives in one universe of mathematics (Lean's classical axioms). A result whose proof uses no axiom of choice (`#print axioms` shows it) also holds in constructive mathematics; those results are the ones that make the crossing. Open: list them.

## Open, in order of value

1. Encode one cited arc's loops as a timeline-labelled graph, and check closure (`checked-finite` with a runner).
2. A toy Sburb session as a finite game: count the winning runs by exhaustion.
3. Make the CTC join explicit: state the alpha timeline as a fixed point in the terms of `CtcReset.lean` (paper first, Lean last).
4. List the Lean results whose axioms exclude `Classical.choice`: the results that carry across to constructive mathematics.
