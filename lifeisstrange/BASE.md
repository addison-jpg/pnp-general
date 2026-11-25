# *Life is Strange* as a formal base: literature first

Sources: *Life is Strange* (Dontnod, 2015) and its prequel *Before the Storm* (Deck Nine, 2017), cited in my own words; no script is reproduced. Video games are read here as literature. That is an established position: Espen Aarseth's *Cybertext* (1997) calls works like these ergodic literature, texts where the reader's choices are part of the work. Labels as elsewhere: **join** (a repository theorem covers it), **analogy**, **open**.

## 1. Max: the doomed-history problem

Max can rewind and replay, and she discards every history that goes wrong. That is Homestuck's "million dead Daves" from the inside: one agent running the search, remembering the failed branches, and keeping one. See `homestuck/BASE.md` §1.

- **Join:** the surviving history as a consistent fixed point (`CtcReset.lean`, `L169.lean`), and failed branches as lost futures (`Fisher.lean`, `lost_mono`).
- **The ending's forced cut** (the town or Chloe) is a branching frame with exactly one surviving future. Every rewind reaches the same fork, which is a fixed point the search cannot avoid. Analogy, with an open edge: state "every rewind path reaches the same binary fork" as reachability on a small branching model, and check it by exhaustion.

## 2. Chloe: argument without rewind

In *Before the Storm*, Chloe has no time power. Her power is argument: dialogue contests won or lost in real time, with no undo.

- **Formal home:** abstract argumentation frameworks (Dung, *Artificial Intelligence* 77, 1995). Arguments are nodes and attacks are edges; the accepted positions are the extensions (grounded, preferred, stable). A dialogue contest is a game played on such a graph. This is a real and well-studied structure. Open: encode one cited contest as an attack graph, compute its extensions (`checked-finite`).
- **The pair:** Max searches over histories, and Chloe argues within one. Rewinding against arguing is the same contrast as the original game against the prequel. A tree with undo, against a single irreversible line.

## 3. Arcadia Bay and the Prescotts

- **The town:** a closed community seen as hostile by the outsiders inside it. That is the Barrès–Beauvoir "barbarians" (`philosophy/`): the self defined against others who seem to threaten it. Analogy.
- **The Prescotts:** one family's wealth shapes the town's institutions and what futures seem possible there. Fisher's capitalist realism (`Fisher.lean`, `no_alternative_of_all_reachable`, a general order fact) is the matching reading: from inside, no alternative appears reachable. Analogy.

## 4. What this adds

The two games are one relationship seen under two time structures: with rewind and without. That is the tree-against-line contrast, and with the DAG correction (`DAG.lean`) it becomes a progression of time models a reader can feel. The formal readings take the work's structures seriously; they do not reduce it.

## Open

1. One cited dialogue contest as an argumentation framework, with its extensions computed (`checked-finite`).
2. The forced-fork claim as reachability on a small branching model.
3. Game-studies sources with read status (Aarseth; others only once found and opened).
