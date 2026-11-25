# Meaning as a continuous field: the semantics lineage, without recomputing

Addison, 2026-11-25: universal love "needs to be considered in tandem with open weights on qwens ... if each open weight can have a continuous semantic vector, that's a game changer. ... there isn't a point in recomputing. we have to look at existing semantics research from early computer scientists. the simple simple coding languages." This file collects that lineage and says how it fits. **Read status:** Steinmetz was checked against OpenAlex metadata; everything else is cited from memory. Readings are analogy.

## Meaning has been a vector for seventy years

| who, when | the idea | here |
|---|---|---|
| J. R. Firth, 1957 | "You shall know a word by the company it keeps": meaning is distribution | the centre store: a finding's meaning is the records it cites and is cited by |
| C. Osgood, G. Suci, P. Tannenbaum, *The Measurement of Meaning*, 1957 | the semantic differential: meaning has three main continuous axes, evaluation (good to bad), potency (strong to weak), activity (active to passive) | the smallest continuous semantic vector: three numbers. A love or quadrant relation could carry one |
| H. P. Luhn, 1957 | statistical indexing of text by word frequency | the tag tables of `ask.py` |
| G. Salton and colleagues, the vector space model (SMART; 1975) | documents and queries as vectors; relevance as the angle between them | `ask` with a continuous score instead of exact words |
| S. Deerwester and colleagues, latent semantic analysis, 1990 | a low-rank space under the word counts | the joins: two pillars meet where their sequences coincide |
| T. Mikolov and colleagues, word2vec, 2013 | dense learned vectors; analogies as differences | open-weight models (Qwen) carry such vectors in every layer |

**The fit with `core/ontology/FIELDS.md`:** words, tags and labels are corners; a semantic vector is the continuous field that agrees with them at the corners. Which properties survive the extension is the question to check, not to assume.

**No recomputing needed for the reading:** an open-weight model's hidden states already give each phrase a vector. Using them is reading off existing weights, not training. What is checked is only what is computed exactly on top (for example, whether two pillars' terms are nearer each other than chance), and that is open.

## The simple simple coding languages

| who, when | the language | why it matters here |
|---|---|---|
| J. McCarthy, LISP, 1960 | a whole language from a handful of primitives and one evaluator | `asteroid/AST_CORE.md`: a small core, everything else in `.ath` |
| P. Landin, "The Next 700 Programming Languages", 1966 | a family of languages from one small core (ISWIM) | `ast` and `asteroid`: one core, two exes |
| J. Weizenbaum, ELIZA, 1966 | conversation from pattern matching and templates, nothing more | `ask.py` stage 1: controlled English, matched exactly |
| T. Winograd, SHRDLU, 1972 | language understood inside a small, closed world | every check here: a small closed world, exhausted |

## Steinmetz: matching without an exact match

Erik S. Steinmetz (Augsburg University), *Computer Go and Monte Carlo Tree Search: Opening Book and Parallel Solutions*, PhD dissertation, University of Minnesota, 2016 (advisor Maria Gini; OpenAlex metadata, abstract not available). With Gini: "Mining expert play to guide Monte Carlo search in the opening moves of Go" (2015), and "More Trees or Larger Trees: Parallelizing Monte Carlo Tree Search", *IEEE Transactions on Games*, 2020, doi:10.1109/tg.2020.3048331 (abstracts read via OpenAlex).

- **Inexact matching.** The opening book matches the current board against *clusters* of expert positions, so it guides search where no exact match exists. Here: match a new question or situation to the nearest recorded one, instead of failing on an exact-word miss. That is what a semantic vector buys.
- **More trees, not larger.** Several independent search trees beat one large tree when time is short. Here: several small independent seats (and the second seat) rather than one large agent. Reading, consistent with the seat tables in `ath_prompt_method.md`.

If the pipeline gets as simple as this (match to the nearest known situation, search a little from there, keep the best of several small trees), feeding the large `ast` is cheap.

## Converging on an art form

Poetry is where exact form and open reading already live together: a sonnet's rhyme scheme is a set partition (checked), its meaning is a reading (open). Every pillar here now has that shape: an exact structure underneath, a labelled reading above. Read that way, the whole repository is a poetics. That is a reading, and the claim of this file.
