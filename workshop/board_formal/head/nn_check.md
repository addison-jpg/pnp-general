# Nearest-neighbour check on static rows (no training)

Question fixed in advance: do the board's label words sit nearer each other than to other words in the static embedding rows?

Data: `math/qwen/semantic_rows.json` and `workshop/route/memory_vectors.json`, 896 dimensions, cosine similarity.

Result:
- 37 usable rows. 10 entries are empty (vector null), including `refuted` and `checked-finite`, two of the board's six labels.
- Label words present with vectors: `checked`, `open`, `tested`, plus `claim`, `check`, `frame`, `record`, which are asteroid statement words and not board labels.
- 7 label rows; 3 of them have a label row as nearest neighbour.
- Chance level, assuming uniform neighbours: 7 × 6/36, about 1.2. So 3 is above chance, but n is too small for any significance claim.

Label: exploratory, not checked. Not a result about the board.

Limits:
- Board labels `refuted`, `checked-finite` and `analogy` have no usable rows, so the test cannot run on the board's own label set.
- The label set was chosen after seeing the data.
- Static token rows, not contextual meanings.

Next step, only if justified: fill the missing rows from the embedding tensor, fix the label set in advance, and run with a pre-declared threshold.
