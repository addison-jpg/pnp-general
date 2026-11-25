# Language families as a forest, read critically

`families.py` checks six families as six trees: one root each, one parent per language, no cycles, every node reachable. It passes. It counts 39 nodes, 23 of them Indo-European (59%).

**The data is from memory.** Glottolog and Wiktionary are not reachable from this container. The checks test shape. They say nothing about whether a branch is right.

**Why a forest, not one tree.** An earlier version had a single root. A single root assumes every language descends from one ancestor. That idea comes from 19th-century comparative philology: the reconstruction of Proto-Indo-European (Bopp, Schleicher and others; cited from memory). In that period the family concept was also used in racial theories, the "Aryan" claims in particular, which tied language to race and ranked peoples by it. The tree-shape of a family is not itself racist. The racialised use of it is documented history.

**What the forest still gets wrong.**
- The sample is still 59% Indo-European, which mirrors where the comparative method was built.
- Isolates (Basque here) and families outside Europe are present, but only as a few nodes each. A real list would have hundreds of families, most of them in Africa, Asia, the Americas and the Pacific, and the count would move sharply.
- Choosing which languages enter the tree is itself a choice. The checks cannot see that. The share printed in the count is the only guard, and it only reports.

**Reading.** Non-European languages were often classified by grammars built on Latin and Greek, which made the European languages the norm. A forest with many roots, and a printed count of who is in it, is a small structural way to stop that norm from being silent. That is analogy until a real data pull is checked against it.

**Next.**
1. Pull a full family list from a source this container can reach, or from a file added to the repo.
2. Report the share of each continent's families in the tree, and assert it against the source's own count.
3. Add cognate edges (for example, the word for "mother") and check that they stay inside each family.

## Scaling to all known languages

`forest.py` reads `data/languages.csv` (columns `id,name,parent,region`) and checks any size: unique ids, parents that exist, no cycles, families counted, and a count per region so a sample's bias is printed. With no file it prints NOT CHECKED, never PASS.

Glottolog, Wiktionary, Wikidata, Wikipedia, ISO 639-3 and WALS are not reachable from this container, so the data file is not here. Add one and the same checks run on all of it.
