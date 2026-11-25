# Language families as trees

`families.py` checks the shape of a coarse Indo-European family tree: one root, a tree (each language has one parent), 24 edges for 25 nodes, every language reachable from the root. It passes.

**The data is from memory.** Glottolog and Wiktionary are not reachable from this container, so the branches are typed in and cited from memory. The checks are about shape. They say nothing about whether a branch is right. A real data pull is needed before any branch is treated as a finding.

**Reading.** An etymology is a path back toward a root. A family is then a tree, and "no one alone" (the household check) applies to cognates: a word with no relative in any branch would be an isolate. That is analogy until the cognate data is pulled.

**Next.**
1. Pull a family list from a source this container can reach, or from a file added to the repo.
2. Add cognate edges (for example, the word for "mother") and check that they stay inside the tree.
