# Clusters: .ath members that hold data gathered by public tools

A cluster is a folder. Each member is a small `.ath` file that makes claims about one data file. The data file is JSON, written by whoever gathered it (a search, a fetch, or a person), and it records the URL of each item. Asteroid checks only what is written in the `.ath` file. It does not fetch anything, and it does not call any tool. The public-tool step is separate and comes before the check.

## Rules

1. Every data item has a URL. An item without one is not counted.
2. Every member's claims are integers or exact sets, checked by `bin/asteroid --no-lean`.
3. A count that a member gets wrong is reported false, not patched.
4. The root `cluster.ath` asks each member a fixed question, so the cluster can be read without opening every file.

## Members

- `kalshi_sources.ath`: counts of sources in the Kalshi review, from `workshop/kalshi_review/` (A.md, B.md, C.md). Checks the totals as written in those files.
