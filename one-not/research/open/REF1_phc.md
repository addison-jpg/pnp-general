# REF1: a refuter sweep on PHC (Lemma D), on git-compute

Seat REF1 (Sonnet), 2026-11-25. Serves: flagship-payment-hall, open-one-not (BottomPay), open-many-not (PHC@0).
Words: **tested** = computed by `REF1_phc.py`. Nothing here proves PHC, BottomPay, the point lemma or `no_minCE`,
and nothing bears on P versus NP.

## Result: no violation of Lemma D's inequality in 2.3 million instances (word: tested)

The check, per instance: slack(J) = |E ∖ J| − Σ_w (c_w(J) − 1) for payer sets J (F1_phc.md, Lemma D); a violation is any
J with slack < 0, including J = E (per-set connectivity). Exhaustive over the useful payers when there are at most 14;
otherwise every deletion set R = E ∖ J with |R| ≤ 3 plus 60 hill-climbing restarts that start from random J and
move by single payers (these find J that cut one set, as F1 says every tight block does). Checker validated first:
1,500 random instances (1,159 with PHC false), 0 disagreements with U1's matroid partition (`--selftest`).

Instance families (`REF1_phc.py`):
* **stored**: BottomPay at DD states (>= 2 DD sets) of the stored one-NOT circuits (n <= 12; Q = D = empty, single
  points, and sampled mixed states; exhaustive over states when 3^n <= 2200).
* **sys**: fresh correct one-NOT switch circuits (checked correct) on linear set systems: Fano, Pasch, 3x3 and 3x4
  grids, K4 edges, 5- and 6-cycles, a 4-cycle of triples, a mixed 2/3-set cycle; BottomPay at sampled DD states.
* **rand**: the same on random systems with pairwise |S_a ∩ S_b| <= 1 (n 6..11, 2..4-sets).
* **prog**: two-set point programs (B9 SAT encoding), shared and disjoint, sizes (2,4) (2,6) (3,3) (3,4) (3,5)
  (3,6) (4,4) (4,5) (5,5), at base, base + 1, base + 2 lines, random phases and blocking clauses; PHC@0.

| run | instances (distinct, after de-duplication) | stored | sys | rand | prog | violations |
|---|---:|---:|---:|---:|---:|---:|
| local sample, 1 core under `nice` (budgets 90-300 s per shard) | 226,712 | 7,042 | 59,718 | 16,435 | 143,517 | 0 |
| compute job, spec `workshop/compute/specs/ref1_phc.json`, 20 shards, run 45536681420, shards 258-650 s | **2,305,227** | 7,344 | 436,772 | 117,127 | 1,743,984 | **0** |

In the compute job: 1,163,351 BottomPay DD states visited; 2,285,122 instances checked exhaustively, 20,105 by the
targeted search (more than 14 useful payers); no shard stopped on its time budget. Results were read from the shard
logs (`SUMMARY` lines); artifact downloads are blocked.

**Tightest slack.** The smallest slack over nonempty R was **0** in 1,826,475 instances and 1 in the other 478,752
(none lower, none negative anywhere). Slack 0 at R ≠ empty is real tightness; for example the 3x4 grid circuits
(`sys:grid34`, up to 23-24 useful payers, 24 tight deletion sets). Hence the bound is sharp in all four families and
is met without violation.

**What this does not cover.** The `sys` and `rand` circuits are one construction (a NOT switch on an OR of ANDs),
so their DD states have one NOT wire h; they are not arbitrary correct one-NOT circuits. Instances with more than
14 useful payers are searched, not exhausted. The `prog` instances are sampled solutions, not all of them, except
the small cases F1 enumerated. States are sampled for n > 7.

## Seed file for the next search

`REF1_phc.py --topk K --seeds FILE` writes the K tightest instances (smallest slack, then most useful payers, then
most tight R), each as `{slack, family, useful_payers, tight_R, info, instance {E, cls, hyp}, sha256}`; the same records
are appended as `{"SEED": ...}` lines to the shard output. `REF1_seeds.json` holds the top 20 of the local sample
(all slack 0, 3x4 grid circuits). `--recheck FILE.json` re-evaluates a saved instance with U1's partition and A14's Edmonds
partition, and prints c_w(J) for the stored R, so a violation would be rechecked independently.

## Reproduce

    nice python3 -I one-not/research/open/REF1_phc.py --selftest
    nice python3 -I one-not/research/open/REF1_phc.py --shard 1 --of 400 --budget 60 --out /dev/null
    gh api -X POST repos/addison-jpg/pnp-general/actions/workflows/compute.yml/dispatches -f ref=main -f 'inputs[spec]=workshop/compute/specs/ref1_phc.json'
