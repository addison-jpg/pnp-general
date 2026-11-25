# Privacy as counting: k-anonymity, uniques, randomized response

What this is: three privacy definitions, checked by exact counting on small **synthetic** tables that `check.py` generates. What this is not: a privacy guarantee for any real release, or a method for any real system. Labels: **fact** (cited), **checked-finite** (exact, exhaustive over a stated finite set, rerunnable), **tested**, **join** (same object as a repo file), **analogy**, **open**. Every number below was printed and asserted by `check.py` (`python3 -I privacy/check.py`, about 3 seconds, Fraction arithmetic).

## The object

A **table** is a list of rows, one per person. A **quasi-identifier** is an attribute that is not a name but can help single someone out (for example a birth date). Here each row has two quasi-identifiers, each with values 0..3.

## 1. k-anonymity

A table is **k-anonymous** if every row matches at least k − 1 other rows on its quasi-identifiers (Sweeney 2002; Samarati 2001; fact). The **largest k** of a table is the size of its smallest group of equal rows.

**Generalization** makes a value coarser. Per attribute there are three levels: 0 exact, 1 pairs {0,1}/{2,3}, 2 suppressed (`*`). The two attributes give a 3 × 3 **lattice** of nine nodes, ordered levelwise. **Height** is the sum of the two levels.

Checked-finite, over all 16^4 = 65536 tables of 4 rows:

- Largest k is 1, 2 or 4, never 3. Counts: k=4: 16 (all rows equal); k=2: 720 = C(16,2)·C(4,2); k=1: 64800.
- Generalizing never lowers k (every pair of comparable lattice nodes, every table).
- Least generalization reaching k = 2: a breadth-first search by height returns exactly the set of minimum-height nodes found by brute force over all nine nodes, for every table. Each node it returns is also minimal in the lattice order.
- Tables by least height reaching k = 2, h = 0..4: 736, 4064, 18368, 25984, 16384. (A first guess of 13984, 26368 for h = 2, 3 was wrong; the listed values are computed.)
- 5088 tables have two tied least nodes; none have three.

## 2. Re-identification as counting

Draw n people's values uniformly from a domain of size D. A **unique** is a person no one else shares a value with. The expected number of uniques is n (1 − 1/D)^(n−1) (each person is unique when the other n − 1 all miss its value).

- Checked-finite: the exact distribution of the number of uniques, by listing all D^n assignments, gives exactly this mean for all 30 pairs with n ≤ 6, D ≤ 5, D^n ≤ 20000.
- Example n = 4, D = 3: P(0 uniques) = 7/27, P(1) = 8/27, P(2) = 4/9, mean 32/27.
- Fact: Sweeney reported that 5-digit ZIP, sex and date of birth likely single out most of the US population (2000 working paper "Simple Demographics Often Identify People Uniquely"; search result only). The same paper reports {county, sex, birth date} likely unique for 18% (search result only). Golle 2006 revisited this with 2000 census data. He found ZIP, sex and full birth date unique for about 63%, fewer than Sweeney's figure (abstract only). Their other numbers are not repeated here.

## 3. Differential privacy: randomized response

A mechanism M is **ε-differentially private** if for any two **neighbouring** databases x, x′ (they differ in one person's entry) and any output o, P[M(x) = o] ≤ e^ε P[M(x′) = o] (Dwork, McSherry, Nissim, Smith 2006; fact). The **privacy loss** is the largest such ratio, so e^ε is a rational number here.

**Randomized response**: each person holds one bit and reports it truthfully with probability p, flipped otherwise.

- Checked-finite, all 98 ordered neighbouring pairs of bit databases with 1 ≤ n ≤ 4, every output: the largest ratio is exactly p/(1 − p): 3 for p = 3/4, 2 for p = 2/3, 1 for p = 1/2.
- **Sequential composition** (run two mechanisms on the same data, release both): the largest ratio is the product. Checked-finite for n ≤ 3: the same p twice gives 9, 4, 1; p = 3/4 then p = 2/3 gives 6. In ε terms, losses add, and the bound is reached here.

## 4. Joins

The equality pattern of n rows (which rows are identical) is a **set partition** of the rows. Its count is the Bell number: 1, 2, 5, 15, 52, 203, 877, 4140 for n = 1..8 (checked-finite, by listing). Partitions with k blocks are counted by Stirling numbers S(n,k), e.g. S(5,·) = 1, 15, 25, 10, 1 (checked-finite). The identity Σ_k S(n,k) D(D−1)…(D−k+1) = D^n holds for n ≤ 6, D ≤ 5 (checked-finite). Uniques are the singleton blocks; counting them through partitions agrees with section 2's direct enumeration for (n, D) = (4,3), (5,3), (4,4) (checked-finite). Largest k in section 1 is the smallest block size.

Join with compbio/ or brain/: none. No file there uses Bell or Stirling numbers. The sequences are in `privacy/fingerprints.json`.

## 5. Open items and limits

- All of this models definitions on synthetic data. It is not a privacy guarantee for any real release.
- k-anonymity says nothing about attribute disclosure (a group sharing one sensitive value); not modelled. Open.
- Only uniform values in section 2; real attributes are not uniform. Open.
- Only randomized response and only pure ε; no Laplace mechanism, no δ, no adaptive composition. Open.
- Lattice is one fixed 3-level hierarchy per attribute, two attributes, 4 rows. Larger cases are open.

## Sources

- Sweeney, L. (2002). k-Anonymity: a model for protecting privacy. Int. J. Uncertainty, Fuzziness and Knowledge-Based Systems 10(5), 557–570. Search result only; volume, issue and pages confirmed by WebSearch.
- Samarati, P. (2001). Protecting respondents' identities in microdata release. IEEE TKDE 13(6), 1010–1027. Search result only; details confirmed by WebSearch (DBLP record).
- Golle, P. (2006). Revisiting the uniqueness of simple demographics in the US population. Abstract only; title, year and 63% finding confirmed by WebSearch. Venue WPES '06 is from memory, not confirmed.
- Sweeney, L. (2000). Simple demographics often identify people uniquely. Carnegie Mellon Data Privacy Working Paper 3. Search result only; the 18% county figure confirmed by WebSearch.
- Dwork, C., McSherry, F., Nissim, K., Smith, A. (2006). Calibrating noise to sensitivity in private data analysis. TCC 2006, LNCS 3876, 265–284. Search result only; venue, volume and pages confirmed by WebSearch.
