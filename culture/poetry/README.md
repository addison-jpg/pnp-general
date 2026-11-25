# Poetry, with a psychoanalytic layer built into the method

A poem is read here as a sequence of lines. Each line ends in a signifier: an end sound or an end word.
Every count below is recomputed by `check.py`, by exhaustion. Nothing is sampled.
No poem is quoted. Forms are described, not reproduced.

Labels, used exactly:
**checked** (a Lean proof; none here), **checked-finite** (exact and exhaustive, run here), **tested** (none here), **refuted**, **analogy** (a reading), **open**, **proposed** (model output).
A reading is never checked.

Files:
- `check.py`: every fact below. `python3 -I culture/poetry/check.py`, standard library, about 8 s. Prints PASS, then a JSON line. Writes `fingerprints.json`.
- `tags.json`: the tags, each with its label. Every tag is agent-made, so marked proposed.
- `../../poetry.ath`: runs the check and makes 12 numeric claims. `bin/asteroid --no-lean poetry.ath`.
- `findings.jsonl`: two board records written by `poetry.ath`. They wait for a second seat.

## 1. Facts about forms (checked-finite)

**F1. Rhyme schemes are set partitions.** Write the first line's rhyme as A, the next new rhyme as B, and so on. That is a restricted growth string. There are Bell(n) of them: 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975 for n = 1..10.

**F2. The sonnet's block profile.** A profile is the multiset of rhyme-class sizes. A profile is counted by n! / (product of size! times product of multiplicity!). This holds for every profile, n ≤ 10.
- 14 lines, 7 rhymes used twice: 135135 schemes (13!!, all enumerated).
- 27 of them keep each rhyme pair inside its quatrain or the final couplet.
- Exactly 1 of those 27 alternates in every quatrain: ABAB CDCD EFEF GG, Shakespeare's form (*Sonnets*, 1609).
- 10395 of the 135135 end on a couplet.
- Petrarch's ABBAABBA CDECDE profile (4, 4, 2, 2, 2) has 1576575 schemes. This number comes from the formula; the formula is enumerated only to n = 10.

**F3. The sestina.** Arnaut Daniel's form (late 12th century). Each new stanza takes the end words of the last in the order: last, first, second last, second, third last, third.
- On 6 words this permutation is one 6-cycle. Its order is 6. No word keeps its place. After six stanzas the order returns.
- The same spiral on n words (Queneau's n-ine) is one n-cycle for n = 1, 2, 3, 5, 6, 9, 11, 14, 18, 23, 26, 29, 30 (all n ≤ 30).
- In that range this list equals: 2n+1 is prime, and 2 has order 2n mod 2n+1, or order n with n odd. Checked for n ≤ 30 only. Beyond that it is a cited characterisation, not read here.
- The spiral has a fixed point exactly when n = 1 mod 3 (n ≤ 30).

**F4. Queneau, *Cent mille milliards de poèmes* (1961).** Ten sonnets; each of the 14 lines can come from any of the ten. That is 10^14 poems. The product rule is enumerated on every case with k, m ≤ 4. The 10^14 is then arithmetic. Every combination keeps the one rhyme scheme, since each line slot's variants share its rhyme.

## 2. The psychoanalytic layer as operations

Each concept is made a precise operation on chains of signifiers. The operation's facts are checked-finite. The psychoanalytic reading of the operation is analogy. Sources are cited from memory and were not re-read in this session.

**P1. Condensation.** Freud, *Die Traumdeutung* (1900), chapter 6: many dream thoughts meet in one image.
- Operation: a map f from k thoughts to m signifiers that is not injective.
- Fact: the kernel of f (which thoughts share a signifier) is a set partition, so it is a rhyme scheme. Maps with a kernel of b blocks number m(m−1)…(m−b+1). Non-injective maps number m^k − m!/(m−k)!. When k > m every map condenses. All maps, k, m ≤ 5.
- Reading (analogy): rhyme is condensation on the axis of sound. Two lines that rhyme are two thoughts sent to one sound.

**P2. Displacement.** Same work: psychic intensity moves from one element to another.
- Operation: a permutation of emphasis weights.
- Fact: the total weight is kept. Total displacement (no element keeps its weight) is a derangement: 0, 1, 2, 9, 44, 265, 1854 for n = 1..7, with D(n) = (n−1)(D(n−1) + D(n−2)).
- The sestina spiral is a total displacement on 6 words.
- Reading (analogy): the sestina displaces every end word in every stanza and loses none.

**P3. Metaphor and metonymy.** Jakobson, "Two Aspects of Language and Two Types of Aphasic Disturbances" (1956). Lacan, "L'instance de la lettre dans l'inconscient" (1957; *Écrits*, 1966).
- Operations: metaphor is substitution inside a paradigm class. Metonymy is contiguity in the chain.
- Fact: over every paradigm partition of up to 4 signifiers and every chain of length ≤ 3, substitution is an equivalence. Its classes number k^L (k classes, length L). Contiguity is symmetric but not transitive; with the reflexive closure it fails from length 3.
- Fact: paradigm partitions, rhyme schemes and equivalence relations have the same count, Bell(n). All 2^(n²) relations on n ≤ 4 points were enumerated; the equivalences are exactly the partitions.
- Reading (analogy): the two axes are two different kinds of relation, not two strengths of one. Bell(n) is also the count of S5 frames in the governance model, fact 1. That match is exact math (both are equivalence relations), not a reading.

**P4. Point de capiton.** Lacan, *Le Séminaire III: Les psychoses* (1955–56); "Subversion du sujet et dialectique du désir" (1960; *Écrits*, 1966). The meaning of a chain is fixed after the fact, at a later signifier.
- Operation: signifiers are codewords, a chain is a bit string, its reading is its parse. The reading of the first signifier is fixed at the first time t where every chain of the same length that agrees up to t has the same first signifier.
- Prefix code {0, 10, 11}: every signifier is fixed the moment it ends.
- Code {0, 01, 11}: every string of length ≤ 12 has at most one parse. It is not a prefix code. Its reversal is a prefix code, so read from the end it is instant.
- For n = 1..12 its chains number 1, 3, 5, 11, 21, … (Jacobsthal, (2^(n+1) + (−1)^n)/3). Those whose first signifier is fixed only after it ends: 0, 1, 4, 8, …, 2048 (2^(n−1) from n = 3). Those fixed only by the very last bit: 2 for each n ≥ 2, namely 0 1…1 and 0 1…1 0.
- Reading (analogy): a chain can be read only from its end. The quilting point is the last signifier.

**P5. Repetition compulsion.** Freud, *Jenseits des Lustprinzips* (1920).
- Operation: a self-map f of a finite set; follow x, f(x), f(f(x)), …
- Fact: every point enters a cycle, with tail + cycle ≤ n. All n^n maps, n ≤ 6. The longest tail is n − 1.
- Pure return, with no tail anywhere: exactly the permutations, n!. The sestina is one of these.
- A refrain is a fixed point. Maps with one: n^n − (n−1)^n (1, 3, 19, 175, 2101, 31031).
- Cyclic points over all maps: the sum over k of n!/(n−k)! · n^(n−k). Idempotent maps: the sum of C(n,k) k^(n−k). Connected maps: 1, 3, 17, 142, 1569, 21576.
- Reading (analogy): in a finite poem return is forced, not chosen. What varies is the tail before it.

**P6. The anchor.** The governance model (scratchpad `governance.md`; Freud, *Das Ich und das Es*, 1923; Lacan, Seminar III) calls a world a an anchor when every world reachable from a sees a back.
- Operation: the reading frame of a scheme. Line i sees line j when j comes later, or when they rhyme (an echo back). Close it reflexively and transitively. This is an S4 frame.
- Fact: over every scheme of n ≤ 8 lines, the anchors are exactly the final cluster (governance fact 5, recomputed here). They are always a suffix of the poem. Schemes whose anchor is the last k lines number Bell(n−k) · A(k), where A(k) counts the partitions that do not split into a prefix and a suffix: 1, 1, 2, 6, 22, 92, 426, 2146.
- Shakespeare: the couplet (lines 13 and 14). Petrarch: the sestet (lines 9 to 14). Terza rima (ABA BCB CDC DED E, Dante's *Commedia*): every line. Unrhymed lines: the last line only.
- Reading (analogy): the closing couplet is the law the sonnet returns to. In terza rima every line governs, as in S5.

## 3. Where the readings fail

- P4 and P6 disagree. In P4 quilting is local: only some chains wait for the end. In P6 the anchor is global. The governance model's own falsifier (section 4 there) asks which one Lacan meant. **Open.**
- P2 treats emphasis as a weight that moves intact. Freud's displacement may change intensity, not only move it. If so, a permutation is too strict. Analogy.
- P1 takes the kernel as the content of condensation. Freud also has composite images that merge features. A map loses that structure. Analogy.
- These are models of form. They say nothing about any poet or any reader's mind. Nothing here is clinical.

## 4. Open

1. The n-ine characterisation for all n: cite and read a proof, or write one in Lean.
2. A Lean `decide` proof of the sestina's order 6, so its label could become checked.
3. Test the anchor model on real rhyme schemes from a public-domain corpus. That would be tested, not checked.
4. A second seat for the two findings in `findings.jsonl`.
