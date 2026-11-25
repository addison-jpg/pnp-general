# queer

Addison: critical transgender theory is a cheap add and fits with love queerness. Radically destroying any consideration of categorical difference between sex and gender could really help.
This folder takes that as a test. Remove the two sides from the love model, count what breaks, then read the theory beside the count.
Run `python3 -I culture/queer/roommates.py`, `python3 -I culture/queer/traits.py`, or `bin/asteroid --no-lean culture/queer/queer.ath`.

Labels: checked-finite (exact, every case in a stated bound), tested, analogy (a reading), open.
Citations are cited from memory; none were re-read here.
This models stated rankings and toy counts. It says nothing about any person and denies no one's identity.

## Small: what the code shows

**Roommates** (`roommates.py`, checked-finite). Drop the two sides. n people each rank all the others. A matching pairs some of them.
A pair blocks when each prefers the other to their current state. Every profile, nothing sampled:

| n | profiles | no stable matching | unique stable matching | most stable on one profile |
|---|---|---|---|---|
| 2 | 1 | 0 | 1 | 1 |
| 3 | 8 | 2 | 6 | 1 |
| 4 | 1296 | 48 | 1098 | 2 |

n=5 has 7.96 million profiles and n=6 has 2.99e12 (120^6). Neither is run. n=6 is far over 20 s in Python.
The smallest failing profile is three people in a cycle: 0 prefers 1 to 2, 1 prefers 2 to 0, 2 prefers 0 to 1.
Every matching on them is blocked by someone. The two-sided model has a stable matching on all 46656 profiles at n=3 per side
(the functions of `culture/love/check.py`, imported). Gale and Shapley (1962) gave a roommates instance with no stable matching.
Irving (1985) gave an algorithm that finds one or says there is none. Both cited from memory.

**Traits** (`traits.py`, checked-finite on the counts and on the grid). Fausto-Sterling, *Sexing the Body* (2000), treats sex as several traits.
Here each trait has two values, for counting only. With k traits there are 2^k combinations and 2 are aligned.
For k = 1..6 the others are 0, 2, 6, 14, 30, 62. One trait labels differently from another on exactly 2^(k-1) combinations.
Then the FIELDS.md move: each trait in [0,1]. The binary is two corners of the cube. On the grid of quarters (k <= 4: 25, 125, 625 points)
no threshold on one trait gives the classification of another, and the mean of the traits matches no single trait.
At the corners the cube agrees with the count. What survives the extension: the traits can disagree.
What does not: any one trait standing in for the others.
This is exact on that grid only. All of [0,1] would need a proof; none is claimed.

**Prevalence, not chosen.** Blackless et al. (2000; Fausto-Sterling is one of six authors) put intersex variation at about 1.7%, a broad definition: any departure from the typical male or female body.
Sax (2002) put it at about 0.018%, a narrow one: chromosomal, gonadal or hormonal discordance only. Both cited from memory.
Sax argues the gap is which variations count. That is his claim, and others dispute where the line falls.
Nothing here settles it, and nothing here depends on it.

## Middle: the theory

- Butler, *Gender Trouble* (1990). Sex is constructed as gender, so sex/gender is not a categorical distinction.
- Stryker, "My Words to Victor Frankenstein Above the Village of Chamounix" (1994), and *Transgender History* (2008).
  Trans people speak for themselves against a story written about them.
- Stone, "The Empire Strikes Back: A Posttranssexual Manifesto" (written 1987, published 1991). Trans people as authors of their own accounts, not as case histories.
- Serano, *Whipping Girl* (2007). Trans women and the way femininity is demeaned.
- Sedgwick, *Epistemology of the Closet* (1990). Much of modern knowledge is organised around the hetero/homo binary.

All cited from memory. One short summary each is not the book.

## Big: the readings (analogy)

1. The love model's two sides are the binary built into the mathematics. Removing it is the roommates problem. (analogy)
2. The exact consequence is small and checked: stability can fail. 2 of 8 profiles at n=3, 48 of 1296 at n=4.
   Checked: stability fails once the sides are removed, and held on every n=3 two-sided profile. Not checked: that the sides caused the guarantee,
   or that they stand for sex or gender. That link is a reading (analogy), and it says nothing about people.
3. Destroying the categorical difference is not a loss to avoid. It is a design change. The new model has to be built on something else.
   Reciprocity is the candidate (Beauvoir, *The Second Sex*, 1949, cited from memory): a blocking pair already needs both people, with no side.
   A new guarantee for that model is not found here. (open)
4. Links.
   Quadrants (`culture/homestuck/quadrants/check.py`): the trolls' relations are not sexed. They label a tie between any two, a signed graph with no sides.
   Love (`culture/love`): k=1 and k=2 are the two-sided case. Roommates is the same rule with the sides taken out.
   Race (`culture/race`): intersectionality margins. A joint table is not fixed by its margins; several traits are not fixed by one label. The same shape in the cube. (analogy)

## Open

- A stability notion for roommates that always exists (for example, fractional or with a few unmatched allowed to be unblocked). Not tried.
- n=5 exhaustively, natively, as `culture/love` does for n=4.
- Whether the theory above wants this count at all. The count is a tool, not an argument for any person's identity, which needs none.
