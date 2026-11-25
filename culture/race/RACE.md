# Race: critical race sociology, small to big

Two exact checks, then readings. Labels: **checked-finite** (exact over a stated finite set), **analogy** (a reading), **open**.
Every source is cited from memory; none was re-read for this file. Run: `bin/asteroid --no-lean culture/race/race.ath`.

## 1. Du Bois: the one-way gaze

W. E. B. Du Bois, *The Souls of Black Folk* (1903; cited from memory). Double consciousness: a sense of always looking at oneself through the eyes of others, a world that looks on in contempt.

- **Checked-finite** (`core/ontology/asymmetry.py`, reused by a check line, no copied logic): every preorder on 1 to 4 worlds (389 of them) is non-symmetric exactly when it maps onto the 2-chain, one world that sees and one that is not seen back.
- **Analogy:** a gaze that goes one way and does not come back is that frame. Double consciousness is living on the seen side while also holding the seer's view. The check says the shape is one shape; it says nothing about what it is like.

## 2. Fanon: the gaze fixes

Frantz Fanon, *Peau noire, masques blancs* (1952; cited from memory). Being looked at as Black fixes a person into an object made of stories told by others.

- **Analogy:** the same 2-chain, now with the seen side handed a mask it did not choose. Not checked.

## 3. Bell and critical race theory: structure without intent

Derrick Bell and others, critical race theory from the 1970s onward (cited from memory). Racism is ordinary, built into law and institutions, not an aberration. Bell's interest-convergence thesis (1980): gains for Black people come when they also serve white interests.

- **Analogy, open:** a structure can produce a racial outcome with no racist intent at any single point. No check here.

## 4. Crenshaw: the joint is not in the margins

Kimberle Crenshaw, "Demarginalizing the Intersection of Race and Sex" (*University of Chicago Legal Forum*, 1989; cited from memory). Courts heard Black women's claims either as race claims or as sex claims, and a claim that lived at the joint fell through both.

- **Checked-finite** (`culture/race/race.py`): over every 2x2 table of nonnegative integers with total N <= 12 (1,820 tables), there are 819 margin classes. 506 of them hold more than one table. The largest holds 7 tables: row and column totals 6 and 6 with N = 12, where the corner cell can be anything from 0 to 6. The Frechet bounds max(0, r + c - N) <= corner <= min(r, c) are exact in every class.
- **Analogy:** a count of "women" and a count of "Black workers" (the margins) does not tell you how many Black women there are (the corner). A firm can hire both women and Black workers and no Black women at all. That is the formal hook, not the whole of Crenshaw's argument.

## 5. Bonilla-Silva: racism without racists

Eduardo Bonilla-Silva, *Racism without Racists* (2003; cited from memory). After the civil-rights era, racial inequality is defended in colour-blind terms: abstract liberalism, naturalisation, cultural racism, minimisation.

- **Analogy:** the margins again. A colour-blind rule looks only at margins and so cannot see the joint where inequality sits. Not checked.

## 6. A case: Anais Nin

Critics and readers have documented racist and exoticizing portrayals in Anais Nin's writing (cited from memory, not re-read here): characters of colour written as closer to nature, the body and sex, as backdrops for white self-discovery, in her erotica and in her diaries. No slur is quoted here.

- **Reading:** this is the primitivist move of section 7, inside a celebrated modernist. It is a reading of texts, not a judgment of a whole person, and the documentation should be re-read before anything stronger is said. **Open.**

## 7. The critique of primitivism

Romanticising "primitive" peoples is a racist move. Marianna Torgovnick, *Gone Primitive* (1990; cited from memory), reads Western modernism's taste for the "primitive" as a fantasy about the self. The "noble savage" and the "savage" are the same gaze with the value flipped: both make living people into a picture of the past.

- **Analogy:** the 2-chain once more. The romantic and the contemptuous viewer both stand on the seeing side.
- **This bears directly on anarcho-primitivism.** A politics that holds up foragers as a lost good life repeats the move unless it listens to living Indigenous people as contemporaries with their own futures. See `philosophy/ANPRIM.md`.

## Limits

- The checks are about tables and relations. That they capture racism is analogy.
- No individual's data is used. Historical persons get readings of their texts, never diagnoses.

## Open

1. Re-read the sources and change their read status.
2. Intersections of more than two attributes: how fast the margin classes grow for 2x2x2 tables.
