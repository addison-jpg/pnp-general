# The zodiac, as a subfield: structure, history, astronomy

Labels as everywhere else: **fact** (astronomy, history, mathematics that holds), **structure** (a formal object worth counting), **belief** (astrology, recorded as a cultural system, with its evidence stated plainly).

## 1. The structure

- The zodiac is a cyclic group: twelve signs, each 30° of the ecliptic, i.e. ℤ/12. Classical astrology overlays more structure on it: four elements (ℤ/12 → ℤ/4), three modalities (ℤ/12 → ℤ/3), and polarity (ℤ/12 → ℤ/2). By the Chinese remainder theorem ℤ/12 ≅ ℤ/4 × ℤ/3, so element and modality together determine the sign. Structure, checkable by exhaustion.
- *Homestuck*'s troll zodiac (its blood-colour spectrum and its sign system) is a further layer on the same twelve. Mapping it "infinitely" means a family of refinements (each sign split into more), i.e. an inverse system of cyclic groups ℤ/12 ← ℤ/24 ← … whose limit is a profinite group. Structure; the comic's own sign tables are to be cited, not reproduced.

## 2. Astronomy (fact)

- The signs are named after constellations on the ecliptic, but because of the precession of the equinoxes (one cycle in about 25,800 years) the tropical signs have drifted by roughly one sign against the constellations since the system was fixed in antiquity.
- Astronomy reaches quantum gravity directly: black holes (Hawking radiation, the information problem), cosmology (inflation, the cosmological constant) and gravitational waves are where gravity and quantum theory meet. This repository's quantum-gravity results (Haar counting, unitary complexity, CTCs) belong to the complexity side of that story. The zodiac does not; it is the ecliptic coordinate system.

## 3. History and religion (fact, with the belief labelled)

- The zodiac comes from Babylonian astronomy (about the 5th century BCE) and passed through Greek and Hellenistic astrology (Ptolemy's *Tetrabiblos*, Greek original) into the Roman, Islamic and Christian worlds.
- Christianity's relation to it is mixed. Early Christian writers often condemned astrology (Augustine, *Confessions* IV and VII, Latin original). Yet the zodiac persisted in church art and calendars, and in folk practice and pagan revivals.
- A real piece of mathematics sits right at the join: the **computus**, the algorithm for the date of Easter. It combines a solar and a lunar cycle with modular arithmetic (the Metonic 19-year cycle, Gauss's 1800 formula). A counted, checkable object.
- **Astrology as belief:** controlled tests have not found predictive power. Carlson's double-blind test (*Nature*, 1985) is the standard one. It is recorded here as a cultural and historical system, not as science.

## Open, in order of value

1. Check by exhaustion that element × modality determines the sign (ℤ/12 ≅ ℤ/4 × ℤ/3), as `checked-finite` with a runner.
2. Implement the Gregorian computus and check it against a published table of Easter dates, as `checked-finite` over a span of years. A real algorithm with a known answer.
3. The precession drift as a computed offset per century, from the IAU precession rate.
